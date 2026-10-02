################################################################################
#
#  RieSrf/Periods/Integrand.jl : evaluation of the differentials
#
#  The basis of differentials is omega_k = g_k(x, y) dx with
#  g_k = prod_l factor_l^e(l, k) (differential_form_data: the factors and the
#  exponents). The quadrature evaluates all g_k on all sheets at every node,
#  which is the innermost loop of the period computation. Each embedded factor
#  factor_l(x, y) = sum_j c_{l,j}(x) y^j is stored once as a contiguous block
#  of coefficients; per node the powers of x and of every y_s are computed
#  once, and every c_{l,j}(x) and every factor value is a single acb_dot.
#  The quadrature weight is the initial value of each entry.
#
#  Entry points: DifferentialFactorCache, _evaluate_differentials!,
#  _evaluate_differentials, _split_in_y.
#
################################################################################

# Split f(x, y) into y-coefficients, each a vector of x-coefficients:
# F[j+1][i+1] = coefficient of x^i y^j.
function _split_in_y(f::AbstractAlgebra.Generic.MPoly{AcbFieldElem})
  CC = base_ring(f)
  dx = max(degree(f, 1), 0)
  dy = max(degree(f, 2), 0)
  F = [[zero(CC) for _ in 0:dx] for _ in 0:dy]
  for (c, e) in zip(coefficients(f), exponent_vectors(f))
    F[e[2]+1][e[1]+1] += c
  end
  return F
end

# The factors of the differentials at one precision, with preallocated
# scratch space. One cache per thread.
mutable struct DifferentialFactorCache
  factor_matrix::Matrix{Int}            # e(l, k): exponent of factor l in g_k
  min_powers::Vector{Int}               # min_k e(l, k)
  power_ranges::Vector{Int}             # max_k e(l, k) - min_k e(l, k)
  prec::Int                             # precision of the coefficients
  # factor l: a (y_lengths[l] x x_lengths[l]) block, row-major: entry (j, i)
  # (0-based) = coefficient of x^i y^j
  coefficient_tables::Vector{Ptr{acb_struct}}
  x_lengths::Vector{Int}                # number of x-coefficients of factor l
  y_lengths::Vector{Int}                # degree in y of factor l, plus 1
  row_lengths::Vector{Vector{Int}}      # lengths of the rows without trailing zeros
  max_x_length::Int                     # maximum of x_lengths
  max_y_length::Int                     # maximum of y_lengths
  x_powers::Ptr{acb_struct}             # scratch: 1, x, ..., x^(max_x_length - 1)
  y_coefficients::Vector{Ptr{acb_struct}}  # scratch: c_{l,j}(x), j = 0, ..., y_lengths[l] - 1
  y_powers::Ptr{acb_struct}             # scratch: per sheet s a row 1, y_s, ..., y_s^(max_y_length - 1)
  allocated_sheets::Int                 # number of rows allocated in y_powers
  powers::Vector{AcbFieldElem}          # scratch: powers of one factor value
  value::AcbFieldElem                   # scratch: one factor value

  function DifferentialFactorCache(factors::Vector{AbstractAlgebra.Generic.MPoly{AcbFieldElem}},
                                   factor_matrix::Matrix{Int}, min_powers::Vector{Int},
                                   power_ranges::Vector{Int})
    CC = base_ring(factors[1])
    entry_size = sizeof(acb_struct)
    L = length(factors)
    coefficient_tables = Vector{Ptr{acb_struct}}(undef, L)
    x_lengths = zeros(Int, L)
    y_lengths = zeros(Int, L)
    row_lengths = Vector{Vector{Int}}(undef, L)
    for l in 1:L
      F = _split_in_y(factors[l])
      y_lengths[l] = length(F)
      x_lengths[l] = maximum(length, F)
      coefficient_tables[l] = acb_vec(y_lengths[l]*x_lengths[l])
      row_lengths[l] = zeros(Int, y_lengths[l])
      for j in 0:y_lengths[l]-1
        row = F[j+1]
        for i in 0:x_lengths[l]-1
          entry = coefficient_tables[l] + (j*x_lengths[l] + i)*entry_size
          if i < length(row)
            ccall((:acb_set, libflint), Nothing, (Ptr{acb_struct}, Ref{AcbFieldElem}), entry, row[i+1])
            iszero(row[i+1]) || (row_lengths[l][j+1] = i + 1)
          else
            ccall((:acb_zero, libflint), Nothing, (Ptr{acb_struct},), entry)
          end
        end
      end
    end
    max_x_length = maximum(x_lengths)
    max_y_length = maximum(y_lengths)
    y_coefficients = [acb_vec(y_lengths[l]) for l in 1:L]
    powers = [CC() for _ in 1:(maximum(power_ranges) + 1)]
    cache = new(factor_matrix, min_powers, power_ranges, precision(CC), coefficient_tables,
                x_lengths, y_lengths, row_lengths, max_x_length, max_y_length,
                acb_vec(max_x_length), y_coefficients, Ptr{acb_struct}(C_NULL), 0, powers, CC())
    finalizer(cache) do c
      for l in eachindex(c.coefficient_tables)
        acb_vec_clear(c.coefficient_tables[l], c.y_lengths[l]*c.x_lengths[l])
        acb_vec_clear(c.y_coefficients[l], c.y_lengths[l])
      end
      acb_vec_clear(c.x_powers, c.max_x_length)
      c.allocated_sheets > 0 && acb_vec_clear(c.y_powers, c.allocated_sheets*c.max_y_length)
    end
    return cache
  end
end

# Room for the powers of m values of y.
function _ensure_y_powers!(cache::DifferentialFactorCache, m::Int)
  if cache.allocated_sheets < m
    cache.allocated_sheets > 0 && acb_vec_clear(cache.y_powers, cache.allocated_sheets*cache.max_y_length)
    cache.y_powers = acb_vec(m*cache.max_y_length)
    cache.allocated_sheets = m
  end
  return cache.y_powers
end

# values[s, k] <- weight * g_k(x, fiber[s]) for the m x g buffer values
# (m = the number of y-values passed, e.g. 1 in the Abel-Jacobi map).
function _evaluate_differentials!(values::Matrix{AcbFieldElem}, cache::DifferentialFactorCache,
                                  x::AcbFieldElem, fiber::Vector{AcbFieldElem}, weight::AcbFieldElem)
  m, g = size(values)
  exponents = cache.factor_matrix
  powers = cache.powers
  value = cache.value
  prec = cache.prec
  entry_size = sizeof(acb_struct)

  @inbounds for k in 1:g, s in 1:m
    Hecke.set!(values[s, k], weight)
  end

  # powers of x (once) and of every y_s (once, shared by all factors)
  _acb_powers_ptr!(cache.x_powers, x, cache.max_x_length - 1, prec)
  if cache.max_y_length > 1
    y_powers = _ensure_y_powers!(cache, m)
    for s in 1:m
      _acb_powers_ptr!(y_powers + (s - 1)*cache.max_y_length*entry_size, fiber[s],
                       cache.max_y_length - 1, prec)
    end
  end

  GC.@preserve cache value begin
  @inbounds for l in eachindex(cache.coefficient_tables)
    x_length = cache.x_lengths[l]
    y_length = cache.y_lengths[l]
    y_coefficients = cache.y_coefficients[l]
    # c_{l,j}(x) = sum_i coefficient(j, i) x^i
    for j in 0:y_length-1
      _acb_dot_ptr!(y_coefficients + j*entry_size, cache.coefficient_tables[l] + j*x_length*entry_size,
                    cache.x_powers, cache.row_lengths[l][j+1], prec)
    end
    min_power = cache.min_powers[l]
    power_range = cache.power_ranges[l]

    if y_length == 1
      # the factor does not depend on y: the same value on all sheets
      ccall((:acb_set, libflint), Nothing, (Ref{AcbFieldElem}, Ptr{acb_struct}), value, y_coefficients)
      _acb_pow_si!(powers[1], value, min_power)
      for t in 1:power_range
        mul!(powers[t+1], powers[t], value)
      end
      for k in 1:g
        e = exponents[l, k]
        e == 0 && continue
        power = powers[e - min_power + 1]
        for s in 1:m
          mul!(values[s, k], values[s, k], power)
        end
      end
    else
      for s in 1:m
        # the value at y_s: sum_j c_{l,j}(x) y_s^j
        _acb_dot_ptr!(value, y_coefficients, cache.y_powers + (s - 1)*cache.max_y_length*entry_size,
                      y_length, prec)
        _acb_pow_si!(powers[1], value, min_power)
        for t in 1:power_range
          mul!(powers[t+1], powers[t], value)
        end
        for k in 1:g
          e = exponents[l, k]
          e == 0 && continue
          mul!(values[s, k], values[s, k], powers[e - min_power + 1])
        end
      end
    end
  end
  end # GC.@preserve
  return values
end

# The m x g matrix of the g_k(x, fiber[s]), without a preallocated cache
# (for the bounds, which are computed rarely).
function _evaluate_differentials(RS::RiemannSurfaceModel,
                                 factors::Vector{AbstractAlgebra.Generic.MPoly{AcbFieldElem}},
                                 x::AcbFieldElem, fiber::Vector{AcbFieldElem})
  _, factor_matrix, min_powers, power_ranges = differential_form_data(RS)
  cache = DifferentialFactorCache(factors, factor_matrix, min_powers, power_ranges)
  CC = base_ring(factors[1])
  values = [CC() for _ in 1:length(fiber), _ in 1:size(factor_matrix, 2)]
  _evaluate_differentials!(values, cache, x, fiber, one(CC))
  return matrix(CC, values)
end
