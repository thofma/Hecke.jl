################################################################################
#
#  Evaluation of the differential factors (the integrand)
#
#  Each embedded factor f_l(x, y) = sum_j c_{l,j}(x) y^j is stored once as a
#  contiguous block of coefficients. Per abscissa the powers of x0 and of every
#  y_s are computed once, and every c_{l,j}(x0) and every factor value is a
#  single acb_dot. The quadrature weight is folded into the initial value of
#  each entry.
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

mutable struct DifferentialFactorCache
  factor_matrix::Matrix{Int}
  min_pows::Vector{Int}
  range_pows::Vector{Int}
  prec::Int
  # coefficients: factor l has a (ny[l] x nx[l]) block at coef[l], row-major:
  # entry (j, i) (0-based) = coefficient of x^i y^j; rowlen[l][j+1] = length
  # of row j without trailing zeros
  coef::Vector{Ptr{acb_struct}}
  nx::Vector{Int}
  ny::Vector{Int}
  rowlen::Vector{Vector{Int}}
  maxnx::Int
  maxny::Int
  # scratch (one cache per worker)
  xpow::Ptr{acb_struct}          # 1, x0, ..., x0^(maxnx-1)
  cxv::Vector{Ptr{acb_struct}}   # cxv[l]: c_{l,j}(x0), j = 0..ny[l]-1
  ypow::Ptr{acb_struct}          # m_alloc rows of length maxny: 1, y_s, ..., y_s^(maxny-1)
  m_alloc::Int
  pows::Vector{AcbFieldElem}
  val::AcbFieldElem

  function DifferentialFactorCache(factors::Vector{AbstractAlgebra.Generic.MPoly{AcbFieldElem}},
                                   factor_matrix::Matrix{Int}, min_pows::Vector{Int},
                                   range_pows::Vector{Int})
    CC = base_ring(factors[1])
    sz = sizeof(acb_struct)
    L = length(factors)
    coef = Vector{Ptr{acb_struct}}(undef, L)
    nx = zeros(Int, L); ny = zeros(Int, L)
    rowlen = Vector{Vector{Int}}(undef, L)
    for l in 1:L
      F = _split_in_y(factors[l])             # F[j+1][i+1] = coeff of x^i y^j
      ny[l] = length(F)
      nx[l] = maximum(length, F)
      coef[l] = acb_vec(ny[l]*nx[l])
      rowlen[l] = zeros(Int, ny[l])
      for j in 0:ny[l]-1
        row = F[j+1]
        for i in 0:nx[l]-1
          p = coef[l] + (j*nx[l] + i)*sz
          if i < length(row)
            ccall((:acb_set, libflint), Nothing, (Ptr{acb_struct}, Ref{AcbFieldElem}), p, row[i+1])
            iszero(row[i+1]) || (rowlen[l][j+1] = i + 1)
          else
            ccall((:acb_zero, libflint), Nothing, (Ptr{acb_struct},), p)
          end
        end
      end
    end
    maxnx = maximum(nx); maxny = maximum(ny)
    cxv = [acb_vec(ny[l]) for l in 1:L]
    m_alloc = 0
    pows = [CC() for _ in 1:(maximum(range_pows) + 1)]
    C = new(factor_matrix, min_pows, range_pows, precision(CC), coef, nx, ny, rowlen,
            maxnx, maxny, acb_vec(maxnx), cxv, Ptr{acb_struct}(C_NULL), 0, pows, CC())
    finalizer(C) do c
      for l in eachindex(c.coef)
        acb_vec_clear(c.coef[l], c.ny[l]*c.nx[l])
        acb_vec_clear(c.cxv[l], c.ny[l])
      end
      acb_vec_clear(c.xpow, c.maxnx)
      c.m_alloc > 0 && acb_vec_clear(c.ypow, c.m_alloc*c.maxny)
    end
    return C
  end
end

function _ensure_ypow!(C::DifferentialFactorCache, m::Int)
  if C.m_alloc < m
    C.m_alloc > 0 && acb_vec_clear(C.ypow, C.m_alloc*C.maxny)
    C.ypow = acb_vec(m*C.maxny)
    C.m_alloc = m
  end
  return C.ypow
end

# res[s, k] <- w * g_k(x0, ys[s]),  res is an m x g Matrix{AcbFieldElem} (reused buffer)
function evaluate_differential_factors_matrix!(res::Matrix{AcbFieldElem}, C::DifferentialFactorCache,
                                               x0::AcbFieldElem, ys::Vector{AcbFieldElem},
                                               w::AcbFieldElem)
  m, g = size(res)                 # m = number of sheets passed (1 in the AJ map)
  fm = C.factor_matrix
  pows = C.pows
  val = C.val
  prec = C.prec
  sz = sizeof(acb_struct)

  @inbounds for k in 1:g, s in 1:m
    Hecke.set!(res[s, k], w)
  end

  # powers of x0 (once) and of every y_s (once, shared by all factors)
  _acb_powers_ptr!(C.xpow, x0, C.maxnx - 1, prec)
  if C.maxny > 1
    ypow = _ensure_ypow!(C, m)
    for s in 1:m
      _acb_powers_ptr!(ypow + (s - 1)*C.maxny*sz, ys[s], C.maxny - 1, prec)
    end
  end

  GC.@preserve C val begin
  @inbounds for l in eachindex(C.coef)
    nxl = C.nx[l]; nyl = C.ny[l]
    cx = C.cxv[l]
    # c_{l,j}(x0) = sum_i coef[j, i] x0^i
    for j in 0:nyl-1
      _acb_dot_ptr!(cx + j*sz, C.coef[l] + j*nxl*sz, C.xpow, C.rowlen[l][j+1], prec)
    end
    mp = C.min_pows[l]
    rp = C.range_pows[l]

    if nyl == 1
      # factor does not depend on y: same value on all sheets
      ccall((:acb_set, libflint), Nothing, (Ref{AcbFieldElem}, Ptr{acb_struct}), val, cx)
      _acb_pow_si!(pows[1], val, mp)
      for t in 1:rp
        mul!(pows[t+1], pows[t], val)
      end
      for k in 1:g
        e = fm[l, k]
        e == 0 && continue
        p = pows[e - mp + 1]
        for s in 1:m
          mul!(res[s, k], res[s, k], p)
        end
      end
    else
      for s in 1:m
        # value at y_s = sum_j c_{l,j}(x0) y_s^j
        _acb_dot_ptr!(val, cx, C.ypow + (s - 1)*C.maxny*sz, nyl, prec)
        _acb_pow_si!(pows[1], val, mp)
        for t in 1:rp
          mul!(pows[t+1], pows[t], val)
        end
        for k in 1:g
          e = fm[l, k]
          e == 0 && continue
          mul!(res[s, k], res[s, k], pows[e - mp + 1])
        end
      end
    end
  end
  end # GC.@preserve
  return res
end

# Backwards-compatible wrapper (used by the bound heuristics, called rarely).
function evaluate_differential_factors_matrix(RS::RiemannSurfaceModel,
                                              factors::Vector{AbstractAlgebra.Generic.MPoly{AcbFieldElem}},
                                              x0::AcbFieldElem, ys::Vector{AcbFieldElem})
  _, fm, mp, rp = differential_form_data(RS)
  C = DifferentialFactorCache(factors, fm, mp, rp)
  CC = base_ring(factors[1])
  res = [CC() for _ in 1:length(ys), _ in 1:size(fm, 2)]
  evaluate_differential_factors_matrix!(res, C, x0, ys, one(CC))
  return matrix(CC, res)
end
