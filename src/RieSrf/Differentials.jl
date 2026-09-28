################################################################################
#
#  RieSrf/Differentials.jl : basis of holomorphic differentials, genus
#
################################################################################

################################################################################
#
#  Lazily computed data
#
################################################################################

# Basis of differentials, genus and the factor data used for integration.
function _ensure_differentials!(RS::RiemannSurfaceModel)
  isdefined(RS, :differential_form_data) && return RS

  f = RS.defining_polynomial

  # Baker's theorem: g <= #interior points of the Newton polygon, with
  # equality iff x^i y^j dx/f_y ((i,j) interior) is a basis. If a reduction
  # modulo a prime certifies equality (see _baker_certified), the exact basis
  # of differentials over the function field (maximal orders over Q, the
  # expensive part) is not needed at all.
  n_interior = length(inner_faces(f))
  if n_interior > 0 && _baker_certified(f, n_interior)
    g = n_interior
  else
    diff_base = _function_field_basis_of_differentials(RS)
    g = length(diff_base)
  end
  @req g > 0 "Cannot construct Riemann surface of genus 0."
  RS.genus = g

  mpoly_kxy = parent(f)
  mpoly_x, mpol_y = gens(mpoly_kxy)

  #Computed a Newton polygon and decide whether we can use a Baker basis or not.
  inner_fac = inner_faces(f)
  RS.inner_faces = inner_fac
  if length(inner_fac) == g
    RS.baker_basis = true
    x, y = gens(parent(f))
    factor_set = [x, y, derivative(f, 2)]
    n = length(factor_set)
    min_x = minimum([t[1] for t in inner_fac])
    max_x = maximum([t[1] for t in inner_fac])
    min_y = minimum([t[2] for t in inner_fac])
    max_y = maximum([t[2] for t in inner_fac])
    min_pows = [min_x - 1, min_y - 1, -1]
	    range_pows = [max_x - 1, max_y - 1, -1] - min_pows

    factor_matrix = zeros(Int, n, g)

    for i in (1:g)
      factor_matrix[1, i] = inner_fac[i][1] - 1
      factor_matrix[2, i] = inner_fac[i][2] - 1
      factor_matrix[3, i] = -1
    end

  else
    RS.baker_basis = false
    RS.basis_of_differentials = diff_base
    #Compute the differential forms data mentioned above.
    factor_set = Set{MPolyRingElem}()
    factored_nums = Dict{AbstractAlgebra.Generic.MPoly{AbsSimpleNumFieldElem}, Int64}[]
    factored_denoms = Dict{AbstractAlgebra.Generic.MPoly{AbsSimpleNumFieldElem}, Int64}[]
    #Gather all the factors occurring in the basis of differential forms
    for i in 1:g
      num_diff_i_fac = Dict(p => e for (p,e) in factor(to_mpoly(mpoly_kxy, numerator(diff_base[i].f))))
      denom_diff_i_fac = Dict(p => e for (p,e) in factor(denominator(diff_base[i].f)(mpoly_x)))

      union!(factor_set, Set(keys(num_diff_i_fac)), Set(keys(denom_diff_i_fac)))

      push!(factored_nums, num_diff_i_fac)
      push!(factored_denoms, denom_diff_i_fac)
    end

    #Turn set into sequence so we can enumerate
    factor_set = collect(factor_set)
    number_of_factors = length(factor_set)
    n = length(factor_set)
    factor_matrix = zero_matrix(Int, n, g)
    for j in 1:g
      for i in 1:n
        if haskey(factored_nums[j], factor_set[i])
          factor_matrix[i,j] = get(factored_nums[j], factor_set[i], 0)
        end

        if haskey(factored_denoms[j], factor_set[i])
          factor_matrix[i,j] = -get(factored_denoms[j], factor_set[i], 0)
        end
      end
    end

		  min_pows= [minimum( factor_matrix[j, 1:g]) for j in 1:n]
	    range_pows= [maximum( factor_matrix[j, 1:g]) for j in 1:n] - min_pows
  end

  RS.differential_form_data = (factor_set, factor_matrix, min_pows, range_pows)

  return RS
end

# Basis of holomorphic differentials of the function field (Riemann-Roch;
# needs both maximal orders). Computed from the equation as given, as before.
function _function_field_basis_of_differentials(RS::RiemannSurfaceModel)
  isdefined(RS, :basis_of_differentials) && return RS.basis_of_differentials
  f0 = RS.input_polynomial
  k0 = base_ring(f0)
  kx0, x0 = rational_function_field(k0, "x")
  kxy0, y0 = polynomial_ring(kx0, "y")
  F0, _ = function_field(f0(x0, y0))
  RS.basis_of_differentials = basis_of_differentials(F0)
  return RS.basis_of_differentials
end

################################################################################
#
#  Certifying a Baker basis modulo primes
#
#  Let n be the number of interior lattice points of the Newton polygon of f.
#  Baker: g <= n. Let p be a prime such that
#    (a) no coefficient of f vanishes mod p (same Newton polygon, same degree),
#    (b) f mod p is geometrically irreducible (irreducible over F_p and has a
#        smooth F_p-rational point, which lies on a single geometric component),
#  then the reduction is a flat degeneration of integral plane curves of the
#  same degree, the delta invariant can only grow, so g_p <= g.
#  Hence g_p == n implies g == n, and the Baker basis is correct.
#  If equality does not occur we learn nothing and use the exact computation.
#  Any failure in the modular computation also just means "not certified".
#
#  Only for curves over QQ (or Q as a number field).
#
################################################################################

# nprimes: number of usable primes to try. One suffices: equality certifies,
# and a smaller genus mod p almost always means g < n_interior, in which case
# more primes would only cost time before the exact computation.
function _baker_certified(f::MPolyRingElem, n_interior::Int; nprimes::Int = 1, maxtries::Int = 20)
  k = base_ring(f)
  (k isa QQField || degree(k) == 1) || return false
  done = 0
  p = next_prime(2^20)
  for _ in 1:maxtries
    done >= nprimes && break
    p = next_prime(p + 1)
    gp = try
      _genus_mod_p(f, p)
    catch e
      @debug "Genus modulo $p failed" exception = e
      nothing
    end
    gp === nothing && continue
    done += 1
    gp == n_interior && return true
  end
  return false
end

# Genus of the reduction of f modulo p, or nothing if p does not satisfy (a), (b).
function _genus_mod_p(f::MPolyRingElem, p::Int)
  k = base_ring(f)
  qs = [k isa QQField ? QQ(c) : QQ(coeff(c, 0)) for c in coefficients(f)]
  any(q -> is_divisible_by(numerator(q), p) || is_divisible_by(denominator(q), p), qs) && return nothing
  Fp = GF(p)
  R, (X, Y) = polynomial_ring(Fp, [:x, :y]; cached = false)
  fp = zero(R)
  for (q, e) in zip(qs, exponent_vectors(f))
    fp += Fp(numerator(q)) * inv(Fp(denominator(q))) * X^e[1] * Y^e[2]
  end
  fac = factor(fp)
  (length(fac) == 1 && all(e == 1 for (_, e) in fac)) || return nothing
  _has_smooth_rational_point(fp) || return nothing

  kx, x = rational_function_field(Fp, "x"; cached = false)
  kxy, y = polynomial_ring(kx, "y"; cached = false)
  F, _ = function_field(fp(x, y), "a"; cached = false)
  return genus(F)
end

function _has_smooth_rational_point(fp::MPolyRingElem; tries::Int = 50)
  Fp = base_ring(fp)
  fx = derivative(fp, 1)
  fy = derivative(fp, 2)
  Ft, t = polynomial_ring(Fp, "t"; cached = false)
  for _ in 1:tries
    a = rand(Fp)
    g = evaluate(fp, [Ft(a), t])
    iszero(g) && continue
    for b in roots(g)
      if !iszero(evaluate(fx, [a, b])) || !iszero(evaluate(fy, [a, b]))
        return true
      end
    end
  end
  return false
end

function differential_form_data(RS::RiemannSurfaceModel)
  _ensure_differentials!(RS)
  return RS.differential_form_data
end
