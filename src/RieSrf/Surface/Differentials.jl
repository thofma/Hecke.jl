################################################################################
#
#  RieSrf/Surface/Differentials.jl : basis of holomorphic differentials, genus
#
#  The basis of holomorphic differentials of a plane model and its genus.
#  If Baker's theorem applies (certified modulo a prime, see below), the basis
#  x^(i-1) y^(j-1) dx / f_y for the interior points (i, j) of the Newton
#  polygon is used; otherwise the basis of the function field (Riemann-Roch,
#  maximal orders). For the integration the differentials are stored as
#  products of powers of common factors (differential_form_data, see
#  Types.jl and Integrand.jl).
#
#  Entry points: _ensure_differentials!, differential_form_data,
#  basis_of_differentials (RiemannSurfaceModel.jl).
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
  interior_points = _newton_polygon_interior_points(f)
  RS.inner_faces = interior_points
  n_interior = length(interior_points)
  if n_interior > 0 && _baker_certified(f, n_interior)
    g = n_interior
  else
    differential_basis = _function_field_basis_of_differentials(RS)
    g = length(differential_basis)
  end
  @req g > 0 "Cannot construct Riemann surface of genus 0."
  RS.genus = g

  R = parent(f)
  x, y = gens(R)
  if n_interior == g
    # Baker basis: x^(i-1) y^(j-1) / f_y, factors x, y, f_y
    RS.baker_basis = true
    factor_set = [x, y, derivative(f, 2)]
    factor_matrix = zeros(Int, 3, g)
    for k in 1:g
      factor_matrix[1, k] = interior_points[k][1] - 1
      factor_matrix[2, k] = interior_points[k][2] - 1
      factor_matrix[3, k] = -1
    end
  else
    # the basis of the function field: factor numerators and denominators
    RS.baker_basis = false
    RS.basis_of_differentials = differential_basis
    factored_numerators = [Dict(p => e for (p, e) in factor(_to_mpoly(R, numerator(omega.f))))
                           for omega in differential_basis]
    factored_denominators = [Dict(p => e for (p, e) in factor(denominator(omega.f)(x)))
                             for omega in differential_basis]
    factor_set = collect(union(Set{MPolyRingElem}(), keys.(factored_numerators)...,
                               keys.(factored_denominators)...))
    factor_matrix = zeros(Int, length(factor_set), g)
    for k in 1:g, (l, p) in enumerate(factor_set)
      haskey(factored_numerators[k], p) && (factor_matrix[l, k] = factored_numerators[k][p])
      haskey(factored_denominators[k], p) && (factor_matrix[l, k] = -factored_denominators[k][p])
    end
  end
  min_pows = [minimum(factor_matrix[l, :]) for l in 1:length(factor_set)]
  range_pows = [maximum(factor_matrix[l, :]) for l in 1:length(factor_set)] - min_pows
  RS.differential_form_data = (factor_set, factor_matrix, min_pows, range_pows)
  return RS
end

# The polynomial h in k[x][y] as an element of R = k[x, y].
function _to_mpoly(R, h)
  x, y = gens(R)
  return sum([coeff(h, i)(x)*y^i for i in 0:degree(h)])
end

# Basis of holomorphic differentials of the function field (Riemann-Roch;
# needs both maximal orders). Computed from the equation as given.
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
