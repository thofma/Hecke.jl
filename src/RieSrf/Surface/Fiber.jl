################################################################################
#
#  RieSrf/Surface/Fiber.jl : fibers of the projection (x, y) -> x
#
#   * fiber(f, x0)                      regular points: certified simple roots
#   * fiber_with_multiplicities(RS, x0) any point: distinct roots + multiplicities
#   * fiber_repeated(RS, x0)            every root repeated by its multiplicity
#
#  For every irreducible factor p of disc_y(f)*lc_y(f) only two pieces of exact
#  information are needed, both cheap:
#    * which y-coefficients of f vanish at the roots of p   (exact: rem mod p)
#    * the multiplicity pattern of f(alpha, y)              (modular, see below)
#  The roots themselves are computed numerically, and the known pattern tells
#  us how to group them. (An exact squarefree decomposition over K[x]/(p) is
#  far too slow when p has large degree.)
#
#  Multiplicity pattern, modular: pick primes l and a root r of p mod l, and
#  compute the squarefree decomposition of f(r, y) over GF(l). For all but
#  finitely many (l, r) this has the same pattern as f(alpha, y) over K[x]/(p)
#  (all roots of p are Galois conjugate, so they share the pattern). A bad
#  reduction can only MERGE roots, never split them, so over a few primes we
#  keep the pattern with the most distinct roots. This is heuristic in
#  principle but extremely reliable in practice; a pattern that is wrong would
#  also make the numerical clustering below fail its separation check.
#
#  Implemented for K of degree 1 (curves over Q). For other K a prime ideal of
#  degree 1 of K would be needed; left for later.
#
#  Computed together with the discriminant points (_ensure_discriminant_points!,
#  serial): _compute_disc_factor_data!(RS).
#
#  Entry points: fiber, fiber_with_multiplicities, fiber_repeated.
#
################################################################################

@doc raw"""
    fiber(f::MPolyRingElem{AcbFieldElem}, x0::AcbFieldElem) -> Vector{AcbFieldElem}

The roots of f(x0, y), certified and sorted by `sheet_ordering`, at the
precision of the coefficients of f. Throws an error if the roots cannot be
isolated, i.e. if x0 is (numerically) too close to a discriminant point.
"""
function fiber(f::MPolyRingElem, x0::AcbFieldElem)
  CC = base_ring(f)
  Cz, z = polynomial_ring(CC, "z")
  ys = _accurate_roots(f(CC(x0), z), precision(CC))
  return sort!(ys, lt = sheet_ordering)
end

function _disc_factor_data(RS::RiemannSurfaceModel)
  # Computed together with the discriminant points (exact arithmetic, serial).
  # By the time threaded code calls this, big_period_matrix has done it.
  isdefined(RS, :disc_factor_data) || _ensure_discriminant_points!(RS)
  return RS.disc_factor_data
end

function _compute_disc_factor_data!(RS::RiemannSurfaceModel)
  fu = defining_polynomial_univariate(RS)          # element of K[x][y]
  Kx = base_ring(fu)
  if degree(base_ring(Kx)) != 1
    # not implemented for number fields yet: fall back to the numerical method
    RS.disc_factor_data = Any[]
    return RS.disc_factor_data
  end

  facs = elem_type(Kx)[]
  for fac in _discriminant_factors(RS)
    for q in fac
      degree(q) >= 1 || continue
      q = q * inv(leading_coefficient(q))
      q in facs || push!(facs, q)
    end
  end

  data = Any[]
  for p in facs
    vanishing = [iszero(rem(coeff(fu, i), p)) for i in 0:degree(fu)]
    ydeg = findlast(!, vanishing) - 1
    pattern = _multiplicity_pattern_modular(fu, p, ydeg)
    push!(data, DiscriminantFactorData(p, vanishing, ydeg, pattern))
  end
  RS.disc_factor_data = data
  return data
end

# Multiplicity pattern of f(alpha, y), alpha a root of p, via reduction mod
# primes l at a root r of p mod l (see header). K has degree 1.
function _multiplicity_pattern_modular(fu, p, ydeg::Int; nprimes::Int = 3, maxtries::Int = 2000)
  toQ(c) = coeff(c, 0)                                    # K of degree 1 -> QQ
  pQ = [toQ(coeff(p, i)) for i in 0:degree(p)]
  fQ = [[toQ(coeff(coeff(fu, i), j)) for j in 0:degree(coeff(fu, i))] for i in 0:degree(fu)]
  dens = vcat([denominator(c) for c in pQ], [denominator(c) for cs in fQ for c in cs])

  best = Int[]
  found = 0
  l = next_prime(ZZ(2)^30)
  for _ in 1:maxtries
    found >= nprimes && break
    l = next_prime(l + 1)
    any(d -> is_divisible_by(d, l), dens) && continue
    F = GF(l)
    toF(q) = F(numerator(q)) * inv(F(denominator(q)))
    Ft, _ = polynomial_ring(F, "t"; cached = false)
    pF = Ft([toF(c) for c in pQ])
    degree(pF) == degree(p) || continue
    rts = roots(pF)
    isempty(rts) && continue
    r = rts[1]
    horner(cs) = (s = zero(F); for c in reverse(cs); s = s*r + toF(c); end; s)
    Fy, _ = polynomial_ring(F, "y"; cached = false)
    fr = Fy([horner(cs) for cs in fQ])
    degree(fr) == ydeg || continue                        # accidental drop mod l
    pat = Int[]
    for (h, e) in factor_squarefree(fr)
      degree(h) > 0 && append!(pat, fill(e, degree(h)))
    end
    found += 1
    length(pat) > length(best) && (best = pat)          # bad reduction only merges roots
  end
  @req found > 0 "Could not determine the multiplicity pattern at a discriminant point."
  return sort!(best, rev = true)
end

# Evaluate c in K[x] at x0 under the embedding of RS.
function _eval_embedded(c::PolyRingElem, v, x0::AcbFieldElem)
  CC = parent(x0)
  prec = precision(CC)
  r = zero(CC)
  for i in degree(c):-1:0
    r = r * x0 + CC(_embed_coefficient(coeff(c, i), v.embedding, prec))
  end
  return r
end

# Group approximate roots into clusters of the given sizes (descending) and
# check that the clusters are clearly separated.
function _cluster_roots(z::Vector{AcbFieldElem}, sizes::Vector{Int})
  n = length(z)
  D = [Float64(abs(z[i] - z[j])) for i in 1:n, j in 1:n]
  avail = trues(n)
  clusters = Vector{Vector{Int}}()
  for e in sizes
    best = Int[]
    bestdiam = Inf
    for i in findall(avail)
      nb = sort(findall(avail), by = j -> D[i, j])[1:e]
      diam = maximum(D[a, b] for a in nb, b in nb)
      if diam < bestdiam
        bestdiam, best = diam, nb
      end
    end
    push!(clusters, best)
    avail[best] .= false
  end
  if length(clusters) > 1
    intra = maximum(maximum(D[a, b] for a in c, b in c) for c in clusters)
    inter = minimum(D[a, b] for k in eachindex(clusters) for l in eachindex(clusters) if k != l
                            for a in clusters[k] for b in clusters[l])
    @req intra < inter / 10 "Roots at a discriminant point are not clearly clustered; increase the precision."
  end
  return clusters
end

@doc raw"""
    fiber_with_multiplicities(RS::RiemannSurfaceModel, x0::AcbFieldElem)
      -> Vector{AcbFieldElem}, Vector{Int}

Distinct finite roots of f(x0, y), sorted with `sheet_ordering`, together with
their multiplicities. The number of roots at infinity is
`RS.degree[1] - sum(multiplicities)`. The precision is that of `parent(x0)`.
"""
function fiber_with_multiplicities(RS::RiemannSurfaceModel, x0::AcbFieldElem)
  CC = parent(x0)
  prec = precision(CC)
  v = embedding(RS)
  z0 = zero(CC)

  data = _disc_factor_data(RS)
  if isempty(data) && degree(base_ring(base_ring(defining_polynomial_univariate(RS)))) != 1
    # curves over number fields: previous numerical method
    ys, mults = _roots_with_multiplicities(complex_defining_polynomial(RS, prec)(x0, gen(polynomial_ring(CC, "y")[1])))
    perm = sortperm(ys, lt = sheet_ordering)
    return ys[perm], mults[perm]
  end
  hits = [d for d in data if contains(_eval_embedded(d.p, v, x0), z0)]
  if isempty(hits)                                     # regular point
    ys = fiber(complex_defining_polynomial(RS, prec), x0)
    return ys, fill(1, length(ys))
  end
  @req length(hits) == 1 "Cannot decide which discriminant point x0 is; increase the precision of x0."
  d = hits[1]

  # f(x0, y) with the exactly vanishing coefficients set to zero
  fu = defining_polynomial_univariate(RS)
  Cy, _ = polynomial_ring(CC, "y")
  fx = Cy([d.vanishing[i + 1] ? z0 : _eval_embedded(coeff(fu, i), v, x0) for i in 0:d.ydeg])

  if all(==(1), d.pattern)                             # only simple finite roots
    ys = sort!(_accurate_roots(fx, prec), lt = sheet_ordering)
    return ys, fill(1, length(ys))
  end

  z = _roots_without_isolation(fx)
  clusters = _cluster_roots(z, d.pattern)
  ys = AcbFieldElem[]
  mults = Int[]
  RR = ArbField(prec)
  for (c, e) in zip(clusters, d.pattern)
    y = _acb_mid(sum(z[c]) / e)
    if e > 1
      # a root of multiplicity e of f is a simple root of f^(e-1): refine the
      # cluster mean by Newton on midpoints (ball Newton would only inflate)
      g = fx
      for _ in 1:e-1
        g = derivative(g)
      end
      dg = derivative(g)
      for _ in 1:4
        y = _acb_mid(y - evaluate(g, y) / evaluate(dg, y))
      end
      # enclosure: the true root lies within the cluster of approximations
      diam = maximum(abs(z[a] - z[b]) + 2*radius_bound(z[a]) for a in c, b in c)
      _add_error!(y, RR(diam))
    else
      y = z[c[1]]
    end
    push!(ys, y)
    push!(mults, e)
  end
  perm = sortperm(ys, lt = sheet_ordering)
  return ys[perm], mults[perm]
end

# The finite roots of f(x0, y), every root repeated by its multiplicity.
function fiber_repeated(RS::RiemannSurfaceModel, x0::AcbFieldElem)
  ys, mults = fiber_with_multiplicities(RS, x0)
  res = AcbFieldElem[]
  for (y, e) in zip(ys, mults)
    append!(res, fill(y, e))
  end
  return res
end

# Approximations of the roots by acb_poly_find_roots, also when they cannot
# be isolated (multiple roots); those come with wide or meaningless radii.
function _roots_without_isolation(f::AcbPolyRingElem)
  m = degree(f)
  temp_vec_res = acb_vec(m)
  CC = base_ring(f)
  prec = precision(CC)
  dd = ccall((:acb_poly_find_roots, libflint), Cint, (Ptr{acb_struct}, Ref{AcbPolyRingElem}, Ptr{acb_struct}, Int, Int), temp_vec_res, f, C_NULL, 0, prec)
  z = array(CC, temp_vec_res, m)
  acb_vec_clear(temp_vec_res, m)
  return z
end 

# The roots with their multiplicities, numerically: a root of multiplicity n
# is a root of the first n - 1 derivatives. m: an upper bound for the
# multiplicities (only that many derivatives are checked). Used for curves
# over number fields of degree > 1 (see fiber_with_multiplicities) and for
# the points at infinity.
function _roots_with_multiplicities(f::PolyRingElem, m::Int = degree(f))
  CC = base_ring(f)
  RR = ArbField(precision(CC))

  roots_found = AcbFieldElem[]
  mult = Int[]
  derivatives = [f]
  for i in (1:m-1)
    push!(derivatives, derivative(derivatives[end]))
  end
  for n in (m:-1:1)
    R = _roots_without_isolation(derivatives[n])
    for r in R
      if all(map(h -> contains(h(r), zero(CC)), derivatives[1:n]))
        if isempty(roots_found)
          push!(roots_found, r)
          push!(mult, n)
        else 
          distance, index = closest_point(r, roots_found)
          if !contains(distance, RR(0))
            push!(roots_found, r)
            push!(mult, n)
          end
        end
      end
    end
  end
  @req sum(mult) == degree(f) "Sum of multiplicities does not match degree. Error in root computation."
  return roots_found, mult
end
