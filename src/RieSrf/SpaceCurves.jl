################################################################################
#
#          RieSrf/SpaceCurves.jl : plane models of curves in P^n
#
################################################################################

#  riemann_surface(F::Vector, prec) for a curve in P^n, given by homogeneous
#  polynomials F over QQ. The curve is projected birationally to P^2 and the
#  resulting plane curve is used as the curve "as given" (the original model).
#
#  Projection. A 3 x (n+1) matrix A of rank 3 maps p in P^n to A*p in P^2
#  (projection from the linear subspace ker A). The plane equation generates
#  the elimination ideal after a linear change of coordinates that makes the
#  rows of A the first three coordinates; see _elimination_generators.
#
#  Checks (errors if they fail). Let G be the gcd of the elimination ideal.
#   * no elimination ideal (zero): the image is all of P^2, dimension >= 2;
#   * G constant: the image is finite, dimension <= 0;
#   * G must be irreducible over QQbar (and hence squarefree): the curve
#     is irreducible and reduced (at least its one-dimensional part).
#   * The projection must be birational. For a complete intersection
#     (n - 1 equations in P^n) the degree of the curve is prod(deg F_i) if it
#     is one, and deg G == prod(deg F_i) certifies all of the above: the
#     equations cut out a curve of that degree, the projection is birational
#     and its center does not meet the curve. Otherwise the degree of the
#     curve is taken from projections with random small coefficients (which
#     are birational with high probability), and other candidates must have
#     the same degree and the same genus modulo a prime.
#
#  Choice of the projection (heuristic). Candidates: the projections to three
#  of the coordinates (sparse, small coefficients, often with a Baker basis)
#  and a few projections with small pseudo-random coefficients. For every
#  valid candidate all six affine charts (which coordinate is set to 1, which
#  is x) are scored by
#     1. number of sheets, min(deg_x f, deg_y f),
#     2. Baker basis (interior points of the Newton polygon == genus mod p),
#     3. total degree, number of terms, coefficient size,
#  and the best chart is oriented so that deg_y f <= deg_x f.
#  No search for rational points on the curve (projecting from them would
#  lower the degree); to be done later.

@doc raw"""
    riemann_surface(F::Vector{<:MPolyRingElem}, prec::Int = 100;
                    projection = nothing, model = :auto, parameters = nothing, kw...)
        -> RiemannSurface

The Riemann surface of the curve in P^n cut out by the homogeneous polynomials
`F` (over QQ, in n + 1 variables). The curve is projected birationally to a
plane curve f(x, y) = 0 (see `plane_model`), which is then treated as the curve
as given: discriminant points, points, monodromy etc. refer to it. The
equations and the projection are kept, see `space_curve`.

`projection` can be a 3 x (n+1) matrix A over QQ (the point p goes to A*p);
otherwise a projection is chosen heuristically. The other keyword arguments
are those of `riemann_surface(f::MPolyRingElem, prec)`.

Throws an `ArgumentError` if `F` does not cut out an irreducible, reduced curve
or if the projection is not birational.
"""
function riemann_surface(F::Vector{<:MPolyRingElem}, prec::Int = 100;
                         projection = nothing, kw...)
  f, A = plane_model(F; projection = projection)
  RS = riemann_surface(f, prec; kw...)
  RS.space_curve = (equations = copy(F), projection = A)
  return RS
end

@doc raw"""
    space_curve(RS::RiemannSurface)

For a Riemann surface created from a curve in P^n: the named tuple
`(equations, projection)`, where the point p of the curve corresponds to the
point A*p = (x : y : 1) of the plane model, A = `projection`. Otherwise `nothing`.
"""
space_curve(RS::RiemannSurface) = isdefined(RS, :space_curve) ? RS.space_curve : nothing

@doc raw"""
    plane_model(F::Vector{<:MPolyRingElem}; projection = nothing) -> (f, A)

A plane model of the curve in P^n cut out by the homogeneous polynomials `F`
over QQ: a polynomial f in QQ[x, y] and a 3 x (n+1) matrix A over QQ such that
p -> A*p is a birational map from the curve to f(x, y) = 0, with A*p = (x : y : 1)
on the affine part. See `riemann_surface(F::Vector, prec)`.
"""
function plane_model(F::Vector{<:MPolyRingElem}; projection = nothing)
  @req !isempty(F) "Give at least one polynomial."
  R = parent(F[1])
  @req all(p -> parent(p) === R, F) "The polynomials must lie in the same ring."
  @req base_ring(R) == QQ "Only curves over QQ are supported for now."
  @req all(p -> !iszero(p) && is_homogeneous(p), F) "The polynomials must be nonzero and homogeneous (a curve in projective space)."
  N = nvars(R)
  @req N >= 3 "The curve must lie in P^n with n >= 2."
  is_ci = length(F) == N - 2
  deg_ci = is_ci ? prod(total_degree(p) for p in F) : 0

  if projection !== nothing
    A = matrix(QQ, 3, N, [QQ(projection[i, j]) for i in 1:3 for j in 1:N])
    @req rank(A) == 3 "The projection must be a 3 x $N matrix of rank 3."
    G = _projected_equation(F, A)
    _check_plane_curve(G)
    if is_ci
      @req total_degree(G) == deg_ci "The projection is not birational, its center meets the curve, or the equations do not cut out a curve of degree $deg_ci (the image has degree $(total_degree(G)))."
    end
    return _best_chart(G, A, _genus_estimate(G))
  end

  # candidates: projections with small pseudo-random coefficients (generic,
  # they define the reference degree if F is not a complete intersection)
  # and coordinate projections (sparse)
  nrand = N == 3 ? 0 : 2
  cands = N == 3 ? [identity_matrix(QQ, 3)] :
          vcat(_small_projections(N, nrand), _coordinate_projections(N))
  valid = Tuple{QQMatrix, QQMPolyRingElem}[]
  errors = String[]
  # First only the candidates that do not need a Groebner basis (the
  # resultant for two surfaces in P^3); the generic Groebner bases are slow.
  for groebner in (false, true)
    for A in cands
      try
        G = _projected_equation(F, A; groebner = groebner)
        G === nothing && continue
        _check_plane_curve(G)
        push!(valid, (A, G))
      catch e
        e isa ArgumentError || rethrow()
        push!(errors, sprint(showerror, e))
      end
    end
    isempty(valid) || break
  end
  isempty(valid) && throw(ArgumentError("Could not find a birational plane model: $(first(errors))"))

  # degree of the curve: prod(deg F_i) for a complete intersection, otherwise
  # the largest degree of an image (a generic projection is birational and
  # its center misses the curve)
  ref_deg = is_ci ? deg_ci : maximum(total_degree(G) for (_, G) in valid)
  valid = [(A, G) for (A, G) in valid if total_degree(G) == ref_deg]
  isempty(valid) && throw(ArgumentError("The equations do not cut out a curve of degree $deg_ci: no projection has an image of that degree (not a complete intersection curve, or not irreducible)."))
  # genus modulo p of the first (preferably generic) candidate; others must agree
  ref_genus = _genus_estimate(valid[1][2])
  best = nothing
  for (A, G) in valid
    if ref_genus !== nothing
      gp = _genus_estimate(G)
      gp !== nothing && gp != ref_genus && continue
    end
    cand = _best_chart(G, A, ref_genus)
    if best === nothing || _chart_score(cand[1], ref_genus) < _chart_score(best[1], ref_genus)
      best = cand
    end
  end
  best === nothing && throw(ArgumentError("Could not find a birational plane model."))
  return best
end

# The generator of the image of the curve under p -> A*p, as a homogeneous
# polynomial in QQ[u0, u1, u2] (gcd of the elimination ideal).
function _projected_equation(F::Vector{<:MPolyRingElem}, A::QQMatrix; groebner::Bool = true)
  N = nvars(parent(F[1]))
  # complete A to an invertible matrix T; new coordinates u = T*x
  T = A
  for j in 1:N
    nrows(T) == N && break
    e = zero_matrix(QQ, 1, N); e[1, j] = 1
    rank(vcat(T, e)) > nrows(T) && (T = vcat(T, e))
  end
  Ti = inv(T)
  # lex ring: the N - 3 coordinates to eliminate first, then u0, u1, u2
  S, s = polynomial_ring(QQ, N, :s; cached = false, internal_ordering = :lex)
  uvar(j) = j <= 3 ? s[N - 3 + j] : s[j - 3]
  xs = [sum(Ti[i, j] * uvar(j) for j in 1:N) for i in 1:N]
  Gs = [p(xs...) for p in F]
  if N == 3
    E = Gs
  elseif _resultant_applies(Gs, N)
    E = [resultant(Gs[1], Gs[2], 1)]
  else
    groebner || return nothing          # the caller only wants the cheap cases
    E = _elimination_generators(Gs, N - 3)
  end
  isempty(E) && throw(ArgumentError("The polynomials do not cut out a curve: the image of the projection is all of P^2 (dimension >= 2)."))
  g = reduce(gcd, E)
  P, u = polynomial_ring(QQ, [:u0, :u1, :u2]; cached = false)
  G = zero(P)
  for i in 1:length(g)
    e = exponent_vector(g, i)
    G += coeff(g, i) * u[1]^e[N - 2] * u[2]^e[N - 1] * u[3]^e[N]
  end
  total_degree(G) >= 1 || throw(ArgumentError("The polynomials do not cut out a curve: the image of the projection is finite (dimension <= 0, or empty)."))
  return G
end

# Two equations in P^3 whose leading coefficients in the eliminated variable
# (the first one) are constants: then their resultant is the equation of the
# image of the curve (no extraneous factors), and much cheaper than a
# Groebner basis. This is the case for a generic projection of a complete
# intersection of two surfaces.
function _resultant_applies(Gs::Vector{<:MPolyRingElem}, N::Int)
  (N == 4 && length(Gs) == 2) || return false
  for p in Gs
    d = degree(p, 1)
    d > 0 || return false
    is_constant(coeff(p, [1], [d])) || return false
  end
  return true
end

@doc raw"""
    _elimination_generators(G::Vector{<:MPolyRingElem}, k::Int)

Generators of the elimination ideal of (G) with respect to the first `k`
variables, i.e. elements of the ideal that do not involve them. The ring of
`G` (over QQ) has lex ordering. This generic version uses AbstractAlgebra's
generic Groebner bases (`AbstractAlgebra.Generic.Ideal`), which work over ZZ
(Euclidean domains): the polynomials are scaled to ZZ[...], whose elimination
ideal generates the one over QQ. It is slow for larger examples. When Oscar is
available it can add a more specific method, e.g.

    Hecke.RiemannSurfaces._elimination_generators(G::Vector{QQMPolyRingElem}, k::Int) =
      gens(eliminate(ideal(G), gens(parent(G[1]))[1:k]))

which is then used automatically.
"""
function _elimination_generators(G::Vector{<:MPolyRingElem}, k::Int)
  S = parent(G[1])
  Z, _ = polynomial_ring(ZZ, nvars(S), :z; cached = false, internal_ordering = internal_ordering(S))
  function toZ(p)
    d = reduce(lcm, [denominator(c) for c in coefficients(p)]; init = ZZ(1))
    return Z([numerator(c*d) for c in coefficients(p)], collect(exponent_vectors(p)))
  end
  I = AbstractAlgebra.Generic.Ideal(Z, [toZ(p) for p in G])
  E = [p for p in gens(I) if all(e -> all(iszero, e[1:k]), exponent_vectors(p))]
  return [S([QQ(c) for c in coefficients(p)], collect(exponent_vectors(p))) for p in E]
end

# The image must be an irreducible (over QQbar), hence reduced, curve.
function _check_plane_curve(G::MPolyRingElem)
  _is_absolutely_irreducible(G) ||
    throw(ArgumentError("The polynomials do not cut out an irreducible, reduced curve (or the projection maps it onto a reducible or non-reduced plane curve)."))
  return G
end

# Hecke's absolute irreducibility test (in the submodule MPolyFact).
_is_absolutely_irreducible(G::QQMPolyRingElem) =
  applicable(Hecke.is_absolutely_irreducible, G) ? Hecke.is_absolutely_irreducible(G) :
                                                   Hecke.MPolyFact.is_absolutely_irreducible(G)

# Genus modulo a prime of the plane curve G (homogeneous in 3 variables), or
# nothing. Used to compare candidates (a projection that is not birational
# lowers the genus) and to recognize a Baker basis.
function _genus_estimate(G::MPolyRingElem)
  for (ix, iy, iz) in ((1, 2, 3), (1, 3, 2), (2, 3, 1))
    f = _dehomogenize(G, ix, iy, iz)
    degree(f, 2) >= 1 || continue
    p = next_prime(2^20)
    for _ in 1:5
      p = next_prime(p + 1)
      gp = try _genus_mod_p(f, p) catch; nothing end
      gp === nothing || return gp
    end
    return nothing
  end
  return nothing
end

# f(x, y) = G with u_ix = x, u_iy = y, u_iz = 1.
function _dehomogenize(G::MPolyRingElem, ix::Int, iy::Int, iz::Int)
  Qxy, (x, y) = polynomial_ring(QQ, [:x, :y])
  f = zero(Qxy)
  for i in 1:length(G)
    e = exponent_vector(G, i)
    f += coeff(G, i) * x^e[ix] * y^e[iy]
  end
  return f
end

function _chart_score(f::MPolyRingElem, g)
  sheets = min(degree(f, 1), degree(f, 2))
  baker = (g !== nothing && length(inner_faces(f)) == g) ? 0 : 1
  height = maximum(max(nbits(numerator(c)), nbits(denominator(c))) for c in coefficients(f))
  return (sheets, baker, total_degree(f), length(f), height)
end

# The best of the six affine charts of G, oriented so that deg_y f <= deg_x f,
# with the matching projection matrix: (x : y : 1) = rows (ix, iy, iz) of A*p.
function _best_chart(G::MPolyRingElem, A::QQMatrix, g)
  best = nothing
  for (ix, iy, iz) in ((1, 2, 3), (2, 1, 3), (1, 3, 2), (3, 1, 2), (2, 3, 1), (3, 2, 1))
    f = _dehomogenize(G, ix, iy, iz)
    (degree(f, 2) >= 1 && degree(f, 2) <= degree(f, 1)) || continue
    if best === nothing || _chart_score(f, g) < _chart_score(best[1], g)
      best = (f, matrix(QQ, [A[r, j] for r in (ix, iy, iz), j in 1:ncols(A)]))
    end
  end
  best === nothing && throw(ArgumentError("The plane model has no chart in which it is a cover of the x-line."))
  return best
end

# Projections to three of the N coordinates.
function _coordinate_projections(N::Int)
  res = QQMatrix[]
  for i in 1:N, j in i+1:N, k in j+1:N
    A = zero_matrix(QQ, 3, N)
    A[1, i] = 1; A[2, j] = 1; A[3, k] = 1
    push!(res, A)
  end
  return res
end

# `count` projections of rank 3 with small pseudo-random entries in -2..2
# (a fixed sequence, so that the result is reproducible).
function _small_projections(N::Int, count::Int)
  res = QQMatrix[]
  state = UInt64(20260927)
  next() = (state = state * 6364136223846793005 + 1442695040888963407; Int((state >> 33) % 5) - 2)
  while length(res) < count
    A = matrix(QQ, 3, N, [next() for _ in 1:3*N])
    rank(A) == 3 && push!(res, A)
  end
  return res
end
