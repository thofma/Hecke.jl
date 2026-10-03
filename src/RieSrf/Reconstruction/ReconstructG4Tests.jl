################################################################################
#
#  ReconstructG4Tests.jl : comparisons and tests of the genus 4 reconstruction
#
#  Bouchet's invariants of the reconstruction against those of the exact
#  canonical model (compare_with_original), Moebius comparison of the
#  Rosenhain invariants (hyperelliptic), the point check in the coordinates of
#  the reconstruction, the exact check of the rational model, diagnostics and
#  random tests. Not needed for the reconstruction itself.
#
################################################################################

################################################################################
#
#  Comparison with the original curve
#
#  compare_with_original(f, RS, hyperelliptic) (ReconstructCurvesG123.jl) calls
#  _compare_with_original_g4 for genus 4:
#
#  Non-hyperelliptic: Bouchet's invariants (Hecke's g4_invariants) of the
#  canonical model of f(x, y) = 0 (exactly, from the monomials x^(i-1) y^(j-1)
#  of the interior points (i, j) of the Newton polygon, Baker's basis of the
#  differentials) and of the reconstructed curve, compared in weighted
#  projective space (compare_invariants). Both quadrics are first brought to
#  X W - Y Z (rank 4) resp. X Z - Y^2 (rank 3), the forms for which
#  g4_invariants computes the invariants directly (_compute_invs_ws).
#
#  Hyperelliptic (no invariants yet): the Rosenhain invariants must be the
#  images of the branch points under a Moebius transformation that maps three
#  of them to 0, 1, oo.
#
################################################################################

function _compare_with_original_g4(f::MPolyRingElem, RS, hyperelliptic::Bool)
  tau = small_period_matrix(RS)
  prec = precision(base_ring(tau))
  data = reconstruct_curve_g4_data(tau)
  failed(d) = (ok = false, all_recognized = false, log2_diff = d, recognized = nothing, case = data.case)
  if hyperelliptic
    data.case === :hyperelliptic || return failed(Inf)
    d = _g4_moebius_distance(f, data.info.rosenhain)
    return (ok = d < -prec/2, all_recognized = false, log2_diff = d, recognized = nothing, case = data.case)
  end
  data.case === :hyperelliptic && return failed(Inf)
  Q0, Gamma0, rank0 = _g4_canonical_model(f)
  rank0 == (data.case === :generic ? 4 : 3) || return failed(Inf)
  Iex, ws = Hecke.g4_invariants(Q0, Gamma0)
  # the midpoints: the radii are pessimistic by 100-150 bits and would
  # dominate the comparison
  Icc, _ = _g4_invariants_numerical(_mpoly_midpoint(data.curve[1]), _mpoly_midpoint(data.curve[2]), rank0)
  CC = base_ring(parent(data.curve[1]))
  Iex = QQFieldElem[QQ(a) for a in Iex]
  Icc = AcbFieldElem[CC(a) for a in Icc]
  return merge(compare_invariants(Iex, Icc, ws), (case = data.case,))
end

_mpoly_midpoint(p::MPolyRingElem) = map_coefficients(_acb_mid, p; parent = parent(p))

# The permutations of 1:n
function _permutations(n::Int)
  n == 1 && return [[1]]
  return [vcat(p[1:k-1], [n], p[k:end]) for p in _permutations(n - 1) for k in 1:n]
end

@doc raw"""
    _g4_canonical_model(f::MPolyRingElem) -> Q, Gamma, rank

The canonical model of the genus 4 curve f(x, y) = 0 over QQ, if Baker's
basis x^(i-1) y^(j-1) dx / f_y ((i, j) the interior points of the Newton
polygon) is a basis of the differentials: the quadric relation between the
four monomials and a cubic Gamma with Gamma(monomials) = f, with the
coordinates permuted so that Q = X W - Y Z (rank 4) or Q = X Z - Y^2 (rank 3).
"""
function _g4_canonical_model(f::MPolyRingElem)
  points = RSR._newton_polygon_interior_points(f)
  @req length(points) == 4 "The Newton polygon of f does not have 4 interior points."
  x, y = gens(parent(f))
  m = [x^(p[1] - 1) * y^(p[2] - 1) for p in points]
  R, X = polynomial_ring(QQ, [:X, :Y, :Z, :W]; cached = false)
  e2 = _exponent_vectors(4, 2)
  e3 = _exponent_vectors(4, 3)
  image(e) = prod(m[i]^e[i] for i in 1:4)
  form(c, es) = sum(c[k] * prod(X[i]^es[k][i] for i in 1:4) for k in eachindex(es))
  # the quadric: the relation between the products of two monomials
  images2 = [image(e) for e in e2]
  monos2 = unique(vcat([collect(monomials(p)) for p in images2]...))
  A = matrix(QQ, length(e2), length(monos2), [coeff(p, mo) for p in images2 for mo in monos2])
  K = kernel(A; side = :left)
  @req nrows(K) == 1 "The monomials do not satisfy exactly one quadric relation."
  Q = form([K[1, k] for k in 1:ncols(K)], e2)
  # the cubic: f as a cubic form in the monomials
  images3 = [image(e) for e in e3]
  monos3 = unique(vcat(collect(monomials(f)), [collect(monomials(p)) for p in images3]...))
  B = matrix(QQ, length(e3), length(monos3), [coeff(p, mo) for p in images3 for mo in monos3])
  b = matrix(QQ, 1, length(monos3), [coeff(f, mo) for mo in monos3])
  solvable, c = can_solve_with_solution(B, b; side = :left)
  @req solvable "f is not a cubic form in the monomials of Baker's basis."
  Gamma = form([c[1, k] for k in 1:ncols(c)], e3)
  # the standard forms
  for p in _permutations(4)
    Xp = [X[p[i]] for i in 1:4]
    Qp = evaluate(Q, Xp)
    for (T, t, lead) in ((X[1]*X[4] - X[2]*X[3], 4, X[1]*X[4]), (X[1]*X[3] - X[2]^2, 3, X[1]*X[3]))
      lambda = coeff(Qp, lead)
      (!iszero(lambda) && Qp == lambda * T) && return T, evaluate(Gamma, Xp), t
    end
  end
  error("The canonical quadric is not of the form X W - Y Z or X Z - Y^2 in the monomial coordinates.")
end

# M with M A M^T = G for complex symmetric 4 x 4 matrices A, G of rank t
# (3 or 4), from their diagonalizations
function _g4_quadric_transformation(A::AcbMatrix, G::AcbMatrix, t::Int)
  CC = base_ring(A)
  S1, d1 = _diagonalize_symmetric(A)
  S2, d2 = _diagonalize_symmetric(G)
  function order(d)
    t == 4 && return collect(1:4)
    z = argmin([_abs64(x) for x in d])
    return vcat(setdiff(1:4, [z]), [z])
  end
  o1, o2 = order(d1), order(d2)
  P1, P2 = zero_matrix(CC, 4, 4), zero_matrix(CC, 4, 4)
  for k in 1:4
    P1[k, o1[k]] = one(CC)
    P2[k, o2[k]] = one(CC)
  end
  Lambda = diagonal_matrix([k <= t ? RSR._rotated_power(d2[o2[k]] / d1[o1[k]], 1//2) : one(CC) for k in 1:4])
  return inv(P2 * S2) * Lambda * P1 * S1
end

# Bouchet's invariants of the curve quadric = cubic = 0 over CC (rank t of the
# quadric): coordinates in which the quadric is X W - Y Z resp. X Z - Y^2
function _g4_invariants_numerical(quadric::MPolyRingElem, cubic::MPolyRingElem, t::Int)
  R = parent(quadric)
  CC = base_ring(R)
  half = inv(CC(2))
  A = zero_matrix(CC, 4, 4)
  for i in 1:4, j in 1:4
    e = zeros(Int, 4)
    e[i] += 1
    e[j] += 1
    A[i, j] = i == j ? coeff(quadric, e) : coeff(quadric, e) * half
  end
  G = zero_matrix(CC, 4, 4)
  if t == 4
    G[1, 4] = G[4, 1] = half
    G[2, 3] = G[3, 2] = -half
  else
    G[1, 3] = G[3, 1] = half
    G[2, 2] = -one(CC)
  end
  M = _g4_quadric_transformation(A, G, t)
  ys = gens(R)
  f0 = evaluate(cubic, [sum(M[j, i] * ys[j] for j in 1:4) for i in 1:4])    # x = M^T y
  invs, ws = Hecke._compute_invs_ws(f0, one(CC), t)
  # diagnostics: log2 of max|M| max|M^-1| (a condition estimate) and of the
  # ratio of the largest to the smallest nonzero coefficient of the cubic
  # before and after the normalization
  Minv = inv(M)
  condition = _safe_log2(maximum(_abs64(M[i, j]) for i in 1:4, j in 1:4) *
                       maximum(_abs64(Minv[i, j]) for i in 1:4, j in 1:4))
  spread(p) = (c = filter(>(0), [_abs64(a) for a in coefficients(p)]); _safe_log2(maximum(c) / minimum(c)))
  return invs, ws, (condition = condition, spread_before = spread(cubic), spread_after = spread(f0))
end

# log2 of the relative distance between the Rosenhain invariants and the
# images of the branch points under the best Moebius map sending three of them
# to 0, 1, oo (found in Float64, evaluated at full precision)
function _g4_moebius_distance(f::MPolyRingElem, lambdas::Vector{AcbFieldElem})
  CC = parent(lambdas[1])
  prec = precision(CC)
  Qt, t = polynomial_ring(QQ, :t; cached = false)
  h = sum(c * t^e[1] for (c, e) in zip(coefficients(f), exponent_vectors(f)) if e[2] == 0)
  CCt, _ = polynomial_ring(CC, :t; cached = false)
  bps = RSR._accurate_roots(map_coefficients(CC, h; parent = CCt), prec)
  # all branch points finite: z -> 1/(z - c), oo -> 0
  c = CC(0.123456, 0.654321)
  pts = [inv(b - c) for b in bps]
  length(pts) == 9 && push!(pts, zero(CC))
  @req length(pts) == 10 "Expected 10 branch points."
  ptsf = [RSR._c64(p) for p in pts]
  lamf = [RSR._c64(l) for l in lambdas]
  best, triple = Inf, (1, 2, 3)
  for i in 1:10, j in 1:10, k in 1:10
    length(unique([i, j, k])) == 3 || continue
    mf(z) = (z - ptsf[i]) * (ptsf[j] - ptsf[k]) / ((z - ptsf[k]) * (ptsf[j] - ptsf[i]))
    d = maximum(minimum(abs(mf(ptsf[l]) - lam) for lam in lamf) for l in 1:10 if !(l in (i, j, k)))
    d < best && ((best, triple) = (d, (i, j, k)))
  end
  i, j, k = triple
  m(z) = (z - pts[i]) * (pts[j] - pts[k]) / ((z - pts[k]) * (pts[j] - pts[i]))
  scale = max(1.0, maximum(abs, lamf))
  worst = 0.0
  for l in 1:10
    l in triple && continue
    z = m(pts[l])
    zf = RSR._c64(z)
    nearest = argmin([abs(zf - lam) for lam in lamf])
    worst = max(worst, _abs64(z - lambdas[nearest]) / scale)
  end
  return _safe_log2(worst)
end

# Where the precision is lost: (1) the numerical invariants of the exact
# canonical model (the invariant code alone), (2) those of the reconstruction,
# (3) the point check of the reconstruction (independent of the invariants).
function g4_invariant_diagnostics(f::MPolyRingElem, prec::Int = 300)
  Q0, Gamma0, t = _g4_canonical_model(f)
  Iex, ws = Hecke.g4_invariants(Q0, Gamma0)
  Iex = QQFieldElem[QQ(a) for a in Iex]
  CC = AcbField(prec)
  R, _ = polynomial_ring(CC, [:x1, :x2, :x3, :x4]; cached = false)
  toCC(p) = map_coefficients(CC, p; parent = R)
  I1, _ = _g4_invariants_numerical(toCC(Q0), toCC(Gamma0), t)
  exact_model = compare_invariants(Iex, AcbFieldElem[CC(a) for a in I1], ws).log2_diff
  # the exact model in random coordinates (like the reconstruction), without
  # and with relative noise 2^-noise_bits on the coefficients
  ys = gens(R)
  A = matrix(CC, 4, 4, [CC(rand() - 0.5, rand() - 0.5) for _ in 1:16])
  move(p) = evaluate(toCC(p), [sum(A[i, j] * ys[j] for j in 1:4) for i in 1:4])
  noise_bits = 200
  function noisy(p)
    s = maximum(_abs64, coefficients(p))
    ctx = MPolyBuildCtx(R)
    for (c, e) in zip(coefficients(p), exponent_vectors(p))
      push_term!(ctx, c + CC(rand() - 0.5, rand() - 0.5) * s * CC(2)^(-noise_bits), e)
    end
    return finish(ctx)
  end
  Qm, Gm = move(Q0), move(Gamma0)
  I2, _, cond_moved = _g4_invariants_numerical(Qm, Gm, t)
  moved = compare_invariants(Iex, AcbFieldElem[CC(a) for a in I2], ws).log2_diff
  I3, _ = _g4_invariants_numerical(noisy(Qm), noisy(Gm), t)
  moved_noise = compare_invariants(Iex, AcbFieldElem[CC(a) for a in I3], ws).log2_diff
  RS = riemann_surface(f, prec; superelliptic = false, model = :original)
  reconstruction = _compare_with_original_g4(f, RS, false)
  data = reconstruct_curve_g4_data(small_period_matrix(RS))
  points = _g4_residual_on_points(RS, data, 4)
  _, _, cond_rec = _g4_invariants_numerical(_mpoly_midpoint(data.curve[1]), _mpoly_midpoint(data.curve[2]), t)
  radius = maximum(_safe_log2(Float64(Hecke.radius(real(c))) + Float64(Hecke.radius(imag(c))))
                   for c in vcat(collect(coefficients(data.curve[1])), collect(coefficients(data.curve[2]))))
  return (exact_model = exact_model, moved = moved, moved_noise200 = moved_noise,
          reconstruction = reconstruction.log2_diff, points = points,
          normalization_moved = cond_moved, normalization_reconstruction = cond_rec,
          log2_max_radius = radius,
          info = data.info)
end

# S with S A S^T diagonal (A complex symmetric): symmetric Gaussian
# elimination with pivoting on the diagonal (a 2 x 2 pivot is replaced by
# adding a row/column to another when the diagonal is small).
function _diagonalize_symmetric(A::AcbMatrix)
  n = nrows(A)
  CC = base_ring(A)
  B = deepcopy(A)
  S = identity_matrix(CC, n)
  for k in 1:n-1
    i = k - 1 + argmax([_abs64(B[l, l]) for l in k:n])
    off = 0.0
    a, b = k, k
    for l in k:n, l2 in k:n
      l == l2 && continue
      if _abs64(B[l, l2]) > off
        off, a, b = _abs64(B[l, l2]), l, l2
      end
    end
    if _abs64(B[i, i]) < 1e-3 * off
      E = identity_matrix(CC, n)
      E[a, b] = one(CC)
      B = E * B * transpose(E)
      S = E * S
      i = a
    end
    P = identity_matrix(CC, n)
    P[k, k] = P[i, i] = zero(CC)
    P[k, i] = P[i, k] = one(CC)
    B = P * B * transpose(P)
    S = P * S
    E = identity_matrix(CC, n)
    for j in k+1:n
      E[j, k] = -B[j, k] / B[k, k]
    end
    B = E * B * transpose(E)
    S = E * S
  end
  return S, [B[i, i] for i in 1:n]
end

################################################################################
#
#  Random tests
#
################################################################################

# kind = :generic: bidegree (3, 3) (canonical model on X W - Y Z);
# :theta_null: y^3 + a(x) y + b(x), deg a <= 3, deg b = 5 (on the cone
# X Z - Y^2); :hyperelliptic: y^2 = h(x), deg h = 9 or 10
function _random_g4_curve(kind::Symbol; coeff_range = -5:5, field = QQ)
  S, (x, y) = polynomial_ring(field, [:x, :y]; cached = false)
  # over a number field K = Q(a): sum_i c_i a^i with c_i in coeff_range
  basis = field isa QQField ? [one(field)] : [gen(field)^i for i in 0:degree(field)-1]
  rnd() = sum(rand(coeff_range) * b for b in basis)
  function nonzero()
    c = rnd()
    while iszero(c)
      c = rnd()
    end
    return c
  end
  if kind === :generic
    corners = ((0, 0), (3, 0), (0, 3), (3, 3))
    return sum((((i, j) in corners) ? nonzero() : rnd()) * x^i * y^j for i in 0:3 for j in 0:3)
  elseif kind === :theta_null
    return y^3 + sum(rnd() * x^i for i in 0:3) * y + x^5 + sum(rnd() * x^i for i in 0:4)
  elseif kind === :hyperelliptic
    d = rand(9:10)
    return x^d + sum(rnd() * x^i for i in 0:d-1) - y^2
  end
  error("kind must be :generic, :theta_null or :hyperelliptic.")
end

@doc raw"""
    random_g4_reconstruction_tests(n; kind = :generic, prec = 300, kw...)

Compute the period matrices of `n` random genus 4 curves of the given kind
(`:generic`, `:theta_null` or `:hyperelliptic`, see `_random_g4_curve`),
reconstruct them and compare with `compare_with_original` (Bouchet's
invariants; for hyperelliptic curves the branch points). Keywords are passed
to `riemann_surface`. Curves of the wrong genus are skipped.
"""
function random_g4_reconstruction_tests(n::Int; kind::Symbol = :generic, prec::Int = 300, kw...)
  results = []
  done = 0
  while done < n
    f = _random_g4_curve(kind)
    RS = riemann_surface(f, prec; kw...)
    RSR.genus(RS) == 4 || continue
    kind === :hyperelliptic || length(RSR._newton_polygon_interior_points(f)) == 4 || continue
    done += 1
    t = @elapsed r = try
      _compare_with_original_g4(f, RS, kind === :hyperelliptic)
    catch e
      (ok = false, all_recognized = false, log2_diff = NaN, recognized = nothing, case = :error,
       error = sprint(showerror, e))
    end
    println(rpad(string(done), 4), rpad(string(r.ok), 7), rpad(string(r.case), 22),
            lpad(string(round(r.log2_diff, digits = 1)), 8),
            lpad(string(round(t, digits = 2), "s"), 9), "  ", f)
    r.ok == true || println("    ", r)
    push!(results, (f = f, result = r, time = t))
  end
  nok = count(r -> r.result.ok == true, results)
  println("$nok of $n reconstructions agree with the original curve (log2_diff < -prec/2).")
  return results
end

################################################################################
#
#  A direct check: points of the curve in the coordinates of the
#  reconstruction (independent of the invariants)
#
#  Points P of the plane curve f(x, y) = 0 are mapped to the coordinates of
#  the reconstruction: y_k = omega_k(P) (the differentials of the big period
#  matrix, without dx), z = Omega_A'^-1 y (the normalized differentials for
#  the period matrix tau' actually used, Omega' = Omega [D^T B^T; C^T A^T] for
#  tau' = (A tau + B)(C tau + D)^-1) and x_k = mu_k <grad theta[xi_k](0, tau'), z>
#  with grad theta[xi_5] = sum_k mu_k grad theta[xi_k] (the tritangent plane
#  of xi_k is x_k = 0, the one of xi_5 is x_1 + .. + x_4 = 0). The quadric and
#  the cubic must vanish there.
#
################################################################################

@doc raw"""
    check_g4_reconstruction(f, prec::Int = 300; points::Int = 6, kw...) -> NamedTuple

Reconstruct the genus 4 curve f(x, y) = 0 (over QQ) from its period matrix
and compare: `case`, `log2_residual` (non-hyperelliptic: log2 of the largest
relative value of the quadric and the cubic at points of the curve;
hyperelliptic: as in compare_with_original; about -prec/2 or below if the
reconstruction is right) and `info` (see `_g4_curve_from_tangents`).
Keywords are passed to `riemann_surface`; non-hyperelliptic curves use the
original model (`model = :original`, `superelliptic = false`).
"""
function check_g4_reconstruction(f::MPolyRingElem, prec::Int = 300; points::Int = 6, kw...)
  hyperelliptic = _is_hyperelliptic_model(f)
  RS = hyperelliptic ? riemann_surface(f, prec; kw...) :
                       riemann_surface(f, prec; superelliptic = false, model = :original, kw...)
  @req RSR.genus(RS) == 4 "The curve does not have genus 4."
  data = reconstruct_curve_g4_data(small_period_matrix(RS))
  if data.case === :hyperelliptic
    @req hyperelliptic "The reconstruction is hyperelliptic, the curve is not of the form y^2 = h(x)."
    return (case = data.case, log2_residual = _g4_moebius_distance(f, data.info.rosenhain), info = data.info)
  end
  return (case = data.case, log2_residual = _g4_residual_on_points(RS, data, points), info = data.info)
end

# y^2 = h(x) or c y^2 + h(x) = 0
function _is_hyperelliptic_model(f::MPolyRingElem)
  for (c, e) in zip(coefficients(f), exponent_vectors(f))
    (e[2] == 0 || e == [0, 2]) || return false
  end
  return true
end

function _g4_residual_on_points(RS, data, npoints::Int)
  C = RSR.computational_model(RS)
  @req isone(C.transform) "The check needs the original model (model = :original)."
  CC = base_ring(data.tau)
  prec = precision(CC)
  L = _g4_coordinates_from_differentials(change_base_ring(CC, big_period_matrix(RS)), data)
  quadric, cubic = data.curve
  qscale = maximum(_abs64, coefficients(quadric))
  cscale = maximum(_abs64, coefficients(cubic))
  # points of the curve and the differentials there
  factor_set, factor_matrix, _, _ = RSR.differential_form_data(C)
  v = RSR.embedding(C)
  factors = [RSR._embed_mpoly(p, v, prec) for p in factor_set]
  fC = RSR.complex_defining_polynomial(C, prec)
  worst = -Inf
  for k in 1:npoints
    x0 = CC(0.37 + 0.61*k, -0.29 + 0.43*k) / 3
    for y0 in RSR.fiber(fC, x0)[1:min(2, end)]
      values = [evaluate(p, [x0, y0]) for p in factors]
      y = [prod(values[l]^factor_matrix[l, j] for l in eachindex(values)) for j in 1:4]
      xpt = L * matrix(CC, 4, 1, y)
      xs = [xpt[i, 1] for i in 1:4]
      norm = maximum(_abs64, xs)
      rq = _abs64(evaluate(quadric, xs)) / (qscale * norm^2)
      rc = _abs64(evaluate(cubic, xs)) / (cscale * norm^3)
      worst = max(worst, _safe_log2(rq), _safe_log2(rc))
    end
  end
  return worst
end

################################################################################
#
#  The model over Q (or a number field): exact checks
#
################################################################################

@doc raw"""
    check_rational_reconstruction_g4(f, prec::Int = 450; place = nothing, normalize = true, reduce_units = true, kw...) -> NamedTuple

For a curve f(x, y) = 0 over K = QQ or a number field (embedded by `place`,
by default the first infinite place) whose differentials have Baker's basis
x^(i-1) y^(j-1) dx / f_y ((i, j) the interior points of the Newton polygon):
reconstruct_rational_curve_g4 over K of its big period matrix (original model)
and the exact check that Q vanishes on the monomials m and that f divides
Gamma(m) (nonzero, since Gamma is not in the ideal of Q). Keywords are passed
to `riemann_surface`.
"""
function check_rational_reconstruction_g4(f::MPolyRingElem, prec::Int = 450; place = nothing,
                                          normalize::Bool = true, reduce_units::Bool = true, kw...)
  K = base_ring(f)
  if K isa QQField
    RS = riemann_surface(f, prec; superelliptic = false, model = :original, kw...)
  else
    place === nothing && (place = infinite_places(K)[1])
    RS = riemann_surface(f, place, prec; superelliptic = false, model = :original, kw...)
  end
  @req RSR.genus(RS) == 4 "The curve does not have genus 4."
  @req length(RSR._newton_polygon_interior_points(f)) == 4 "The Newton polygon of f does not have 4 interior points."
  Q, Gamma = reconstruct_rational_curve_g4(big_period_matrix(RS), K; place = place, normalize, reduce_units)
  x, y = gens(parent(f))
  m = [x^(p[1] - 1) * y^(p[2] - 1) for p in RSR._newton_polygon_interior_points(f)]
  Gm = evaluate(Gamma, m)
  return (quadric = Q, cubic = Gamma, quadric_vanishes = iszero(evaluate(Q, m)),
          cubic_vanishes = !iszero(Gm) && divides(Gm, f)[1])
end

@doc raw"""
    random_rational_g4_reconstruction_tests(n; kind = :generic, field = QQ, prec = 450, all_places = false, normalize = true, reduce_units = true, kw...)

check_rational_reconstruction_g4 for `n` random genus 4 curves of the given
kind (`:generic` or `:theta_null`, see `_random_g4_curve`) over `field`; with
`all_places`, for every infinite place of the field. Keywords are passed to
`riemann_surface`.
"""
function random_rational_g4_reconstruction_tests(n::Int; kind::Symbol = :generic, field = QQ,
                                                 prec::Int = 450, all_places::Bool = false,
                                                 normalize::Bool = true, reduce_units::Bool = true, kw...)
  @req kind in (:generic, :theta_null) "kind must be :generic or :theta_null."
  places = field isa QQField ? [nothing] :
           (all_places ? infinite_places(field) : [infinite_places(field)[1]])
  results = []
  done = 0
  while done < n
    f = _random_g4_curve(kind; field = field)
    length(RSR._newton_polygon_interior_points(f)) == 4 || continue
    RSR.genus(riemann_surface(f, 64)) == 4 || continue
    done += 1
    for v in places
      t = @elapsed r = try
        check_rational_reconstruction_g4(f, prec; place = v, normalize, reduce_units, kw...)
      catch e
        (quadric_vanishes = false, cubic_vanishes = false, error = sprint(showerror, e))
      end
      ok = r.quadric_vanishes && r.cubic_vanishes
      println(rpad(string(done), 4), rpad(string(ok), 7),
              lpad(string(round(t, digits = 2), "s"), 9), "  ", f)
      ok || println("    ", r)
      push!(results, (f = f, place = v, ok = ok, result = r, time = t))
    end
  end
  nok = count(r -> r.ok, results)
  println("$nok of $(length(results)) rational reconstructions verified exactly.")
  return results
end
