################################################################################
#
#  ReconstructG4.jl : genus 4 curves from their theta constants
#
#  Hanselman, Pieper, Schiavone, "Equations of genus 4 curves from their
#  theta constants" (arXiv:2402.03160), following the Magma package
#  reconstructing-g4 (magma/reconstruction.m). The case is decided by the
#  number of vanishing even theta constants of the (Siegel reduced) tau:
#
#   0   generic: the tritangent planes H_i, H_i' (generalized Jacobi
#       derivative formula, the tables of ReconstructG4Tables.jl),
#       the bitangents l_i of the Prym (Schottky-Jung and Aronhold-Weber),
#       the map phi with phi(H_i H_i') = lambda_i l_i^2, the quadric
#       Q = ker(phi) and the Cayley cubic Gamma with Gamma^2 = det(Delta);
#   1   one vanishing theta null (the quadric is a cone): tau is transformed
#       so that the vanishing characteristic is (0,1,1,1,0,1,0,1); then the
#       Prym is hyperelliptic and its bitangents are replaced by the lines
#       through pairs of its Weierstrass points (Remark 4.5); otherwise as in
#       the generic case (the Cayley cubic is also exact here);
#   10  hyperelliptic: Rosenhain invariants by Takase's formula.
#
#  Characteristics are bit tuples (a1, ..., a4, b1, ..., b4), the keys of
#  theta_constants. Uses ThetaCharacteristics.jl, ReconstructCurvesG123.jl
#  (Takase's quotients, Weber moduli, the genus 3 signs and bitangents),
#  ReconstructNumerics.jl (square roots of forms) and ReconstructG4Tables.jl;
#  the tests and comparisons are in ReconstructG4Tests.jl.
#
#  Usage:
#    r = reconstruct_curve_g4_data(small_period_matrix(RS))
#    r.case, r.curve     # [quadric, cubic] in P^3, or a hyperelliptic curve
#    check_g4_reconstruction(f, 300)    # compares with the curve f(x, y) = 0
#    reconstruct_rational_curve_g4(big_period_matrix(RS))   # a model over QQ
#
################################################################################

@doc raw"""
    reconstruct_curve_g4(tau::AcbMatrix)

A model of the genus 4 curve with small period matrix `tau`: `[quadric,
cubic]` (polynomials in four variables over the complex field of `tau`) for a
non-hyperelliptic curve, or a hyperelliptic curve y^2 = x (x-1) prod (x -
lambda_l) over that field.
"""
_reconstruct_genus4(tau::AcbMatrix) = reconstruct_curve_g4_data(tau).curve

@doc raw"""
    reconstruct_curve_g4_data(tau::AcbMatrix) -> NamedTuple

The reconstruction together with the data needed to check it: `case`
(`:generic`, `:vanishing_theta_null` or `:hyperelliptic`), `curve`, `tau`
(the period matrix actually used, `transform`(tau) as in
`Hecke.siegel_transform`), `transform` (a symplectic 8 x 8 matrix) and
`info` (numerical diagnostics, log2 of relative sizes; see
`_g4_curve_from_tangents`).

The balls of the result contain the exact curve for every tau in the balls of
`tau` (ball arithmetic through all steps; the kernels assume the ranks the
theory predicts). They are pessimistic: for non-hyperelliptic curves the
radii are about 2^110 to 2^150 times the radius of tau, for hyperelliptic
curves a few bits. For a result with relative radius 2^-p, compute tau with
about p + 150 bits (resp. p + 10). This is much cheaper than first-order
certification with the theta derivatives (tried, see the git history: the
second order theta jets alone cost more than 10 times the reconstruction).
"""
function reconstruct_curve_g4_data(tau::AcbMatrix)
  @req nrows(tau) == 4 && ncols(tau) == 4 "tau must be a 4 x 4 matrix."
  T, tau_red = Hecke.siegel_reduction(tau)
  return _g4_reconstruct_reduced(tau_red, T, precision(base_ring(tau)))
end

# The reconstruction from a reduced tau (T: the transformation of the
# reduction); prec: the precision of the original tau (for the vanishing
# theta constants).
function _g4_reconstruct_reduced(tau_red::AcbMatrix, T::ZZMatrix, prec::Int)
  th = theta_constants(tau_red)
  vanishing = _vanishing_even_theta_constants(th, prec)
  if isempty(vanishing)
    quadric, cubic, info = _g4_generic(th)
    info = merge(info, (radius_thetas = _log2_relative_radius([th[c] for c in keys(th) if _is_even(c)]),))
    return (case = :generic, curve = [quadric, cubic], tau = tau_red, transform = T, info = info,
            vanishing = vanishing, move = identity_matrix(ZZ, 8))
  elseif length(vanishing) == 1
    M, tau2, th2 = _g4_move_vanishing_characteristic(tau_red, vanishing[1], prec)
    quadric, cubic, info = _g4_vanishing_theta_null(th2)
    info = merge(info, (radius_thetas = _log2_relative_radius([th2[c] for c in keys(th2) if _is_even(c)]),))
    return (case = :vanishing_theta_null, curve = [quadric, cubic], tau = tau2,
            transform = M * T, info = info, vanishing = vanishing, move = M)
  elseif length(vanishing) == 10
    X, info = _g4_hyperelliptic(th, vanishing)
    return (case = :hyperelliptic, curve = X, tau = tau_red, transform = T, info = info,
            vanishing = vanishing, move = identity_matrix(ZZ, 8))
  end
  error("$(length(vanishing)) even theta constants vanish; expected 0 (generic), 1 (vanishing theta null) or 10 (hyperelliptic). Is the Jacobian decomposable, or the precision too low?")
end

################################################################################
#
#  The three cases
#
################################################################################

function _g4_generic(th)
  tritangents = _g4_tritangents(th)
  bitangents = _g4_prym_bitangents(th)
  # the bitangents l_i of the Prym corresponding to the pairs (H_i, H_i')
  # (Milne's bijection), in the numbering of _aronhold_bitangents
  selected = [bitangents[i] for i in _g4_prym_bitangent_selection()]
  return _g4_curve_from_tangents(tritangents, selected)
end

# As in the generic case; the Cayley cubic (Lemma 3.8) also works when the
# quadric is a cone, so no square root modulo the cone is needed (Magma:
# ComputeCurveVanTheta0 with ComputeSquareRootOnCone).
function _g4_vanishing_theta_null(th)
  tritangents = _g4_tritangents(th)
  lines = _g4_hyperelliptic_prym_lines(th)
  selected = [lines[i] for i in _g4_weierstrass_line_selection()]
  return _g4_curve_from_tangents(tritangents, selected)
end

# The 10 vanishing even characteristics are eta_U + eta_i (i = 1..10, eta_10 = 0
# for the branch point at infinity), so eta_i = v_i + v_10 for any numbering
# v_1, ..., v_10 (a numbering of the branch points).
function _g4_hyperelliptic(th, vanishing)
  CC = parent(th[ntuple(_ -> 0, 8)])
  lambdas = _g4_rosenhain(th, vanishing)
  CCx, x = polynomial_ring(CC, :x; cached = false)
  f = x*(x - 1)*prod(x - l for l in lambdas)
  return hyperelliptic_curve(f), (rosenhain = lambdas,)
end

# The Rosenhain invariants lambda_3..lambda_9
function _g4_rosenhain(th, vanishing)
  v = sort([collect(c) for c in vanishing])
  eta = [mod.(v[i] + v[10], 2) for i in 1:9]
  push!(eta, zeros(Int, 8))
  U = union([i for i in 1:10 if _is_odd_characteristic(eta[i])], [10])
  eta_U = mod.(sum(eta[i] for i in U), 2)
  @req all(mod.(eta_U + eta[i], 2) == v[i] for i in 1:10) "The vanishing even theta constants do not have the configuration of a hyperelliptic curve."
  thetas_sq = Dict(ch => x^2 for (ch, x) in th)
  return [_takase_quotient(thetas_sq, eta, U, 1, l, 2) for l in 3:9]
end

################################################################################
#
#  Tritangent planes
#
#  In the coordinates x_1..x_4 in which the tritangent planes of the odd
#  characteristics xi_1, ..., xi_5 (_g4_tritangent_basis) are x_k = 0 and
#  x_1 + ... + x_4 = 0, the plane of an odd characteristic c is
#  sum_k D(xi_1, .., c, .., xi_4) / D(xi_1, .., xi_5, .., xi_4) x_k = 0
#  (c resp. xi_5 in position k, Cramer's rule; eq. (4.1)). The Jacobian
#  nullvalues D are sums of two products of six theta constants (Fay's
#  generalized Jacobi formula), _g4_jacobian_nullvalue_table() in
#  ReconstructG4Tables.jl; the denominators are the entries of the first pair
#  (chi_1 = xi_5).
#
################################################################################

function _g4_jacobian_nullvalue(th, formula)
  S1, S2, signs = formula
  return signs[1]*prod(th[c] for c in S1) + signs[2]*prod(th[c] for c in S2)
end

# tritangents[i][j]: the coefficients of the plane of the characteristic
# _g4_tritangent_pairs()[i][j] (H_i for j = 1, H_i' for j = 2)
function _g4_tritangents(th)
  table = _g4_jacobian_nullvalue_table()
  normalization = [_g4_jacobian_nullvalue(th, table[1][1][k]) for k in 1:4]
  return [[[_g4_jacobian_nullvalue(th, table[i][j][k]) / normalization[k] for k in 1:4]
           for j in 1:2] for i in 1:10]
end

################################################################################
#
#  Bitangents of the Prym (generic case)
#
#  theta_X[d]^2 = theta_C[0 d1; 0 d2] theta_C[0 d1; 1 d2] for the genus 3
#  curve X with Jac(X) = Prym (Schottky-Jung, [FR70]); the signs of the square
#  roots are fixed by Riemann's quartic relations (_correct_theta_signs_g3),
#  up to signs that only change the signs of whole bitangent vectors.
#
################################################################################

function _g4_prym_bitangents(th)
  CC = parent(th[ntuple(_ -> 0, 8)])
  th3 = Dict{NTuple{6, Int}, AcbFieldElem}()
  for c in even_theta_characteristics(3)
    p = th[(0, c[1], c[2], c[3], 0, c[4], c[5], c[6])] * th[(0, c[1], c[2], c[3], 1, c[4], c[5], c[6])]
    th3[Tuple(c)] = RSR._rotated_power(p, 1//2)      # any branch; away from the branch cut
  end
  for c in odd_theta_characteristics(3)
    th3[Tuple(c)] = zero(CC)
  end
  th3 = _correct_theta_signs_g3(th3)
  return _aronhold_bitangents(_moduli_from_theta(th3))
end

################################################################################
#
#  The vanishing theta null case: moving the characteristic, the lines through
#  the Weierstrass points of the hyperelliptic Prym
#
################################################################################

# M o c for tau -> (A tau + B)(C tau + D)^-1 (theta[M o c](M tau) is a multiple
# of theta[c](tau); characteristics in bits; checked numerically)
function _g4_characteristic_action(M::Matrix{Int}, c)
  g = div(size(M, 1), 2)
  A, B, C, D = M[1:g, 1:g], M[1:g, g+1:2*g], M[g+1:2*g, 1:g], M[g+1:2*g, g+1:2*g]
  a, b = collect(c[1:g]), collect(c[g+1:2*g])
  new_a = D*a - C*b + [sum(C[i, k]*D[i, k] for k in 1:g) for i in 1:g]
  new_b = -B*a + A*b + [sum(A[i, k]*B[i, k] for k in 1:g) for i in 1:g]
  return Tuple(mod.(vcat(new_a, new_b), 2))
end

function _symplectic_generators(g::Int)
  I = _integer_identity(g)
  Z = zeros(Int, g, g)
  gens = [[Z I; -I Z]]
  for i in 1:g, j in i:g
    S = zeros(Int, g, g)
    S[i, j] = S[j, i] = 1
    push!(gens, [I S; Z I])
  end
  for i in 1:g, j in 1:g
    i == j && continue
    A = copy(I)
    A[i, j] = 1
    Ainv = copy(I)
    Ainv[i, j] = -1
    push!(gens, [A Z; Z permutedims(Ainv)])
  end
  return gens
end

_integer_identity(g::Int) = [i == j ? 1 : 0 for i in 1:g, j in 1:g]

# A short word M in the generators with M o v = target (breadth first search
# on the 136 even characteristics).
function _symplectic_matrix_moving(v, target)
  g = div(length(v), 2)
  gens = _symplectic_generators(g)
  start = _integer_identity(2*g)
  seen = Dict(Tuple(v) => start)
  queue = [Tuple(v)]
  while !isempty(queue)
    c = popfirst!(queue)
    c == Tuple(target) && return seen[c]
    for G in gens
      M = G * seen[c]
      d = _g4_characteristic_action(M, Tuple(v))
      haskey(seen, d) && continue
      seen[d] = M
      push!(queue, d)
    end
  end
  error("No symplectic matrix found (internal error).")
end

function _g4_move_vanishing_characteristic(tau::AcbMatrix, v, prec::Int = precision(base_ring(tau)))
  target = (0, 1, 1, 1, 0, 1, 0, 1)
  M = _symplectic_matrix_moving(v, target)
  @assert _g4_characteristic_action(M, Tuple(v)) == target
  MZ = matrix(ZZ, M)
  tau2 = Hecke.siegel_transform(MZ, tau)
  tau2 = (tau2 + transpose(tau2)) * inv(base_ring(tau2)(2))
  th2 = theta_constants(tau2)
  vanishing = _vanishing_even_theta_constants(th2, prec)
  @req vanishing == [target] "Moving the vanishing even theta constant failed (vanishing after the transformation: $vanishing)."
  return MZ, tau2, th2
end

# The Prym is hyperelliptic with Mumford's eta map (the vanishing genus 3
# characteristic is (1,1,1,1,0,1) = eta_U): its Weierstrass points on the conic
# (1 : t : t^2), t = 0, 1, lambda_3..lambda_7, oo, and the 28 lines through
# pairs of them (in the order (1,2), (1,3), ..., (7,8)).
function _g4_hyperelliptic_prym_lines(th)
  CC = parent(th[ntuple(_ -> 0, 8)])
  o, z = one(CC), zero(CC)
  thetas_sq = Dict{NTuple{6, Int}, AcbFieldElem}()
  for c in Iterators.product(ntuple(_ -> 0:1, 6)...)
    c = reverse(c)
    thetas_sq[c] = th[(0, c[1], c[2], c[3], 0, c[4], c[5], c[6])] * th[(0, c[1], c[2], c[3], 1, c[4], c[5], c[6])]
  end
  eta = _mumford_eta()
  U = union([i for i in 1:8 if _is_odd_characteristic(eta[i])], [8])
  lambdas = [_takase_quotient(thetas_sq, eta, U, 1, l, 2) for l in 3:7]
  points = vcat([[o, z, z], [o, o, o]], [[o, l, l^2] for l in lambdas], [[z, z, o]])
  cross(p, q) = [p[2]*q[3] - p[3]*q[2], p[3]*q[1] - p[1]*q[3], p[1]*q[2] - p[2]*q[1]]
  return [cross(points[i], points[j]) for i in 1:8 for j in i+1:8]
end

################################################################################
#
#  The curve from the tritangent pairs and the bitangents (Magma: ComputeCurve,
#  ComputeCurveVanTheta0; the paper, Section 4)
#
################################################################################

# (h h'^T + h' h^T)/2, the symmetric matrix of the quadric H H'
function _sym_outer(h::Vector{AcbFieldElem}, h2::Vector{AcbFieldElem})
  CC = parent(h[1])
  return matrix(CC, 4, 4, [(h[i]*h2[j] + h2[i]*h[j]) / 2 for i in 1:4 for j in 1:4])
end

# the coefficients of (b0 y0 + b1 y1 + b2 y2)^2 at y0^2, y0y1, y0y2, y1^2, y1y2, y2^2
_square_coefficients(b) = [b[1]^2, 2*b[1]*b[2], 2*b[1]*b[3], b[2]^2, 2*b[2]*b[3], b[3]^2]

function _quadratic_form(R::MPolyRing, M::AcbMatrix)
  xs = gens(R)
  return sum(M[i, j]*xs[i]*xs[j] for i in 1:4 for j in 1:4)
end

@doc raw"""
    _g4_curve_from_tangents(tritangents, bitangents) -> quadric, cubic, info

The steps (4)-(10) of the paper: the relations between the products H_i H_i'
(3 of them; V_{C,eta} has dimension 7), the lambda_i with
phi(H_i H_i') = lambda_i l_i^2 (unique up to scaling), the quadric
Q = ker(phi), the right inverse psi of phi with image W_eta (W_eta^perp from
Lemma 3.8) and the Cayley cubic Gamma = sqrt(det(Delta)) (an exact square in
P^3, also when Q is a cone).

`info`: log2 of relative sizes that should be about -precision: `relations`
(the rank defect of the H_i H_i'), `lambda` (the linear system for the
lambda_i: not small means that the bitangents do not match the tritangent
pairs) and `square_root` (the residual of the square root); `radii`: log2
of the relative radii of the balls after each step.
"""
function _g4_curve_from_tangents(tritangents, bitangents)
  CC = parent(tritangents[1][1][1])
  r = length(tritangents)
  mats = [_sym_outer(t[1], t[2]) for t in tritangents]
  upper = [(i, j) for i in 1:4 for j in i:4]
  X = matrix(CC, r, 10, [m[i, j] for m in mats for (i, j) in upper])
  # the relations n_k (sum_i n_k[i] H_i H_i' = 0) and 7 independent products
  relations_data = _numerical_kernel_data(transpose(X); nullity = 3)
  relations, basis = relations_data.kernel, relations_data.pivot_columns
  q_relations = _log2_relative_residual(transpose(X), relations)
  @req q_relations < -precision(CC) / 4 "The products of the tritangent pairs do not satisfy 3 linear relations (log2 residual $q_relations); is the precision too low?"
  fsq = matrix(CC, r, 6, [c for b in bitangents for c in _square_coefficients(b)])
  # lambda: sum_i lambda_i n_k[i] l_i^2 = 0 for k = 1, 2, 3
  N = zero_matrix(CC, r, 18)
  for k in 1:3, i in 1:r, j in 1:6
    N[i, 6*(k - 1) + j] = relations[i, k] * fsq[i, j]
  end
  lambda = numerical_kernel(transpose(N); nullity = 1)[1]
  q_lambda = _log2_relative_residual(transpose(N), lambda)
  @req q_lambda < -precision(CC) / 4 "The bitangents do not match the tritangent pairs (log2 residual $q_lambda); is the precision too low?"
  # phi on the basis H_i H_i', i in basis, of V_{C,eta}
  phi = matrix(CC, 7, 6, [lambda[i, 1] * fsq[i, j] for i in basis for j in 1:6])
  kernel_phi = numerical_kernel(transpose(phi); nullity = 1)[1]
  Qm = sum(kernel_phi[a, 1] * mats[basis[a]] for a in 1:7)
  # V_{C,eta}^perp (trace pairing) and Q' = (Q1^-1 + Q2^-1)^-1 in W_eta^perp
  perp = numerical_kernel(X; nullity = 3)[1]
  function perp_matrix(k)
    W = zero_matrix(CC, 4, 4)
    for (l, (i, j)) in enumerate(upper)
      W[i, j] = perp[l, k]
    end
    return (W + transpose(W)) * inv(CC(2))
  end
  Qsharp = _inv_precond(_inv_precond(perp_matrix(1)) + _inv_precond(perp_matrix(2)))
  extra = [sum(mats[basis[a]][i, j] * Qsharp[i, j] for i in 1:4 for j in 1:4) for a in 1:7]
  phiext = zero_matrix(CC, 7, 7)
  for a in 1:7
    for j in 1:6
      phiext[a, j] = phi[a, j]
    end
    phiext[a, 7] = extra[a]
  end
  Tinv = _inv_precond(transpose(phiext))
  R, _ = polynomial_ring(CC, [:x1, :x2, :x3, :x4]; cached = false)
  dual = [_quadratic_form(R, mats[i]) for i in basis]
  d = [sum(dual[a] * Tinv[a, c] for a in 1:7) for c in 1:6]
  # Delta = [d1 d2 d3; d2 d4 d5; d3 d5 d6]
  G = d[1]*(d[4]*d[6] - d[5]^2) - d[2]*(d[2]*d[6] - d[5]*d[3]) + d[3]*(d[2]*d[5] - d[4]*d[3])
  quadric = _quadratic_form(R, Qm)
  cubic, q_sqrt = _sqrt_homogeneous(G)
  # log2 of the relative radii after each step
  radii = (tritangents = _log2_relative_radius(vcat(tritangents...)), bitangents = _log2_relative_radius(bitangents),
           relations = _log2_relative_radius(relations), lambda = _log2_relative_radius(lambda),
           kernel_phi = _log2_relative_radius(kernel_phi), Qsharp = _log2_relative_radius(Qsharp),
           Tinv = _log2_relative_radius(Tinv), Delta = _log2_relative_radius(d), G = _log2_relative_radius(G),
           quadric = _log2_relative_radius(quadric), cubic = _log2_relative_radius(cubic))
  return quadric, cubic, (relations = q_relations, lambda = q_lambda, square_root = q_sqrt, radii = radii)
end

################################################################################
#
#  A model over Q (or a number field) from the big period matrix
#
#  Magma: RationalReconstructCurveG4. The small period matrix determines the
#  curve only up to isomorphism over C; the big period matrix Pi also fixes
#  a basis of the differentials. If that basis is defined over K (e.g. the
#  basis of big_period_matrix(RS) for a curve over K), the canonical model in
#  the coordinates of these differentials is defined over K up to scaling.
#
################################################################################

# x = L y: the coordinates x of the reconstruction from the coordinates y of
# the differentials of the big period matrix Omega = [Omega_A Omega_B] (rows:
# the differentials, tau = Omega_A^-1 Omega_B): z = Omega_A'^-1 y (the
# normalized differentials for tau' = T(tau), Omega' = Omega [D^T B^T; C^T A^T]
# for T = [A B; C D]) and x_k = mu_k <grad theta[xi_k](0, tau'), z> with
# grad theta[xi_5] = sum_k mu_k grad theta[xi_k] (the tritangent plane of xi_k
# is x_k = 0, the one of xi_5 is x_1 + .. + x_4 = 0). Magma: TritangentPlanes.
function _g4_coordinates_from_differentials(Omega::AcbMatrix, data)
  tau = data.tau
  CC = base_ring(tau)
  T = change_base_ring(CC, data.transform)
  Cb, D = T[5:8, 1:4], T[5:8, 5:8]
  OmegaA = Omega[:, 1:4] * transpose(D) + Omega[:, 5:8] * transpose(Cb)
  jets = Hecke.theta_jets([zero(CC) for _ in 1:4], tau, 1)
  unit(i) = Tuple(j == i ? 1 : 0 for j in 1:4)
  grad(c) = [jets[c][unit(i)] for i in 1:4]
  xi = _g4_tritangent_basis()
  Gm = matrix(CC, 4, 4, [grad(xi[k])[i] for i in 1:4 for k in 1:4])     # columns: grad xi_k
  mu = _solve_precond(Gm, matrix(CC, 4, 1, grad(xi[5])))
  return diagonal_matrix([mu[k, 1] for k in 1:4]) * transpose(Gm) * _inv_precond(OmegaA)
end

# K, the embedding K -> CC and the recognition CC -> K (nothing on failure)
function _g4_field_data(K, place, CC::AcbField)
  if K isa QQField
    return QQ, (c -> CC(c)), _recognize_rational, nothing
  end
  v = place === nothing ? infinite_places(K)[1] : place
  embed(c) = CC(RSR._embed_coefficient(c, v.embedding, precision(CC)))
  function recognize(a)
    try
      return RSR.algebraize_element(a, K, v)
    catch
      return nothing
    end
  end
  return K, embed, recognize, v
end

# The normalized multiple of a polynomial p over QQ or a number field K:
# over QQ the primitive integral multiple with positive leading coefficient;
# over K an integral multiple (coefficients in the maximal order O_K) and, if
# the ideal of O_K generated by the coefficients is principal, divided by a
# generator (so the coefficients generate O_K; unique up to a unit). With
# reduce_units, then multiplied by the unit that makes the coefficients
# smallest (_reduce_by_units).
function _normalize_model(p::MPolyRingElem{QQFieldElem}; reduce_units::Bool = true)
  d = reduce(lcm, [denominator(c) for c in coefficients(p)]; init = ZZ(1))
  n = reduce(gcd, [numerator(d * c) for c in coefficients(p)]; init = ZZ(0))
  p = (d // n) * p
  return leading_coefficient(p) < 0 ? -p : p
end

function _normalize_model(p::MPolyRingElem; reduce_units::Bool = true)
  K = base_ring(p)
  OK = maximal_order(K)
  d = reduce(lcm, [denominator(c, OK) for c in coefficients(p)]; init = ZZ(1))
  p = d * p
  I = reduce(+, [OK(c) * OK for c in coefficients(p)])
  principal, g = is_principal_with_data(I)
  principal && (p = inv(K(g)) * p)
  reduce_units && (p = _reduce_by_units(p))
  return p
end

# p multiplied by the unit u of O_K for which the vector of the logarithms
# x_v = log max_i |v(u c_i)| (v the infinite places, c_i the coefficients)
# is closest to the line spanned by (1, .., 1) (weights 1 for real and 2 for
# complex places); found by coordinate descent on the exponents of the
# fundamental units (rounded optimal steps). Then, if K has a real place, the
# leading coefficient is made positive at the first real place.
function _reduce_by_units(p::MPolyRingElem)
  K = base_ring(p)
  OK = maximal_order(K)
  U, mU = unit_group(OK)
  units = [K(mU(U[i])) for i in 2:ngens(U)]       # U[1]: the torsion units
  places = infinite_places(K)
  weights = [is_real(v) ? 1 : 2 for v in places]
  value(c, v) = RSR._c64(evaluate(c, v.embedding, 128))
  logabs(c, v) = log(abs(value(c, v)))
  if !isempty(units)
    cs = collect(coefficients(p))
    x = [maximum(logabs(c, v) for c in cs) for v in places]
    x .-= sum(weights .* x) / degree(K)
    ls = [[logabs(u, v) for v in places] for u in units]
    inner(a, b) = sum(weights .* a .* b)
    e = zeros(Int, length(units))
    for _ in 1:100
      changed = false
      for i in eachindex(units)
        k = round(Int, -inner(x, ls[i]) / inner(ls[i], ls[i]))
        k == 0 && continue
        x .+= k .* ls[i]
        e[i] += k
        changed = true
      end
      changed || break
    end
    p = prod(units[i]^e[i] for i in eachindex(units)) * p
  end
  real_places = filter(is_real, places)
  if !isempty(real_places) && real(value(leading_coefficient(p), real_places[1])) < 0
    p = -p
  end
  return p
end

@doc raw"""
    reconstruct_rational_curve_g4(Pi::AcbMatrix, K = QQ; place = nothing, normalize = true, reduce_units = true) -> Vector{MPolyRingElem}

The canonical model [Q, Gamma] over K (QQ or a number field, embedded by
`place`, by default its first infinite place) of a non-hyperelliptic genus 4
curve with big period matrix Pi = [Omega_A Omega_B] (4 x 8; the rows: a basis
of the differentials defined over K, e.g. big_period_matrix(RS) for a curve
over K), in the coordinates of these differentials. The reconstruction over
CC (reconstruct_curve_g4_data) is moved to these coordinates with the
gradients of the theta functions; Q is scaled by its largest coefficient,
Gamma is reduced modulo Q times linear forms (zero coefficients at the pivots
of these multiples) and scaled by its largest coefficient, and the
coefficients are recognized in K (algebraize_element). With `normalize`, Q
and Gamma are then made integral and primitive: over QQ with coprime integer
coefficients and positive leading coefficient, over a number field with
coefficients in the maximal order O_K that generate O_K when their ideal is
principal (unique up to a unit; otherwise only integral). With
`reduce_units` (number fields, only with `normalize`) the remaining unit is
chosen to make the coefficients small: the logarithms of the largest
coefficient at the infinite places are balanced by the fundamental units, and
the leading coefficient is made positive at the first real place (if any).
Needs enough precision
for the recognition (about 150 bits are lost in the reconstruction, see
reconstruct_curve_g4_data). Magma: RationalReconstructCurveG4.
"""
function reconstruct_rational_curve_g4(Pi::AcbMatrix, K = QQ; place = nothing, normalize::Bool = true,
                                       reduce_units::Bool = true)
  @req nrows(Pi) == 4 && ncols(Pi) == 8 "Pi must be a 4 x 8 matrix."
  CCin = base_ring(Pi)
  tau = _solve_precond(Pi[:, 1:4], Pi[:, 5:8])
  tau = (tau + transpose(tau)) * inv(CCin(2))
  data = reconstruct_curve_g4_data(tau)
  @req data.case !== :hyperelliptic "The curve is hyperelliptic; only non-hyperelliptic curves are supported."
  CC = base_ring(data.tau)
  L = _g4_coordinates_from_differentials(change_base_ring(CC, Pi), data)
  quadric, cubic = data.curve
  ys = gens(parent(quadric))
  xy = [sum(L[i, j] * ys[j] for j in 1:4) for i in 1:4]
  Qy = evaluate(quadric, xy)
  Gy = evaluate(cubic, xy)
  F, embed, recognize, v = _g4_field_data(K, place, CC)
  S, X = polynomial_ring(F, [:x, :y, :z, :w]; cached = false)
  e2 = _exponent_vectors(4, 2)
  e3 = _exponent_vectors(4, 3)
  monomial(e) = prod(X[j]^e[j] for j in 1:4)
  # the quadric, scaled by its largest coefficient
  qc = [coeff(Qy, e) for e in e2]
  qs = qc[argmax(map(_abs64, qc))]
  Qk = [recognize(c / qs) for c in qc]
  @req all(!isnothing, Qk) "Could not recognize the coefficients of the quadric in K (more precision needed?)."
  QK = sum(Qk[k] * monomial(e2[k]) for k in eachindex(e2))
  # the cubic modulo Q * (linear forms): zero coefficients at the pivots of
  # the multiples X_k Q
  U = matrix(F, 4, 20, [coeff(QK * X[k], e) for k in 1:4 for e in e3])
  _, Ur = rref(U)
  v = [coeff(Gy, e) for e in e3]
  for k in 1:4
    pc = findfirst(c -> !iszero(Ur[k, c]), 1:20)
    f = v[pc]
    for c in 1:20
      iszero(Ur[k, c]) || (v[c] -= f * embed(Ur[k, c]))
    end
    v[pc] = zero(CC)
  end
  cs = v[argmax(map(_abs64, v))]
  Gk = [recognize(c / cs) for c in v]
  @req all(!isnothing, Gk) "Could not recognize the coefficients of the cubic in K (more precision needed?)."
  GK = sum(Gk[k] * monomial(e3[k]) for k in eachindex(e3))
  normalize && return [_normalize_model(QK; reduce_units), _normalize_model(GK; reduce_units)]
  return [QK, GK]
end
