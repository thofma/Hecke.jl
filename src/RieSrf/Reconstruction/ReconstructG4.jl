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
#       derivative formula, the hard-coded table at the end of this file),
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
#  theta_constants. Load after ThetaCharacteristics.jl and
#  ReconstructCurvesG123.jl (theta_constants, _vanishing_even_theta_constants,
#  _moduli_from_theta, _mumford_eta, _takase_quotient, _is_odd_characteristic).
#
#  Usage:
#    r = reconstruct_curve_g4_data(small_period_matrix(RS))
#    r.case, r.curve     # [quadric, cubic] in P^3, or a hyperelliptic curve
#    check_g4_reconstruction(f, 300)    # compares with the curve f(x, y) = 0
#
################################################################################

@doc raw"""
    reconstruct_curve_g4(tau::AcbMatrix)

A model of the genus 4 curve with small period matrix `tau`: `[quadric,
cubic]` (polynomials in four variables over the complex field of `tau`) for a
non-hyperelliptic curve, or a hyperelliptic curve y^2 = x (x-1) prod (x -
lambda_l) over that field.
"""
reconstruct_curve_g4(tau::AcbMatrix) = reconstruct_curve_g4_data(tau).curve

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
    info = merge(info, (radius_thetas = _g4_log2_radius([th[c] for c in keys(th) if _is_even(c)]),))
    return (case = :generic, curve = [quadric, cubic], tau = tau_red, transform = T, info = info,
            vanishing = vanishing, move = identity_matrix(ZZ, 8))
  elseif length(vanishing) == 1
    M, tau2, th2 = _g4_move_vanishing_characteristic(tau_red, vanishing[1], prec)
    quadric, cubic, info = _g4_vanishing_theta_null(th2)
    info = merge(info, (radius_thetas = _g4_log2_radius([th2[c] for c in keys(th2) if _is_even(c)]),))
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
  selected = [bitangents[i] for i in (10, 23, 4, 20, 17, 9, 12, 1, 5, 11)]
  return _g4_curve_from_tangents(tritangents, selected)
end

# As in the generic case; the Cayley cubic (Lemma 3.8) also works when the
# quadric is a cone, so no square root modulo the cone is needed (Magma:
# ComputeCurveVanTheta0 with ComputeSquareRootOnCone).
function _g4_vanishing_theta_null(th)
  tritangents = _g4_tritangents(th)
  lines = _g4_hyperelliptic_prym_lines(th)
  selected = [lines[i] for i in (24, 20, 21, 23, 17, 16, 15, 14, 19, 26)]
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
#  generalized Jacobi formula); for the 10 pairs of _g4_tritangent_pairs they
#  are listed in hard_coded_s1_s2(), for the denominators in
#  _g4_normalization_formulas(). (Checked numerically: D = pi^4 (s1 T1 + s2 T2)
#  for all 84 entries.)
#
################################################################################

_g4_tritangent_basis() = [(1, 1, 1, 0, 1, 1, 1, 0), (1, 0, 1, 0, 0, 0, 1, 0),
                          (1, 1, 1, 0, 0, 0, 1, 0), (1, 0, 1, 0, 0, 1, 1, 0),
                          (0, 1, 1, 0, 0, 1, 0, 0)]

# the pairs (chi_i, chi_i') with chi_i' = chi_i + eta, eta = (0,0,0,0,1,0,0,0)
_g4_tritangent_pairs() = [
  [(0, 1, 1, 0, 0, 1, 0, 0), (0, 1, 1, 0, 1, 1, 0, 0)],
  [(0, 1, 0, 0, 0, 1, 0, 0), (0, 1, 0, 0, 1, 1, 0, 0)],
  [(0, 1, 0, 1, 0, 1, 0, 0), (0, 1, 0, 1, 1, 1, 0, 0)],
  [(0, 1, 1, 1, 0, 1, 0, 0), (0, 1, 1, 1, 1, 1, 0, 0)],
  [(0, 1, 0, 1, 0, 1, 1, 0), (0, 1, 0, 1, 1, 1, 1, 0)],
  [(0, 1, 0, 0, 0, 1, 1, 0), (0, 1, 0, 0, 1, 1, 1, 0)],
  [(0, 1, 0, 0, 0, 1, 1, 1), (0, 1, 0, 0, 1, 1, 1, 1)],
  [(0, 1, 1, 1, 0, 1, 1, 1), (0, 1, 1, 1, 1, 1, 1, 1)],
  [(0, 1, 0, 0, 0, 1, 0, 1), (0, 1, 0, 0, 1, 1, 0, 1)],
  [(0, 1, 1, 0, 0, 1, 0, 1), (0, 1, 1, 0, 1, 1, 0, 1)]]

# D(xi_1, .., xi_5, .., xi_4) (xi_5 in position k) = s1 T1 + s2 T2 (up to pi^4),
# T = products of six theta constants: (S1, S2, (s1, s2)) for k = 1..4
_g4_normalization_formulas() = [
  ([(1, 1, 0, 1, 0, 1, 1, 1), (0, 1, 1, 1, 1, 1, 0, 1), (1, 1, 0, 1, 0, 1, 0, 1),
    (0, 1, 1, 1, 1, 1, 1, 0), (1, 1, 1, 0, 1, 1, 0, 0), (0, 1, 1, 0, 1, 1, 1, 1)],
   [(0, 1, 0, 1, 0, 1, 0, 1), (1, 1, 1, 1, 1, 1, 1, 1), (0, 1, 0, 1, 0, 1, 1, 1),
    (1, 1, 1, 1, 1, 1, 0, 0), (0, 1, 1, 0, 1, 1, 1, 0), (1, 1, 1, 0, 1, 1, 0, 1)], (-1, 1)),
  ([(0, 1, 0, 1, 0, 1, 1, 1), (1, 0, 1, 1, 0, 0, 1, 1), (0, 1, 0, 1, 0, 1, 0, 1),
    (1, 0, 1, 1, 0, 0, 0, 0), (0, 1, 1, 0, 1, 1, 1, 0), (1, 0, 1, 0, 0, 0, 0, 1)],
   [(1, 0, 0, 1, 1, 0, 0, 1), (0, 1, 1, 1, 1, 1, 0, 1), (1, 0, 0, 1, 1, 0, 1, 1),
    (0, 1, 1, 1, 1, 1, 1, 0), (1, 0, 1, 0, 0, 0, 0, 0), (0, 1, 1, 0, 1, 1, 1, 1)], (1, -1)),
  ([(0, 1, 0, 1, 0, 1, 1, 1), (1, 1, 1, 1, 0, 0, 1, 1), (0, 1, 0, 1, 0, 1, 0, 1),
    (1, 1, 1, 1, 0, 0, 0, 0), (0, 1, 1, 0, 1, 1, 1, 0), (1, 1, 1, 0, 0, 0, 0, 1)],
   [(1, 1, 0, 1, 1, 0, 0, 1), (0, 1, 1, 1, 1, 1, 0, 1), (1, 1, 0, 1, 1, 0, 1, 1),
    (0, 1, 1, 1, 1, 1, 1, 0), (1, 1, 1, 0, 0, 0, 0, 0), (0, 1, 1, 0, 1, 1, 1, 1)], (-1, 1)),
  ([(0, 1, 0, 1, 0, 1, 0, 1), (1, 0, 1, 1, 0, 1, 1, 1), (0, 1, 0, 1, 0, 1, 1, 1),
    (1, 0, 1, 1, 0, 1, 0, 0), (0, 1, 1, 0, 1, 1, 1, 0), (1, 0, 1, 0, 0, 1, 0, 1)],
   [(1, 0, 0, 1, 1, 1, 1, 1), (0, 1, 1, 1, 1, 1, 0, 1), (1, 0, 0, 1, 1, 1, 0, 1),
    (0, 1, 1, 1, 1, 1, 1, 0), (1, 0, 1, 0, 0, 1, 0, 0), (0, 1, 1, 0, 1, 1, 1, 1)], (-1, 1))]

function _g4_jacobian_nullvalue(th, formula)
  S1, S2, signs = formula
  return signs[1]*prod(th[c] for c in S1) + signs[2]*prod(th[c] for c in S2)
end

# tritangents[i][j]: the coefficients of the plane of the characteristic
# _g4_tritangent_pairs()[i][j] (H_i for j = 1, H_i' for j = 2)
function _g4_tritangents(th)
  normalization = [_g4_jacobian_nullvalue(th, F) for F in _g4_normalization_formulas()]
  table = hard_coded_s1_s2()
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

# sum of c v over the pairs (c, v) (v: coefficient vectors of length 3)
_combine(terms...) = [sum(c * v[j] for (c, v) in terms) for j in 1:3]

# The 28 bitangents of the plane quartic with Weber moduli mods (as in
# _moduli_from_theta), as coefficient vectors in the coordinates y0, y1, y2 of
# the Riemann model, in the order of Magma's ComputeBitangents: y0, y1, y2,
# y0+y1+y2, the three Aronhold lines a_i, u0, u1, u2, y0+y1+u2, y0+u1+y2,
# u0+y1+y2, then the families (3)-(7) of Dolgachev's Theorem 6.1.9 (three
# each). (Checked numerically: all 28 are bitangents of the Riemann model.)
function _aronhold_bitangents(mods::Vector{AcbFieldElem})
  CC = parent(mods[1])
  a = [mods[3*(i - 1) + j] for i in 1:3, j in 1:3]     # row i: the bitangent a_i0 y0 + a_i1 y1 + a_i2 y2
  unit(i) = [k == i ? one(CC) : zero(CC) for k in 1:3]
  t0, t1, t2 = unit(1), unit(2), unit(3)
  M = matrix(CC, 3, 3, [one(CC), one(CC), one(CC), a[1, 1], a[1, 2], a[1, 3], a[2, 1], a[2, 2], a[2, 3]])
  Mb = matrix(CC, 3, 3, [one(CC), one(CC), one(CC), inv(a[1, 1]), inv(a[1, 2]), inv(a[1, 3]),
                         inv(a[2, 1]), inv(a[2, 2]), inv(a[2, 3])])
  U = -inv(Mb) * M
  u0, u1, u2 = [[U[i, j] for j in 1:3] for i in 1:3]
  lines = Vector{Vector{AcbFieldElem}}([t0, t1, t2, t0 + t1 + t2])
  append!(lines, [[a[i, 1], a[i, 2], a[i, 3]] for i in 1:3])
  append!(lines, [u0, u1, u2, t0 + t1 + u2, t0 + u1 + t2, u0 + t1 + t2])
  # (3), (4), (5) (with k_i = 1 for these moduli)
  append!(lines, [_combine((inv(a[i, 1]), u0), (a[i, 2], t1), (a[i, 3], t2)) for i in 1:3])
  append!(lines, [_combine((inv(a[i, 2]), u1), (a[i, 1], t0), (a[i, 3], t2)) for i in 1:3])
  append!(lines, [_combine((inv(a[i, 3]), u2), (a[i, 1], t0), (a[i, 2], t1)) for i in 1:3])
  # (6): the u's of the "transposed" Aronhold system
  mt = transpose(matrix(CC, 3, 3, [a[i, j] for i in 1:3 for j in 1:3]))
  mtinv = inv(mt)
  ones3 = matrix(CC, 3, 1, [one(CC), one(CC), one(CC)])
  s = mtinv * ones3
  D = diagonal_matrix([inv(s[i, 1]) for i in 1:3])
  modstra = transpose(D * mtinv)
  Atra = transpose(matrix(CC, 3, 3, [inv(modstra[i, j]) for i in 1:3 for j in 1:3]))
  lam = inv(Atra) * (-ones3)                          # Atra lam = (-1, -1, -1)
  Btra = transpose(modstra) * diagonal_matrix([lam[i, 1] for i in 1:3])
  ks = inv(Btra) * (-ones3)
  k, kp = ks[1, 1], ks[2, 1]
  M2 = matrix(CC, 3, 3, [one(CC), one(CC), one(CC),
                         k*modstra[1, 1], k*modstra[1, 2], k*modstra[1, 3],
                         kp*modstra[2, 1], kp*modstra[2, 2], kp*modstra[2, 3]])
  AtraT = transpose(Atra)
  Mb2 = matrix(CC, 3, 3, [one(CC), one(CC), one(CC),
                          AtraT[1, 1], AtraT[1, 2], AtraT[1, 3], AtraT[2, 1], AtraT[2, 2], AtraT[2, 3]])
  U2 = -inv(Mb2) * M2 * inv(modstra)
  append!(lines, [[U2[r, j] for j in 1:3] for r in 1:3])
  # (7)
  for i in 1:3
    b0, b1, b2 = a[i, 1], a[i, 2], a[i, 3]
    push!(lines, _combine((inv(b0*(1 - b1*b2)), u0), (inv(b1*(1 - b0*b2)), u1), (inv(b2*(1 - b0*b1)), u2)))
  end
  return lines
end

################################################################################
#
#  Signs of the genus 3 theta constants (Magma: signs.m)
#
#  The signs that change all 36 even theta constants by (-1)^(c^T T c) (T
#  upper triangular) or by a common sign form a 21-dimensional space; the
#  signs on a set of 21 characteristics (pivots) are taken as given, the other
#  15 are determined by Riemann's quartic relations: for isotropic planes
#  {0, b1, b2, b1 + b2} with q(b1) = q(b2) (q(v) = a.b) the relation
#  sum_{j=1..3} c_j prod_{4 chars of coset j} theta = 0 holds; for a relation
#  with one term of known signs, the two unknown sign parities are those
#  for which the relation is (numerically) satisfied.
#
################################################################################

function _gf2_reduce(rows::Vector{Vector{Int}}, ncols::Int)
  R = [copy(r) for r in rows]
  pivots = Int[]
  r = 1
  for c in 1:ncols
    p = findfirst(i -> R[i][c] == 1, r:length(R))
    p === nothing && continue
    p += r - 1
    R[r], R[p] = R[p], R[r]
    for i in eachindex(R)
      if i != r && R[i][c] == 1
        R[i] = xor.(R[i], R[r])
      end
    end
    push!(pivots, c)
    r += 1
    r > length(R) && break
  end
  return R, pivots
end

_gf2_rank(rows::Vector{Vector{Int}}, ncols::Int) = length(_gf2_reduce(rows, ncols)[2])

# x with A x = b over GF(2) (A given by its rows)
function _gf2_solve(A::Vector{Vector{Int}}, b::Vector{Int})
  n = length(A[1])
  R, pivots = _gf2_reduce([vcat(A[i], [b[i]]) for i in eachindex(A)], n)
  @req all(R[i][n + 1] == 0 for i in length(pivots)+1:length(R)) "Inconsistent sign conditions (internal error)."
  x = zeros(Int, n)
  for (i, c) in enumerate(pivots)
    x[c] = R[i][n + 1]
  end
  return x
end

function _g3_sign_correction_data()
  g = 3
  even = sort([Tuple(c) for c in even_theta_characteristics(3)])
  q(v) = mod(sum(v[i]*v[g + i] for i in 1:g), 2)                       # v J1 v^T
  bil(u, v) = mod(sum(u[i]*v[g + i] + u[g + i]*v[i] for i in 1:g), 2)   # u J v^T
  first1(v) = findfirst(==(1), v)
  # the sign changes: a common sign and (-1)^(c^T T c), T upper triangular
  gauge = [ones(Int, 36)]
  for t in 1:21
    T = zeros(Int, 6, 6)
    pos = 0
    for i in 1:6, j in i:6
      pos += 1
      T[i, j] = pos == t ? 1 : 0
    end
    push!(gauge, [mod(sum(c[i]*T[i, j]*c[j] for i in 1:6, j in 1:6), 2) for c in even])
  end
  pivots = _gf2_reduce(gauge, 36)[2][1:21]
  fixed = [even[i] for i in pivots]
  free = [even[i] for i in 1:36 if !(i in pivots)]
  W = sort([reverse(v) for v in vec(collect(Iterators.product(ntuple(_ -> 0:1, 6)...)))])
  planes = Tuple{NTuple{6, Int}, NTuple{6, Int}}[]
  for b2 in W, b1 in W
    (any(!iszero, b1) && any(!iszero, b2)) || continue
    bil(b1, b2) == 0 || continue
    first1(b1) < first1(b2) || continue
    b1[first1(b2)] == 0 || continue
    q(b1) == q(b2) || continue
    push!(planes, (b1, b2))
  end
  add(vs...) = Tuple(mod.(sum(collect.(vs)), 2))
  reps = [[c for c in even if bil(b1, c) == q(b1) && bil(b2, c) == q(b2) &&
                              c[first1(b1)] == 0 && c[first1(b2)] == 0] for (b1, b2) in planes]
  cosets = [[[r, add(r, b1), add(r, b2), add(r, b1, b2)] for r in reps[i]]
            for (i, (b1, b2)) in enumerate(planes)]
  S = [[i for i in eachindex(planes) if all(c in fixed for c in cosets[i][k])] for k in 1:3]
  rows_of = Vector{Vector{Vector{Int}}}()
  for k in 1:3
    others = [j for j in 1:3 if j != k]
    for i in S[k]
      push!(rows_of, [[Int(any(cosets[i][others[1]][x] == c for x in 1:4)) for c in free],
                      [Int(any(cosets[i][others[2]][x] == c for x in 1:4)) for c in free]])
    end
  end
  Si = vcat(S...)
  X = copy(rows_of[1])
  used = [Si[1]]
  known_term = [1]
  i = 2
  while _gf2_rank(X, 15) < 15
    candidate = vcat(X, rows_of[i])
    if _gf2_rank(candidate, 15) > _gf2_rank(X, 15)
      X = candidate
      push!(used, Si[i])
      push!(known_term, i <= length(S[1]) ? 1 : (i <= length(S[1]) + length(S[2]) ? 2 : 3))
    end
    i += 1
  end
  return (X = X, planes = planes[used], reps = reps[used], known_term = known_term, free = free)
end

function _correct_theta_signs_g3(thetas::Dict{NTuple{6, Int}, AcbFieldElem})
  g = 3
  data = _g3_sign_correction_data()
  bits = Int[]
  for (n, (b1, b2)) in enumerate(data.planes)
    v1, v2 = collect(b1), collect(b2)
    cosets = [[collect(r), collect(r) + v1, collect(r) + v2, collect(r) - v1 - v2] for r in data.reps[n]]
    # the coefficients of Riemann's relation (with the carries of the
    # characteristics outside {0, 1})
    coefficient = Int[]
    for j in 1:3
      total = 0
      for mu in 1:4
        e = 0
        for xi in 1:4
          m = cosets[j][xi] - [zeros(Int, 6), v1, v2, v1 + v2][mu]
          carry = fld.(m, 2)
          e += sum(m[t]*carry[g + t] for t in 1:g)
        end
        total += iseven(e) ? 1 : -1
      end
      push!(coefficient, total)
    end
    iszero(collect(data.reps[n][1])) && (coefficient[1] -= 8)
    known = data.known_term[n]
    others = [j for j in 1:3 if j != known]
    sign_options = [[coefficient[j] for _ in 1:4] for j in 1:3]
    sign_options[others[1]][2] *= -1         # option 2: first unknown term flipped
    sign_options[others[2]][3] *= -1         # option 3: second unknown term flipped
    sign_options[others[1]][4] *= -1         # option 4: both
    sign_options[others[2]][4] *= -1
    values = [abs(RSR._c64(sum(sign_options[j][nu] * prod(thetas[Tuple(mod.(cosets[j][xi], 2))] for xi in 1:4)
                               for j in 1:3))) for nu in 1:4]
    best = argmin(values) - 1
    append!(bits, [best & 1, (best >> 1) & 1])
  end
  solution = _gf2_solve(data.X, bits)
  result = copy(thetas)
  for (j, c) in enumerate(data.free)
    isodd(solution[j]) && (result[c] = -result[c])
  end
  return result
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
#  Numerical linear algebra in ball arithmetic (no LinearAlgebra)
#
################################################################################

_g4_mag(z::AcbFieldElem) = abs(RSR._c64(z))
_g4_log2(x::Float64) = x > 0 ? log2(x) : -Inf

# radius of a ball (upper bound in Float64)
_g4_radius(z::AcbFieldElem) = Float64(Hecke.radius(real(z))) + Float64(Hecke.radius(imag(z)))

# log2 of the largest radius relative to the largest midpoint: for vectors,
# matrices and polynomials the maximum over the entries of max radius / max
# |entry| (vectors of vectors: per vector)
_g4_log2_radius(z::AcbFieldElem) = _g4_log2(_g4_radius(z) / max(_g4_mag(z), 1e-300))
_g4_log2_radius(v::Vector{AcbFieldElem}) = _g4_log2(maximum(_g4_radius, v) / max(maximum(_g4_mag, v), 1e-300))
_g4_log2_radius(v::Vector{Vector{AcbFieldElem}}) = maximum(_g4_log2_radius, v)
_g4_log2_radius(v::Vector{<:MPolyRingElem}) = maximum(_g4_log2_radius, v)
_g4_log2_radius(M::AcbMatrix) = _g4_log2_radius([M[i, j] for i in 1:nrows(M) for j in 1:ncols(M)])
_g4_log2_radius(p::MPolyRingElem) = _g4_log2_radius(collect(coefficients(p)))

@doc raw"""
    _numerical_kernel(A::AcbMatrix, dim::Int) -> AcbMatrix, Vector{Int}, Vector{Int}, Float64

A basis (the columns of an n x dim matrix) of the right kernel of A, for a
matrix A that is known to have rank r = ncols(A) - dim. Gaussian elimination
with complete pivoting on the midpoints chooses r pivot rows and columns; the
kernel vectors (the free columns set to the unit vectors) are then the
solutions of the r x r pivot system, by FLINT's preconditioned solver. If A
(the exact matrix in the balls) has rank r, the balls contain its kernel
vectors with tight radii. Also returns the pivot rows and columns, log2 of the
size of the largest midpoint entry left after the elimination relative to the
first pivot (about -precision if A has rank r).
"""
function _numerical_kernel(A::AcbMatrix, dim::Int)
  m, n = nrows(A), ncols(A)
  r = n - dim
  @req 0 <= r <= m "Inconsistent kernel dimension."
  CC = base_ring(A)
  B = map_entries(_acb_mid, A)
  rowp = collect(1:m)
  colp = collect(1:n)
  first_pivot = 0.0
  for k in 1:r
    best, bi, bj = -1.0, k, k
    for i in k:m, j in k:n
      v = _g4_mag(B[rowp[i], colp[j]])
      if v > best
        best, bi, bj = v, i, j
      end
    end
    k == 1 && (first_pivot = best)
    rowp[k], rowp[bi] = rowp[bi], rowp[k]
    colp[k], colp[bj] = colp[bj], colp[k]
    p = B[rowp[k], colp[k]]
    for i in k+1:m
      f = _acb_mid(B[rowp[i], colp[k]] / p)
      for j in k:n
        B[rowp[i], colp[j]] = _acb_mid(B[rowp[i], colp[j]] - f * B[rowp[k], colp[j]])
      end
    end
  end
  rest = 0.0
  for i in r+1:m, j in r+1:n
    rest = max(rest, _g4_mag(B[rowp[i], colp[j]]))
  end
  K = zero_matrix(CC, n, dim)
  if dim > 0 && r > 0
    pivot_block = matrix(CC, r, r, [A[rowp[i], colp[j]] for i in 1:r for j in 1:r])
    free_block = matrix(CC, r, dim, [-A[rowp[i], colp[r + c]] for i in 1:r for c in 1:dim])
    X = _solve_precond(pivot_block, free_block)
    for c in 1:dim, k in 1:r
      K[colp[k], c] = X[k, c]
    end
  end
  for c in 1:dim
    K[colp[r + c], c] = one(CC)
  end
  quality = first_pivot > 0 ? _g4_log2(rest / first_pivot) : -Inf
  return K, rowp[1:r], colp[1:r], quality
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
    i = k - 1 + argmax([_g4_mag(B[l, l]) for l in k:n])
    off = 0.0
    a, b = k, k
    for l in k:n, l2 in k:n
      l == l2 && continue
      if _g4_mag(B[l, l2]) > off
        off, a, b = _g4_mag(B[l, l2]), l, l2
      end
    end
    if _g4_mag(B[i, i]) < 1e-3 * off
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
  relations, _, basis, q_relations = _numerical_kernel(transpose(X), 3)
  fsq = matrix(CC, r, 6, [c for b in bitangents for c in _square_coefficients(b)])
  # lambda: sum_i lambda_i n_k[i] l_i^2 = 0 for k = 1, 2, 3
  N = zero_matrix(CC, r, 18)
  for k in 1:3, i in 1:r, j in 1:6
    N[i, 6*(k - 1) + j] = relations[i, k] * fsq[i, j]
  end
  lambda, _, _, q_lambda = _numerical_kernel(transpose(N), 1)
  # phi on the basis H_i H_i', i in basis, of V_{C,eta}
  phi = matrix(CC, 7, 6, [lambda[i, 1] * fsq[i, j] for i in basis for j in 1:6])
  kernel_phi, _, _, _ = _numerical_kernel(transpose(phi), 1)
  Qm = sum(kernel_phi[a, 1] * mats[basis[a]] for a in 1:7)
  # V_{C,eta}^perp (trace pairing) and Q' = (Q1^-1 + Q2^-1)^-1 in W_eta^perp
  perp, _, _, _ = _numerical_kernel(X, 3)
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
  radii = (tritangents = _g4_log2_radius(vcat(tritangents...)), bitangents = _g4_log2_radius(bitangents),
           relations = _g4_log2_radius(relations), lambda = _g4_log2_radius(lambda),
           kernel_phi = _g4_log2_radius(kernel_phi), Qsharp = _g4_log2_radius(Qsharp),
           Tinv = _g4_log2_radius(Tinv), Delta = _g4_log2_radius(d), G = _g4_log2_radius(G),
           quadric = _g4_log2_radius(quadric), cubic = _g4_log2_radius(cubic))
  return quadric, cubic, (relations = q_relations, lambda = q_lambda, square_root = q_sqrt, radii = radii)
end

################################################################################
#
#  Square roots of sextic forms
#
################################################################################

# all exponent vectors of length n and total degree d
function _exponent_vectors(n::Int, d::Int)
  n == 1 && return [[d]]
  return [vcat([i], e) for i in d:-1:0 for e in _exponent_vectors(n - 1, d - i)]
end

function _polynomial_from_dict(R::MPolyRing, D::Dict{Vector{Int}, AcbFieldElem})
  ctx = MPolyBuildCtx(R)
  for (e, c) in D
    push_term!(ctx, c, e)
  end
  return finish(ctx)
end

# log2 of max |coefficient of F - H^2| / max |coefficient of F|
function _square_residual(F::Dict{Vector{Int}, AcbFieldElem}, H::Dict{Vector{Int}, AcbFieldElem})
  D = copy(F)
  for (e1, c1) in H, (e2, c2) in H
    e = e1 + e2
    D[e] = get(D, e, zero(c1)) - c1*c2
  end
  return _g4_log2(maximum(_g4_mag, values(D)) / maximum(_g4_mag, values(F)))
end

# H^2 = F (exponent dicts; H with all its monomials as keys): Newton steps on
# the midpoints (solve 2 H D = F - H^2 by least squares, H += D; each step
# doubles the number of correct bits; the recurrence of _sqrt_homogeneous
# alone loses many bits when the leading coefficient is
# small), then a rigorous enclosure (_enclose_square_root!).
function _refine_square_root!(F::Dict{Vector{Int}, AcbFieldElem}, H::Dict{Vector{Int}, AcbFieldElem};
                              steps::Int = 3)
  Fm = Dict(e => _acb_mid(c) for (e, c) in F)
  for e in keys(H)
    H[e] = _acb_mid(H[e])
  end
  for _ in 1:steps
    J, R, _ = _square_root_system(Fm, H)
    n = ncols(J)
    A = hcat(J, R)
    K, _, _, _ = _numerical_kernel(A, 1)
    t = -K[n + 1, 1]
    for (k, mk) in enumerate(collect(keys(H)))
      H[mk] = _acb_mid(H[mk] + K[k, 1] / t)
    end
  end
  return _enclose_square_root!(F, H)
end

# The linearization at H: J (2 H D = J D, columns: the keys of H in the order
# of keys(H)) and R = F - H^2 (one row per monomial)
function _square_root_system(F::Dict{Vector{Int}, AcbFieldElem}, H::Dict{Vector{Int}, AcbFieldElem})
  CC = parent(first(values(F)))
  unknowns = collect(keys(H))
  D = copy(F)
  for (e1, c1) in H, (e2, c2) in H
    e = e1 + e2
    D[e] = get(D, e, zero(CC)) - c1*c2
  end
  equations = collect(keys(D))
  index = Dict(e => i for (i, e) in enumerate(equations))
  J = zero_matrix(CC, length(equations), length(unknowns))
  for (k, mk) in enumerate(unknowns), (e, c) in H
    J[index[e + mk], k] += 2*c
  end
  R = matrix(CC, length(equations), 1, [D[e] for e in equations])
  return J, R, equations
end

# H (exact midpoints, close to a square root of the ball polynomial F) is
# replaced by balls containing the square root of F near H: with H~ = H + D,
# the equations for D are J D + D^2 = R; on n independent equations
# (n = number of unknowns) D = J_s^-1 (R_s - (D^2)_s), a contraction on the
# ball of radius eps around 0 if |J_s^-1 R_s| + |J_s^-1| n eps^2 <= eps.
function _enclose_square_root!(F::Dict{Vector{Int}, AcbFieldElem}, H::Dict{Vector{Int}, AcbFieldElem})
  CC = parent(first(values(F)))
  J, R, _ = _square_root_system(F, H)
  n = ncols(J)
  _, rows, _, _ = _numerical_kernel(J, 0)
  Js = matrix(CC, n, n, [J[i, k] for i in rows for k in 1:n])
  Rs = matrix(CC, n, 1, [R[i, 1] for i in rows])
  Jinv = _inv_precond(Js)
  E = Jinv * Rs
  upper(z) = (a = abs(z); Float64(Hecke.midpoint(a)) + Float64(Hecke.radius(a)))
  e_max = maximum(upper(E[k, 1]) for k in 1:n)
  jinv_norm = maximum(sum(upper(Jinv[i, k]) for k in 1:n) for i in 1:n)
  eps = 2*e_max + 2.0^(-2*precision(CC))
  quadratic = jinv_norm * n * eps^2
  @req e_max + quadratic <= eps "Could not enclose the square root (increase the precision)."
  err = ArbField(precision(CC))(quadratic * (1 + 1e-10))
  for (k, mk) in enumerate(collect(keys(H)))
    H[mk] = H[mk] + E[k, 1]
    _add_error!(H[mk], err)
  end
  return H
end

# Square root H of a form F of degree 2d that is a square: the variable x_i0
# with the largest coefficient c of x_i0^(2d); H = sqrt(c) x_i0^d + ..., the
# coefficients of x_i0^(d - i) m (m of degree i in the other variables) from
# the coefficient of x_i0^(2d - i) m in F - (known part)^2, i = 1..d.
# (Magma: ComputeSqrtHomogeneous.)
function _sqrt_homogeneous(F::MPolyRingElem)
  R = parent(F)
  n = nvars(R)
  Fd = Dict{Vector{Int}, AcbFieldElem}(e => c for (c, e) in zip(coefficients(F), exponent_vectors(F)))
  CC = base_ring(R)
  d = div(total_degree(F), 2)
  pure(i, e) = [j == i ? e : 0 for j in 1:n]
  i0 = argmax([_g4_mag(get(Fd, pure(i, 2*d), zero(CC))) for i in 1:n])
  r0 = RSR._rotated_power(Fd[pure(i0, 2*d)], 1//2)
  H = Dict{Vector{Int}, AcbFieldElem}(pure(i0, d) => r0)
  others = [j for j in 1:n if j != i0]
  for i in 1:d
    known = copy(H)
    for m in _exponent_vectors(n - 1, i)
      e = zeros(Int, n)
      e[others] = m
      target = copy(e)
      target[i0] = 2*d - i
      s = get(Fd, target, zero(CC))
      for (e1, c1) in known, (e2, c2) in known
        e1 + e2 == target && (s -= c1*c2)
      end
      e[i0] = d - i
      H[e] = s / (2*r0)
    end
  end
  _refine_square_root!(Fd, H)
  return _polynomial_from_dict(R, H), _square_residual(Fd, H)
end

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
    z = argmin([_g4_mag(x) for x in d])
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
  condition = _g4_log2(maximum(_g4_mag(M[i, j]) for i in 1:4, j in 1:4) *
                       maximum(_g4_mag(Minv[i, j]) for i in 1:4, j in 1:4))
  spread(p) = (c = filter(>(0), [_g4_mag(a) for a in coefficients(p)]); _g4_log2(maximum(c) / minimum(c)))
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
    worst = max(worst, _g4_mag(z - lambdas[nearest]) / scale)
  end
  return _g4_log2(worst)
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
    s = maximum(_g4_mag, coefficients(p))
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
  radius = maximum(_g4_log2(Float64(Hecke.radius(real(c))) + Float64(Hecke.radius(imag(c))))
                   for c in vcat(collect(coefficients(data.curve[1])), collect(coefficients(data.curve[2]))))
  return (exact_model = exact_model, moved = moved, moved_noise200 = moved_noise,
          reconstruction = reconstruction.log2_diff, points = points,
          normalization_moved = cond_moved, normalization_reconstruction = cond_rec,
          log2_max_radius = radius,
          info = data.info)
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
  qscale = maximum(_g4_mag, coefficients(quadric))
  cscale = maximum(_g4_mag, coefficients(cubic))
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
      norm = maximum(_g4_mag, xs)
      rq = _g4_mag(evaluate(quadric, xs)) / (qscale * norm^2)
      rc = _g4_mag(evaluate(cubic, xs)) / (cscale * norm^3)
      worst = max(worst, _g4_log2(rq), _g4_log2(rc))
    end
  end
  return worst
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
  qs = qc[argmax(map(_g4_mag, qc))]
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
  cs = v[argmax(map(_g4_mag, v))]
  Gk = [recognize(c / cs) for c in v]
  @req all(!isnothing, Gk) "Could not recognize the coefficients of the cubic in K (more precision needed?)."
  GK = sum(Gk[k] * monomial(e3[k]) for k in eachindex(e3))
  normalize && return [_normalize_model(QK; reduce_units), _normalize_model(GK; reduce_units)]
  return [QK, GK]
end

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

################################################################################
#  Jacobian nullvalues D(xi_1, .., chi, .., xi_4) for the tritangent pairs:
#  output[i][j][k] = (S1, S2, (s1, s2)) for _g4_tritangent_pairs()[i][j] in
#  position k (D = pi^4 (s1 prod theta[S1] + s2 prod theta[S2]))
################################################################################

function hard_coded_s1_s2()
output = 
[
    [
        [ [
            [
                (1, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 1, 0, 1, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 1)
            ],
            [
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 1, 1, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 1, 1, 1, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 1, 0, 1, 1, 0, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 0, 1, 1, 0, 0, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 0, 0, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 1, 0, 0, 0, 0, 1)
            ],
            [
                (1, 0, 0, 1, 1, 0, 0, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 0, 1, 1, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 1)
            ],
            [ 1, -1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 1, 1, 0, 0, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 1, 1, 1, 0, 0, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 1, 0, 0, 0, 0, 1)
            ],
            [
                (1, 1, 0, 1, 1, 0, 0, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 0, 1, 1, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 0, 1, 1, 0, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 1, 0, 0, 1, 0, 1)
            ],
            [
                (1, 0, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 0, 1, 1, 1, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 0, 0, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 1)
            ],
            [ -1, 1, ]
        ] ],
        [ [
            [
                (1, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 1, 0, 1, 1, 0, 0),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 1, 1, 0, 1, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 1, 1, 1, 1, 1, 0, 0)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 0, 0, 1, 1, 0, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 0, 1, 1, 0, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 0, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 0, 0, 1, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 1, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 1, 1, 0, 0, 0, 0)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 1, 0, 1, 1, 0, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 1, 0, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 0, 0, 1, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 1, 1, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 1, 1, 1, 0, 0, 0, 0)
            ],
            [ 1, -1, ]
        ], [
            [
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 1, 1, 0, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 1, 0, 0, 1, 0, 1)
            ],
            [
                (1, 0, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 0, 1, 1, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 1, 0, 0, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 1)
            ],
            [ -1, 1, ]
        ] ]
    ],
    [
        [ [
            [
                (1, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 1)
            ],
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 1, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 0, 1, 1, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 0, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 0, 0, 1, 1),
                (1, 0, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 0, 1, 0, 0, 0, 0)
            ],
            [
                (1, 0, 1, 1, 1, 0, 0, 1),
                (1, 0, 0, 1, 1, 0, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0)
            ],
            [ 1, -1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 1, 1, 0, 0, 1, 1),
                (1, 1, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 1, 0, 0, 0, 0)
            ],
            [
                (1, 1, 1, 1, 1, 0, 0, 1),
                (1, 1, 0, 1, 1, 0, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 0, 0, 1, 0, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 1)
            ],
            [
                (1, 0, 0, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 1, 1, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 1)
            ],
            [ -1, 1, ]
        ] ],
        [ [
            [
                (1, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 1, 1, 0, 0),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 1, 1, 1, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 0, 0, 1, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 1, 0, 1, 1, 1, 0, 0)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 0, 1, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 0, 1, 1, 0, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 1, 1, 0, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 0, 1, 0, 0, 0, 0)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 1, 1, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 1, 0, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 1, 1, 1, 0, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 1, 0, 1, 0, 0, 0, 0)
            ],
            [ 1, -1, ]
        ], [
            [
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 0, 1, 0, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 1)
            ],
            [
                (1, 0, 0, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 1, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 1)
            ],
            [ -1, 1, ]
        ] ]
    ],
    [
        [ [
            [
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 0, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 1, 1, 0, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 1, 0, 0, 1, 1, 1)
            ],
            [
                (1, 1, 0, 0, 1, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 1, 0, 1, 1, 0, 1),
                (1, 1, 0, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 0, 1, 0, 1, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 0, 1, 0, 0, 0, 0),
                (1, 0, 0, 1, 1, 0, 0, 1),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 0, 0, 0, 0, 0, 0),
                (1, 0, 1, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 1, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 1, 1, 0, 1, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 1, 0, 1, 0, 0, 0, 0),
                (1, 1, 0, 1, 1, 0, 0, 1),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 1, 0, 0, 0, 0, 0, 0),
                (1, 1, 1, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 1, 1)
            ],
            [ 1, -1, ]
        ], [
            [
                (1, 0, 0, 1, 0, 1, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 0, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 0),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 0, 0, 0, 1, 1, 1),
                (1, 0, 1, 0, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1)
            ],
            [ 1, -1, ]
        ] ],
        [ [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 0, 1, 1, 1, 0, 0),
                (1, 1, 1, 0, 0, 1, 1, 1)
            ],
            [
                (1, 1, 0, 0, 1, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 1, 1, 0, 1, 1, 0, 1),
                (1, 1, 0, 0, 1, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 0, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 0, 1, 0, 0, 0, 0),
                (1, 0, 1, 0, 1, 0, 1, 1)
            ],
            [
                (1, 0, 0, 0, 0, 0, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 0, 1, 0, 0, 0, 0, 1),
                (1, 0, 0, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 0, 1, 0, 0, 0, 0),
                (1, 1, 1, 0, 1, 0, 1, 1)
            ],
            [
                (1, 1, 0, 0, 0, 0, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 1, 1, 0, 0, 0, 0, 1),
                (1, 1, 0, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [ 1, -1, ]
        ], [
            [
                (1, 0, 0, 0, 0, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 1, 0, 0, 1, 0, 1),
                (1, 0, 0, 0, 0, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 0, 1, 1, 1, 0, 1),
                (1, 0, 0, 1, 0, 1, 0, 0),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 1, 0, 1, 1, 1, 1)
            ],
            [ -1, 1, ]
        ] ]
    ],
    [
        [ [
            [
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 1, 1, 1, 1, 0, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 1, 0, 0, 1, 1, 1)
            ],
            [
                (1, 1, 1, 0, 1, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 0, 1),
                (1, 1, 0, 0, 1, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 0, 1, 1, 0, 0, 0, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 0, 1, 0, 1, 1),
                (1, 0, 1, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 0, 0, 0, 0, 0, 1),
                (1, 0, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 1, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 1, 1, 1, 0, 0, 0, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 1, 0, 1, 0, 1, 1),
                (1, 1, 1, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 0, 0, 0, 0, 1),
                (1, 1, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 1, 1)
            ],
            [ 1, -1, ]
        ], [
            [
                (1, 0, 1, 1, 0, 1, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 1, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 1, 0, 0, 1, 0, 0),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 0, 0, 0, 1, 1, 1),
                (1, 0, 0, 0, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1)
            ],
            [ 1, -1, ]
        ] ],
        [ [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 1, 1, 1, 1, 0, 0),
                (1, 1, 1, 0, 0, 1, 1, 1)
            ],
            [
                (1, 1, 0, 0, 1, 1, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 1, 0, 0, 1, 1, 1, 1),
                (1, 1, 1, 0, 1, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 0, 1, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 1, 1, 0, 0, 0, 0),
                (1, 0, 1, 0, 1, 0, 1, 1)
            ],
            [
                (1, 0, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 1, 1),
                (1, 0, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 1, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 1, 1, 0, 0, 0, 0),
                (1, 1, 1, 0, 1, 0, 1, 1)
            ],
            [
                (1, 1, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 1, 1),
                (1, 1, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [ 1, -1, ]
        ], [
            [
                (1, 0, 1, 0, 0, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 1),
                (1, 0, 0, 0, 0, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 1, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 0, 1, 0, 0),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 1, 0, 1, 1, 1, 1)
            ],
            [ -1, 1, ]
        ] ]
    ],
    [
        [ [
            [
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 0, 1, 1, 1, 1, 0),
                (1, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [
                (1, 1, 1, 0, 1, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 0, 0, 1, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 0, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 0, 1, 0, 0, 1, 0),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 0, 1, 1, 0, 1, 1),
                (1, 0, 1, 0, 1, 0, 1, 1)
            ],
            [
                (1, 0, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 1, 0, 0, 0, 0, 1),
                (1, 0, 0, 0, 0, 0, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 0, 1, 0, 0, 1, 0),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 0, 1, 1, 0, 1, 1),
                (1, 1, 1, 0, 1, 0, 1, 1)
            ],
            [
                (1, 1, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 1, 0, 0, 0, 0, 1),
                (1, 1, 0, 0, 0, 0, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1)
            ],
            [ 1, -1, ]
        ], [
            [
                (1, 0, 1, 0, 0, 1, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 0, 0, 0, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 1)
            ],
            [
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 0, 1, 0, 1, 1, 0),
                (1, 0, 0, 1, 1, 1, 1, 1),
                (1, 0, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [ -1, 1, ]
        ] ],
        [ [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 0, 1, 1, 1, 1, 0),
                (1, 1, 1, 0, 0, 1, 1, 1)
            ],
            [
                (1, 1, 0, 0, 1, 1, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 1, 1, 0, 1, 1, 0, 1),
                (1, 1, 0, 0, 1, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 1, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 0, 0, 1, 1, 0, 1, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 0, 1, 0, 0, 1, 0),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 1, 0, 1, 0, 1, 1)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 1, 0),
                (1, 0, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 1, 0, 0, 0, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 1, 0, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 0, 1, 0, 0, 1, 0),
                (1, 1, 1, 0, 1, 0, 1, 1)
            ],
            [
                (1, 1, 0, 0, 0, 0, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 1, 1, 0, 0, 0, 0, 1),
                (1, 1, 0, 0, 0, 0, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 1, 1)
            ],
            [ 1, -1, ]
        ], [
            [
                (1, 0, 1, 0, 0, 1, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 0, 0, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 1)
            ],
            [
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 0, 1, 1, 1, 1, 1),
                (1, 0, 0, 1, 0, 1, 1, 0),
                (1, 0, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (0, 1, 1, 1, 0, 1, 0, 1)
            ],
            [ -1, 1, ]
        ] ]
    ],
    [
        [ [
            [
                (1, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 1)
            ],
            [
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 1, 1, 1, 1, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 1, 1, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 1, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 0, 0, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 0, 1, 0, 0, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 0, 0, 0, 0, 1, 1)
            ],
            [
                (1, 0, 0, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 1, 1, 1, 0, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 0, 0, 0, 0, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 1)
            ],
            [ 1, -1, ]
        ], [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 1, 1, 0, 0, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 0, 0, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 0, 0, 0, 1, 1)
            ],
            [
                (1, 1, 0, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 1, 1, 1, 1, 0, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 0, 0, 0, 0, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 1)
            ],
            [ -1, 1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 0, 1, 1, 1),
                (1, 0, 0, 0, 0, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 0, 1, 0, 1, 1, 0)
            ],
            [
                (1, 0, 1, 1, 1, 1, 0, 1),
                (1, 0, 0, 1, 1, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 0, 0, 0, 0, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 1, 0)
            ],
            [ -1, 1, ]
        ] ],
        [ [
            [
                (1, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 1, 1, 1, 0),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 0, 0, 1, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 1, 0, 1, 1, 1, 1, 0)
            ],
            [ -1, 1, ]
        ], [
            [
                (1, 0, 1, 1, 0, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 0, 0, 0, 0, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 0, 1, 0, 0, 1, 0)
            ],
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 0, 0, 1, 1, 0, 0, 1),
                (1, 0, 1, 1, 1, 0, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 1, 0),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [ 1, -1, ]
        ], [
            [
                (1, 1, 1, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 0, 1, 1, 0, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 1, 0),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 0, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 0, 0, 0, 0, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 1, 0, 1, 0, 0, 1, 0)
            ],
            [ 1, -1, ]
        ], [
            [
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 0, 1, 0, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 1, 1)
            ],
            [
                (1, 0, 1, 1, 1, 1, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 0, 0, 1, 1, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 1)
            ],
            [ -1, 1, ]
        ] ]
    ],
    [
        [ [
            [
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 1, 1, 1, 0, 0),
                (1, 1, 0, 0, 1, 1, 1, 0),
                (1, 1, 1, 1, 1, 1, 0, 0),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (1, 1, 0, 0, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 0, 1, 0, 1, 1, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 0, 0, 0, 0, 0, 1, 0),
                (1, 0, 1, 1, 0, 0, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 0, 1, 0, 0, 0, 0),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 0, 0, 0, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 1, 0, 1, 0),
                (1, 0, 0, 1, 1, 0, 1, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 1, 0, 0, 0, 0, 1, 0),
                (1, 1, 1, 1, 0, 0, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 1, 0, 0, 0, 0),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 0, 0, 0, 0, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 1, 0, 1, 0),
                (1, 1, 0, 1, 1, 0, 1, 1)
            ],
            [ 1, 1, ]
        ], [
            [
                (1, 0, 0, 1, 0, 1, 0, 0),
                (1, 0, 1, 1, 0, 1, 0, 0),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 0, 1, 0, 1, 1, 1)
            ],
            [
                (0, 1, 1, 1, 1, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 0, 0, 0, 0, 1, 1, 1),
                (1, 0, 1, 1, 1, 1, 1, 0)
            ],
            [ 1, 1, ]
        ] ],
        [ [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 1, 1, 1, 1),
                (1, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (1, 1, 0, 1, 1, 1, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 1, 1, 1, 1, 0, 0),
                (1, 1, 0, 0, 1, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 1, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 0, 0, 1, 1, 0, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 0, 0, 0, 0, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 1, 0, 1, 0)
            ],
            [
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 0, 0, 0, 0, 1, 0),
                (1, 0, 0, 1, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 1, 1, 0, 0, 0, 0),
                (0, 1, 0, 1, 1, 1, 1, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 1, 0, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 1, 1),
                (1, 1, 1, 1, 1, 0, 1, 0)
            ],
            [
                (1, 1, 0, 1, 0, 0, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 1, 1, 0, 0, 0, 0),
                (1, 1, 0, 0, 0, 0, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 1, 1)
            ],
            [ 1, 1, ]
        ], [
            [
                (1, 0, 0, 0, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 1, 1, 1, 0),
                (1, 0, 0, 1, 1, 1, 1, 1)
            ],
            [
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 0, 1, 0, 1, 0, 0),
                (1, 0, 0, 0, 0, 1, 1, 0),
                (1, 0, 1, 1, 0, 1, 0, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 1, 0)
            ],
            [ 1, 1, ]
        ] ]
    ],
    [
        [ [
            [
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 1, 1, 1, 1, 1, 1),
                (1, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [
                (1, 1, 1, 0, 1, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 0, 0)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 0, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 1, 0),
                (1, 0, 0, 0, 0, 0, 0, 0)
            ],
            [
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 1, 0, 1, 0, 1, 1),
                (1, 0, 1, 1, 0, 0, 1, 1),
                (1, 0, 1, 1, 1, 0, 1, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 1, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 1, 0),
                (1, 1, 0, 0, 0, 0, 0, 0)
            ],
            [
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 1, 0, 1, 0, 1, 1),
                (1, 1, 1, 1, 0, 0, 1, 1),
                (1, 1, 1, 1, 1, 0, 1, 0),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [ 1, 1, ]
        ], [
            [
                (1, 0, 1, 0, 0, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 0)
            ],
            [
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 0, 1, 1, 1),
                (1, 0, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [ 1, 1, ]
        ] ],
        [ [
            [
                (1, 1, 1, 0, 1, 1, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 1, 0),
                (1, 1, 0, 0, 1, 1, 0, 0)
            ],
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 1, 1, 1, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 0, 1, 1, 1, 0, 1, 0),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 0, 0, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 1, 0, 1, 0, 1, 1)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 1, 0),
                (1, 0, 0, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 1, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 1, 0, 0, 0, 0, 1, 0),
                (1, 1, 0, 0, 0, 0, 0, 0)
            ],
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 1, 0, 1, 0, 1, 1),
                (1, 1, 1, 1, 1, 0, 1, 0),
                (1, 1, 1, 1, 0, 0, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1)
            ],
            [ 1, 1, ]
        ], [
            [
                (1, 0, 1, 0, 0, 1, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 1, 0),
                (1, 0, 0, 0, 0, 1, 0, 0)
            ],
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 1, 0, 1, 1, 1),
                (1, 0, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1)
            ],
            [ 1, 1, ]
        ] ]
    ],
    [
        [ [
            [
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 1, 1, 1, 1, 0, 0),
                (1, 1, 0, 0, 1, 1, 0, 0),
                (1, 1, 0, 1, 1, 1, 1, 0),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (1, 1, 0, 0, 1, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 0, 1, 0, 1, 0, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 0, 1, 1, 1, 0, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 0, 1),
                (1, 0, 0, 1, 1, 0, 0, 1),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 0, 0, 0, 0, 0, 0),
                (1, 0, 1, 1, 0, 0, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 0, 0, 1, 0, 0, 1, 0)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 1, 1, 1, 1, 0, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 0, 1),
                (1, 1, 0, 1, 1, 0, 0, 1),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 1, 0, 0, 0, 0, 0, 0),
                (1, 1, 1, 1, 0, 0, 0, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (0, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 0, 1, 0, 0, 1, 0)
            ],
            [ 1, 1, ]
        ], [
            [
                (1, 0, 0, 0, 0, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 1, 1, 1, 0),
                (1, 0, 0, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 1, 1, 0, 1, 0, 0),
                (1, 0, 0, 0, 0, 1, 0, 0),
                (1, 0, 0, 1, 0, 1, 1, 0),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [ 1, 1, ]
        ] ],
        [ [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 1, 1, 0, 1),
                (1, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (1, 1, 0, 1, 1, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 1, 1, 1, 1, 0, 0),
                (1, 1, 0, 0, 1, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 0, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 0, 0, 0, 0, 0, 0, 1),
                (1, 0, 1, 1, 1, 0, 1, 0)
            ],
            [
                (1, 0, 0, 1, 0, 0, 1, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 1, 0, 0, 0, 0),
                (1, 0, 0, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 1, 0, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 0, 0, 0, 0, 0, 1),
                (1, 1, 1, 1, 1, 0, 1, 0)
            ],
            [
                (1, 1, 0, 1, 0, 0, 1, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 1, 1, 0, 0, 0, 0),
                (1, 1, 0, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 0, 1)
            ],
            [ 1, 1, ]
        ], [
            [
                (1, 0, 0, 0, 0, 1, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 1, 1, 1, 0),
                (1, 0, 0, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 1, 1, 0, 1, 0, 0),
                (1, 0, 0, 0, 0, 1, 0, 0),
                (1, 0, 0, 1, 0, 1, 1, 0),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0)
            ],
            [ 1, 1, ]
        ] ]
    ],
    [
        [ [
            [
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 1, 1, 1, 0, 0),
                (1, 1, 1, 0, 1, 1, 0, 0),
                (1, 1, 0, 1, 1, 1, 1, 0),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (1, 1, 1, 0, 1, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 1, 1, 0, 1, 1, 0),
                (1, 1, 1, 1, 0, 1, 0, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 0, 1, 0, 0, 0, 0, 0),
                (1, 0, 0, 1, 0, 0, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 0, 1, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 1, 0, 0, 0, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 0, 1, 1, 1, 0, 1, 0),
                (1, 0, 1, 1, 1, 0, 0, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (1, 1, 1, 0, 0, 0, 0, 0),
                (1, 1, 0, 1, 0, 0, 1, 0),
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 1, 0, 1, 0, 0, 0, 0),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 1, 1, 0, 0, 0, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (1, 1, 1, 1, 1, 0, 1, 0),
                (1, 1, 1, 1, 1, 0, 0, 1)
            ],
            [ 1, 1, ]
        ], [
            [
                (1, 0, 1, 0, 0, 1, 0, 1),
                (0, 1, 0, 1, 1, 1, 1, 1),
                (0, 1, 1, 0, 1, 1, 1, 1),
                (0, 1, 0, 1, 1, 1, 0, 1),
                (1, 0, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 0, 1, 1, 1, 0),
                (1, 0, 0, 1, 0, 1, 0, 0),
                (1, 0, 1, 0, 0, 1, 0, 0),
                (1, 0, 0, 1, 0, 1, 1, 0),
                (0, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 1, 1, 0, 1, 1, 0)
            ],
            [ 1, 1, ]
        ] ],
        [ [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 1, 1, 0, 1, 0, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 1, 0, 1, 1, 0, 1),
                (1, 1, 1, 1, 0, 1, 1, 0)
            ],
            [
                (1, 1, 0, 1, 1, 1, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 0, 1, 1, 1, 1, 0),
                (1, 1, 1, 0, 1, 1, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 0, 1, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 0, 1, 0, 0, 0, 0, 1),
                (1, 0, 1, 1, 1, 0, 1, 0)
            ],
            [
                (1, 0, 0, 1, 0, 0, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 0, 0, 1, 0, 0, 1, 0),
                (1, 0, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [ -1, -1, ]
        ], [
            [
                (0, 1, 0, 1, 0, 1, 1, 1),
                (1, 1, 1, 1, 1, 0, 0, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (1, 1, 1, 0, 0, 0, 0, 1),
                (1, 1, 1, 1, 1, 0, 1, 0)
            ],
            [
                (1, 1, 0, 1, 0, 0, 0, 0),
                (0, 1, 1, 1, 1, 1, 1, 0),
                (1, 1, 0, 1, 0, 0, 1, 0),
                (1, 1, 1, 0, 0, 0, 0, 0),
                (0, 1, 1, 0, 0, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 0, 1)
            ],
            [ 1, 1, ]
        ], [
            [
                (1, 0, 1, 0, 0, 1, 0, 1),
                (0, 1, 0, 1, 0, 1, 1, 1),
                (0, 1, 1, 0, 0, 1, 1, 1),
                (0, 1, 0, 1, 0, 1, 0, 1),
                (1, 0, 1, 1, 1, 1, 1, 0),
                (1, 0, 1, 1, 1, 1, 0, 1)
            ],
            [
                (0, 1, 1, 0, 0, 1, 1, 0),
                (1, 0, 0, 1, 0, 1, 0, 0),
                (1, 0, 1, 0, 0, 1, 0, 0),
                (1, 0, 0, 1, 0, 1, 1, 0),
                (0, 1, 1, 1, 1, 1, 0, 1),
                (0, 1, 1, 1, 1, 1, 1, 0)
            ],
            [ 1, 1, ]
        ] ]
    ]
]
return output
end