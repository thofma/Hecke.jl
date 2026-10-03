################################################################################
#
#  ReconstructCurves.jl -- reconstruct a curve of genus 1, 2 or 3 from its
#  small period matrix (via theta constants) and compare it with the original
#  curve by invariants. With random curves this tests the period matrices
#  independently of the code that computed them.
#
#    genus 1        y^2 = x(x-1)(x-lambda), lambda = (theta[1,0]/theta[0,0])^4
#    genus 2        Rosenhain form y^2 = x(x-1)(x-l1)(x-l2)(x-l3) (Thomae)
#    genus 3, hyp.  exactly one even theta constant vanishes; Rosenhain form
#                   y^2 = x(x-1)(x-l3)...(x-l7) by Takase's formula (as in
#                   Balakrishnan-Ionica-Lauter-Vincent, "Constructing genus 3
#                   hyperelliptic Jacobians with CM", Thm. 3 / Prop. 6)
#    genus 3, quartic: no even theta constant vanishes; Riemann model from the
#                   Weber moduli
#
#  At the end: the genus 3 parts of the genus 4 reconstruction (the Prym is a
#  genus 3 Jacobian): the 28 bitangents of a plane quartic from its Weber
#  moduli and the signs of the genus 3 theta constants from Riemann's quartic
#  relations.
#
#  Comparison (curves over QQ): the invariants of the original curve are
#  computed exactly (j, Igusa-Clebsch, Shioda, Dixmier-Ohno; Hecke's HypellCrv
#  and G3Crv code), those of the reconstructed curve over CC with the same
#  code; the latter are scaled to the former in weighted projective space and
#  recognized as rational numbers (Algebraization.jl).
#
#  Usage:
#    include("ReconstructCurvesG123.jl")
#    RS = riemann_surface(f, 200)
#    C = reconstruct_curve_from_tau(small_period_matrix(RS))
#    compare_with_original(f, RS, hyperelliptic)   # (ok, all_recognized, log2_diff, recognized)
#    random_reconstruction_tests(10; genus = 3, hyperelliptic = false)
#
################################################################################

using Hecke
const RSR = Hecke.RiemannSurfaces

function _log2abs(z)
  a = abs(z)
  RR = parent(a)
  u = RR(Hecke.midpoint(a)) + RR(radius(a))
  iszero(u) && return -Inf
  return Float64(Hecke.midpoint(log(u) / log(RR(2))))
end

################################################################################
#  Reconstruction
################################################################################

"""
    reconstruct_curve(tau::AcbMatrix) -> Vector{MPolyRingElem}

Reconstruct a model of the curve from the small period matrix of a Riemann surface
(genus 1, 2 or 3). 
"""

function reconstruct_curve_from_tau(tau::AcbMatrix)
  g = nrows(tau)
  g == 1 && return _reconstruct_genus1(tau)
  g == 2 && return _reconstruct_genus2(tau)
  g == 3 && return _reconstruct_genus3(tau)
  g == 4 && return _reconstruct_genus4(tau)    
  error("Reconstruction only for genus 1, 2, 3 and 4.")
end

function _reconstruct_genus1(tau::AcbMatrix)
  j = j_invariant(tau[1])
  return elliptic_curve_from_j_invariant(j)
end

function _reconstruct_genus2(tau::AcbMatrix)
  CC = base_ring(tau)
  th = theta_constants(tau)
  t1 = th[0, 0, 1, 0]
  t2 = th[0, 0, 1, 1]
  t3 = th[0, 1, 1, 0]
  t4 = th[1, 0, 0, 0]
  t5 = th[1, 0, 0, 1]
  t6 = th[1, 1, 0, 0]
  l1 = (-t1^2 * t3^2) / (t6^2 * t4^2)
  l2 = (-t2^2 * t3^2) / (t6^2 * t5^2)
  l3 = (-t2^2 * t1^2) / (t4^2 * t5^2)
  CCx, x = polynomial_ring(CC, :x)
  f = x*(x-1)*(x-l1)*(x-l2)*(x-l3)
  X = hyperelliptic_curve(f)
  return X
end

function _reconstruct_genus3(tau::AcbMatrix)
  CC = base_ring(tau)
  prec = precision(CC)
  th = theta_constants(tau)
  van = _vanishing_even_theta_constants(th, prec)
  if isempty(van)
    F = _riemann_model_from_moduli(_moduli_from_theta(th))
    return F
  end
  @req length(van) == 1 "$(length(van)) even theta constants vanish; expected 0 (plane quartic) or 1 (hyperelliptic). Is the Jacobian decomposable, or the precision too low?"
  delta = collect(van[1])
  lambdas = _takase_rosenhain(th, delta)
  CCx, x = polynomial_ring(CC, :x)
  f = x*(x-1)*prod(x-lambda for lambda in lambdas)
  X = hyperelliptic_curve(f)
  return X
end

################################################################################
#  Genus 3 hyperelliptic: Takase's formula
#
#  As in Balakrishnan-Ionica-Lauter-Vincent and the Magma code
#  (curve_reconstruction/rosenhain.m, precomp.m): the characteristic of the
#  vanishing even theta constant determines a matrix gamma (precomputed by
#  BILV), which transforms Mumford's eta map; the Rosenhain invariants are
#  Takase's quotients of squares of theta constants (Thm. 4.5 there).
#  Characteristics are bit vectors (a1, a2, a3, b1, b2, b3), i.e. 2 * the
#  characteristic in {0, 1/2}^6.
################################################################################

# Mumford's eta map: eta_1, ..., eta_7 for the finite branch points, eta_8 = 0
# for the one at infinity.
_mumford_eta() = [[1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0],
                  [0, 1, 0, 1, 1, 0], [0, 0, 1, 1, 1, 0], [0, 0, 1, 1, 1, 1],
                  [0, 0, 0, 1, 1, 1], [0, 0, 0, 0, 0, 0]]

# the BILV matrix gamma for the vanishing characteristic v (not symplectic;
# it acts linearly on the characteristics mod 1)
function _precomputed_gamma(v::Vector{Int})
  gammas = Dict{NTuple{6, Int}, Vector{Int}}(
    (0, 1, 0, 0, 0, 0) => [1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1],
    (0, 1, 1, 0, 1, 1) => [0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0],
    (0, 0, 0, 0, 1, 0) => [0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1],
    (1, 1, 1, 1, 1, 0) => [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1],
    (1, 1, 1, 0, 0, 0) => [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1],
    (0, 0, 1, 1, 0, 0) => [1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1],
    (0, 1, 1, 1, 0, 0) => [1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    (1, 0, 1, 0, 1, 0) => [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    (0, 0, 1, 1, 1, 0) => [1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    (0, 0, 1, 0, 0, 0) => [0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1],
    (0, 1, 1, 0, 0, 0) => [0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1],
    (0, 0, 1, 0, 1, 0) => [0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0],
    (1, 0, 0, 0, 0, 0) => [0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1],
    (1, 1, 0, 0, 0, 0) => [1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    (1, 0, 1, 0, 0, 0) => [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0],
    (0, 1, 0, 0, 0, 1) => [1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1],
    (1, 1, 0, 1, 1, 1) => [1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0],
    (1, 1, 0, 0, 0, 1) => [1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0],
    (0, 0, 0, 1, 0, 1) => [1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1],
    (0, 1, 0, 1, 0, 1) => [0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0],
    (1, 0, 0, 0, 1, 1) => [0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0],
    (0, 0, 0, 1, 1, 1) => [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    (0, 0, 0, 0, 0, 1) => [0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0],
    (1, 0, 1, 1, 0, 1) => [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0],
    (1, 1, 1, 1, 0, 1) => [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1],
    (0, 0, 0, 0, 1, 1) => [0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0],
    (1, 0, 1, 1, 1, 1) => [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    (1, 1, 0, 1, 1, 0) => [1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    (1, 0, 0, 0, 0, 1) => [1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1],
    (0, 0, 0, 1, 0, 0) => [1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0],
    (0, 1, 0, 1, 0, 0) => [1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1],
    (1, 1, 1, 0, 1, 1) => [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1],
    (0, 1, 1, 1, 1, 1) => [1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1],
    (1, 0, 0, 0, 1, 0) => [1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    (0, 0, 0, 1, 1, 0) => [1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1],
  )
  # v = 0: gamma from Example 4.3
  gamma0 = [1, 1, 1, -1, 1, 1,  0, 1, 0, 0, -1, 0,  0, 1, 0, -1, 1, 1,
            -1, -1, -1, 2, -1, -1,  0, 0, -1, 1, -1, -1,  0, -1, -1, -1, 1, 0]
  entries = get(gammas, Tuple(v), gamma0)
  return [entries[6*(i - 1) + j] for i in 1:6, j in 1:6]        # row-major
end

# a characteristic (a_1, ..., a_g, b_1, ..., b_g) in bits is odd iff a.b is odd
function _is_odd_characteristic(v)
  g = div(length(v), 2)
  return isodd(sum(v[i]*v[g + i] for i in 1:g))
end

# Takase's quotient (Thm. 4.5) for the branch points k, l, m of a hyperelliptic
# curve of genus g (eta: the 2g + 2 values of the eta map, U as in BILV)
function _takase_quotient(thetas_sq, eta, U, k::Int, l::Int, m::Int)
  g = div(length(eta[1]), 2)
  rest = sort(setdiff(1:2*g + 1, [k, l, m]))
  V = rest[1:g - 1]
  W = rest[g:2*g - 2]
  eta_value(S) = Tuple(mod.(sum((eta[i] for i in S); init = zeros(Int, 2*g)), 2))
  theta_sq(S) = thetas_sq[eta_value(symdiff(U, S))]
  # sign: (-1)^(<eta_k, eta_k + eta_l + eta_m> + [k not in U] - 1)
  e1 = eta[k]
  e2 = mod.(eta[k] + eta[l] + eta[m], 2)
  exponent = sum(e1[i]*e2[g + i] for i in 1:g) + (k in U ? 0 : 1) - 1
  sign = iseven(exponent) ? 1 : -1
  return sign * theta_sq(vcat(V, [k, l])) * theta_sq(vcat(W, [k, l])) /
         (theta_sq(vcat(V, [k, m])) * theta_sq(vcat(W, [k, m])))
end

# The Rosenhain invariants lambda_3, ..., lambda_7: the curve is
# y^2 = x (x - 1) prod (x - lambda_l). delta: the vanishing even
# characteristic (bits).
function _takase_rosenhain(th, delta::Vector{Int})
  @req !_is_odd_characteristic(delta) "The vanishing characteristic is odd."
  gamma = _precomputed_gamma(delta)
  eta = [mod.(gamma * e, 2) for e in _mumford_eta()]
  U = union([i for i in 1:8 if _is_odd_characteristic(eta[i])], [8])
  thetas_sq = Dict(ch => v^2 for (ch, v) in th)
  return [_takase_quotient(thetas_sq, eta, U, 1, l, 2) for l in 3:7]
end

################################################################################
#  Genus 3 non-hyperelliptic: Riemann model from the Weber moduli
################################################################################

function _moduli_from_theta(theta_dict)
  inds = Hecke.theta_characteristics_indices(3)
  thetas = [theta_dict[inds[i]] for i in (1:64)]
  I = onei(parent(thetas[1]))
  a1 = I*thetas[34]*thetas[6]/(thetas[41]*thetas[13])
  a2 = I*thetas[22]*thetas[50]/(thetas[29]*thetas[57])
  a3 = I*thetas[8]*thetas[36]/(thetas[15]*thetas[43])
  ap1 = I*thetas[6]*thetas[55]/(thetas[28]*thetas[41])
  ap2 = I*thetas[50]*thetas[3]/(thetas[48]*thetas[29])
  ap3 = I*thetas[36]*thetas[17]/(thetas[62]*thetas[15])
  as1 = -thetas[55]*thetas[34]/(thetas[13]*thetas[28])
  as2 = thetas[3]*thetas[22]/(thetas[57]*thetas[48])
  as3 = thetas[17]*thetas[8]/(thetas[43]*thetas[62])
  return [a1, a2, a3, ap1, ap2, ap3, as1, as2, as3]
end

function _riemann_model_from_moduli(mods)
  a1, a2, a3, ap1, ap2, ap3 = mods[1:6]
  CC = parent(a1)
  P, (x1, x2, x3) = polynomial_ring(CC, [:x1, :x2, :x3])
  M = matrix(CC, 3, 3, [1, 1, 1, a1, a2, a3, ap1, ap2, ap3])
  Mb = matrix(CC, 3, 3, [1, 1, 1, 1/a1, 1/a2, 1/a3, 1/ap1, 1/ap2, 1/ap3])
  U = -inv(Mb) * M
  xs = [x1, x2, x3]
  u = [sum(U[i, t] * xs[t] for t in 1:3) for i in 1:3]
  return (x1*u[1] + x2*u[2] - x3*u[3])^2 - 4*x1*u[1]*x2*u[2]
end

################################################################################
#  Comparison: scale the reconstructed invariants to the original ones and
#  recognize them as rational numbers
################################################################################

function _recognize_rational(a::AcbFieldElem)
  K, _ = rationals_as_number_field()
  try
    return coeff(RSR.algebraize_element(a, K), 0)
  catch
    return nothing
  end
end

"""
    compare_invariants(Iex, Icc, ws)

`Iex`: invariants of the original curve over QQ, `Icc`: those of the
reconstructed curve over CC, weights `ws`. Scale `Icc` in weighted projective
space so that its entry r (the nonzero original invariant of smallest weight)
equals Iex[r] (trying all ws[r]-th roots), then recognize the entries as
rational numbers. Returns a named tuple with
  * `ok`: the scaled invariants agree with `Iex` to more than half of the
    precision (`log2_diff < -prec/2`),
  * `all_recognized`: all scaled invariants are recognized as rational
    numbers and equal to `Iex` (needs more precision than `ok`: roughly twice
    the height of the invariants in bits),
  * `log2_diff`: log2 of the largest relative difference,
  * `recognized`: the recognized rational numbers (`nothing` where not).
"""
function compare_invariants(Iex::Vector{QQFieldElem}, Icc::Vector{AcbFieldElem}, ws::Vector{Int})
  CC = parent(Icc[1])
  prec = precision(CC)
  nz = findall(!iszero, Iex)
  if isempty(nz)
    # only possible for absolute invariants (j = 0); weighted invariants of a
    # smooth curve do not all vanish
    diff = maximum(_log2abs(z) for z in Icc)
    rec = [diff < -prec/3 ? QQ(0) : nothing for _ in Icc]
    return (ok = diff < -prec/2, all_recognized = all(r -> r == QQ(0), rec), log2_diff = diff, recognized = rec)
  end
  r = nz[argmin(ws[nz])]
  if ws[r] == 0                                    # absolute invariants (j)
    lams = [one(CC)]
  else
    q = CC(Iex[r]) / Icc[r]
    # a w-th root of q; q is rotated by its Float64 argument first, since for a
    # real curve q is often a negative real number whose ball straddles the
    # branch cut of log (then log(q) has an imaginary part covering [-pi, pi])
    theta = angle(ComplexF64(Float64(real(q)), Float64(imag(q))))
    rot = exp(onei(CC) * CC(theta))
    base = exp(log(q / rot) / ws[r]) * exp(onei(CC) * CC(theta) / ws[r])
    zeta = exp(2 * const_pi(CC) * onei(CC) / ws[r])
    lams = [base * zeta^s for s in 0:ws[r]-1]
  end
  best = (ok = false, all_recognized = false, log2_diff = Inf, recognized = nothing)
  for lam in lams
    scaled = [Icc[i] * lam^ws[i] for i in eachindex(ws)]
    # scale of the invariants: |Iex[r]|^(w_i/w_r)
    scalar(i) = ws[r] == 0 ? 1.0 : exp2(ws[i] / ws[r] * _log2abs(CC(Iex[r])))
    diff = maximum(_log2abs(scaled[i] - CC(Iex[i])) - log2(max(scalar(i), exp2(_log2abs(CC(Iex[i]))), 1e-300))
                   for i in eachindex(ws))
    diff < best.log2_diff || continue
    rec = [iszero(Iex[i]) ? (_log2abs(scaled[i]) < log2(scalar(i)) - prec/3 ? QQ(0) : nothing) :
           _recognize_rational(scaled[i]) for i in eachindex(ws)]
    best = (ok = diff < -prec/2, all_recognized = all(rec[i] == Iex[i] for i in eachindex(ws)),
            log2_diff = diff, recognized = rec)
  end
  return best
end

"""
    compare_with_original(f, RS, hyperelliptic::Bool) -> NamedTuple

Reconstruct the curve from the period matrix of `RS` and compare its
invariants with the exact invariants of the original curve over QQ:
j (genus 1), Igusa-Clebsch (genus 2), Shioda (genus 3 hyperelliptic),
Dixmier-Ohno (plane quartics). The reconstructed invariants are scaled to the
original ones (weighted projective space) and recognized as rational numbers
(Algebraization.jl). `f` is the curve over QQ (y^2 = h(x) for genus 1, 2
and hyperelliptic genus 3, a plane quartic otherwise). Genus 4: Bouchet's
invariants of the canonical model, or the branch points for hyperelliptic
curves (see _compare_with_original_g4 in ReconstructG4.jl); the result also
has the field `case`. See
`compare_invariants` for the fields of the result (`ok`, `all_recognized`,
`log2_diff`, `recognized`).
"""
function compare_with_original(f, RS, hyperelliptic)
  g = genus(RS)
  g == 4 && return _compare_with_original_g4(f, RS, hyperelliptic)    # ReconstructG4.jl
  CC = base_ring(small_period_matrix(RS))
  prec = precision(CC)
  tau = small_period_matrix(RS)
  if g == 1
    R, x = polynomial_ring(QQ)
    fx = f(x, R(0))
    E = elliptic_curve(fx)
    j = j_invariant(E)
    j_CC = j_invariant(tau[1])
    return compare_invariants([j], [j_CC], [0])
  elseif g == 2 
    R, x = polynomial_ring(QQ)
    fx = f(x, R(0))
    C = hyperelliptic_curve(fx)
    I, ws = igusa_invariants(C)
    C_CC = reconstruct_curve_from_tau(tau)
    I_CC, ws = igusa_invariants(C_CC)
    return compare_invariants(I, I_CC, ws)
  elseif g == 3 && hyperelliptic
    R, x = polynomial_ring(QQ)
    fx = f(x, R(0))
    C = hyperelliptic_curve(fx)
    I, ws = shioda_invariants(C)
    C_CC = reconstruct_curve_from_tau(tau)
    I_CC, ws = shioda_invariants(C_CC)
    return compare_invariants(I, I_CC, ws)
  else
    f_hom = Hecke.RiemannSurfaces.homogenization_RS(f)
    I, ws = dixmier_ohno_invariants(f_hom)
    quartic_CC = reconstruct_curve_from_tau(tau)
    I_CC, ws = dixmier_ohno_invariants(quartic_CC)
    return compare_invariants(I, I_CC, ws)
  end
end

################################################################################
#  Random tests
################################################################################

function _random_curve(genus::Int, hyperelliptic::Bool; coeff_range = -5:5)
  S, (x, y) = polynomial_ring(QQ, [:x, :y])
  rnd() = QQ(rand(coeff_range))
  if genus <= 2 || hyperelliptic
    d = 2*genus + 1
    h = sum(rnd() * x^i for i in 0:d-1) + x^d
    return h - y^2
  end
  S, (x, y) = polynomial_ring(QQ, [:x, :y])
  f = sum(rnd() * x^i * y^j for i in 0:4 for j in 0:4-i)
  return f + x^4 + y^4                                          # keep the degree 4 in x and y
end

"""
    random_reconstruction_tests(n; genus, hyperelliptic = false, prec = nothing, kw...)

Compute the period matrices of `n` random curves (y^2 = h(x) for genus 1, 2
and hyperelliptic genus 3, plane quartics otherwise), reconstruct them and
compare. Keywords are passed to `riemann_surface` (e.g. `superelliptic = false`).
Curves of the wrong genus (singular) are skipped. Default precision: 1000
bits. `ok` (agreement to half the precision) needs much less precision than
recognizing all invariants as rationals (`all_recognized`): for hyperelliptic
genus 3 about 400 bits, for plane quartics more (the Dixmier-Ohno invariants
are rationals with ~50-100 digits).
"""
function random_reconstruction_tests(n::Int; genus::Int, hyperelliptic::Bool = false,
                                     prec = 1000, kw...)
  genus == 4 && return random_g4_reconstruction_tests(n; kind = hyperelliptic ? :hyperelliptic : :generic,
                                                     prec = prec, kw...)
  results = []
  done = 0
  while done < n
    f = _random_curve(genus, hyperelliptic)
    RS = riemann_surface(f, prec; kw...)
    RSR.genus(RS) == genus || continue
    done += 1
    t = @elapsed r = try
      compare_with_original(f, RS, hyperelliptic)
    catch e
      (ok = false, all_recognized = false, log2_diff = NaN, recognized = nothing,
       error = sprint(showerror, e))
    end
    println(rpad(string(done), 4), rpad(string(r.ok), 7), rpad(string(r.all_recognized), 7),
            lpad(string(round(r.log2_diff, digits = 1)), 8),
            lpad(string(round(t, digits = 2), "s"), 9), "  ", f)
    r.ok == true || println("    ", r)
    push!(results, (f = f, result = r, time = t))
  end
  nok = count(r -> r.result.ok == true, results)
  nrec = count(r -> r.result.all_recognized == true, results)
  println("$nok of $n reconstructions agree with the original curve (log2_diff < -prec/2); ",
          "for $nrec all invariants were recognized.")
  return results
end

################################################################################
#  Diagnostics for the hyperelliptic genus 3 reconstruction
################################################################################

# The Shioda invariants of a reconstruction, made independent of the scaling:
# J_k^2 / J_2^k for k = 3, ..., 10 (J_2 must not vanish).
function _scale_free_shioda(tau::AcbMatrix)
  I, ws = shioda_invariants(_reconstruct_genus3(tau))
  return [I[i]^2 / I[1]^ws[i] for i in 2:length(I)]
end

# A random integral symplectic 2g x 2g matrix (a product of `steps` generators).
function _random_symplectic(g::Int; steps::Int = 12)
  T = identity_matrix(ZZ, 2*g)
  for _ in 1:steps
    G = identity_matrix(ZZ, 2*g)
    kind = rand(1:3)
    if kind == 1                       # [I S; 0 I], S symmetric
      i, j = rand(1:g), rand(1:g)
      G[i, g + j] += 1
      i != j && (G[j, g + i] += 1)
    elseif kind == 2                   # [A 0; 0 A^-T], A = I + E_ij
      i, j = rand(1:g), rand(1:g)
      i == j && continue
      G[i, j] = 1
      G[g + j, g + i] = -1
    else                               # [0 I; -I 0]
      G = zero_matrix(ZZ, 2*g, 2*g)
      for k in 1:g
        G[k, g + k] = 1
        G[g + k, k] = -1
      end
    end
    T = G * T
  end
  return T
end

"""
    check_takase_table(tau; tries = 300)

For the small period matrix `tau` of a hyperelliptic genus 3 curve: transform
it by random symplectic matrices (the same curve, other vanishing
characteristics) and compare the scale-free Shioda invariants of the
reconstructions with those for `tau`. Prints, per vanishing characteristic
reached, log2 of the largest relative difference; a characteristic with a
large difference points to a wrong entry of the gamma table (or a wrong sign
in Takase's quotient).
"""
function check_takase_table(tau::AcbMatrix; tries::Int = 300)
  prec = precision(base_ring(tau))
  reference = _scale_free_shioda(tau)
  worst = Dict{NTuple{6, Int}, Float64}()
  for _ in 1:tries
    t2 = Hecke.siegel_transform(_random_symplectic(3), tau)
    van = _vanishing_even_theta_constants(theta_constants(t2), prec)
    length(van) == 1 || continue
    v0 = van[1]
    other = try
      _scale_free_shioda(t2)
    catch
      nothing
    end
    d = other === nothing ? Inf :
        maximum(_log2abs(other[i] - reference[i]) - _log2abs(reference[i]) for i in eachindex(reference))
    worst[v0] = max(get(worst, v0, -Inf), d)
  end
  for v0 in sort(collect(keys(worst)))
    println(v0, "  ", round(worst[v0], digits = 1))
  end
  println(length(worst), " of 36 even characteristics reached.")
  return worst
end

################################################################################
#
#  Bitangents of a plane quartic from its Weber moduli (used by the genus 4
#  reconstruction for the Prym)
#
################################################################################

# sum of c v over the pairs (c, v) (v: coefficient vectors of length 3)
_linear_combination(terms...) = [sum(c * v[j] for (c, v) in terms) for j in 1:3]

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
  append!(lines, [_linear_combination((inv(a[i, 1]), u0), (a[i, 2], t1), (a[i, 3], t2)) for i in 1:3])
  append!(lines, [_linear_combination((inv(a[i, 2]), u1), (a[i, 1], t0), (a[i, 3], t2)) for i in 1:3])
  append!(lines, [_linear_combination((inv(a[i, 3]), u2), (a[i, 1], t0), (a[i, 2], t1)) for i in 1:3])
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
    push!(lines, _linear_combination((inv(b0*(1 - b1*b2)), u0), (inv(b1*(1 - b0*b2)), u1), (inv(b2*(1 - b0*b1)), u2)))
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
