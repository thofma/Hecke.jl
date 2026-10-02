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
  g == 4 && return reconstruct_curve_g4(tau)          # ReconstructG4.jl
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
