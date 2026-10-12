################################################################################
#
#  ReconstructCurvesG123.jl -- reconstruct a curve of genus 1, 2 or 3 from
#  its small period matrix (via theta constants).
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
#  The comparison with the original curve by invariants and the tests on
#  random curves are in test/RieSrf/Reconstruction/ReconstructionHelpers.jl.
#
################################################################################

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
(genus 1, 2, 3 or 4). 
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
#  Following Balakrishnan-Ionica-Lauter-Vincent: the characteristic of the
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
#  Rational numbers from balls (used by the model over Q of genus 4)
################################################################################

function _recognize_rational(a::AcbFieldElem)
  K, _ = rationals_as_number_field()
  try
    return coeff(algebraize_element(a, K), 0)
  catch
    return nothing
  end
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
#  Signs of the genus 3 theta constants 
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
    values = [abs(_c64(sum(sign_options[j][nu] * prod(thetas[Tuple(mod.(cosets[j][xi], 2))] for xi in 1:4)
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
