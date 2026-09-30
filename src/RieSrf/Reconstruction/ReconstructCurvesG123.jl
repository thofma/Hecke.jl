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
#  recognized as rational numbers (Algebraization.jl). Hyperelliptic curves
#  are also compared by their branch points (Moebius equivalence).
#
#  Usage:
#    include("ReconstructCurves.jl")
#    RS = riemann_surface(f, 200)
#    r = reconstruct_curve(RS)           # the reconstructed model
#    compare_with_original(RS)           # (ok = ..., kind = ..., details...)
#    random_reconstruction_tests(10; genus = 3, hyperelliptic = false)
#
################################################################################

using Hecke
import LinearAlgebra
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
  error("Reconstruction only for genus 1, 2 and 3.")
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
  if iszero(delta)
    # Takase's formula needs a nonzero vanishing characteristic: move it
    # with an integral translation of tau (same curve).
    t2 = deepcopy(tau)
    t2[1, 1] += 1
    return _reconstruct_genus3(t2)
  end
  lambdas = _takase_rosenhain(th, delta)
  CCx, x = polynomial_ring(CC, :x)
  f = x*(x-1)*prod(x-lambda for lambda in lambdas)
  X = hyperelliptic_curve(f)
  return X
end

################################################################################
#  Genus 3 hyperelliptic: Takase's formula
################################################################################

# Mumford's eta map for g = 3 (characteristics as bit vectors (a1,a2,a3,b1,b2,b3),
# eta = bits/2); eta_infinity = 0; U = {2, 4, 6, infinity}.
function _mumford_eta3()
  e = Dict{Int, Vector{Int}}()
  for i in 1:4
    v = zeros(Int, 6)
    i <= 3 && (v[i] = 1)
    for t in 1:i-1
      v[3 + t] = 1
    end
    e[2i - 1] = v
  end
  for i in 1:3
    v = zeros(Int, 6)
    v[i] = 1
    for t in 1:i
      v[3 + t] = 1
    end
    e[2i] = v
  end
  return e
end

_q(v) = mod(v[1]*v[4] + v[2]*v[5] + v[3]*v[6], 2)

# Generators (mod 2) of the image of Gamma_{1,2} acting on characteristics:
# [[I, 0], [S, I]], [[I, S], [0, I]] with S symmetric with zero diagonal and
# [[A, 0], [0, A^-T]] with A elementary. They preserve the quadratic form q.
function _gamma12_generators()
  gens = Matrix{Int}[]
  I3 = Matrix{Int}(LinearAlgebra.I, 3, 3)
  Z3 = zeros(Int, 3, 3)
  for i in 1:3, j in i+1:3
    S = zeros(Int, 3, 3); S[i, j] = S[j, i] = 1
    push!(gens, [I3 Z3; S I3])
    push!(gens, [I3 S; Z3 I3])
  end
  for i in 1:3, j in 1:3
    i == j && continue
    A = copy(I3); A[i, j] = 1                      # elementary, A^-1 = A mod 2
    push!(gens, [A Z3; Z3 permutedims(A)])         # A^-T = A^T mod 2
  end
  for p in ([2, 1, 3], [1, 3, 2])
    A = I3[p, :]
    push!(gens, [A Z3; Z3 A])
  end
  return gens
end

# a matrix M in the group generated by _gamma12_generators with M v = w (mod 2)
function _find_gamma(v::Vector{Int}, w::Vector{Int})
  gens = _gamma12_generators()
  I6 = Matrix{Int}(LinearAlgebra.I, 6, 6)
  seen = Dict(v => I6)
  queue = [v]
  while !isempty(queue)
    u = popfirst!(queue)
    u == w && return seen[u]
    for G in gens
      u2 = mod.(G * u, 2)
      if !haskey(seen, u2)
        seen[u2] = mod.(G * seen[u], 2)
        push!(queue, u2)
      end
    end
  end
  error("No transformation found for the vanishing characteristic $w.")
end

function _takase_rosenhain(th, delta::Vector{Int})
  et = _mumford_eta3()
  U = [2, 4, 6]                                    # and infinity (eta = 0)
  v0 = mod.(sum(et[i] for i in U), 2)              # (1,1,1,1,0,1)
  @req _q(delta) == 0 "The vanishing characteristic is odd."
  M = _find_gamma(v0, delta)
  eta = Dict(i => mod.(M * et[i], 2) for i in 1:7)
  etaS(S) = Tuple(mod.(sum((eta[i] for i in S); init = zeros(Int, 6)), 2))
  symdiff(A, B) = setdiff(union(A, B), intersect(A, B))
  T(S) = th[etaS(symdiff(U, S))...]              # U o S (infinity cancels or not: eta_inf = 0)
  lambdas = AcbFieldElem[]
  for k in 3:7
    others = setdiff(3:7, [k])
    vals = AcbFieldElem[]
    for (V, W) in (([others[1], others[2]], [others[3], others[4]]),
                   ([others[1], others[3]], [others[2], others[4]]),
                   ([others[1], others[4]], [others[2], others[3]]))
      R = T(vcat(V, [k, 1])) * T(vcat(W, [k, 1])) / (T(vcat(V, [k, 2])) * T(vcat(W, [k, 2])))
      r = R^2                                      # (k, 1, 2) = +1 since 1, 2 < k
      push!(vals, r / (r - 1))                     # (l_k - 0)/(l_k - 1) = r
    end
    CC = parent(vals[1])
    tol = ArbField(precision(CC))(2)^(-div(precision(CC), 3))
    @req all(abs(v - vals[1]) < tol * (1 + abs(vals[1])) for v in vals) "Takase's formula gives different values for different decompositions (conventions?)."
    push!(lambdas, vals[1])
  end
  return lambdas
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
rational numbers. `ok`: all recognized and equal to `Iex`. Also returns
log2 of the largest relative difference (for diagnosis).
"""
function compare_invariants(Iex::Vector{QQFieldElem}, Icc::Vector{AcbFieldElem}, ws::Vector{Int})
  CC = parent(Icc[1])
  prec = precision(CC)
  nz = findall(!iszero, Iex)
  isempty(nz) && return (ok = false, reason = "all original invariants vanish")
  r = nz[argmin(ws[nz])]
  if ws[r] == 0                                    # absolute invariants (j)
    lams = [one(CC)]
  else
    q = CC(Iex[r]) / Icc[r]
    base = exp(log(q) / ws[r])
    zeta = exp(2 * const_pi(CC) * onei(CC) / ws[r])
    lams = [base * zeta^s for s in 0:ws[r]-1]
  end
  best = (ok = false, log2_diff = Inf, recognized = nothing)
  for lam in lams
    scaled = [Icc[i] * lam^ws[i] for i in eachindex(ws)]
    # scale of the invariants: |Iex[r]|^(w_i/w_r)
    scalar(i) = ws[r] == 0 ? 1.0 : exp2(ws[i] / ws[r] * _log2abs(CC(Iex[r])))
    diff = maximum(_log2abs(scaled[i] - CC(Iex[i])) - log2(max(scalar(i), exp2(_log2abs(CC(Iex[i]))), 1e-300))
                   for i in eachindex(ws))
    diff < best.log2_diff || continue
    rec = [iszero(Iex[i]) ? (_log2abs(scaled[i]) < log2(scalar(i)) - prec/3 ? QQ(0) : nothing) :
           _recognize_rational(scaled[i]) for i in eachindex(ws)]
    best = (ok = all(rec[i] == Iex[i] for i in eachindex(ws)), log2_diff = diff, recognized = rec)
  end
  return best
end

"""
    compare_with_original(RS) -> NamedTuple

Reconstruct the curve from the period matrix of `RS` and compare its
invariants with the exact invariants of the original curve over QQ:
j (genus 1), Igusa-Clebsch (genus 2), Shioda (genus 3 hyperelliptic),
Dixmier-Ohno (plane quartics). The reconstructed invariants are scaled to the
original ones (weighted projective space) and recognized as rational numbers
(Algebraization.jl); `ok` means that all of them are recognized and equal to
the original ones. `ok = nothing` if the original model is not of a supported
form (y^2 = h(x) resp. a plane quartic over QQ). For hyperelliptic curves
`moebius` also tells whether the branch points are equivalent under PGL_2.
"""
function compare_with_original(f, RS, hyperelliptic)
  CC = base_ring(small_period_matrix(RS))
  prec = precision(CC)
  g = genus(RS)
  tau = small_period_matrix(RS)
  if g == 1
    R, x = polynomial_ring(QQ)
    fx = f(x, R(0))
    E = elliptic_curve(fx)
    j = j_invariant(E)
    j_CC = j_invariant(tau[1])
    j_QQ = _recognize_rational(j_CC)
    return compare_invariants([j_QQ], [j_CC], [0])
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
Curves of the wrong genus (singular) are skipped. Default precision: 200
bits, 500 for plane quartics (the Dixmier-Ohno invariants of the original
curve are rationals with ~50-100 digits, which have to be recognized).
"""
function random_reconstruction_tests(n::Int; genus::Int, hyperelliptic::Bool = false,
                                     prec = 1000, kw...)
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
      (ok = false, kind = :error, reason = sprint(showerror, e))
    end
    println(rpad(string(done), 4), rpad(string(r.ok), 8),
            lpad(string(round(t, digits = 2), "s"), 8), "  ", f)
    r.ok == true || println("    ", r)
    push!(results, (f = f, result = r, time = t))
  end
  nok = count(r -> r.result.ok == true, results)
  println("$nok of $n reconstructions agree with the original curve.")
  return results
end
