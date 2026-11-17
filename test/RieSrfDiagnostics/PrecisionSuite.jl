################################################################################
#
#  PrecisionTests.jl -- measurement only, no assertions on accuracy
#
#  For every curve and every precision p this records
#
#    claimed  bits  -log2(max radius of the entries of the big period matrix)
#    true     bits  -log2(max |mid(P_p) - mid(P_ref)|), P_ref at a higher precision
#    margin         true - claimed. Negative = the balls are too small (the
#                   radii are not rigorous). This is what breaks the
#                   endomorphism computations.
#    contained      every entry of P_p overlaps the entry of P_ref
#    loss           p - true bits (how much of the input precision was lost)
#    tau_cl, tau_tr claimed and true bits of the small period matrix
#                   (claimed - tau_cl = what the inversion of P1 costs)
#    predictors     genus, sheets, #discriminant points, log2 of the integrand
#                   bound M, #quadrature nodes, computational precision
#    clus           log2(diameter / min distance) of the discriminant points
#    inf            direct loop around infinity: 1 agrees with the composed
#                   one, -1 does not (a warning), 0 not checked
#    K, T, retry    general algorithm: #subpaths, quadrature target T
#                   (prec + 10 + ceil(log2 K), raised by a retry), and whether
#                   the integration was redone because tau claimed < prec bits
#
#  All accuracies are absolute; `scale` is log2 max |P_ij| for reference.
#  The :auto model choice only depends on degrees, so every precision uses the
#  same model and the same bases.
#
#  Usage (from a session where Hecke is loaded):
#
#      include("PrecisionTests.jl")
#      rows = run_precision_suite(tier = 1)                 # HE curves + small
#      rows = run_precision_suite(tier = 2, precs = [100, 200])
#      run_endomorphism_precision_suite(precs = [150, 200, 300, 500])
#
#  Tiers: 1 = HeuristicEndomorphisms curves and a few small ones,
#         2 = Neurohr's genus 22 - 36 curves, 3 = genus 43, 45, 54.
#  Results are appended to `csv` (default "precision_results.csv").
#
################################################################################

using Hecke
import Random
using Hecke.RiemannSurfaces
import Hecke.Nemo            # binds `Nemo` (for Nemo.midpoint)
import Hecke.RiemannSurfaces: computational_model

################################################################################
#  Curves
################################################################################

function _qq_curves_tier(tier::Int)
  S, (x, y) = polynomial_ring(QQ, [:x, :y])
  if tier == 1
    return [
      (name = "e_small", genus = 1, f = y^2 - 4*x*(x - 1)*(x + 1)),
      (name = "q_klein", genus = 3, f = x^3*y + y^3 + x),
      (name = "h1", genus = 8, f = -x^18 + 3*x^17 - 12*x^16 - 12*x^15 + 9*x^14 + 3*x^13 + 15*x^12 - 7*x^11 + 7*x^10 - 15*x^9 - 8*x^8 + 8*x^7 - 20*x^6 - 4*x^5 + 16*x^4 + 4*x^3 + 5*x^2 + y^2 - 5),
      (name = "g4_hard", genus = 12, f = ((y^3 + x^2)^2 + x^3*y^2)^2 + x^2*y^3),
      # failing in Neurohr's Magma code
      (name = "sf1", genus = 1, f = 10*x^2*y^2 + 17*x^2 - 7*x*y^2 - 12*x + 26*y^2 + 10),
      (name = "sf2", genus = -1, f = x^4 + x^3*y + 2*x^3 - 6*x^2*y^2 + 3*x^2*y - 6*x*y^3 + 3*x*y
                                      - 2*x + 4*y^4 + 5*y^3 - 3*y^2 - 3*y + 1),
      (name = "vh1", genus = -1, f = 17//26*x^5*y^2 - 3*x^5 + 10//13*x^4*y^2 + 41//17*x^4
                                      + 36//55*x^3*y^2 + 1//5*x^3*y + 23//2*x^3 + 14//41*x^2*y
                                      - 9//23*x*y + 17//22*y^2 - 1//5*y + 47//4),
    ]
  elseif tier == 2
    return filter(c -> c.genus <= 36, _neurohr_high_genus(x, y))
  elseif tier == 3
    return filter(c -> c.genus > 36, _neurohr_high_genus(x, y))
  elseif tier == 4
    return _big_coefficient_curves(x, y)
  elseif tier == 5
    return _mid_genus_curves(x, y)
  end
  error("tier must be 1, 2, 3, 4 or 5")
end

# Tier 5: genus 3 to 6, for the homomorphism tests (swap / transform suites):
# generic curves (End = ZZ expected) and curves with many automorphisms (large
# endomorphism rings, many generators). genus = -1: not checked.
function _mid_genus_curves(x, y)
  return [
    (name = "m_picard", genus = 3, f = y^3 - x^4 - 1),                 # CM by ZZ[zeta_3]
    (name = "m_trig4", genus = -1, f = y^3 + x^2*y + x^5 + 2*x - 1),
    (name = "m_hyp4", genus = 4, f = y^2 - x^9 + x),                    # extra automorphisms
    (name = "m_cm5_3", genus = 4, f = y^5 - x^3 + 1),                   # CM by ZZ[zeta_5]
    (name = "m_gen4", genus = -1, f = y^3 - x^6 + 3*x^2*y + x + 2),
    (name = "m_gen5", genus = -1, f = y^4 + x^5 - 2*x*y^2 + x + 1),
    (name = "m_quint", genus = -1, f = x^5 + y^5 + x^2*y^2 + 2*x - y + 1),
    (name = "m_fermat5", genus = 6, f = x^5 + y^5 + 1),                 # large End
  ]
end

# Tier 4: curves (not superelliptic) with coefficients of very different sizes
# and high degree in x, like f26_g45 (which the superelliptic algorithm
# handles): evaluating f and the differentials then cancels many bits.
# genus = -1: not checked.
function _big_coefficient_curves(x, y)
  return [
    # the pattern of f26_g45 (1 - P(x^k), P with coefficients 1, 1e-7, 1e-18, 1e-32),
    # with k = 8 and a cubic in y with a y-term
    (name = "bigc1", genus = -1, f = y^3 + 5*x^3*y - 2*y + 1 - x^8 + QQ(1, ZZ(10)^7)*x^16 - QQ(1, ZZ(10)^18)*x^24 + QQ(1, ZZ(10)^32)*x^32),
    (name = "bigc2", genus = -1, f = y^4 + x^2*y^2 - 3*y + QQ(1, ZZ(10)^25)*x^30 - 7*QQ(1, ZZ(10)^14)*x^21 + QQ(1, ZZ(10)^6)*x^13 + 2*x^5 - 1),
    (name = "bigc4", genus = -1, f = big_coefficient_curve(x, y; m = 4, n = 24, seed = 2)),
  ]
end

"""
    big_coefficient_curve(x, y; m = 3, n = 30, nterms = 6, spread = 30, seed = 1)

A random curve y^m + a x^b y + c + sum_i c_i x^(e_i) with degree n in x, whose
coefficients c_i = +-d * 10^(k_i) (d in 1:99, k_i in -spread:spread) have very
different sizes. Not superelliptic (the term a x^b y).
"""
function big_coefficient_curve(x, y; m::Int = 3, n::Int = 30, nterms::Int = 6, spread::Int = 30, seed::Int = 1)
  rng = Random.MersenneTwister(seed)
  f = y^m + rand(rng, 1:9) * x^rand(rng, 1:4) * y + rand(rng, [-3, -2, -1, 1, 2, 3])
  exps = unique(vcat([n], rand(rng, 1:n-1, nterms - 1)))
  for e in exps
    c = QQ(rand(rng, [-1, 1]) * rand(rng, 1:99)) * QQ(10)^rand(rng, -spread:spread)
    f += c * x^e
  end
  return f
end

# From Neurohr's testfunctions.m. (In the Magma file f44 is the same
# polynomial as f22, and the genus 45 curve reuses the name f26.)
function _neurohr_high_genus(x, y)
  return [
    (name = "f8", genus = 22, f = 6*x^12-9*x^11+8*x^10-9*x^9+7*x^8-7*x^7+x^6+8*x^5-2*x^4+8*x^3+10*x^2+9*x+y^5+6),
    (name = "f36", genus = 24, f = -18*x^4*y^9-4*x^4*y^8-20*x^4*y^7-2*x^4*y^6+7*x^4*y^5-6*x^4*y^4+8*x^4*y^2+12*x^4*y-19*x^4-17*x^3*y^9+8*x^3*y^8-20*x^3*y^7+13*x^3*y^6+13*x^3*y^5+6*x^3*y^4+14*x^3*y^3+2*x^3*y^2+5*x^3*y+18*x^3+9*x^2*y^9+18*x^2*y^8-x^2*y^6+6*x^2*y^5+8*x^2*y^4+6*x^2*y^3-2*x^2*y^2+5*x^2*y+10*x^2+18*x*y^9+3*x*y^8+5*x*y^7-16*x*y^6+9*x*y^5+7*x*y^4+7*x*y^3+14*x*y^2-14*x*y+14*x-19*y^9-9*y^8-18*y^7-12*y^6+8*y^5-18*y^4-15*y^3+17*y^2+5*y-2),
    (name = "f31", genus = 28, f = 3*x^5*y^9+9*x^5*y^7-x^4*y^7+2*x^4*y^4+5*x^3*y^9+8*x^2*y^10-7*x*y^3-6*x-7*y^7-7*y),
    (name = "f37", genus = 30, f = x^6*y^7-3*x^6*y^6+5*x^6*y^5+3*x^6*y^3+2*x^6*y-x^6-2*x^5*y^7+2*x^5*y^4-2*x^5*y^3+2*x^5*y-x^5-4*x^4*y^6-5*x^4*y^4+4*x^4*y^3+5*x^4*y^2+4*x^4*y+x^4-x^3*y^6-5*x^3*y^5-x^3*y^4-2*x^3*y^2-4*x^3*y-2*x^2*y^7-4*x^2*y^5-5*x^2*y^4-3*x^2*y^3+2*x^2*y^2-5*x^2*y-x*y^6+5*x*y^5-4*x*y^4+3*x*y^3+4*x*y^2+2*x-5*y^7-4*y^6-2*y^5-3*y^4-5*y^2-y+1),
    (name = "f38", genus = 36, f = -11*x^5*y^10+17*x^5*y^9-16*x^5*y^8+15*x^5*y^7+16*x^5*y^6+7*x^5*y^5+7*x^5*y^4+11*x^5*y^3+18*x^5*y^2-13*x^5*y+x^5+12*x^4*y^10+15*x^4*y^9-11*x^4*y^8-x^4*y^7+8*x^4*y^6+6*x^4*y^5-10*x^4*y^4-14*x^4*y^3+19*x^4*y^2-9*x^4*y-11*x^4+15*x^3*y^10-12*x^3*y^9+7*x^3*y^8+9*x^3*y^7+4*x^3*y^6+20*x^3*y^5-12*x^3*y^3+20*x^3*y^2-9*x^3*y-6*x^3-15*x^2*y^10-13*x^2*y^9-15*x^2*y^8+7*x^2*y^7-12*x^2*y^6-2*x^2*y^5+7*x^2*y^4+20*x^2*y^3-19*x^2*y^2+5*x^2*y+18*x^2+5*x*y^10-16*x*y^9+4*x*y^8+8*x*y^7-15*x*y^6-12*x*y^5-15*x*y^4-10*x*y^3+15*x*y^2-18*x*y-11*x-y^10+19*y^9+12*y^8+20*y^7+19*y^6+11*y^5+10*y^3-16*y^2-12*y-5),
    (name = "f22", genus = 43, f = ((y^4-16)^2-2*x)*y^3-x^12),
    (name = "f26_g45", genus = 45, f = -QQ(big"1", big"55572324035428505185378394701824")*x^92+QQ(big"17615723936275", big"13893081008857126296344598675456")*x^69-QQ(big"6625328352560281666119755", big"55572324035428505185378394701824")*x^46+QQ(big"6624738056749922952079435", big"6624737266949237011120128")*x^23+y^2-1),
    (name = "f19", genus = 54, f = x^9*y^2+7*x^9*y+6*x^8*y^6-6*x^8*y^4-7*x^7*y-x^6*y^5-9*x^6*y^4-7*x^6*y^3-4*x^6*y^2+6*x^5*y^6+x^5*y^4+3*x^5+5*x^4*y^8-5*x^4*y^6+x^4*y^5+8*x^4*y^4+5*x^4*y^3+5*x^4*y^2-6*x^3*y^6+3*x^3*y^4-4*x^3*y^3+7*x^3+x^2*y^9+3*x^2*y^6-6*x^2*y^4+7*x^2*y-7*x*y^9-7*x*y^7+8*x*y^2-2*x*y+3*y^5-9*y^3),
  ]
end

# The curves of Hecke's HeuristicEndomorphisms test, with the expected answer.
function _he_curves()
  R, t = polynomial_ring(QQ, :t)
  out = []

  F, r = number_field(t^2 - 5)
  L, _ = number_field(t^4 + 3*t^2 + 1)
  S, (x, y) = polynomial_ring(F, [:x, :y])
  push!(out, (name = "HE1", F = F, v = infinite_places(F)[2], f = x^5 + r*x^3 + x - y^2,
              L = L, nendo = 8))

  F, r = number_field(t^2 - t + 1)
  S, (x, y) = polynomial_ring(F, [:x, :y])
  f = (-22*r + 62)*x^6 + (156*r - 312)*x^5 + (-90*r + 126)*x^4 + (-1456*r + 1040)*x^3 +
      (-66*r + 186)*x^2 + (-156*r + 312)*x - 30*r + 42 - y^2
  push!(out, (name = "HE2", F = F, v = infinite_places(F)[1], f = f, L = F, nendo = 4))

  F, r = rationals_as_number_field()
  S, (x, y) = polynomial_ring(F, [:x, :y])
  f = 10*x^10 + 24*x^9 + 23*x^8 + 48*x^7 + 35*x^6 + 35*x^4 - 48*x^3 + 23*x^2 - 24*x + 10 - y^2
  push!(out, (name = "HE3", F = F, v = infinite_places(F)[1], f = f, L = F, nendo = 4))

  F, r = rationals_as_number_field()
  L, _ = number_field(t^6 - t^5 + 2*t^4 + 8*t^3 - t^2 - 5*t + 7)
  S, (x, y) = polynomial_ring(F, [:x, :y])
  f = x^4 - x^3*y + 2*x^3 + 2*x^2*y + 2*x^2 - 2*x*y^2 + 4*x*y - y^3 + 3*y^2 + 2*y + 1
  push!(out, (name = "HE4", F = F, v = infinite_places(F)[1], f = f, L = L, nendo = 6))
  return out
end

function _curves(tier::Int)
  # Vector{Any}: the curves live in different polynomial rings (QQ and number fields).
  cs = Any[(name = c.name, f = c.f, v = nothing) for c in _qq_curves_tier(tier)]
  tier == 1 && append!(cs, [(name = c.name, f = c.f, v = c.v) for c in _he_curves()])
  return cs
end

################################################################################
#  Measurements
################################################################################

_log2(x::ArbFieldElem) = iszero(x) ? -Inf : Float64(Nemo.midpoint(log(x) / log(parent(x)(2))))

# P: an AcbMatrix or any array of AcbFieldElem (e.g. a chain's integral matrix)
function _max_radius(P)
  RR = ArbField(precision(parent(first(P))))
  m = zero(RR)
  for z in P
    m = max(m, RR(radius(real(z))), RR(radius(imag(z))))
  end
  return m
end

function _max_abs(P::AcbMatrix)
  RR = ArbField(precision(base_ring(P)))
  m = zero(RR)
  for z in P
    m = max(m, abs(RR(Nemo.midpoint(real(z)))), abs(RR(Nemo.midpoint(imag(z)))))
  end
  return m
end

# max |mid(P) - mid(Q)| and whether all entries overlap, computed at the
# precision of Q (the reference).
function _compare(P::AcbMatrix, Q::AcbMatrix)
  CR = base_ring(Q)
  RR = ArbField(precision(CR))
  m = zero(RR)
  ok = true
  for i in 1:nrows(P), j in 1:ncols(P)
    p, q = CR(P[i, j]), Q[i, j]
    ok &= overlaps(p, q)
    m = max(m, abs(Nemo.midpoint(real(p)) - Nemo.midpoint(real(q))),
               abs(Nemo.midpoint(imag(p)) - Nemo.midpoint(imag(q))))
  end
  return m, ok
end

function _symmetry_defect(tau::AcbMatrix)
  RR = ArbField(precision(base_ring(tau)))
  m = zero(RR)
  for i in 1:nrows(tau), j in i+1:ncols(tau)
    d = tau[i, j] - tau[j, i]
    m = max(m, abs(Nemo.midpoint(real(d))), abs(Nemo.midpoint(imag(d))))
  end
  return m
end

# log2(diameter / minimal distance) of a set of points (0 for fewer than 2):
# how strongly the discriminant points are clustered, relative to their spread.
function _clustering(pts)
  z = [ComplexF64(Float64(real(p)), Float64(imag(p))) for p in pts if isfinite(p)]
  length(z) < 2 && return 0.0
  dmin, diam = Inf, 0.0
  for i in eachindex(z), j in i+1:length(z)
    d = abs(z[i] - z[j])
    dmin = min(dmin, d); diam = max(diam, d)
  end
  return log2(diam / dmin)
end

function _predictors(RS)
  C = computational_model(RS)
  if C isa Hecke.RiemannSurfaces.SuperellipticModel
    # sheets = m, ndisc = n (branch points), logM in bits, nodes over all edges
    pm = maximum(_log2(abs(z)) for v in C.elementary_integrals for z in v)
    return (sheets = C.m, ndisc = C.n, logM = maximum(E.log2_bound for E in C.tree),
            nodes = sum(E.method === :de ? 2*E.N + 1 : E.N for E in C.tree),
            comp_prec = C.computational_precision, pathmax = pm,
            target = C.target_precision, nsub = length(C.tree), retries = C.precision_retries,
            clus = _clustering(C.branch_points), inf = 0)
  end
  nodes = 0
  for fld in (:integration_schemes_GL, :integration_schemes_DE)
    isdefined(C, fld) || continue
    # nodes per scheme (not per path; the paths share schemes)
    nodes += sum(length(s.abscissae) for s in getfield(C, fld); init = 0)
  end
  logM = isempty(C.bounds) ? NaN : _log2(maximum(C.bounds))
  ndisc = isdefined(C, :discriminant_points) ? length(C.discriminant_points) : -1
  # log2 of the largest integral along a path (cancellation: pathmax - scale)
  pm = -Inf
  for ch in C.closed_chains, p in ch.paths
    isdefined(p, :integral_matrix) && (pm = max(pm, _log2(_max_abs(p.integral_matrix))))
  end
  clus = _clustering(C.discriminant_points)
  nsub = sum(length(Hecke.RiemannSurfaces.subpaths(p))
             for p in Hecke.RiemannSurfaces.fundamental_group_of_punctured_P1(C)[1]; init = 0)
  return (sheets = C.degree[1], ndisc = ndisc, logM = logM, nodes = nodes,
          comp_prec = C.computational_precision, pathmax = pm,
          target = C.target_precision, nsub = nsub, retries = C.precision_retries, clus = clus,
          inf = C.infinity_check)
end

function _surface(c, prec; model, kw...)
  c.v === nothing && return riemann_surface(c.f, prec; model = model, kw...)
  return riemann_surface(c.f, c.v, prec; model = model, kw...)
end

"""
    measure_precision(c, precs; ref_prec, model, kw...) -> Vector{NamedTuple}

Compute the big period matrix of the curve `c` at every precision in `precs`
and at `ref_prec`, and compare. Nothing is asserted.
"""
function measure_precision(c, precs::Vector{Int}; ref_prec::Int = maximum(precs) + 128,
                           model = :auto, kw...)
  @info "$(c.name): reference run at $ref_prec bits"
  t_ref = @elapsed begin
    R = _surface(c, ref_prec; model = model, kw...)
    Pref = big_period_matrix(R)
  end
  tauref = small_period_matrix(R)
  scale = _log2(_max_abs(Pref))
  ref_claimed = -_log2(_max_radius(Pref))
  @info "$(c.name): reference claims $(_r(ref_claimed)) bits ($(round(t_ref, digits = 1))s)"
  # The true error can only be measured up to the accuracy of the reference.
  ref_claimed < maximum(precs) + 16 &&
    @warn "$(c.name): the reference is not more accurate than the runs; `true` is capped at about $(_r(ref_claimed)) bits."
  rows = NamedTuple[]
  for p in precs
    local RS, P
    t = @elapsed begin
      RS = _surface(c, p; model = model, kw...)
      P = big_period_matrix(RS)
    end
    err, ok = _compare(P, Pref)
    claimed = -_log2(_max_radius(P))
    truebits = -_log2(err)
    tau = small_period_matrix(RS)
    sym = -_log2(_symmetry_defect(tau))
    tau_claimed = -_log2(_max_radius(tau))
    tau_true = -_log2(_compare(tau, tauref)[1])
    pr = _predictors(RS)
    row = (curve = c.name, genus = genus(RS), prec = p, claimed = claimed, true_bits = truebits,
           margin = truebits - claimed, contained = ok, loss = p - truebits, sym_bits = sym,
           tau_claimed = tau_claimed, tau_true = tau_true,
           scale = scale, time = t, ref_prec = ref_prec, ref_claimed = ref_claimed,
           ref_time = t_ref, pr..., canc = pr.pathmax - scale)
    push!(rows, row)
    _print_row(row)
    # A huge discrepancy (a few bits of agreement) usually means that the two
    # runs chose different homology bases, not a precision problem.
    truebits < 10 && @warn "$(c.name) at $p: only $(round(truebits, digits = 1)) bits agree with the reference; different homology basis?"
  end
  return rows
end

function _print_header()
  println(rpad("curve", 10), lpad("g", 4), lpad("prec", 6), lpad("claimed", 9), lpad("true", 8),
          lpad("margin", 8), lpad("cont", 6), lpad("loss", 7), lpad("sym", 8), lpad("tau_cl", 8), lpad("tau_tr", 8), lpad("logM", 7),
          lpad("nodes", 7), lpad("K", 6), lpad("T", 6), lpad("cprec", 7), lpad("retry", 6), lpad("clus", 6), lpad("inf", 4),
          lpad("canc", 7), lpad("time", 9))
end

_r(x) = isfinite(x) ? string(round(x, digits = 1)) : string(x)

function _print_row(r)
  println(rpad(r.curve, 10), lpad(r.genus, 4), lpad(r.prec, 6), lpad(_r(r.claimed), 9),
          lpad(_r(r.true_bits), 8), lpad(_r(r.margin), 8), lpad(r.contained ? "yes" : "NO", 6),
          lpad(_r(r.loss), 7), lpad(_r(r.sym_bits), 8), lpad(_r(r.tau_claimed), 8), lpad(_r(r.tau_true), 8), lpad(_r(r.logM), 7), lpad(r.nodes, 7),
          lpad(r.nsub, 6), lpad(r.target, 6), lpad(r.comp_prec, 7), lpad(r.retries, 6), lpad(_r(r.clus), 6), lpad(r.inf, 4),
          lpad(_r(r.canc), 7), lpad(string(round(r.time, digits = 2), "s"), 9))
end

function _write_csv(rows, path)
  isempty(rows) && return
  ks = keys(rows[1])
  new = !isfile(path)
  open(path, "a") do io
    new && println(io, join(ks, ","))
    for r in rows
      println(io, join((string(getfield(r, k)) for k in ks), ","))
    end
  end
end

"""
    run_precision_suite(; tier = 1, precs = [100, 200, 500, 1000], model = :auto,
                          csv = "precision_results.csv", only = nothing, kw...)

Run `measure_precision` on all curves of the tier (or only those whose name
is in `only`). Further keywords (e.g. `int_style = :gl`,
`adaptive = false`) are passed on to `riemann_surface`.
"""
function run_precision_suite(; tier::Int = 1, precs::Vector{Int} = [100, 200, 500, 1000],
                             model = :auto, csv = "precision_results.csv",
                             only = nothing, kw...)
  rows = NamedTuple[]
  _print_header()
  for c in _curves(tier)
    only === nothing || c.name in only || continue
    try
      append!(rows, measure_precision(c, precs; model = model, kw...))
    catch e
      @warn "$(c.name) failed" exception = (e, catch_backtrace())
    end
  end
  _write_csv(rows, csv)
  n_bad = count(r -> !r.contained || r.margin < 0, rows)
  println("\n$(length(rows)) measurements, $n_bad with too small balls (margin < 0 or not contained).")
  n_retry = count(r -> r.retries > 0, rows)
  n_short = count(r -> r.tau_claimed < r.prec, rows)
  n_short_P = count(r -> r.claimed < r.prec, rows)
  println("$n_retry with a precision retry, $n_short with tau and $n_short_P with the big period matrix claiming fewer bits than prec.")
  return rows
end

################################################################################
#  Endomorphisms (sensitive to incorrect radii)
################################################################################

"""
    run_endomorphism_precision_suite(; precs = [150, 200, 300, 500], kw...)

For the curves of the HeuristicEndomorphisms test, record at every precision
whether `geometric_homomorphism_representation_nf` gives the expected field
and number of generators, how long it took, and the claimed accuracy.
"""
function run_endomorphism_precision_suite(; precs::Vector{Int} = [150, 200, 300, 500],
                                          model = :auto, kw...)
  results = NamedTuple[]
  for c in _he_curves(), p in precs
    status = "ok"
    claimed = NaN
    t = @elapsed try
      RS = riemann_surface(c.f, c.v, p; model = model, kw...)
      P = big_period_matrix(RS)
      claimed = -_log2(_max_radius(P))
      A, h = Hecke.RiemannSurfaces.geometric_homomorphism_representation_nf(P, P, c.F, c.v)
      field_ok = is_isomorphic(codomain(h), c.L)
      len_ok = length(A) == c.nendo
      status = field_ok && len_ok ? "ok" :
               "WRONG (field $(field_ok ? "ok" : "wrong"), $(length(A)) generators, expected $(c.nendo))"
    catch e
      status = "ERROR: " * first(sprint(showerror, e), 120)
    end
    r = (curve = c.name, prec = p, claimed = claimed, time = t, status = status)
    push!(results, r)
    println(rpad(c.name, 6), lpad(p, 6), lpad(_r(claimed), 9), lpad(string(round(t, digits = 2), "s"), 10), "  ", status)
  end
  return results
end

"""
    run_swap_homomorphism_suite(; tiers = [1, 5], prec = 200, gmax = 6, kw...)

Stress test of the homomorphism code: for every curve of the tiers with
genus <= gmax, compute the period matrices of the models f(x, y) and
f(y, x) (the same curve), and Hom between the two Jacobians. Expected: at
least one generator, and one of them (for End = ZZ: the only one) is an
isomorphism, i.e. its homology representation has determinant +-1. Reports
the times of the two period matrices and of the homomorphism computation.
"""
function run_swap_homomorphism_suite(; tiers = [1, 5], prec::Int = 200, gmax::Int = 6,
                                     only = nothing, kw...)
  R = Hecke.RiemannSurfaces
  println(rpad("curve", 10), lpad("g", 4), lpad("t_P", 9), lpad("t_Q", 9), lpad("t_hom", 9),
          lpad("#gens", 7), "  status")
  results = NamedTuple[]
  for c in reduce(vcat, [_curves(t) for t in tiers])
    only === nothing || c.name in only || continue
    status = "ok"; g = -1; tP = tQ = th = NaN; ngens = -1
    try
      RS1 = _surface(c, prec; model = :original, superelliptic = false, kw...)
      g = genus(RS1)
      if g > gmax || g < 1
        continue
      end
      RS2 = _surface(c, prec; model = :swapped, superelliptic = false, kw...)
      tP = @elapsed P = big_period_matrix(RS1)
      tQ = @elapsed Q = big_period_matrix(RS2)
      th = @elapsed gens = R.geometric_homomorphism_representation(P, Q)
      ngens = length(gens)
      iso = any(abs(det(gen[2])) == 1 for gen in gens)
      status = ngens == 0 ? "NO HOMOMORPHISMS" : (iso ? "ok" : "no isomorphism among the generators")
    catch e
      e isa InterruptException && rethrow()
      status = "ERROR: " * first(sprint(showerror, e), 120)
    end
    push!(results, (curve = c.name, genus = g, t_P = tP, t_Q = tQ, t_hom = th, ngens = ngens, status = status))
    println(rpad(c.name, 10), lpad(g, 4), lpad(_r(tP), 9), lpad(_r(tQ), 9), lpad(_r(th), 9),
            lpad(ngens, 7), "  ", status)
  end
  return results
end

"""
    run_transform_homomorphism_suite(; tiers = [1, 5], prec = 200, gmax = 6, seed = 1,
                                     ops = 6, kinds = (:rational, :analytic, :both), kw...)

Test of the homomorphism code with a known answer: for every curve of the
tiers with genus <= gmax take its big period matrix P and build
Q = A * P * R^-1 with R a random unimodular 2g x 2g integer matrix (`ops`
random elementary row operations with multipliers in -2:2) and A a random
invertible complex g x g matrix (`kind` = :rational: A = 1, :analytic: R = 1,
:both). Then A * P = Q * R, and Hom(P, Q) is computed. Checked: R lies in the
ZZ-span of the homology representations found, and the tangent
representation of R overlaps A.
"""
function run_transform_homomorphism_suite(; tiers = [1, 5], prec::Int = 200, gmax::Int = 6,
                                          seed::Int = 1, ops::Int = 6,
                                          kinds = (:rational, :analytic, :both),
                                          only = nothing, kw...)
  R_ = Hecke.RiemannSurfaces
  println(rpad("curve", 10), lpad("g", 4), rpad("  kind", 11), lpad("t_hom", 9), lpad("#gens", 7), "  status")
  results = NamedTuple[]
  for c in reduce(vcat, [_curves(t) for t in tiers])
    only === nothing || c.name in only || continue
    local P, g
    try
      RS = _surface(c, prec; model = :auto, kw...)
      g = genus(RS)
      (g > gmax || g < 1) && continue
      P = big_period_matrix(RS)
    catch e
      e isa InterruptException && rethrow()
      println(rpad(c.name, 10), "  period matrix failed: ", first(sprint(showerror, e), 100))
      continue
    end
    CC = base_ring(P)
    rng = Random.MersenneTwister(seed)
    for kind in kinds
      status = "ok"; th = NaN; ngens = -1
      try
        R = identity_matrix(ZZ, 2*g)
        if kind !== :analytic
          for _ in 1:ops
            i, j = rand(rng, 1:2*g), rand(rng, 1:2*g)
            i == j && continue
            a = rand(rng, [-2, -1, 1, 2])
            for k in 1:2*g
              R[i, k] += a * R[j, k]
            end
          end
        end
        A = identity_matrix(CC, g)
        if kind !== :rational
          while true
            A = matrix(CC, g, g, [CC(rand(rng, -3:3) + rand(rng), rand(rng, -3:3) + rand(rng)) for _ in 1:g^2])
            contains(det(A), zero(CC)) || break
          end
        end
        Q = A * P * change_base_ring(CC, inv(R))
        th = @elapsed gens = R_.geometric_homomorphism_representation(P, Q)
        ngens = length(gens)
        if ngens == 0
          status = "NO HOMOMORPHISMS"
        else
          # R in the ZZ-span of the generators
          B = reduce(vcat, [matrix(ZZ, 1, 4*g^2, vec(permutedims(Matrix(gen[2])))) for gen in gens])
          r = matrix(ZZ, 1, 4*g^2, vec(permutedims(Matrix(R))))
          in_span, _ = can_solve_with_solution(B, r; side = :left)
          At, _ = R_.tangent_representation(R, P, Q)
          A_ok = all(overlaps(At[i, j], A[i, j]) for i in 1:g, j in 1:g)
          status = in_span && A_ok ? "ok" :
                   "WRONG (R in span: $in_span, tangent representation matches A: $A_ok)"
        end
      catch e
        e isa InterruptException && rethrow()
        status = "ERROR: " * first(sprint(showerror, e), 120)
      end
      push!(results, (curve = c.name, genus = g, kind = kind, t_hom = th, ngens = ngens, status = status))
      println(rpad(c.name, 10), lpad(g, 4), "  ", rpad(string(kind), 9), lpad(_r(th), 9), lpad(ngens, 7), "  ", status)
    end
  end
  return results
end

################################################################################
#  Diagnostics: where does the radius of a period matrix come from?
################################################################################

# -log2 of the largest radius among the entries (real and imaginary parts)
_bits_of(v) = isempty(v) ? Inf : minimum(-_log2(ArbField(precision(parent(z)))(
                              z isa AcbFieldElem ? max(radius(real(z)), radius(imag(z))) : radius(z)))
                              for z in v)

"""
    diagnose_precision(RS)

Print the accuracy (in bits, from the radii) of every ingredient of the
period matrix of `RS`: the embedded defining polynomial and differentials,
the discriminant points, the quadrature nodes and weights, and the
integrals along the closed chains.
"""
function diagnose_precision(RS)
  C = computational_model(RS)
  P = big_period_matrix(RS)
  p = C.computational_precision
  println("computational precision      ", p)
  println("big period matrix            ", _r(_bits_of(collect(P))))
  f = Hecke.RiemannSurfaces._embed_mpoly(Hecke.RiemannSurfaces.defining_polynomial(C),
                                        Hecke.RiemannSurfaces.embedding(C), p)
  println("embedded f (coefficients)    ", _r(_bits_of(collect(coefficients(f)))))
  println("discriminant points          ", _r(_bits_of(C.discriminant_points)))
  for (nm, fld) in (("GL", :integration_schemes_GL), ("DE", :integration_schemes_DE))
    isdefined(C, fld) || continue
    for (i, s) in enumerate(getfield(C, fld))
      println("$nm scheme $i (N = $(length(s.abscissae)), prec $(s.prec))  nodes ",
              _r(_bits_of(s.abscissae)), "  weights ", _r(_bits_of(s.weights)))
    end
  end
  chains = vcat(C.closed_chains, [C.inf_chain])
  cb = [_bits_of(collect(ch.integral_matrix)) for ch in chains]
  println("closed chains                min ", _r(minimum(cb)), " (chain $(argmin(cb))), max ", _r(maximum(cb)))
  return nothing
end

"""
    diagnose_chain(RS, k = :worst; n = 8)

For closed chain `k` (index as in `diagnose_precision`, the last one is the
chain around infinity; `:worst` picks the chain with the largest radius),
print the `n` paths with the largest radius: accuracy in bits, size of the
integral, precision of its matrix, path type, whether the path is a
reversed copy, and its end points.
"""
function diagnose_chain(RS, k = :worst; n::Int = 8, subpaths::Bool = false)
  C = computational_model(RS)
  big_period_matrix(RS)
  chains = vcat(C.closed_chains, [C.inf_chain])
  if k === :worst
    k = argmin([_bits_of(collect(ch.integral_matrix)) for ch in chains])
  end
  ch = chains[k]
  M = ch.integral_matrix
  println("chain $k of $(length(chains)): $(length(ch.paths)) paths, ",
          "$(length(unique(objectid, ch.paths))) distinct objects")
  println("  chain integral: bits ", _r(_bits_of(collect(M))), ", log2 max|entry| ", _r(_log2(_max_abs(M))))
  RR = ArbField(64)
  rsum = sum(RR(_max_radius(p.integral_matrix)) for p in ch.paths)
  println("  sum of the path radii: bits ", _r(-_log2(rsum)))
  b = [_bits_of(collect(p.integral_matrix)) for p in ch.paths]
  forward = Set(objectid(p) for c in C.pi1_chains for p in c.paths)
  C64 = AcbField(32)
  for i in sortperm(b)[1:min(n, length(b))]
    p = ch.paths[i]
    println("  path $i: bits ", _r(b[i]),
            ", log2 max|entry| ", _r(_log2(_max_abs(p.integral_matrix))),
            ", matrix prec ", precision(base_ring(p.integral_matrix)),
            ", type ", Hecke.RiemannSurfaces.path_type(p),
            objectid(p) in forward ? "" : ", only in the infinity chain",
            ", ", C64(p.start_point_high), " -> ", C64(p.end_point_high))
    if subpaths && !isdefined(p, :subpaths)
      println("      (no subpaths: reverse of a forward path, see diagnose_path)")
    elseif subpaths
      for (j, sp) in enumerate(Hecke.RiemannSurfaces.subpaths(p))
        bd = isdefined(sp, :bounds) && !isempty(sp.bounds) ? _r(_log2(maximum(sp.bounds))) : "-"
        println("      sub $j: type ", Hecke.RiemannSurfaces.path_type(sp),
                ", ", isdefined(sp, :integration_scheme) ? sp.integration_scheme : "-",
                ", r ", isdefined(sp, :quadrature_parameter) ? _r(Float64(sp.quadrature_parameter)) : "-",
                ", log2 bound ", bd,
                ", ", C64(Hecke.RiemannSurfaces.start_point(sp)), " -> ",
                C64(Hecke.RiemannSurfaces.end_point(sp)))
      end
    end
  end
  return nothing
end

"""
    diagnose_path(RS, i = :worst)

Re-integrate one path of the fundamental group (default: the one with the
widest integral matrix) subpath by subpath, (1) as in the period matrix
computation, (2) without the adaptive step control, and (3) node by node
with fresh fibers (no continuation), and report the accuracy of the
abscissae x, the roots y, the integrand values and the sums. Tells whether
the radius comes from the continuation or from the evaluation itself.
"""
function diagnose_path(RS, i = :worst)
  R = Hecke.RiemannSurfaces
  C = computational_model(RS)
  big_period_matrix(RS)
  paths = R.fundamental_group_of_punctured_P1(C)[1]
  if i === :worst
    i = argmin([_bits_of(collect(p.integral_matrix)) for p in paths])
  end
  p = paths[i]
  W = C.computational_precision
  println("path $i of $(length(paths)): bits ", _r(_bits_of(collect(p.integral_matrix))),
          ", log2 max|entry| ", _r(_log2(_max_abs(p.integral_matrix))), ", W = $W")
  v = R.embedding(C)
  f = R._embed_mpoly(R.defining_polynomial(C), v, W)
  Ky, _ = polynomial_ring(base_ring(f), "y")
  difs, fm, mp, rp = R.differential_form_data(C)
  emb = [R._embed_mpoly(d, v, W) for d in difs]
  Cp = AcbField(W)
  ws = R.ContinuationWorkspace(R._split_in_y(f), Ky)
  cache = R.DifferentialFactorCache(emb, fm, mp, rp)
  m = degree(f, 2); g = ncols(p.integral_matrix)   # emb are the factors, not the differentials
  vals = [Cp() for _ in 1:m, _ in 1:g]
  C32 = AcbField(32)
  mp_prec = C.resolved_parameters.midpoint_precision
  lo_prec = mp_prec > 0 ? max(100, min(mp_prec, W)) : W
  lo = nothing
  if lo_prec < W
    f_lo = R._embed_mpoly(R.defining_polynomial(C), v, lo_prec)
    lo = R.ContinuationWorkspace(R._split_in_y(f_lo), polynomial_ring(base_ring(f_lo), "y")[1])
  end
  for (j, sp) in enumerate(R.subpaths(p))
    sc = sp.integration_scheme === :gl ? C.integration_schemes_GL[sp.integration_scheme_index] :
                                         C.integration_schemes_DE[sp.integration_scheme_index]
    N = length(sc.abscissae)
    println("  sub $j: type ", R.path_type(sp), ", ", sp.integration_scheme, " N = $N, ",
            C32(R.start_point(sp)), " -> ", C32(R.end_point(sp)))
    if j == 1 && length(R.subpaths(p)) == 1
      # stored vs recomputed, per differential (column): log2 of the ratio of
      # the largest entries (a constant ratio means the two use differently
      # scaled differentials)
      res = R._integrate_chunk(sp, sc, 1, N + 2, Cp, W, ws, cache, vals, nothing, true)
      Mst = p.integral_matrix
      lr = [_log2(maximum(abs(Mst[a, k]) for a in 1:m)) - _log2(maximum(abs(res.integrals[a, k]) for a in 1:m))
            for k in 1:g]
      println("    log2(stored/recomputed) per differential: ", join(_r.(lr), " "))
      println("    computational_model(RS) === RS: ", C === RS, ", stored matrix prec ",
              precision(base_ring(Mst)), ", size ", size(Mst))
    end
    runs = Any[("adaptive", true, nothing), ("bisection", false, nothing)]
    lo === nothing || push!(runs, ("adaptive, midpoint prec $lo_prec", true, lo))
    for (name, ad, l) in runs
      t = @elapsed res = R._integrate_chunk(sp, sc, 1, N + 2, Cp, W, ws, cache, vals, l, ad)
      println("    continuation ($name): sum bits ", _r(_bits_of(vec(res.integrals))),
              ", log2 max ", _r(_log2(maximum(abs(z) for z in res.integrals))),
              ", end fiber bits ", _r(_bits_of(res.fiber_end)), "  (", round(t, digits = 2), "s)")
    end
    # node by node, fresh fibers
    xb = Inf; yb = Inf; yrel = Inf; vb = Inf; vmax = -Inf; worst = 0
    acc = [Cp() for _ in 1:m, _ in 1:g]
    for l in 1:N
      x = R.evaluate(sp, sc.abscissae[l])
      wi = R.is_line(sp) ? Cp(sc.weights[l]) : sc.weights[l] * R.evaluate_derivative(sp, sc.abscissae[l])
      z = R._fresh_fiber!(ws, x, W)
      R._evaluate_differentials!(vals, cache, x, z, wi)
      for a in eachindex(acc); add!(acc[a], acc[a], vals[a]); end
      xb = min(xb, _bits_of([x]))
      yb = min(yb, _bits_of(z))
      yrel = min(yrel, minimum(_bits_of([y]) + _log2(abs(y)) for y in z))
      b = _bits_of(vec(vals))
      if b < vb
        vb = b; worst = l
      end
      vmax = max(vmax, _log2(maximum(abs(u) for u in vals)))
    end
    println("    fresh fibers: x bits ", _r(xb), ", y bits (abs) ", _r(yb), ", y bits (rel) ", _r(yrel),
            ", weighted integrand bits ", _r(vb), " (node $worst), log2 max ", _r(vmax),
            ", sum bits ", _r(_bits_of(vec(acc))))
    x = R.evaluate(sp, sc.abscissae[worst])
    z = R._fresh_fiber!(ws, x, W)
    println("    at node $worst: x = ", C32(x), ", y = ", [C32(y) for y in z])
  end
  return nothing
end

################################################################################
#  A single run without a reference (for curves where a reference is too
#  expensive, e.g. genus 54): timings of the stages, claimed accuracy,
#  symmetry of tau, predictors.
################################################################################

"""
    probe_precision(name_or_curve, prec = 100; kw...)

Build the Riemann surface of the curve (a name from the tiers, or a
polynomial), and report the time of the model choice, the genus (basis of
differentials), the period matrix and tau, together with the claimed bits of
P and tau, the bits to which tau is symmetric (a lower bound for its true
accuracy up to conditioning) and the predictors. Keywords are passed to
`riemann_surface`.
"""
function probe_precision(c, prec::Int = 100; kw...)
  if c isa AbstractString
    cs = vcat(_curves(1), _curves(2), _curves(3), _curves(4), _curves(5))
    c = only(filter(d -> d.name == c, cs))
  elseif !(c isa NamedTuple)
    c = (name = "curve", f = c, v = nothing)
  end
  local RS, C, P, tau
  t_model = @elapsed begin
    RS = _surface(c, prec; model = :auto, kw...)
    C = computational_model(RS)
  end
  println("model choice   ", round(t_model, digits = 2), "s  (", typeof(C), ")")
  t_genus = @elapsed g = genus(RS)
  println("genus $g       ", round(t_genus, digits = 2), "s")
  t_P = @elapsed P = big_period_matrix(RS)
  println("period matrix  ", round(t_P, digits = 2), "s")
  t_tau = @elapsed tau = small_period_matrix(RS)
  println("tau            ", round(t_tau, digits = 2), "s")
  pr = _predictors(RS)
  r = (curve = c.name, genus = g, prec = prec,
       claimed = -_log2(_max_radius(P)), scale = _log2(_max_abs(P)),
       tau_claimed = -_log2(_max_radius(tau)), sym_bits = -_log2(_symmetry_defect(tau)),
       t_model = t_model, t_genus = t_genus, t_periods = t_P, t_tau = t_tau, pr...)
  for k in keys(r)
    println(rpad(string(k), 14), r[k] isa Float64 ? _r(r[k]) : r[k])
  end
  return r
end
