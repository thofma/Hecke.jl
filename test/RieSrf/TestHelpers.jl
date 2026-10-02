################################################################################
#
#  Helpers for the RieSrf tests (included first by test/RieSrf.jl).
#
#  Most checks do not depend on the choice of basis of differentials or of
#  homology:
#    * Riemann-Hurwitz: the genus from the monodromy equals the genus of the
#      function field.
#    * Riemann bilinear relations: tau symmetric, Im(tau) positive definite.
#    * The Abel-Jacobi map of a principal divisor vanishes modulo the lattice.
#  Comparisons between runs with the same bases (same curve, model and
#  precision) compare the monodromy and the period matrices directly.
#
################################################################################

RSM = Hecke.RiemannSurfaces

# Hecke's switch for the long tests (runtests.jl sets Main.long_test).
riesrf_long_tests() = isdefined(Main, :long_test) && Main.long_test

#
################################################################################

# The general algorithm unless a test asks for the superelliptic one: most
# tests check the general code (monodromy, Tretkoff homology, ...), and many
# of their curves are superelliptic, which would switch algorithm by default.
function _rs(f, prec::Int = 100; kw...)
  return RSM.riemann_surface(f, prec; integration_method = :heuristic,
                             (; superelliptic = false, kw...)...)
end

# riemann_surface is lazy: this does the actual (numerical) work, with timing.
function _computed(RS; time::Bool = false)
  time ? (@time RSM.big_period_matrix(RS)) : RSM.big_period_matrix(RS)
  return RS
end

function _overlap(A::AcbMatrix, B::AcbMatrix)
  size(A) == size(B) || return false
  return all(overlaps(A[i, j], B[i, j]) for i in 1:nrows(A), j in 1:ncols(A))
end

function _is_symmetric(T::AcbMatrix)
  n = nrows(T)
  z = zero(base_ring(T))
  return all(contains(T[i, j] - T[j, i], z) for i in 1:n for j in i+1:n)
end

# Sylvester's criterion; every leading minor must be certainly positive.
function _is_positive_definite(M::ArbMatrix)
  n = nrows(M)
  return all(k -> det(M[1:k, 1:k]) > 0, 1:n)
end

# Genus from the monodromy via Riemann–Hurwitz:
#   2g - 2 = -2m + sum over branch points (incl. infinity) of sum_cycles (len - 1)
# (On the computational model: there the monodromy is a by-product of the
# periods. The monodromy of the curve as given is tested in "Plane models".)
function _riemann_hurwitz_genus(RS)
  C = RSM.computational_model(RS)
  m = C.degree[1]
  mon = RSM.monodromy_representation(C)       # includes the loop around infinity
  ram = sum((m - length(collect(cycles(p))) for p in mon); init = 0)
  twog = -2m + ram + 2
  @assert iseven(twog) "Riemann–Hurwitz sum has the wrong parity"
  return div(twog, 2)
end

# Basis-independent checks, returned as a NamedTuple so failures are readable.
function sanity_report(RS)
  g = RSM.genus(RS)
  rh = _riemann_hurwitz_genus(RS)
  if g == 0
    return (genus = g, rh_genus = rh, symmetric = true, posdef = true)
  end
  tau = RSM.small_period_matrix(RS)
  return (genus = g, rh_genus = rh,
          symmetric = _is_symmetric(tau),
          posdef = _is_positive_definite(imag(tau)))
end

function test_sanity(RS; expected_genus = nothing)
  r = sanity_report(RS)
  expected_genus === nothing || @test r.genus == expected_genus
  @test r.rh_genus == r.genus
  @test r.symmetric
  @test r.posdef
  return r
end

# Same bases (same precision, same curve): compare monodromy and tau.
function test_same_result(RS1, RS2)
  C1, C2 = RSM.computational_model(RS1), RSM.computational_model(RS2)
  @test string(C1.defining_polynomial) == string(C2.defining_polynomial)   # same model
  @test RSM.monodromy_representation(C1) == RSM.monodromy_representation(C2)
  @test _overlap(RSM.big_period_matrix(RS1), RSM.big_period_matrix(RS2))
end

# Message of the underlying error (unwraps TaskFailedException / CompositeException).
function _root_message(e)
  while true
    if e isa TaskFailedException
      e = e.task.exception
    elseif e isa CompositeException
      e = first(e.exceptions)
    else
      break
    end
  end
  return sprint(showerror, e)
end

_is_clean_refusal(msg::String) =
  any(occursin(t, msg) for t in ("isolate", "precision", "Increase the precision"))

# random points for the Abel-Jacobi tests (reproducible)
riesrf_rng = MersenneTwister(20260924)
_rand_cc(CC) = CC(QQ(rand(riesrf_rng, -10^3:10^3), rand(riesrf_rng, 1:10^3))) +
               onei(CC) * CC(QQ(rand(riesrf_rng, -10^3:10^3), rand(riesrf_rng, 1:10^3)))

# Points of RS lying over x = x0 (generic x0: m finite points).
function _points_over_x(RS, x0)
  f = RSM.complex_defining_polynomial(RS)
  return [RS([x0, y]) for y in RSM.fiber(f, x0)]
end

# Points of RS with y = y0 (generic y0: deg_x(f) finite points).
function _points_over_y(RS, y0)
  f = RSM.complex_defining_polynomial(RS)
  CC = base_ring(f)
  Cz, z = polynomial_ring(CC, "z")
  xs = roots(f(z, Cz(y0)), initial_prec = precision(CC))
  return [RS([x, y0]) for x in xs]
end

function _is_small(v::AcbFieldElem, tol)
  return contains(v, zero(parent(v))) || abs(v) < tol
end

# Neurohr's AJM tests: AJ of a principal divisor vanishes modulo the lattice.
function test_abel_jacobi_principal(RS; ntests::Int = 2)
  CC = RSM.complex_field(RS)
  tol = ArbField(precision(CC))(2)^(-div(precision(RS), 2))
  for _ in 1:ntests
    # div((x - x1)/(x - x2))
    P1 = _points_over_x(RS, _rand_cc(CC))
    P2 = _points_over_x(RS, _rand_cc(CC))
    D = RSM.divisor(vcat(P1, P2), vcat(fill(1, length(P1)), fill(-1, length(P2))))
    V = RSM.abel_jacobi_map(D, :swap, :complex)
    @test all(_is_small(v, tol) for v in V)

    # div((y - y1)/(y - y2))
    Q1 = _points_over_y(RS, _rand_cc(CC))
    Q2 = _points_over_y(RS, _rand_cc(CC))
    @test length(Q1) == length(Q2)
    E = RSM.divisor(vcat(Q1, Q2), vcat(fill(1, length(Q1)), fill(-1, length(Q2))))
    W = RSM.abel_jacobi_map(E, :swap, :complex)
    @test all(_is_small(w, tol) for w in W)
  end
end

# Different models have different bases of differentials and of homology. The
# small period matrices tau1, tau2 describe the same Jacobian iff there is
# R = [a b; c d] in GL_2g(Z) with (a + tau1 c) tau2 = b + tau1 d. This is a
# linear condition on the 4g^2 integer unknowns: find integer kernel vectors
# of the scaled real equations with LLL, and check for one with det R = +-1
# (small combinations of kernel vectors too, for curves with extra
# endomorphisms).
function _round_zz(x::ArbFieldElem)
  ok, z = Hecke.Nemo.unique_integer(floor(Hecke.Nemo.midpoint(x) + parent(x)(1//2)))
  @assert ok
  return z
end

function _period_matrices_isomorphic(tau1::AcbMatrix, tau2::AcbMatrix; bits::Int = 120)
  g = nrows(tau1)
  g == nrows(tau2) || return false
  CC = base_ring(tau1)
  n = 4*g^2
  unit(i, j) = (E = zero_matrix(CC, g, g); E[i, j] = one(CC); E)
  maps = [(i, j) -> unit(i, j)*tau2, (i, j) -> -unit(i, j),
          (i, j) -> tau1*unit(i, j)*tau2, (i, j) -> -tau1*unit(i, j)]   # a, b, c, d
  B = zero_matrix(ZZ, n, n + 2*g^2)
  S = ArbField(precision(CC))(2)^bits
  k = 0
  for F in maps, i in 1:g, j in 1:g
    k += 1
    B[k, k] = 1
    E = F(i, j)
    t = n
    for r in 1:g, s in 1:g
      B[k, t + 1] = _round_zz(S*real(E[r, s]))
      B[k, t + 2] = _round_zz(S*imag(E[r, s]))
      t += 2
    end
  end
  L = lll(B)
  small = ZZ(2)^div(bits, 4)
  kernel = [[L[k, t] for t in 1:n] for k in 1:n if all(abs(L[k, t]) < small for t in 1:ncols(L))]
  isempty(kernel) && return false
  function unimodular(v)
    R = zero_matrix(ZZ, 2*g, 2*g)
    for (o, (r0, c0)) in zip((0, g^2, 2*g^2, 3*g^2), ((0, 0), (0, g), (g, 0), (g, g)))
      for i in 1:g, j in 1:g
        R[r0 + i, c0 + j] = v[o + (i - 1)*g + j]
      end
    end
    return abs(det(R)) == 1
  end
  r = min(length(kernel), 4)
  for coeffs in Iterators.product(fill(-1:1, r)...)
    all(iszero, coeffs) && continue
    v = sum(coeffs[i] .* kernel[i] for i in 1:r)
    unimodular(v) && return true
  end
  return false
end

# J(P) and J(Q) (big period matrices, g x 2g, symplectic bases) are isomorphic
# as principally polarized abelian varieties iff Hom(J(P), J(Q)) contains an
# R with R^T J R = J (J the standard symplectic form; such an R is invertible
# over ZZ). The heuristic endomorphism code gives a ZZ-basis R_1, ..., R_r of
# the homology representations (A*P = Q*R); search small combinations of it.
# (With both Im(tau) positive definite a holomorphic isomorphism gives +J; -J
# is accepted as well so that an orientation convention cannot hide a match.)
function _jacobians_isomorphic(P::AcbMatrix, Q::AcbMatrix; maxcoeff::Int = 2, maxtries::Int = 2*10^5)
  nrows(P) == nrows(Q) || return false
  gens = RSM.geometric_homomorphism_representation(P, Q)
  isempty(gens) && return false
  Rs = [R for (A, R) in gens]
  r = length(Rs)
  g = nrows(P)
  J = zero_matrix(ZZ, 2*g, 2*g)
  for i in 1:g
    J[i, g + i] = 1
    J[g + i, i] = -1
  end
  for c in 1:maxcoeff
    (2*c + 1)^r > maxtries && break
    for coeffs in Iterators.product(fill(-c:c, r)...)
      maximum(abs, coeffs) == c || continue          # the smaller ones were tried already
      R = sum(coeffs[i] * Rs[i] for i in 1:r)
      t = transpose(R) * J * R
      (t == J || t == -J) && return true
    end
  end
  return false
end

# div(x - x0) for x0 = x(P), P a place of the curve as given: the places over
# x0 with their ramification indices, minus the places at infinity with theirs.
# (For curves monic in y, so that no place over x0 lies at y = infinity.)
# Involves the critical points over x0 and the points at infinity.
function _divisor_of_x_minus(RS, P)
  O = RSM.original_model(RS)
  chain = only(c for c in O.closed_chains if any(Q -> Q === P, c.points))
  pts = RSM.RiemannSurfacePoint[]
  mults = Int[]
  for Q in chain.points
    push!(pts, Q); push!(mults, Q.ramification_index)
  end
  for R in RSM.infinite_points(RS)
    push!(pts, R); push!(mults, -R.ramification_index)
  end
  return RSM.divisor(pts, mults)
end

################################################################################
#

#  Test curves (from Neurohr's list; genus as given there)
#
################################################################################

Qxy, (x, y) = polynomial_ring(QQ, [:x, :y])

FAST_CURVES = [
  # name       polynomial                                              genus
  ("e1",   y^2 - 4*x*(x - 1)*(x + 1),                                      1),
  ("e5",   -x^3 - x^2 + 3*x + y^2 - 9,                                     1),
  ("f6",   2*x*y^2 - x^2 - 1,                                              1),
  ("f14",  y^3 - x^2 - 1,                                                  1),
  ("f2",   y^3 - x^7 + 2*x^3*y,                                            2),
  ("g2",   y^3 + x^4 + x^2,                                                2),
  ("cm1",  y^2 - (x^5 - 1),                                                2),
  ("g3",   y^3 - x^4 + 1,                                                  3),
  ("g6",   y^4 + x^4 - 1,                                                  3),
  ("g15",  x^3*y + y^3 + x,                                                3),
  ("q1",   -4*x^4 - 5*x^3*y + x^3 + 2*x^2*y^2 - 5*x^2*y + 3*x^2 + 3*x*y^3
             + x*y - 5*x - 8*y^3 - 3,                                      3),
  ("f1",   y^3 - (x^3 + y)^2 + 1,                                          4),
  ("f18",  y^3 - x^5 + 2*(10*x - 1)^2,                                     4),
  ("f30",  2*y^3*x^5 + 5*y^3*x^4 - 3*y^3*x - 9*y^2*x^4 - 4*y^2*x^2
             + 3*y*x^3 + 1,                                                5),
]

LONG_CURVES = [
  ("f35",  -7*x^3*y^4 + 8*x^3*y^2 + 9*x^3*y + 8*x^2*y^3 + 9*x^2*y^2
             + 2*x*y^3 + 3,                                                5),
  ("f40",  17*x^3*y^4 + 10*x^3*y^2 - 7*x^3 + 20*x^2*y^4 + 10*x^2*y^3
             - 10*x*y^4 - 7*x*y - 15*x - 7*y^3 + 6*y,                      6),
  ("f39",  x^6 + x^3*y - x^2*y^3 - 3*x^2*y^2 - 2*x^2*y + 2*x*y^4
             + 3*x*y^3 + x*y^2 - y^5 - y^4,                                7),
  ("g9",   2*x^7*y + 2*x^7 + y^3 + 3*y^2 + 3*y,                            9),
  ("f16",  (y^3 - x)*((y - 1)^2 - x)*(y - 2 - x^2) + x^2*y^5,              9),
  ("f7",   -2*x^6 + 7*x^5 - 7*x^4 + 5*x^3 + 4*x^2 + 6*x + y^5 - 3,        10),
  ("f10",  -9*x^5*y^4 + 9*x^5*y^3 - 8*x^5*y^2 - 2*x^5*y - 3*x^4*y^4
             + 3*x^4*y^2 + 8*x^3*y^2 + 2*x^3 + 8*x^2*y^4 - 5*x^2*y^3
             + x^2*y^2 + 2*x*y - 3*y^3,                                   11),
  ("f43",  x^6*y^6 + x^3 + y^2 + 1,                                       11),
]

# Curves on which Neurohr's Magma code fails (testfunctions.m, "Fail!"); for
# sf1 its period matrix depended on the precision.
NEUROHR_FAIL_CURVES = [
  ("sf1",  10*x^2*y^2 + 17*x^2 - 7*x*y^2 - 12*x + 26*y^2 + 10),
  ("sf2",  x^4 + x^3*y + 2*x^3 - 6*x^2*y^2 + 3*x^2*y - 6*x*y^3 + 3*x*y
             - 2*x + 4*y^4 + 5*y^3 - 3*y^2 - 3*y + 1),
  ("vh1",  17//26*x^5*y^2 - 3*x^5 + 10//13*x^4*y^2 + 41//17*x^4
             + 36//55*x^3*y^2 + 1//5*x^3*y + 23//2*x^3 + 14//41*x^2*y
             - 9//23*x*y + 17//22*y^2 - 1//5*y + 47//4),
]

VERY_LONG_CURVES = [
  ("g4",   ((y^3 + x^2)^2 + x^3*y^2)^2 + x^2*y^3,                         12),  # "Very hard!"
  ("f45",  15*x^5*y^5 + 44*x^4*y + 24*x^3*y^3 + 15*x*y^4 - 49,            14),
]

# Superelliptic families y^m = p_n(x) (Neurohr's SE_TestFamilies)
function superelliptic_family(m::Int, n::Int)
  Qt, t = polynomial_ring(QQ, :t)
  cyc  = t^n + 1
  expn = sum(t^k / factorial(ZZ(k)) for k in 0:n)
  cheb = sum(binomial(ZZ(n), ZZ(2k)) * (t^2 - 1)^k * t^(n - 2k) for k in 0:div(n, 2))
  lag  = sum(binomial(ZZ(n), ZZ(k)) * QQ(-1)^k / factorial(ZZ(k)) * t^k for k in 0:n)
  lift(p) = y^m - sum(coeff(p, k) * x^k for k in 0:degree(p))
  return [("cyclotomic($m,$n)", lift(cyc)), ("exp($m,$n)", lift(expn)),
          ("chebyshev($m,$n)", lift(cheb)), ("laguerre($m,$n)", lift(lag))]
end

# Stress tests: branch points at distance ~ eps. Degree 3 in y (Theorem 4.4.1
# assumes m >= 3).
stress_two_close(eps)   = y^3 - (x^2 - eps^2)*(x^3 - 1)              # branch points ±eps
stress_three_close(eps) = y^3 - ((x - 1)^3 - eps^3)*(x^2 + 2)        # 3 points on |x-1| = eps
stress_perturbed(eps)   = y^3 - x^2*(x^2 + 1)*(x - 2) + eps*(x*y + y + 1)  # perturbed singular curve

################################################################################
#
#  Tests

# (family, k) with eps = 10^-k that are beyond what the default precision
# max(200, 4k + 100) can handle: tested separately in "Precision limits".
# (Globals: Hecke's @long_test does not escape its body, so the body only
# sees global variables.)
LIMIT_CASES = [("three_close", 20), ("three_close", 30), ("three_close", 40),
               ("perturbed", 40)]
STRESS_FAMILIES = [("two_close", stress_two_close),
                   ("three_close", stress_three_close),
                   ("perturbed", stress_perturbed)]
