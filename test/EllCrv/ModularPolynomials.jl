@testset "Classical" begin
  Zxy, (x, y) = ZZ["x", "y"]
  p = @inferred classical_modular_polynomial(1)
  @test base_ring(p) == ZZ
  @test p(x, y) == x + y
  # test caching
  p = @inferred classical_modular_polynomial(1)
  @test base_ring(p) == ZZ
  @test p(x, y) == x + y

  p = @inferred classical_modular_polynomial(2)
  @test base_ring(p) == ZZ
  @test p(x, y) == x^3 - x^2*y^2 + 1488*x^2*y - 162000*x^2 + 1488*x*y^2 + 40773375*x*y + 8748000000*x + y^3 - 162000*y^2 + 8748000000*y - 157464000000000

  p = @inferred classical_modular_polynomial(25)
  @test constant_coefficient(p) == 14386245985272883324015703111660587192675726207106874718351335853206325654615424338254825121125498589319271599569067149492491688571248840175657900729489337202694836796781744548654922311933270371526939116126423746856625240926636499707485146768291922848003590590567564246007279019912714416725791203246166108581436154959822182988259800760898050588672000
  @test total_degree.(classical_modular_polynomial.(1:12)) == [1, 4, 6, 9, 10, 18, 14, 20, 20, 30, 22, 38]

  p = @inferred classical_modular_polynomial(Zxy, 1)
  @test parent(p) === Zxy

  Fxy, (x, y) = GF(2)["x", "y"]
  p = @inferred classical_modular_polynomial(Fxy, 1)
  @test parent(p) === Fxy

  F = GF(13)
  E = elliptic_curve_from_j_invariant(F(1))
  E = elliptic_curve(F, [1, 0, 0, 8, 6])
  Fx, x = F["x"]
  g = x^18 + 11*x^16 + 7*x^15 + 6*x^13 + x^12 + 9*x^11 + 12*x^10 + 8*x^9 + 3*x^8 + 4*x^7 + 4*x^6 + 5*x^5 + 7*x^4 + 3*x^3 + 8*x^2 + 6*x + 5
  i = isogeny_from_kernel(E, g)
  EE = codomain(i)
  @test degree(i) == 37
  classical_modular_polynomial(37)(j_invariant(E), j_invariant(EE))

  @test_throws ArgumentError classical_modular_polynomial(-1)
  @test_throws ArgumentError classical_modular_polynomial(0)
  @test_throws ArgumentError classical_modular_polynomial(60)
  @test_throws ArgumentError classical_modular_polynomial(121)
  @test_throws ArgumentError classical_modular_polynomial(typemax(Int))
  # prime levels with no order of the family in the word size fail at once
  for n in (6810301, 2^61 - 1)
    @test_throws ArgumentError classical_modular_polynomial(n)
  end
  for R in (polynomial_ring(ZZ, [:x])[1], ZZ["x", "y", "z"][1]), n in (3, 61)
    @test_throws ArgumentError classical_modular_polynomial(R, n)
  end
end

@testset "Classical, prime levels above 59" begin
  # The algorithm of Broker-Lauter-Sutherland for prime levels above 59:
  # against the database below 60, over Z and modulo m by the explicit CRT,
  # for the order the search finds and for orders of each kind of
  # presentation and of conductor; at level 61, the properties of Cox,
  # Theorem 11.18, and isogenies.
  for l in (3, 5, 7, 11, 13, 17)
    phi = classical_modular_polynomial(l)
    c = [coeff(phi, [a, b]) for a in 0:(l + 1) for b in 0:a]
    ord = Hecke._modular_polynomial_order(l)
    ps = Hecke._modular_polynomial_crt_primes(l, ord.D)
    @test Hecke._modular_polynomial_coefficients(l, ord, ps) == c
    for m in (2, 3, l, 6, 61 * 7, 1000003, next_prime(ZZ(2)^64), ZZ(2)^70)
      @test Hecke._modular_polynomial_coefficients_mod(l, ord, ps, ZZ(m)) ==
            mod.(c, m)
    end
    for R in (GF(1000003), GF(7, 2), residue_ring(ZZ, 6)[1],
              residue_ring(ZZ, 1)[1])
      S, _ = polynomial_ring(R, [:x, :y])
      @test Hecke._classical_modular_polynomial_crt(S, l) ==
            classical_modular_polynomial(S, l)
    end
  end

  # (l, D0, u, h, cl(O) split, cl(R) split): conductors 1, a prime ramified,
  # inert or split in K, and its square or cube (descents of depth 1 to 3)
  for (l, D0, u, h, sO, sR) in ((3, -95, 1, 8, false, true),
                                (3, -119, 1, 10, true, true),
                                (5, -39, 3, 12, false, true),
                                (7, -31, 3, 12, false, true),
                                (7, -31, 5, 12, false, true),
                                (3, -47, 7, 30, true, true),
                                (7, -31, 25, 60, false, true),
                                (11, -7, 49, 49, false, false),
                                (11, -7, 27, 36, false, true))
    phi = classical_modular_polynomial(l)
    c = [coeff(phi, [a, b]) for a in 0:(l + 1) for b in 0:a]
    ord = Hecke._modular_polynomial_order_presentation(l, D0, u, h)
    @test (ord.PO.g1 !== nothing, ord.PR.g1 !== nothing) == (sO, sR)
    ps = Hecke._modular_polynomial_crt_primes(l, ord.D)
    @test Hecke._modular_polynomial_coefficients(l, ord, ps) == c
    @test Hecke._modular_polynomial_coefficients_mod(l, ord, ps, ZZ(1000003)) ==
          mod.(c, 1000003)
  end

  # the descent from a root of H_{O_K} gives a root of H_O, also for
  # conductors with two primes, which no order above has
  Zx, _ = ZZ["x"]
  for (l, D0, u) in ((7, -31, 15), (7, -31, 45), (11, -39, 35))
    D = u^2 * D0
    p, _ = first(Hecke._modular_polynomial_crt_primes(l, D))
    F = Native.GF(p)
    Fx, _ = polynomial_ring(F, :X)
    T = Dict(q => change_base_ring(F, Hecke._modular_polynomial_table(q))
             for (q, _) in factor(u))
    HK = map_coefficients(F, hilbert_class_polynomial(D0, Zx); parent = Fx)
    j = Hecke._descend_to_order(Fx, T, first(roots(HK)), u)
    HO = map_coefficients(F, hilbert_class_polynomial(D, Zx); parent = Fx)
    @test iszero(HO(j))
  end

  # the primes use several v in 4p = t^2 - v^2 l^2 D
  ord = Hecke._modular_polynomial_order(13)
  ps = Hecke._modular_polynomial_crt_primes(13, ord.D)
  vs = [isqrt(div(t^2 - 4 * p, 13^2 * ord.D)) for (p, t) in ps]
  @test length(unique(vs)) > 1

  # the height bound holds for the database, and the primes stop at the
  # first sum of logarithms above the bound plus 2 log 2 (at 383, one prime
  # before B + log 4 + 1 does)
  for l in (3, 13, 59, 383)
    B = Hecke._modular_polynomial_height_bound(l)
    R = parent(B)
    if l <= 59
      phi = classical_modular_polynomial(l)
      @test all(log(R(abs(c))) < B for c in coefficients(phi))
    end
    D = Hecke._modular_polynomial_order(l).D
    ps = Hecke._modular_polynomial_crt_primes(l, D)
    s = [log(R(p)) for (p, _) in ps]
    @test sum(s) > B + log(R(4)) && !(sum(s[1:(end - 1)]) > B + log(R(4)))
  end

  # the order of least h(O), then least |D|, of the family of BLS12,
  # Section 6.6, as found independently with PARI's qfbclassno
  ord = Hecke._modular_polynomial_order(61)
  @test (ord.h, ord.D0, ord.u, ord.l1) == (70, -119, 7, 17)

  # no order with h(O) >= l + 2 and l^2 |D| in the word size
  @test_throws ArgumentError Hecke._modular_polynomial_order(6810301)

  F = Native.GF(1009)
  Fx, _ = polynomial_ring(F, :X)
  T = change_base_ring(F, Hecke._modular_polynomial_table(5))
  j = F(17)
  @test Hecke._modular_polynomial_at(Fx, T, j) ==
        Fx([sum(T[a, b] * j^(b - 1) for b in 1:7) for a in 1:7])

  # the shared interpolation tree, against interpolation column by column
  nodes = F.(1:9)
  A = UInt[mod(7 * i + 13 * k^2, 1009) for i in 1:9, k in 1:4]
  B = Hecke._interpolate_columns(F, nodes, A)
  for k in 1:4
    f = interpolate(Fx, nodes, F.(A[:, k]))
    @test B[:, k] == [UInt(lift(coeff(f, b))) for b in 0:8]
  end

  l = 61
  f = @inferred classical_modular_polynomial(l)
  @test parent(f) === Hecke.Globals.Zxy
  @test classical_modular_polynomial(l) === f
  x, y = gens(parent(f))
  @test f == evaluate(f, [y, x])
  @test degree(f, 1) == l + 1 && coeff(f, [l + 1, 0]) == 1
  @test total_degree(f) == 2 * l
  Zt, t = ZZ["t"]
  @test abs(leading_coefficient(evaluate(f, [t, t]))) == 1
  Fl = GF(l)
  Sl, (u, v) = polynomial_ring(Fl, [:x, :y])
  @test map_coefficients(Fl, f; parent = Sl) == (u^l - v) * (u - v^l)

  F = GF(1009)
  S, _ = polynomial_ring(F, [:x, :y])
  g = @inferred classical_modular_polynomial(S, l)
  @test parent(g) === S
  @test classical_modular_polynomial(S, l) === g
  @test g == map_coefficients(F, f; parent = S)
  Random.seed!(1)
  @test Hecke._classical_modular_polynomial_crt(S, l) == g
  SQ, _ = polynomial_ring(QQ, [:x, :y])
  @test classical_modular_polynomial(SQ, l) ==
        map_coefficients(QQ, f; parent = SQ)

  # an l-isogeny over F_1009, by Kohel's formulas and by Velu's of BLS12;
  # E has 976 = 16 * 61 points
  E = elliptic_curve(F, [1, 4])
  P = 16 * rand(E)
  while is_infinite(P)
    P = 16 * rand(E)
  end
  @test is_infinite(l * P)
  Fz, z = F["z"]
  psi = prod(z - (k * P)[1] for k in 1:div(l - 1, 2))
  EE = codomain(isogeny_from_kernel(E, psi))
  @test iszero(evaluate(g, [j_invariant(E), j_invariant(EE)]))
  A, B = a_invariants(E)[4], a_invariants(E)[5]
  A1, B1 = Hecke._velu_codomain(A, B, P, l)
  @test Hecke._short_weierstrass_j_invariant(A1, B1) == j_invariant(EE)

  # no prime of the CRT fits the word size
  @test_throws ArgumentError Hecke._modular_polynomial_crt_primes(2^31 - 1,
                                                                  -3359)
end

@testset "Atkin" begin
  Zxy, (x, y) = ZZ["x", "y"]
  p = @inferred atkin_modular_polynomial(2)
  @test base_ring(p) == ZZ
  @test p(x, y) == x^3 - x^2*y + 744*x^2 - x*y + 184512*x + y^2 + 7256*y + 15252992
  # test caching
  p = @inferred atkin_modular_polynomial(2)
  @test base_ring(p) == ZZ
  @test p(x, y) == x^3 - x^2*y + 744*x^2 - x*y + 184512*x + y^2 + 7256*y + 15252992

  p = @inferred atkin_modular_polynomial(23)
  @test constant_coefficient(p) == 1073741824
  p = @inferred atkin_modular_polynomial(223)
  @test constant_coefficient(p) == 15152690493256589832960153283553072259220674788850853681254083433291324627559120896000000000000

  @test total_degree.(atkin_modular_polynomial.([2, 3, 5, 7, 11, 13])) == [3, 4, 6, 8, 12, 14]

  p = @inferred atkin_modular_polynomial(Zxy, 2)
  @test parent(p) === Zxy

  Fxy, (x, y) = GF(2)["x", "y"]
  p = @inferred atkin_modular_polynomial(Fxy, 2)
  @test parent(p) === Fxy

  @test_throws ArgumentError atkin_modular_polynomial(-1)
  @test_throws ArgumentError atkin_modular_polynomial(0)
  @test_throws ArgumentError atkin_modular_polynomial(60)
  @test_throws ArgumentError atkin_modular_polynomial(1)
  @test_throws ArgumentError atkin_modular_polynomial(401)
end
