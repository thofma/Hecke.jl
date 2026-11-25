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
  for R in (polynomial_ring(ZZ, [:x])[1], ZZ["x", "y", "z"][1]), n in (3, 61)
    @test_throws ArgumentError classical_modular_polynomial(R, n)
  end
end

@testset "Classical, prime levels above 59" begin
  # The algorithm of Broker-Lauter-Sutherland for prime levels above 59:
  # against the database below 60, over Z and modulo m by the explicit CRT;
  # at level 61, the properties of Cox, Theorem 11.18, and isogenies.
  for l in (3, 5, 7, 11, 13)
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

  F = Native.GF(1009)
  Fx, _ = polynomial_ring(F, :X)
  T = change_base_ring(F, Hecke._modular_polynomial_table(5))
  j = F(17)
  @test Hecke._modular_polynomial_at(Fx, T, j) ==
        Fx([sum(T[a, b] * j^(b - 1) for b in 1:7) for a in 1:7])

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
