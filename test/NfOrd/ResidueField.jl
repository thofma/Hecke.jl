@testset "residue_field" begin

  Qx, x = FlintQQ["x"]
  f = x^6 + x^5 + 41*x^4 - 34*x^3 + 355*x^2 - 100*x + 125
  K, a = number_field(f, cached = false);
  OK = maximal_order(K);
  lp = prime_decomposition(OK, 5)
  B = basis(OK)
  for i = 1:length(lp)
    P = lp[i][1]
    F, mF = residue_field(OK, P)
    F1, mF1 = Hecke.ResidueFieldSmall(OK, P)
    F2, mF2 = Hecke.ResidueFieldSmallDegree1(OK, P)
    F3, mF3 = Hecke.ResidueFieldDegree1(OK, P)
    @test order(F1) == order(F2)
    @test order(F1) == order(F3)
    @test order(F1) == order(F)

    for b in B
      a1 = mF(b)
      a2 = mF1(b)
      a3 = mF2(b)
      a4 = mF3(b)
      @test (mF\(a1) - b) in P
      @test (mF1\(a2) - b) in P
      @test (mF2\(a3) - b) in P
      @test (mF3\(a4) - b) in P
    end
  end

  lp = prime_decomposition(OK, 47)
  for i = 1:length(lp)
    P = lp[i][1]
    F, mF = residue_field(OK, P)
    F1, mF1 = Hecke.ResidueFieldSmall(OK, P)
    F2, mF2 = Hecke.ResidueFieldSmallDegree1(OK, P)
    F3, mF3 = Hecke.ResidueFieldDegree1(OK, P)
    @test order(F1) == order(F2)
    @test order(F1) == order(F3)
    @test order(F1) == order(F)

    for b in B
      a1 = mF(b)
      a2 = mF1(b)
      a3 = mF2(b)
      a4 = mF3(b)
      @test (mF\(a1) - b) in P
      @test (mF1\(a2) - b) in P
      @test (mF2\(a3) - b) in P
      @test (mF3\(a4) - b) in P
    end
  end

  # 1284

  P, x = polynomial_ring(ZZ)
  K, a = number_field(x^5 + x^3 - x^2 - x - 1)
  M = Order(K, [1, 121*a, a^2 - 17*a, a^3 - 72*a, a^4 - 76*a])
  P = prime_ideals_over(M, 11)

  for i in 1:1000
    for p in P
      k, h = residue_field(M, p, false)
      y = Hecke.primitive_element(k)
      tmp = preimage(h, y)
      @test h(tmp) == y
    end
  end
end

