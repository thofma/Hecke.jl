@testset "Hilbert symbols" begin
  v = [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, -1, -1, 1, 1, 1, -1, -1, 1, 1, 1,
       -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, -1, 1, -1, 1, -1, 1, 1,
       -1, -1, -1, -1, 1, 1, -1, 1, 1, -1, -1, 1, 1, 1, -1, 1, -1, -1, 1, 1 ]

  for i in 1:8
    for j in 1:8
      @test hilbert_symbol(i, j, 2) == v[(i - 1) * 8 + j]
      @test hilbert_symbol(ZZRingElem(i), ZZRingElem(j), 2) == v[(i - 1) * 8 + j]
      @test hilbert_symbol(ZZRingElem(i), ZZRingElem(j), ZZRingElem(2)) == v[(i - 1) * 8 + j]
      @test hilbert_symbol(QQFieldElem(i), QQFieldElem(j), 2) == v[(i - 1) * 8 + j]
      @test hilbert_symbol(QQFieldElem(i), QQFieldElem(j), ZZRingElem(2)) == v[(i - 1) * 8 + j]
    end
  end

  for p in PrimesSet(3, 100)
    for a in 1:100
      for b in 1:00
        h = hilbert_symbol(a, b, p)
        a = ZZRingElem(a)
        b = ZZRingElem(b)
        r = (-1)^(valuation(a, p) * valuation(b, p)) * a^(valuation(b, p)) * b^(valuation(a, p))
        @test h == jacobi_symbol(r, ZZRingElem(p))
      end
    end
  end

  Qx, x = polynomial_ring(FlintQQ, "x")
  K, b = number_field(x^3-3*x-1, "a")
  OK = maximal_order(K)
  for P in prime_ideals_up_to(OK, 200)
    @test hilbert_symbol(b, -3, P) == 1
  end

  @test quadratic_defect(QQ(1//9),3) == PosInf()
  @test quadratic_defect(QQ(1//9),ZZ(3)) == PosInf()

  # Test where Magma div(x, y) differs from julia div(x, y) (internally)
  K, a = cyclotomic_real_subfield(8, "a") # x^2 - 2
  z = 9278908160780559301//4*a+6561375391013480455//2
  w = K(-2)
  p = prime_decomposition(maximal_order(K), 2)[1][1]
  @test hilbert_symbol(z, w, p) == 1

  k, a = rationals_as_number_field()
  kt, t = k["t"]
  LS, LSb = number_field(t^2 - 2)
  LNS, LNSb = number_field([t^2 - 2])
  KS, KSb = number_field(x^2 - 2)
  KNS, KNSb = number_field([x^2 - 2])
  p = prime_decomposition(maximal_order(k), 2)[1][1]
  pKS = prime_decomposition(maximal_order(KS), 2)[1][1]
  pKNS = prime_decomposition(maximal_order(KNS), 2)[1][1]
  pLS = prime_decomposition(maximal_order(LS), p)[1][1]
  pLNS = prime_decomposition(maximal_order(LNS), p)[1][1]

  q = prime_decomposition(maximal_order(k), 3)[1][1]
  qKS = prime_decomposition(maximal_order(KS), 3)[1][1]
  qKNS = prime_decomposition(maximal_order(KNS), 3)[1][1]
  qLS = prime_decomposition(maximal_order(LS), q)[1][1]
  qLNS = prime_decomposition(maximal_order(LNS), q)[1][1]

  for i in 1:10
    z = rand(KS, -2:2)
    v = quadratic_defect(z, pKS)
    #@test v == quadratic_defect(KNS(coordinates(z)), pKNS)
    #@test v == quadratic_defect(LS(k.(coordinates(z))), pLS)
    #@test v == quadratic_defect(LNS(k.(coordinates(z))), pLNS)
    v = quadratic_defect(z, qKS)
    #@test v == quadratic_defect(KNS(coordinates(z)), qKNS)
    #@test v == quadratic_defect(LS(k.(coordinates(z))), qLS)
    #@test v == quadratic_defect(LNS(k.(coordinates(z))), qLNS)
  end

  for i in 1:8
    for j in 1:8
      v = hilbert_symbol(i, j, 2)
      @test v == hilbert_symbol(k(i), k(j), p)
      #@test v == hilbert_symbol(KNS(i), KNS(i), pKNS)
      #@test v == hilbert_symbol(LS(i), LS(i), pLS)
      #@test v == hilbert_symbol(LNS(i), LNS(i), pLNS)
    end
  end

  K, a = quadratic_field(3)
  P = prime_ideals_over(maximal_order(K), 3)[1]
  @test is_local_square(3, P)
  @test !is_local_square(-3, P)
end
