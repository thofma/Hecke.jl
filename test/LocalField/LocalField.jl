@testset "LocalField" begin
  
  @testset "Creation" begin
    Qx, x = FlintQQ["x"]
    f = x^2-2*x+2
    K, a = local_field(f, 2, 10, "a", Hecke.EisensteinLocalField, check = false)
    @test precision(K) == 20
    @test characteristic(K) == 0
    @test prime(K) == 2

    Kt, t = PolynomialRing(K, "t")
    g = t^2+2
    L, b = local_field(g, "b", Hecke.EisensteinLocalField, check = false)
    @test precision(L) == 2*precision(g)
    @test precision(b) == precision(L)
    @test degree(L) == 2
    @test absolute_degree(L) == 4
    @test prime(L) == 2
    
    Q2 = PadicField(2, 10)
    Q2s, s = PolynomialRing(Q2, "s")
    f = s^2+s+1
    Ku, c = local_field(f, "s", Hecke.UnramifiedLocalField, check = false)
    @test precision(Ku) == precision(f)
    @test precision(f) == precision(c)
    @test degree(Ku) == 2
    @test absolute_degree(Ku) == 2
    @test inertia_degree(Ku) == 2
    @test ramification_index(Ku) == 1
    @test absolute_ramification_index(Ku) == 1
    @test absolute_inertia_degree(Ku) == 2

    Lu, u = PolynomialRing(L, "u")
    Lu, d = local_field(u^2+u+1, "s", Hecke.UnramifiedLocalField, check = false)
    @test absolute_degree(Lu) == 8
    @test ramification_index(Lu, K) == 2
    @test inertia_degree(Lu, K) == 2

  end

  @testset "Completions" begin
    K, gK = cyclotomic_field(15)
    OK = maximal_order(K)
    lP = prime_decomposition(OK, 3)
    P = lP[1][1]
    Kp, mKp = @inferred Hecke.generic_completion(K, P, 100)
    @test isone(valuation(mKp\(uniformizer(Kp)), P))
    @test valuation(mKp(elem_in_nf(uniformizer(P)))) == fmpq(1, 2)
    @test valuation(mKp(gen(K)))*2 == valuation(gen(K), P)
    @test iszero(defining_polynomial(K)(mKp(gen(K))))

    P = prime_decomposition(OK, 7)[1][1]
    Kp, mKp = @inferred Hecke.unramified_completion(K, P, 100)
    @test isone(valuation(mKp\(uniformizer(Kp)), P))
    @test isone(valuation(mKp(elem_in_nf(uniformizer(P)))))
    @test valuation(mKp(gen(K))) == valuation(gen(K), P)
    @test iszero(defining_polynomial(K)(mKp(gen(K))))

    K, gK = cyclotomic_field(9)
    OK = maximal_order(K)
    lP = prime_decomposition(OK, 3)
    P = lP[1][1]
    Kp, mKp = @inferred Hecke.totally_ramified_completion(K, P, 100)
    @test valuation(mKp(elem_in_nf(uniformizer(P)))) == fmpq(1, 6)
    @test isone(valuation(mKp\(uniformizer(Kp)), P))
    @test valuation(mKp(gen(K)))*2 == valuation(gen(K), P)
    @test iszero(defining_polynomial(K)(mKp(gen(K))))

    K, gK = cyclotomic_field(55)
    OK = maximal_order(K)
    lP = prime_decomposition(OK, 11)
    P = lP[1][1]
    Kp, mKp = @inferred Hecke.generic_completion(K, P, 100)
    @test isone(valuation(mKp\(uniformizer(Kp)), P))
    @test valuation(mKp(elem_in_nf(uniformizer(P)))) == fmpq(1, 10)
    @test valuation(mKp(gen(K)))*10 == valuation(gen(K), P)
    @test iszero(defining_polynomial(K)(mKp(gen(K))))

    lP = prime_decomposition(OK, 7)
    P = lP[1][1]
    Kp, mKp = @inferred Hecke.unramified_completion(K, P, 100)
    @test isone(valuation(mKp(elem_in_nf(uniformizer(P)))))
    @test isone(valuation(mKp\(uniformizer(Kp)), P))
    @test valuation(mKp(gen(K))) == valuation(gen(K), P)
    @test iszero(defining_polynomial(K)(mKp(gen(K))))

    Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
    f = x^10 + 5*x^9 - 633*x^8 + 38157*x^7 + 1360601*x^6 - 39808345*x^5 - 464252491*x^4 - 17622187401*x^3 + 2826886632714*x^2 - 96335539805104*x + 1313743135204448
    K, a = number_field(f, check = false, cached = false)
    OK = maximal_order(K)
    P = prime_decomposition(OK, 2)[1][1]
    Kp, mKp = @inferred Hecke.unramified_completion(K, P, 100)
    @test isone(valuation(mKp(elem_in_nf(uniformizer(P)))))
    @test isone(valuation(mKp\(uniformizer(Kp)), P))
    @test valuation(mKp(gen(K))) == valuation(gen(K), P)
    @test iszero(defining_polynomial(K)(mKp(gen(K))))

    lP = prime_decomposition(OK, 11)
    if lP[1][2] == 5
      P = lP[1][1]
    else
      P = lP[2][1]
    end
    Kp, mKp = @inferred Hecke.totally_ramified_completion(K, P, 100)
    @test valuation(mKp(elem_in_nf(uniformizer(P)))) == fmpq(1, 5)
    @test isone(valuation(mKp\(uniformizer(Kp)), P))
    @test valuation(mKp(gen(K)))*5 == valuation(gen(K), P)
    #@test iszero(defining_polynomial(K)(mKp(gen(K))))

  end


end