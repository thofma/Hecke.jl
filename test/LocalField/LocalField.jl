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

  @testset "Norm" begin
    K = QadicField(3, 4, 10)[1]
    Kx, x = PolynomialRing(K, "x")
    L = eisenstein_extension(x^20+3)[1]
    b = @inferred basis(L)
    for i = 1:10
      r = 1+2*uniformizer(L)^i * sum([rand(1:10)*b[i] for i in 1:5])
      M = @inferred representation_matrix(r)
      n = @inferred norm(r)
      @test n == det(M)
      @test trace(r) == trace(M)
    end
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


  @testset "Exp and Log" begin
    K = PadicField(2, 100)
    Kx, x = PolynomialRing(K, "x", cached = false)
    L, b = Hecke.eisenstein_extension(x^7+2, "a")
    pi = uniformizer(L)
    @test iszero(log(pi))
    @test iszero(log(one(L)))
    B = basis(L)
    for i = 15:20
      el = sum([rand(FlintZZ, 0:10)*B[j] for j = 1:7])*pi^i
      explog = exp(log(1+el))
      logexp = log(exp(el))
      @test iszero(explog - 1 - el) || valuation(explog - 1 - el) > 80
      @test iszero(logexp - el) || valuation(logexp - el) > 80 #need improving
    end
  end

  @testset "Maps" begin
    # FlintQadicField -> FlintQadicField
    Qq, a = QadicField(2, 3, 100)
    rt = roots(map_coefficients(Qq, defining_polynomial(Qq)))

    i = findfirst(x -> x == a, rt)
    img = rt[mod(i-2, 3)+1]
    invimg = rt[mod(i, 3)+1]

    f = @inferred hom(Qq, Qq, img)
    @test f(a) == img
    @test f\(f(a)) == a
    @test f(f(a)) == invimg

    k, mk = ResidueField(Qq)
    for i in 1:10
      z = mk\(rand(k))
      @test z == f\(f(z))
      fl, w = @inferred haspreimage(f, z)
      @test fl
      @test f(w) == z
    end

    @test_throws ErrorException hom(Qq, Qq, Qq(2))

    f = @inferred hom(Qq, Qq, img, inverse = (invimg))
    @test f(a) == img
    @test f\a == invimg
    @test_throws ErrorException hom(Qq, Qq, Qq(2), inverse = a + 1)
    @test_throws ErrorException hom(Qq, Qq, a, inverse = Qq(2))

    g = @inferred inv(f)

    for i in 1:10
      z = mk\(rand(k))
      @test f(g(z)) == z
      @test g(f(z)) == z
    end

    # FlintQadicField -> LocalField
    Qqt, t = Qq["t"]
    L, b = eisenstein_extension(t^3 + 2, "b")
    f = @inferred hom(Qq, L, L(gen(Qq)))

    @test f(a) == L(gen(Qq))
    @test_throws ErrorException hom(Qq, L, b)
    @test f\(L(gen(Qq))) == gen(Qq)
    fl, z = @inferred haspreimage(f, b^3)
    @test fl
    @test f(z) == L(-2)

    # LocalField -> FlintQadicField
    Qp = PadicField(2, 100)
    Qpx, x = PolynomialRing(Qp)
    K, a = Hecke.unramified_extension(x^2+x+1)
    Qq, gQq = QadicField(2, 2, 100)
    rt = roots(map_coefficients(Qq, defining_polynomial(K)))

    f = @inferred hom(K, Qq, rt[1])
    g = @inferred inv(f)
    k, mk = ResidueField(Qq)
    for i in 1:10
      w = mk\(rand(k))
      @test f(g(w)) == w
    end
  end

  @testset "Automorphisms" begin
    K = PadicField(2, 200)
    Kt, t = PolynomialRing(K)
    L, b = Hecke.eisenstein_extension(t^2+2, "a")
    @test length(automorphism_list(L)) == 2
    Qq, a = QadicField(2, 2, 100)
    @test length(automorphism_list(Qq)) == 2
    Qqx, x = PolynomialRing(Qq)
    L, b = Hecke.eisenstein_extension(x^3+2, "a")
    @test length(automorphism_list(L)) == 3
    @test length(absolute_automorphism_list(L)) == 6
    G, mG = absolute_automorphism_group(L)
    @test order(G) == 6
    @test !is_abelian(G)
  end

  @testset "Unramified extension" begin
    Qx,x = FlintQQ["x"]
    f = Qx([ 1, 8, -40, -46, 110, 71, -113, -43, 54, 11, -12, -1, 1 ])
    L = number_field(f)[1];
    P = prime_decomposition(maximal_order(L),7)[1][1];
    lp, mp = Hecke.generic_completion(L,P);
    Qy,y = PolynomialRing(lp,"y")
    f, mf = ResidueField(lp)
    N = Hecke.unramified_extension(y^3+preimage(mf,(gen(f))) +4 )[1]
    F, mF = ResidueField(N)
    @test order(F) == 7^6
    G, mG = automorphism_group(N)
    @test order(G) == 3
    @test mG(G[1]^2) == mG(G[1])^2
  end

  @testset "Ali-Inverse" begin
    Qx,x = FlintQQ["x"]
    L = number_field(x^6-6*x^4+9*x^2+23)[1]
    P = prime_decomposition(maximal_order(L),23)[1][1]
    lp,mp = Hecke.generic_completion(L,P)
    a = uniformizer(lp)
    Qy,y = PolynomialRing(lp,"y")
    N = Hecke.unramified_extension(y^2+13*y+4)[1]
    r = N(53)*basis(N)[1] + N(165)*basis(N)[2]
    @test isone(r*r^-1)
  end

  @testset "extend extend extend" begin
    K, = QadicField(5, 2, 10)
    L, = unramified_extension(K, 3)
    M, = unramified_extension(L, 3)
  end
end



