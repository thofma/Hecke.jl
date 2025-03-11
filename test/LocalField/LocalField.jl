@testset "LocalField" begin

  @testset "Creation" begin
    Qx, x = QQ["x"]
    f = x^2-2*x+2
    K, a = local_field(f, 2, 10, "a", Hecke.EisensteinLocalField, check = false)
    @test precision(K) == 20
    @test characteristic(K) == 0
    @test prime(K) == 2

    Kt, t = polynomial_ring(K, "t")
    g = t^2+2
    L, b = local_field(g, "b", Hecke.EisensteinLocalField, check = false)
    @test precision(L) == 2*precision(g)
    @test precision(b) == precision(L)
    @test degree(L) == 2
    @test absolute_degree(L) == 4
    @test prime(L) == 2

    Q2 = padic_field(2, precision = 10)
    Q2s, s = polynomial_ring(Q2, "s")
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

    Lu, u = polynomial_ring(L, "u")
    Lu, d = local_field(u^2+u+1, "s", Hecke.UnramifiedLocalField, check = false)
    @test absolute_degree(Lu) == 8
    @test ramification_index(Lu, K) == 2
    @test inertia_degree(Lu, K) == 2

  end

  @testset "Norm" begin
    K = qadic_field(3, 4, precision = 10)[1]
    Kx, x = polynomial_ring(K, "x")
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
    Kp, mKp = @inferred Hecke.completion(K, P, 100)
    @test isone(valuation(mKp\(uniformizer(Kp)), P))
    @test valuation(mKp(elem_in_nf(uniformizer(P)))) == QQFieldElem(1, 2)
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
    @test valuation(mKp(elem_in_nf(uniformizer(P)))) == QQFieldElem(1, 6)
    @test isone(valuation(mKp\(uniformizer(Kp)), P))
    @test valuation(mKp(gen(K)))*2 == valuation(gen(K), P)
    @test iszero(defining_polynomial(K)(mKp(gen(K))))

    K, gK = cyclotomic_field(55)
    OK = maximal_order(K)
    lP = prime_decomposition(OK, 11)
    P = lP[1][1]
    Kp, mKp = @inferred Hecke.completion(K, P, 100)
    @test isone(valuation(mKp\(uniformizer(Kp)), P))
    @test valuation(mKp(elem_in_nf(uniformizer(P)))) == QQFieldElem(1, 10)
    @test valuation(mKp(gen(K)))*10 == valuation(gen(K), P)
    @test iszero(defining_polynomial(K)(mKp(gen(K))))

    lP = prime_decomposition(OK, 7)
    P = lP[1][1]
    Kp, mKp = @inferred Hecke.unramified_completion(K, P, 100)
    @test isone(valuation(mKp(elem_in_nf(uniformizer(P)))))
    @test isone(valuation(mKp\(uniformizer(Kp)), P))
    @test valuation(mKp(gen(K))) == valuation(gen(K), P)
    @test iszero(defining_polynomial(K)(mKp(gen(K))))

    Qx, x = polynomial_ring(QQ, "x", cached = false)
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
    @test valuation(mKp(elem_in_nf(uniformizer(P)))) == QQFieldElem(1, 5)
    @test isone(valuation(mKp\(uniformizer(Kp)), P))
    @test valuation(mKp(gen(K)))*5 == valuation(gen(K), P)
    #@test iszero(defining_polynomial(K)(mKp(gen(K))))

  end


  @testset "Exp and Log" begin
    K = padic_field(2, precision = 100)
    Kx, x = polynomial_ring(K, "x", cached = false)
    L, b = eisenstein_extension(x^7+2, :a)
    pi = uniformizer(L)
    @test iszero(log(pi))
    @test iszero(log(one(L)))
    B = basis(L)
    for i = 15:20
      el = sum([rand(ZZ, 0:10)*B[j] for j = 1:7])*pi^i
      explog = exp(log(1+el))
      logexp = log(exp(el))
      @test iszero(explog - 1 - el) || valuation(explog - 1 - el) > 80
      @test iszero(logexp - el) || valuation(logexp - el) > 80 #need improving
    end

    KK, a = qadic_field(2, 2, precision = 16)
    KKx, x = KK["x"]
    f = x + 2^1 + 2^2 + 2^3 + 2^4 + 2^5 + 2^6 + 2^7 + 2^8 + 2^9 + 2^10 + 2^11 + 2^12 + 2^13 + 2^14 + 2^15
    L, b = eisenstein_extension(f, "b");
    c = L((2^1 + 2^2 + 2^5 + 2^7 + 2^9 + 2^10 + 2^11 + 2^12)*a + 2^0 + 2^6 + 2^8 + 2^9 + 2^10 + 2^11 + 2^14)
    @test valuation(log(c)) == 1
  end

  @testset "Maps" begin
    # QadicField -> QadicField
    Qq, a = qadic_field(2, 3, precision = 100)
    rt = roots(map_coefficients(Qq, defining_polynomial(Qq)))

    i = findfirst(x -> x == a, rt)
    img = rt[mod(i-2, 3)+1]
    invimg = rt[mod(i, 3)+1]

    f = @inferred hom(Qq, Qq, img)
    @test f(a) == img
    @test f\(f(a)) == a
    @test f(f(a)) == invimg

    k, mk = residue_field(Qq)
    for i in 1:10
      z = mk\(rand(k))
      @test z == f\(f(z))
      fl, w = @inferred has_preimage_with_preimage(f, z)
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

    # QadicField -> LocalField
    Qqt, t = Qq["t"]
    L, b = eisenstein_extension(t^3 + 2, "b")
    f = @inferred hom(Qq, L, L(gen(Qq)))

    @test f(a) == L(gen(Qq))
    @test_throws ErrorException hom(Qq, L, b)
    @test f\(L(gen(Qq))) == gen(Qq)
    fl, z = @inferred has_preimage_with_preimage(f, b^3)
    @test fl
    @test f(z) == L(-2)

    # LocalField -> QadicField
    Qp = padic_field(2, precision = 100)
    Qpx, x = polynomial_ring(Qp)
    K, a = unramified_extension(x^2+x+1)
    Qq, gQq = qadic_field(2, 2, precision = 100)
    rt = roots(map_coefficients(Qq, defining_polynomial(K)))

    f = @inferred hom(K, Qq, rt[1])
    g = @inferred inv(f)
    k, mk = residue_field(Qq)
    for i in 1:10
      w = mk\(rand(k))
      @test f(g(w)) == w
    end
  end

  @testset "Automorphisms" begin
    K = padic_field(2, precision = 200)
    Kt, t = polynomial_ring(K)
    L, b = eisenstein_extension(t^2+2, "a")
    @test length(automorphism_list(L)) == 2
    Qq, a = qadic_field(2, 2, precision = 100)
    @test length(automorphism_list(Qq)) == 2
    Qqx, x = polynomial_ring(Qq)
    L, b = eisenstein_extension(x^3+2, "a")
    @test length(automorphism_list(L)) == 3
    @test length(absolute_automorphism_list(L)) == 6
    G, mG = absolute_automorphism_group(L)
    @test order(G) == 6
    @test !is_abelian(G)
  end

  @testset "Unramified extension" begin
    Qx,x = QQ["x"]
    f = Qx([ 1, 8, -40, -46, 110, 71, -113, -43, 54, 11, -12, -1, 1 ])
    L = number_field(f)[1];
    P = prime_decomposition(maximal_order(L),7)[1][1];
    lp, mp = Hecke.completion(L,P, 128);
    Qy,y = polynomial_ring(lp,"y")
    f, mf = residue_field(lp)
    N = Hecke.unramified_extension(y^3+preimage(mf,(gen(f))) +4 )[1]
    F, mF = residue_field(N)
    @test order(F) == 7^6
    G, mG = automorphism_group(N)
    @test order(G) == 3
    @test mG(G[1]^2) == mG(G[1])^2
  end

  @testset "Ali-Inverse" begin
    Qx,x = QQ["x"]
    L = number_field(x^6-6*x^4+9*x^2+23)[1]
    P = prime_decomposition(maximal_order(L),23)[1][1]
    lp,mp = Hecke.completion(L,P)
    a = uniformizer(lp)
    Qy,y = polynomial_ring(lp,"y")
    N = unramified_extension(y^2+13*y+4)[1]
    r = N(53)*basis(N)[1] + N(165)*basis(N)[2]
    @test isone(r*r^-1)
  end

  @testset "extend extend extend" begin
    K, = qadic_field(5, 2, precision = 10)
    L, = unramified_extension(K, 3)
    M, = unramified_extension(L, 3)
  end

  Qx, x = QQ["x"]
  k, a = number_field(x^12 - 6*x^11 + 30*x^10 - 55*x^9 + 21*x^8 + 210*x^7 + 379*x^6 + 150*x^5 + 261*x^4 + 125*x^3 + 45*x^2 + 9*x + 1)
  zk = maximal_order(k)
  @test length(prime_decomposition(zk, 3)) == 1
  l3 = prime_decomposition(zk, 3)
  k3, _ = completion(k, l3[1][1])
  @test length(automorphism_list(k3)) == 3

  @testset "image of one units under log" begin
    Qp = padic_field(3, precision = 10)
    Qpt, t = Qp["t"]
    E, a = eisenstein_extension(t^2 - 3)
    n, x = Hecke.image_of_logarithm_one_units(E)
    @test n == 1 && length(x) == 1
    E, a = eisenstein_extension(t^2 + 3)
    n, x = Hecke.image_of_logarithm_one_units(E)
    @test n == 2 && length(x) == 1

    n, x = Hecke.image_of_logarithm_one_units(Qp)
    @test n == 1 && length(x) == 1
  end

  @testset "log problems" begin
    Qx, x = QQ["x"]
    f = x^4 - 52*x^2 + 26
    K, a = number_field(f; cached = false)
    u = 1//5*a^2 - 51//5
    OK = maximal_order(K)
    P = prime_decomposition(OK, 2)[1][1]
    C, mC = completion(K, P)
    @test valuation(log(mC(u))) == 1//2
  end

  let
    # missing canonical unit
    K, a = quadratic_field(5);
    OK = maximal_order(K)
    lp = prime_decomposition(OK, 7)
    C, mC = completion(K, lp[1][1], 20)
    Ct, t = C["t"];
    s = sprint(show, "text/plain", t//(1 + t))
    @test s isa String
  end

  let
    # some maps
    Qx, x = QQ[:x]
    K, a = number_field(x^3 - x^2 - 30*x + 64)
    KK, aa = number_field(x^3 - x^2 - 30*x - 27)
    # isomorphic over 13
    P, = prime_ideals_over(maximal_order(K), 13)
    Q, = prime_ideals_over(maximal_order(KK), 13)
    CP, mCP = completion(K, P)
    CQ, mCQ = completion(KK, Q)
    fl, h = is_isomorphic(CP, CQ)
    @test fl
    @test is_one(h(one(CP)))
    @test is_zero(h(zero(CP)))

    # not isomorphic over 7
    P, = prime_ideals_over(maximal_order(K), 7)
    Q, = prime_ideals_over(maximal_order(KK), 7)
    CP, mCP = completion(K, P)
    CQ, mCQ = completion(KK, Q)
    fl, h = is_isomorphic(CP, CQ)
    @test !fl
  end

  let
    # local isomormophism
    Qx, x = QQ[:x]
    K, a = number_field(x^3 - x^2 - 30*x + 64)
    KK, aa = number_field(x^3 - x^2 - 30*x - 27)
    @test Hecke._is_locally_isomorphic(K, KK, 13)
    @test !Hecke._is_locally_isomorphic(K, KK, 7)

    f = x^4 + 6*x^2 + 4
    g = x^4 - 6*x^2 + 4
    K, = number_field(f)
    L, = number_field(g)
    @test Hecke._is_locally_isomorphic(K, L, 5)
    #@test !Hecke._is_locally_isomorphic(K, L, 2)
  end
end
