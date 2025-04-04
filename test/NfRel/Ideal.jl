@testset "Relative ideals" begin
  @testset "Arithmetic" begin
     Qx, x = QQ["x"]
    f = x^2 + 12*x - 92
     K, a = number_field(f, "a")
    OK = maximal_order(K)
    Ky, y = K["y"]
    g = y^2 - 54*y - 73
    L, b = number_field(g, "b")
    OL = maximal_order(L)

    coeff_ideals = [ deepcopy(Hecke.pseudo_basis(OL, copy = false)[i][2]) for i = 1:2 ]
    PM = Hecke.pseudo_matrix(matrix(K, [1 0; 0 1]), coeff_ideals)
    PM1 = pseudo_hnf(Hecke.pseudo_matrix(matrix(K, [3 0; 0 3]), coeff_ideals), :lowerleft, true)
    PM2 = pseudo_hnf(Hecke.pseudo_matrix(matrix(K, [6 0; 0 6]), coeff_ideals), :lowerleft, true)
    PM3 = pseudo_hnf(Hecke.pseudo_matrix(matrix(K, [9 0; 0 9]), coeff_ideals), :lowerleft, true)
    I = ideal(OL, PM)
    I1 = fractional_ideal(OL, PM)
    A = ideal(OL, PM1)
    A1 = fractional_ideal(OL, PM1)
    B = ideal(OL, PM2)
    C = ideal(OL, PM3)
    C1 = fractional_ideal(OL, PM3)

    @test A == B + C
    @test B == intersect(A, B)
    @test K(2)*C == A*B
    @test inv(C)*C1 == I1
    @test norm(A) == OK(9)*OK
    @test norm(I) == OK(1)*OK
    @test norm(I//5) == norm(I)//25
    D = divexact(C, B)
    D = ZZRingElem(2)*D
    @test D == A1
    @test isone(I)
    @test minimum(A) == numerator(PM1.coeffs[1])
  end

  @testset "Prime decomposition" begin
    Qx, x = QQ["x"]
    f = x^2 + 12*x - 92
    K, a = number_field(f, "a")
    OK = maximal_order(K)
    Ky, y = K["y"]
    g = y^2 - 54*y - 73
    L, b = number_field(g, "b")
    OL = maximal_order(L)

    p = prime_decomposition(OK, 11)[1][1]
    (p1, e1), (p2, e2) = prime_decomposition(OL, p)
    @test e1 == 1 && e2 == 1
    @test p1*p2 == p*OL

    p = prime_decomposition(OK, 2)[1][1]
    (p1, e1), (p2, e2) = prime_decomposition(OL, p)
    @test e1 == 1 && e2 == 1
    @test p1*p2 == p*OL

    L1, gL1 = number_field([y^2+2, y^2+3])
    OL1 = maximal_order(L1)
    lp = prime_decomposition(OL1, 2)
    @test length(lp) == 1
    @test lp[1][2] == 4
    @test lp[1][1].splitting_type[2] == 2

    Q, q = number_field(x, "q")
    Z = maximal_order(Q)
    Qy, y = Q["y"]
    g =  y^3 + 34*y^2 + 45*y + 98
    p = prime_decomposition(Z, 11)[1][1]
    L, b = number_field(g, "b")
    OL = maximal_order(L)
    (p1, e1), (p2, e2) = prime_decomposition(OL, p)
    @test e1 == 1 && e2 == 1
    @test p1*p2 == p*OL
    @test p1.splitting_type[2] == 2 || p2.splitting_type[2] == 2

    g = y^4 + 56*y^3 + 27*y^2 + -10*y + 56
    p = prime_decomposition(Z, 2)[1][1]
    L, b = number_field(g, "b")
    OL = maximal_order(L)
    (p1, e1), (p2, e2), (p3, e3) = prime_decomposition(OL, p)
    @test p1^e1*p2^e2*p3^e3 == p*OL
    @test p1.splitting_type[2] == 1 && p2.splitting_type[2] == 1 && p3.splitting_type[2] == 1
  end

  @testset "Residue fields" begin
     Qx, x = QQ["x"]
    f = x^4 - 95x^3 - 91x^2 + 90x - 31
     K, a = number_field(f, "a")
    OK = maximal_order(K)
    Ky, y = K["y"]
    g = y^3 - 70y^2 + 27y + 97
    L, b = number_field(g, "b")
    OL = maximal_order(L)

    # p is not a index divisor
    p = prime_decomposition(OK, 13)[1][1]
    P = prime_decomposition(OL, p)[1][1]
    F, mF = residue_field(OL, P)
    @test degree(F) == p.splitting_type[2]*P.splitting_type[2]

    pb = pseudo_basis(P, copy = false)
    for i = 1:degree(OL)
      b = OL(minimum(pb[i][2])*pb[i][1])
      @test iszero(mF(b))
    end

    for i = 1:1
      c = rand(OL, 100)
      d = rand(OL, 100)
      pinv = pseudo_inv(mF)
      @test mod(pinv(mF(c)), P) == mod(c, P)
      @test mod(pinv(mF(d)), P) == mod(d, P)
      @test mF(c + d) == mF(c) + mF(d)
      @test mF(c*d) == mF(c)*mF(d)
      e = mF(c)
      f = mF(d)
      @test mod(pinv(e + f), P) == mod(pinv(e) + pinv(f), P)
      @test mod(pinv(e*f), P) == mod(pinv(e)*pinv(f), P)
    end

    # p is a index divisor
    p = prime_decomposition(OK, 5)[1][1]
    PP = prime_decomposition(OL, p)
    P = PP[1][1]
    if P.splitting_type[2] == 1
      P = PP[2][1]
    end
    F, mF = residue_field(OL, P)
    @test degree(F) == p.splitting_type[2]*P.splitting_type[2]

    pb = pseudo_basis(P, copy = false)
    for i = 1:degree(OL)
      b = OL(minimum(pb[i][2])*pb[i][1])
      @test iszero(mF(b))
    end

    for i = 1:1
      c = rand(OL, 100)
      d = rand(OL, 100)
      pinv = pseudo_inv(mF)
      @test mod(pinv(mF(c)), P) == mod(c, P)
      @test mod(pinv(mF(d)), P) == mod(d, P)
      @test mF(c + d) == mF(c) + mF(d)
      @test mF(c*d) == mF(c)*mF(d)
      e = mF(c)
      f = mF(d)
      @test mod(pinv(e + f), P) == mod(pinv(e) + pinv(f), P)
      @test mod(pinv(e*f), P) == mod(pinv(e)*pinv(f), P)
    end

  end

  @testset "Idempotents and uniformizers" begin
     Qx, x = QQ["x"]
    f = x^2 + 12*x - 92
     K, a = number_field(f, "a")
    OK = maximal_order(K)
    Ky, y = K["y"]
    g = y^2 - 54*y - 73
    L, b = number_field(g, "b")
    OL = maximal_order(L)

    I = OL(2)*OL
    J = OL(3)*OL
    u, v = idempotents(I, J)
    @test u in I
    @test v in J
    @test u + v == OL(1)

    p = prime_decomposition(OK, 11)[1][1]
    (p1, e1), (p2, e2) = prime_decomposition(OL, p)

    u, v = idempotents(p1, p2)
    @test u in p1
    @test v in p2
    @test u + v == OL(1)

    # p1.splitting_type[1] == 1
    u1 = uniformizer(p1)
    @test u1 in p1
    @test valuation(u1, p1) == 1

    u2 = anti_uniformizer(p1)
    @test valuation(u2, p1) == -1

    p = prime_decomposition(OK, 401)[1][1]
    P = prime_decomposition(OL, p)[1][1]

    # P.splitting_type[1] == 2
    u3 = uniformizer(P)
    @test u3 in P
    @test valuation(u3, P) == 1

    u4 = anti_uniformizer(P)
    @test valuation(u4, P) == -1

    Q, q = number_field(x, "q")
    Z = maximal_order(Q)
    Qy, y = Q["y"]
    f = y^2 + 12*y - 92
     K, a = number_field(f, "a")
    OK = maximal_order(K)

    p = prime_decomposition(Z, 2)[1][1]
    P = prime_decomposition(OK, p)[1][1]

    u5 = uniformizer(P)
    @test u5 in P
    @test valuation(u5, P) == 1

    u6 = anti_uniformizer(P)
    @test valuation(u6, P) == -1

    f = x^4 - x^3 - 4x^2 + 4x + 1
    K, a = number_field(f, "a")
    OK = maximal_order(K)
    Ky, y = K["y"]
    g = y^2 + (a^3 - a^2 - 4a + 5)
    L, b = number_field(g, "b")
    OL = maximal_order(L)
    p = prime_decomposition(OK, 2)[1][1]
    pdec = prime_decomposition(OL, p)
    for i = 1:2
      P = pdec[i][1]
      u7 = anti_uniformizer(P)
      for (Q, e) in factor(u7*OL)
        if Q == P
          @test e == -1
        else
          @test e >= 0
        end
      end
    end
  end

  @testset "Weird modulus" begin
    K, a = Hecke.rationals_as_number_field()
    Kt, t = K["t"]
    E, z = number_field(t^2 + 1, "z")
    OE = order(E, pseudo_matrix(matrix(K, 2, 2, [1, 0, 0, 1]), [1 * maximal_order(K), 2 * maximal_order(K)]))
    I = OE(1) * OE
    @test I * I == I
    @test I + I == I
    @test intersect(I, I) == I
    @test isone(I//I)
  end

  let
    K, a = rationals_as_number_field()
    Kt, t = polynomial_ring(K, "t")
    L, b = number_field(t^2 + 1, "b")
    OL = maximal_order(L)
    I = 0 * OL
    @test iszero(I)
    @test nrows(basis_pmatrix(I)) == 0
    @test isempty(pseudo_basis(I))
    I = 1 * OL
    @test !iszero(L)
    @test 0 * OL + 1 * OL == 1 * OL
    @test 1 * OL + 0 * OL == 1 * OL
    @test 0 * OL + 0 * OL == 0 * OL
    @test is_zero(minimum(0 * OL))
  end
end
