Qx,x = QQ["x"]
K,a = number_field(x^6+108)
OK = ring_of_integers(K)
lp = prime_decomposition(OK, 5)
P = lp[1][1]
L = localization(OK, P)

@testset "OrderLocalization" begin

  @testset "Constructor" begin

    @test parent_type(OrdLocElem{AbsSimpleNumFieldElem}) == OrdLoc{AbsSimpleNumFieldElem}

    lp = prime_decomposition(OK, 3)
    P = lp[1][1]
    L = localization(OK, P)

    @test elem_type(L) == OrdLocElem{AbsSimpleNumFieldElem}
    @test Hecke.nf(L) == K
    @test Hecke.nf(L()) == K

end

#=
  @testset "Canonicalisation" begin
  for i in 1:300
    a = rand(L, -10:10)
    c = canonical_unit(a)
    @test is_unit(c)
  end
end

    @testset "Valuation" begin

      @test valuation(L(5)) == 1
      @test valuation(L(5//5)) == 0
      @test valuation(L(5//12)) == 1
      @test valuation(L(500)) == 3

      for i in 1:300
        a = rand(L, -10:10)
        while iszero(a)
          a = rand(L, -10:10)
        end
        @test valuation(a) >= 0
      end

    end
    =#

    @testset "Parent object call overloading" begin

      @test parent(L(3)) == L
      @test L(6//3) == L(2)
      @test L(K(5)) == L(5)
      @test L(OK(5)) == L(5)
      @test_throws ErrorException L(24//90)
    end

    @testset "GCDX" begin
      for i in 1:550
        a = rand(L, -10:10)
        b = rand(L, -10:10)
        (g,u,v) = gcdx(a,b)
        @test g == u*a + v*b
      end
    end

    @testset "GCD" begin
      for i in 1:550
        a = rand(L, -10:10)
        b = rand(L, -10:10)
        g = gcd(a,b)
        @test divides(a,g)[1] && divides(b,g)[1]
      end
    end

    @testset "Exact division" begin

      @test divides(L(15),L(3)) == (true, L(5))
      @test divides(L(15),L(30)) == (true, L(1//2))
      @test divides(L(15),L(25)) == (false, L(0))
      @test_throws ErrorException divexact(L(8),L(10))
      for i in 1:300
        a = rand(L, -10:10)
        b = rand(L, -10:10)
        d = divides(a,b)
        if d[1]
          @test a == d[2] * b
        end
      end
    end

    @testset "Inversion" begin

      @test inv(L(8)) == L(1//8)
      @test inv(L(23)) == L(1//23)
      @test_throws ErrorException inv(L(40))
      @test_throws DivideError inv(L())
    end

    @testset "Binary operators" begin

      @test L(19) + L(1) == L(20)
      @test L(19) - L(1) == L(18)
      @test L(3) * L(4//2) == L(6)


      @test L(18//2) + L(2//1) == L(11)
      @test L(18//3) - L(1) == L(5)
      @test L(32) * L(4) == L(128)
    end

    @testset "Basic manipulation" begin

      @test iszero(L()) == true
      @test iszero(L(0)) == true
      @test isone(L(2//3)) == false
      @test is_unit(L(24)) == true


      @test iszero(L(4//3)) == false
      @test isone(L(13//13)) == true
      @test is_unit(L(50//2)) == false
    end

  let
    # hashing
    Qx, x = QQ["x"]
    K, a = number_field(x^6 + 108)
    OK = ring_of_integers(K)
    lp = prime_decomposition(OK, 5)
    P = lp[1][1]
    L = localization(OK, P)
    @test hash(one(L)) == hash(one(L))
  end

  let
    # principal generators of ideals in the localization at a prime
    Qx, x = QQ["x"]
    K, a = number_field(x^6 + 108)
    OK = ring_of_integers(K)
    lp = prime_decomposition(OK, 5)
    P, Q = lp[1][1], lp[2][1]
    L = localization(OK, P)
    for I in [P, P^2, P * Q, Q, 3 * P]
      g = principal_generator(L, I)
      @test Hecke.data(g) in I
      @test valuation(g, P) == valuation(I, P)
      @test all(b -> divides(L(b), g)[1], basis(I))
    end
  end

  @testset "Principal generators" begin
    # Check equality of extended ideals, including composite localization ideals.
    Qx, x = QQ["x"]
    K, a = number_field(x^2 + 1, "a")
    O = maximal_order(K)
    P = prime_decomposition(O, 5)[1][1]
    I = ideal(O, 13, O(a + 5))
    J = ideal(O, basis_matrix(I))
    for S in (P, P^2, 26*O, 52*O, 13*O, 2*O, 1*O)
      L = localization(O, S)
      for A in (I, J, 3*I, ideal(O, 1), ideal(O, 13, O(0)))
        g = principal_generator(L, A)
        @test parent(g) === L
        @test Hecke.data(g) in A
        for b in basis(A)
          @test divides(L(b), g)[1]
        end
        for Q in keys(factor(S))
          @test valuation(g, Q) == valuation(A, Q)
        end
      end
      @test iszero(principal_generator(L, ideal(O, 0)))
    end

    L = localization(O, 26*O)
    @test !divides(L(13), L(a + 5))[1]
    g = principal_generator(L, I)
    @test is_unit(divexact(g, L(3 - 2*a)))
    @test !(K(1//2) in L)
    @test K(1//5) in L
    C = localization(O, P; comp=true)
    @test !(K(1//5) in C)
    @test K(1//5) in localization(O, 5*O; comp=true)
    @test !(K(1//2) in C)
    @test_throws ArgumentError principal_generator(C, I)
    @test_throws ArgumentError principal_generator(localization(O, 0*O), I)

    F, b = number_field(x^2 + 5, "b")
    R = maximal_order(F)
    A = ideal(R, 2, R(1 + b))
    @test !is_principal(A)
    M = localization(R, 6*R)
    g = principal_generator(M, A)
    @test Hecke.data(g) in A
    @test all(t -> divides(M(t), g)[1], basis(A))
    @test_throws ArgumentError principal_generator(M, I)

    F, b = number_field(x^2 - 5, "b")
    R = equation_order(F)
    @test !is_maximal(R)
    @test_throws ArgumentError principal_generator(localization(R, 2*R), 2*R)
  end

end
