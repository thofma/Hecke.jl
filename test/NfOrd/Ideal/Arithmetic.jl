@testset "Ideal arithmetic" begin
  Qx, x = polynomial_ring(QQ, "x")

  K1, a1 = number_field(x^3 - 2, "a")
  O1 = order(K1, Hecke.FakeFmpqMat(ZZ[1 0 0; 0 2 0; 0 0 4], one(ZZ)))

  I = ideal(O1, -17)
  J = ideal(O1, ZZ(-17))

  @testset "Binary operations" begin
    K = @inferred I + J # I == J
    @test K == I
    K = @inferred ideal(O1, 15) + ideal(O1, 10)
    @test K == ideal(O1, 5)

    K = @inferred intersect(ideal(O1, 15), ideal(O1, 10))
    @test K == ideal(O1, 30)
    K = @inferred lcm(ideal(O1, 15), ideal(O1, 10))
    @test K == ideal(O1, 30)

    K = @inferred ideal(O1, 15) * ideal(O1, 10)
    @test K == ideal(O1, 150)
    K = @inferred ideal(O1, O1(2*a1)) * ideal(O1, O1(4*a1^2))
    @test K == ideal(O1, 16)
  end

  # Multiplication must retain the ideal type before checking consistency.
  @testset "Multiplication type" begin
    Kns, _ = number_field([x^2 - 2, x^2 - 3])
    for O in (O1, maximal_order(K1), maximal_order(Kns))
      I = ideal(O, ZZRingElem(2), basis(O)[2])
      J = ideal(O, ZZRingElem(3), basis(O)[end])
      for (A, B) in ((I, J), (I, ideal(O, 0)), (ideal(O, 1), J))
        C = @inferred A * B
        @test typeof(C) === typeof(A)
        @test order(C) === O
        @test C == Hecke.mul_gen(A, B)
      end
    end
  end

  @testset "Ad hoc binary operations" begin
    I = ideal(O1, O1(2*a1))
    J = ideal(O1, 3)
    K = ideal(O1, ZZRingElem(3))

    @test ideal(O1, O1(10*a1)) == @inferred 5 * I
    @test ideal(O1, O1(10*a1)) == @inferred I * 5

    @test ideal(O1, O1(10*a1)) == @inferred ZZRingElem(5) * I
    @test ideal(O1, O1(10*a1)) == @inferred I * ZZRingElem(5)

    @test ideal(O1, 30) == @inferred 10 * J
    @test ideal(O1, 30) == @inferred J * 10

    @test ideal(O1, 30) == @inferred ZZRingElem(10) * J
    @test ideal(O1, 30) == @inferred J * ZZRingElem(10)

    @test ideal(O1, 30) == @inferred 10 * K
    @test ideal(O1, 30) == @inferred K * 10

    @test ideal(O1, 30) == @inferred ZZRingElem(10) * K
    @test ideal(O1, 30) == @inferred K * ZZRingElem(10)

    @test ideal(O1, O1(4*a1^2)) == @inferred I * O1(2*a1)
    @test ideal(O1, O1(4*a1^2)) == @inferred O1(2*a1) * I
  end

  @testset "Idempotents" begin
    I = ideal(O1, 2)
    J = ideal(O1, 3)
    e, f = @inferred idempotents(I, J)
    @test in(e, I)
    @test in(f, J)
    @test e + f == 1

    I = ideal(O1, O1(2*a1))
    J = ideal(O1, O1(1 - 2*a1))
    e, f = @inferred idempotents(I, J)
    @test in(e, I)
    @test in(f, J)
    @test e + f == 1

    @test_throws ErrorException idempotents(I, I)
  end

  #
  let
    Qx, x = polynomial_ring(QQ, "x")
    K, a = number_field(x^2 - 5, "a")
    O = maximal_order(K)
    @test divides(2*O, 1*O)
    @test !divides(1*O, 2*O)
    @test is_subset(2*O, 1*O)
    @test !is_subset(1*O, 2*O)
  end
end
