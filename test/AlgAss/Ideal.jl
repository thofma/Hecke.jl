@testset "Ideals in algebras" begin

  let
    A = matrix_algebra(GF(3), 2)
    I = A[2]*A
    @test algebra(I) === A
    @test ideal(A, [A[2]], side = :right) == I
    I = A*A[2]
    @test algebra(I) === A
    @test ideal(A, [A[2]], side = :left) == I
    I = A[2]*A + A[3]*A
    @test algebra(I) === A
    @test ideal(A, [A[2], A[3]], side = :right) == I
    I = A*A[2] + A*A[3]
    @test algebra(I) === A
    @test ideal(A, [A[2], A[3]], side = :left) == I

    sprint(show, "text/plain", I) isa String
    sprint(show, I) isa String
    @test !is_zero(I)
    @test is_one(I)

    @test basis(I) !== basis(I; copy = false)

    I = A*zero(A)
    @test algebra(I) === A
    @test ideal(A, elem_type(A)[], side = :left) == I
    @test is_zero(I)
    @test !is_one(I)

    I = A * zero(A)
    @test hash(I) == hash(A * zero(A))
  end


  @testset "Left / Right" begin
    A = matrix_algebra(GF(3), 2)
    I = A[2]*A

    @test !is_left_ideal(I)
    @test is_right_ideal(I)

    J = ideal(A, [A[1]]; side = :twosided)
    @test J == one(A) * A

    J = twosided_ideal(A, [A[2]])
    @test J == one(A) * A
  end

  @testset "Quotients" begin
    Qx, x = QQ["x"]
    # f = x^2 + 1
    # g = x^3 + 3x^2 + 5x - 5
    f2g3 = x^13 + 9x^12 + 44x^11 + 120x^10 + 205x^9 + 153x^8 + 32x^7 - 168x^6 - 5x^5 - 485x^4 + 500x^3 - 400x^2 + 375x - 125 # = f^2*g^3
    A = StructureConstantAlgebra(f2g3)
    J = radical(A)
    Q, AtoQ = quo(A, J)

    @test dim(Q) == 5
    @test iszero(radical(Q))

    @test iszero(AtoQ(zero(A)))
    @test AtoQ\zero(Q) in J
    @test isone(AtoQ(one(A)))
    @test mod(one(A), J) == mod(AtoQ\one(Q), J)

    for i = 1:5
      c = rand(A, -10:10)
      d = rand(A, -10:10)
      @test mod(AtoQ\(AtoQ(c)), J) == mod(c, J)
      @test mod(AtoQ\(AtoQ(d)), J) == mod(d, J)
      @test AtoQ(c + d) == AtoQ(c) + AtoQ(d)
      @test AtoQ(c*d) == AtoQ(c)*AtoQ(d)

      e = rand(Q, -10:10)
      f = rand(Q, -10:10)
      @test AtoQ(AtoQ\e) == e
      @test AtoQ(AtoQ\f) == f
      @test mod(AtoQ\(e + f), J) == mod((AtoQ\e + AtoQ\f), J)
      @test mod(AtoQ\(e*f), J) == mod(((AtoQ\e)*(AtoQ\f)), J)
    end

    J2 = J^2
    Q, AtoQ = quo(J, J2)

    @test dim(Q) == 5

    @test iszero(AtoQ(zero(A)))
    @test AtoQ\zero(Q) in J2
    @test_throws ErrorException AtoQ(one(A))

    for i = 1:5
      c = rand(J, -10:10)
      d = rand(J, -10:10)
      @test mod(AtoQ\(AtoQ(c)), J2) == mod(c, J2)
      @test mod(AtoQ\(AtoQ(d)), J2) == mod(d, J2)
      @test AtoQ(c + d) == AtoQ(c) + AtoQ(d)
      @test AtoQ(c * d) == AtoQ(c) * AtoQ(d)

      e = rand(Q, -10:10)
      f = rand(Q, -10:10)
      @test AtoQ(AtoQ\e) == e
      @test AtoQ(AtoQ\f) == f
      @test mod(AtoQ\(e + f), J2) == mod((AtoQ\e + AtoQ\f), J2)
      @test mod(AtoQ\(e * f), J2) == mod((AtoQ\e) * (AtoQ\f), J2)
    end

    # An example where the multiplication table of the quotient is not 0,
    # see https://github.com/thofma/Hecke.jl/issues/1399 .
    G = small_group(8, 4)
    A, _ = StructureConstantAlgebra(group_algebra(QQ, G))
    I = left_ideal(A, one(A))
    J = left_ideal(A, sum(A[i] for i in 1:8))
    Q, AtoQ = quo(I, J)

    @test dim(Q) == 7

    @test iszero(AtoQ(zero(A)))
    @test AtoQ\zero(Q) in J
    for i in 1:7
      for j in 1:7
        @test Q[i]*Q[j] == AtoQ((AtoQ\Q[i])*(AtoQ\Q[j]))
      end
    end

    for i = 1:5
      c = rand(A, -10:10)
      d = rand(A, -10:10)
      @test mod(AtoQ\(AtoQ(c)), J) == mod(c, J)
      @test mod(AtoQ\(AtoQ(d)), J) == mod(d, J)
      @test AtoQ(c + d) == AtoQ(c) + AtoQ(d)
      @test AtoQ(c * d) == AtoQ(c) * AtoQ(d)

      e = rand(Q, -10:10)
      f = rand(Q, -10:10)
      @test AtoQ(AtoQ\e) == e
      @test AtoQ(AtoQ\f) == f
      @test mod(AtoQ\(e + f), J) == mod((AtoQ\e + AtoQ\f), J)
      @test mod(AtoQ\(e * f), J) == mod((AtoQ\e) * (AtoQ\f), J)
    end
  end

  @testset "rand" begin
    A = matrix_algebra(GF(7), 2)
    I = A[2]*A

    E = elem_type(A)
    @test rand(I) isa E
    @test rand(rng, I) isa E
    @test rand(rng, Hecke.RandomExtensions.make(I), 2, 3) isa Matrix{E}

    Random.seed!(rng, rand_seed)
    a = rand(rng, I)
    Random.seed!(rng, rand_seed)
    @test a == rand(rng, I)
  end

  let
    A = matrix_algebra(GF(3), 2)
    J = Hecke.ideal(A, [A[1]]; side = :twosided)
    a = @inferred Hecke.left_principal_generator(J)
    @test A * a == J
    a = @inferred Hecke.right_principal_generator(J)
    @test a * A == J
  end
end
