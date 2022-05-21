@testset "Ideals in algebras" begin

  @testset "Left / Right" begin
    A = matrix_algebra(GF(3), 2)
    I = A[2]*A

    @test is_left_ideal(I) == false
    @test is_right_ideal(I) == true
  end

  @testset "Quotients" begin
    Qx, x = FlintQQ["x"]
    # f = x^2 + 1
    # g = x^3 + 3x^2 + 5x - 5
    f2g3 = x^13 + 9x^12 + 44x^11 + 120x^10 + 205x^9 + 153x^8 + 32x^7 - 168x^6 - 5x^5 - 485x^4 + 500x^3 - 400x^2 + 375x - 125 # = f^2*g^3
    A = AlgAss(f2g3)
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

      e = rand(Q, -10:10)
      f = rand(Q, -10:10)
      @test AtoQ(AtoQ\e) == e
      @test AtoQ(AtoQ\f) == f
      @test mod(AtoQ\(e + f), J2) == mod((AtoQ\e + AtoQ\f), J2)
    end
  end

  @testset "rand" begin
    A = matrix_algebra(GF(7), 2)
    I = A[2]*A

    E = elem_type(A)
    @test rand(I) isa E
    @test rand(rng, I) isa E
    @test rand(rng, I, 2, 3) isa Matrix{E}

    Random.seed!(rng, rand_seed)
    a = rand(rng, I)
    Random.seed!(rng, rand_seed)
    @test a == rand(rng, I)
  end
end
