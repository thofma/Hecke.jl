@testset "RelNonSimpleNumField" begin
  Qx, x = FlintQQ["x"]
  K, _ = number_field(x^2 - 2)
  Ky, y = K["y"]
  L, (a, b) = @inferred number_field([y^2 - 3, y^3 - 5])

  @testset "Basics" begin
    @test K == @inferred base_field(L)
    @test 6 == @inferred degree(L)
    @test [2, 3] == @inferred degrees(L)
    @test 2 == @inferred ngens(L)
    @test [a, b] == @inferred gens(L)
    @test [Symbol(a), Symbol(b)] == @inferred vars(L)
    @test [one(L), a, b, a * b, b^2, a * b^2] == @inferred basis(L)
    @test string(L) isa String
    @test string(a) isa String
  end

  @testset "coercion" begin
    @test QQ(2*a^0) == 2*one(QQ)
    @test_throws ArgumentError QQ(a)
    @test_throws ErrorException QQ(gen(K) * a^0)
    @test is_rational(2*a^0)
    @test !is_rational(gen(K) * a^0)
  end
end
