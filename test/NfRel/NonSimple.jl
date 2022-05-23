@testset "NfRelNS" begin
  Qx, x = FlintQQ["x"]
  K, _ = number_field(x^2 - 2)
  Ky, y = K["y"]
  L, (a, b) = @inferred number_field([x^2 - 3, x^3 - 5])

  @testset "Basics" begin
    @test FlintQQ == @inferred base_ring(L)
    @test 6 == @inferred degree(L)
    @test [2, 3] == @inferred degrees(L)
    @test 2 == @inferred ngens(L)
    @test [a, b] == @inferred gens(L)
    @test [Symbol(a), Symbol(b)] == @inferred vars(L)
    @test [one(L), a, b, a * b, b^2, a * b^2] == @inferred basis(L)
    @test string(L) isa String
    @test string(a) isa String
  end

  
end
