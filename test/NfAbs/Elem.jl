@testset "Random" begin
  Qx, x = PolynomialRing(FlintQQ, "x")
  K, a = NumberField(x^32 + 2, "a")

  b = @inferred rand([a], -10:10)
  @test b isa nf_elem
  @test_throws ErrorException rand(nf_elem[], -10:10)

  b = @inferred rand(basis(K), 1:100, 10)
  @test count(!iszero, (coeff(b, i) for i in 0:31)) <= 10
  @test_throws ErrorException rand(nf_elem[], -10:10, 5)
  @test_throws ErrorException rand([a, a^2], -10:10, -10)
  @test_throws ErrorException rand(basis(K), -10:10, 100)

  @inferred rand!(b, basis(K), 1:100, 20)
  @test count(!iszero, (coeff(b, i) for i in 0:31)) <= 20
  @test_throws ErrorException rand!(b, basis(K), 1:100, 120)
  @test_throws ErrorException rand!(b, basis(K), 1:100, -100)

  @inferred rand!(b, basis(K), 1:100)
  @test_throws ErrorException rand!(b, nf_elem[], 1:100)
end

@testset "Polynomial" begin
  Qx, x = QQ["x"]
  K, _a = NumberField(x^3 - 3*x - 1, "a")
  Kt, t = K["t"]
  f = t^4+(-28*_a^2 + 26*_a + 124)*t^2+(81*_a^2 + 504*_a + 936)
  @test @inferred isirreducible(f)

  f = x^3-7*x^2+6*x-1
  K, a = number_field(f, "a")
  Ky, y = K["y"]
  h = y^3+(15037//140*a^2 - 109//40*a - 915//14)*y^2+(16375724527//78400*a^2 - 993527643//4900*a + 393774209//11200)*y+(107296943419277//878080*a^2 - 2594040461688323//21952000*a + 17784340885567//878080)
  @assert isirreducible(h)
end

@testset "Is integral" begin
  Qx, x = FlintQQ["x"]
  f = x^2 + 1
  K, a = number_field(f, "a")

  @test Hecke.isintegral(a) == true
  @test Hecke.isintegral(fmpq(1, 2)*a) == false

  g = x^3 + 3
  L, b = number_field([f, g], "b")

  @test Hecke.isintegral(b[1]) == true
  @test Hecke.isintegral(fmpq(1, 2)*b[1]) == false
end

@testset "Compositum" begin
  Qx, x = FlintQQ["x"]
  f = x^2 + 1
  K, a = number_field(f, "a")
  L, b = number_field(x^2-3, "b")
  C, mK, mL = compositum(K, L)

  @test iszero(K.pol(mK(gen(K))))
  @test iszero(L.pol(mL(gen(L))))
end

@testset "PolyFactor" begin
  Zx, x = FlintZZ["x"]
  k, a = number_field(swinnerton_dyer(3, x))
  kt, t = k["t"]

  g = swinnerton_dyer(8, x)
  @test length(factor((t^2-a)*(t^3-a-1))) == 2 #Trager
  @test length(factor((t^2-a)*(t^3-a-1)*(t+a^2+1)*(t^5+t+a))) == 4 #Zassenhaus
  @test length(factor(change_base_ring(g, k))) == 8 # van Hoeij

  K, a = NumberField(x - 1, "a") 
  Kt, t = K["t"]
  f = t^5 -3 * t^4 - 104 * t^3 + 312 * t^2 + 400t -1200
  @test length(factor(f)) == 5
  @test length(factor(f*t)) == 6
end
