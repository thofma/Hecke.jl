@testset "Linear disjoint" begin
  Qx, x = polynomial_ring(FlintQQ, "x")
  _K, _ = number_field([x^2 - 2, x^2 - 3], "a", cached = false)
  K, _ = simple_extension(_K)
  L, b = number_field(x^2 - 2, "b", cached = false)
  @test !is_linearly_disjoint(K, L)

  M, c = number_field(x^2 - 3, "c", cached = false)
  @test is_linearly_disjoint(L, M)
end

@testset "Random" begin
  Qx, x = polynomial_ring(FlintQQ, "x")
  K, a = number_field(x^32 + 2, "a")

  b = @inferred rand([a], -10:10)
  @test b isa AbsSimpleNumFieldElem
  @test_throws ErrorException rand(AbsSimpleNumFieldElem[], -10:10)

  b = @inferred rand(basis(K), 1:100, 10)
  @test count(!iszero, (coeff(b, i) for i in 0:31)) <= 10
  @test_throws ErrorException rand(AbsSimpleNumFieldElem[], -10:10, 5)
  @test_throws ErrorException rand([a, a^2], -10:10, -10)
  @test_throws ErrorException rand(basis(K), -10:10, 100)

  @inferred rand!(b, basis(K), 1:100, 20)
  @test count(!iszero, (coeff(b, i) for i in 0:31)) <= 20
  @test_throws ErrorException rand!(b, basis(K), 1:100, 120)
  @test_throws ErrorException rand!(b, basis(K), 1:100, -100)

  @inferred rand!(b, basis(K), 1:100)
  @test_throws ErrorException rand!(b, AbsSimpleNumFieldElem[], 1:100)
end

@testset "Polynomial" begin
  Qx, x = QQ["x"]
  K, _a = number_field(x^3 - 3*x - 1, "a")
  Kt, t = K["t"]
  f = t^4+(-28*_a^2 + 26*_a + 124)*t^2+(81*_a^2 + 504*_a + 936)
  @test @inferred is_irreducible(f)

  f = x^3-7*x^2+6*x-1
  K, a = number_field(f, "a")
  Ky, y = K["y"]
  h = y^3+(15037//140*a^2 - 109//40*a - 915//14)*y^2+(16375724527//78400*a^2 - 993527643//4900*a + 393774209//11200)*y+(107296943419277//878080*a^2 - 2594040461688323//21952000*a + 17784340885567//878080)
  @assert is_irreducible(h)
end

@testset "Is integral" begin
  Qx, x = FlintQQ["x"]
  f = x^2 + 1
  K, a = number_field(f, "a")

  @test Hecke.is_integral(a) == true
  @test Hecke.is_integral(QQFieldElem(1, 2)*a) == false

  g = x^3 + 3
  L, b = number_field([f, g], "b")

  @test Hecke.is_integral(b[1]) == true
  @test Hecke.is_integral(QQFieldElem(1, 2)*b[1]) == false
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
  @test length(factor(change_base_ring(k, g))) == 8 # van Hoeij
  @test length(factor(t)) == 1
  @test length(factor(t^10)) == 1

  # Now the same with non-nice defining polynomial

  for i in 1:10
    n = rand(1:10)
    d = rand(1:10)
    k, a = number_field(n//d * change_base_ring(FlintQQ, swinnerton_dyer(3, x)))
    kt, t = k["t"]
    g = swinnerton_dyer(8, x)
    @test length(factor((t^2-a)*(t^3-a-1))) == 2 #Trager
    @test length(factor((t^2-a)*(t^3-a-1)*(t+a^2+1)*(t^5+t+a))) == 4 #Zassenhaus
    @test length(factor(change_base_ring(k, g))) == 8 # van Hoeij
    @test length(factor(t)) == 1
    @test length(factor(t^10)) == 1
  end

  K, a = number_field(x - 1, "a")
  Kt, t = K["t"]
  f = t^5 -3 * t^4 - 104 * t^3 + 312 * t^2 + 400*t -1200
  @test length(factor(f)) == 5
  @test length(factor(f*t)) == 6

  for i in 1:10
    n = rand(1:10)
    d = rand(1:10)
    K, a = number_field(n//d * change_base_ring(FlintQQ, x - 1), "a")
    Kt, t = K["t"]
    f = t^5 -3 * t^4 - 104 * t^3 + 312 * t^2 + 400*t -1200
    @test length(factor(f)) == 5
    @test length(factor(f*t)) == 6

    K, a = number_field(change_base_ring(FlintQQ, x) - n//d, "a")
    Kt, t = K["t"]
    f = t^5 -3 * t^4 - 104 * t^3 + 312 * t^2 + 400*t -1200
    @test length(factor(f)) == 5
    @test length(factor(f*t)) == 6
  end

  #Tommys
  K, a = number_field(x^2 - x - 4)
  Ky, y = K["y"]
  f = y^16+(39)*y^14+(449)*y^12+(1794)*y^10+(2830)*y^8+(1794)*y^6+(449)*y^4+(39)*y^2+(1)
  @test length(factor(f)) == 2

  # Dan's example #76
  K, a = number_field(x^2 + x + 1, cached = false);
  Kt, t = K["t"]
  g = t^4-t^3-t+(1)
  @test length(factor(g)) == 3

  f = x^4 + 24*x^2+28
  K, a = number_field(f, "a", cached = false);
  g = x^8-1
  @test length(factor(K, g)) == 4

  K, a = number_field(x^3 - 2, "a")
  Kx, x = polynomial_ring(K, "x")
  fa = factor(x^4+(1//2*a^2 + 1*a + 2)*x^3+(a^2 + 2*a + 2)*x^2+(1//2*a^2 + 1*a + 2)*x+1)
  @test length(fa) == 3

  # 1072
  R, x = polynomial_ring(QQ, "x");
  F, z = number_field(x^2+1);
  f = polynomial(F, [1, 2, 3])
  facts = factor(f)
  @test unit(facts) * prod(p^e for (p, e) in facts) == f
  facs = factor_squarefree(f)
  @test unit(facts) * prod(p^e for (p, e) in facts) == f
end

@testset "Root computation" begin
  Qx, x = QQ["x"]
  f = x^3-39*x-65
  K, a = number_field(f, "a")
  r = @inferred roots(K, f)
  @test length(r) == 3
  @test all(iszero, (f(b) for b in r))
end

@testset "Norm of factored element" begin
  Qx, x = QQ["x"]
  f = x^3 - 2
  K, a = number_field(f, "a")
  Kt, t = K["t"]
  L, b = number_field(x^6 - 6*x^4 - 4*x^3 + 12*x^2 - 24*x - 4)
  h = hom(K, L, -12//155*b^5 - 9//310*b^4 + 16//31*b^3 + 78//155*b^2 - 76//155*b + 182//155)
  z = -3*b^5 - 4*b^3 + 3*b^2 + 6*b + 2
  @test norm(h, z) == 1620*a^2 - 3342*a + 1120
  @test evaluate(norm(h, FacElem(z))) == evaluate(FacElem(K, Dict(1620*a^2 - 3342*a + 1120 => 1)))
  @test evaluate(norm(h, FacElem(L))) == evaluate(FacElem(K))
end
