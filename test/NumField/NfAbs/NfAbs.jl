@testset "NumField/NfAbs/NfAbs" begin
  cyclo_expl = function(n, m)
    Fn, zn = cyclotomic_field(n)
    Fnm, znm = cyclotomic_field(n*m)
    x = zn
    x_up = Hecke.force_coerce_cyclo(Fnm, x)
    x_down = Hecke.force_coerce_cyclo(Fn, x_up)
    return (x, x_up, x_down)
  end

  res = cyclo_expl(3, 4)
  @test (res[1]^3, res[2]^3) == (1, 1)

  res = cyclo_expl(3, 2)
  z6 = gen(parent(res[2]))
  # Test that z3 is mapped to z6^2
  @test z6^2 == res[2]
end

@testset "Splitting Field" begin

  Qx, x = polynomial_ring(FlintQQ, "x")
  f = x^3-2
  K = splitting_field(f)
  @test typeof(K) == AbsSimpleNumField
  K1 = number_field([x^3-2, x^2+x+1])[1]
  K1abs = simple_extension(K1)[1]
  @test is_isomorphic(K, K1abs)
  K, R = splitting_field(f, do_roots = true)
  for r in R
    @test iszero(f(r))
    @test all(x->parent(x) === K, R)
  end

  K, a = number_field(x^2+1)
  Kt, t = polynomial_ring(K, "t")
  g = t^4-2
  L = splitting_field(g)
  @test typeof(L) == Hecke.RelSimpleNumField{AbsSimpleNumFieldElem}
  @test absolute_degree(L) == 8
end

@testset "simplify" begin

  Qx, x = polynomial_ring(FlintQQ, "x")
  K = number_field(x^5 - x^4 - x^3 - 220*x^2 - 360*x - 200)[1]
  @test typeof(K) == AbsSimpleNumField
  L = simplify(K, canonical = true)[1]
  @test L.pol == x^5 - x^4 + x^3 - 19*x^2 + 35*x + 77
end

@testset "simplify-Gunter" begin

  Qx, x = polynomial_ring(FlintQQ, "x")
  f = x^18 - x^16 - 6*x^14 - 4*x^12 - 4*x^10 + 2*x^8 + 6*x^6 - 4*x^4 + 3*x^2 - 1
  g = x^18 - 3*x^16 + 4*x^14 - 6*x^12 - 2*x^10 + 4*x^8 + 4*x^6 + 6*x^4 + x^2 - 1
  h = x^18 + x^16 - x^14 - 8*x^12 - 3*x^8 + 27*x^6 - 25*x^4 + 8*x^2 - 1
  @test simplify(number_field(f)[1], canonical = true)[1].pol == g
  @test simplify(number_field(g)[1], canonical = true)[1].pol == g
  @test simplify(number_field(h)[1], canonical = true)[1].pol == g
end

@testset "simplify-Fabian" begin
  Qx, x = polynomial_ring(FlintQQ, "x")
  f = x^8 + 4*x^7 - 56*x^6 - 168*x^5 + 758*x^4 + 2412*x^3 - 1656*x^2 - 9508*x - 6828
  g = x^8 - 4*x^7 - 30*x^6 + 44*x^5 + 298*x^4 + 108*x^3 - 614*x^2 - 680*x - 199
  @test simplify(number_field(f)[1], canonical = true)[1].pol == g
  @test simplify(number_field(g)[1], canonical = true)[1].pol == g
end


@testset "factor-van-Hoeij" begin
 Qx, x = polynomial_ring(FlintQQ, "x")
 f = x^12 + 4*x^10 + 11*x^8 + 4*x^6 - 41*x^4 - 8*x^2 + 37
 K, a = number_field(f)
 @test length(factor(K, f).fac) == 4
end

@testset "automorphisms" begin
  Qx, x = QQ["x"]
  K, a = number_field([x^2 - 2, x^2 - 3], "a", cached = false)
  @test is_normal(K)
  @test length(automorphism_list(K)) == 4
  K, a = number_field([x^2 - 2, x^3 - 2], "a", cached = false)
  @test !is_normal(K)
  @test length(automorphism_list(K)) == 2
end
