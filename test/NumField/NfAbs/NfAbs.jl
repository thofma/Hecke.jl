@testset "NumField/NfAbs/NfAbs" begin
  cyclo_expl = function(n, m)
    Fn, zn = CyclotomicField(n)
    Fnm, znm = CyclotomicField(n*m)
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

  Qx, x = PolynomialRing(FlintQQ, "x")
  f = x^3-2
  K = splitting_field(f)
  @test typeof(K) == AnticNumberField
  K1 = number_field([x^3-2, x^2+x+1])[1]
  K1abs = simple_extension(K1)[1]
  @test is_isomorphic(K, K1abs)
  K, R = splitting_field(f, do_roots = true)
  for r in R
    @test iszero(f(r))
  end

  K, a = number_field(x^2+1)
  Kt, t = PolynomialRing(K, "t")
  g = t^4-2
  L = splitting_field(g)
  @test typeof(L) == Hecke.NfRel{nf_elem}
  @test absolute_degree(L) == 8
end

@testset "simplify" begin

  Qx, x = PolynomialRing(FlintQQ, "x")
  K = number_field(x^5 - x^4 - x^3 - 220*x^2 - 360*x - 200)[1]
  @test typeof(K) == AnticNumberField
  L = simplify(K, canonical = true)[1]
  @test L.pol == x^5 - x^4 + x^3 - 19*x^2 + 35*x + 77
end

@testset "simplify-Gunter" begin

  Qx, x = PolynomialRing(FlintQQ, "x")
  f = x^18 - x^16 - 6*x^14 - 4*x^12 - 4*x^10 + 2*x^8 + 6*x^6 - 4*x^4 + 3*x^2 - 1
  g = x^18 - 3*x^16 + 4*x^14 - 6*x^12 - 2*x^10 + 4*x^8 + 4*x^6 + 6*x^4 + x^2 - 1
  h = x^18 + x^16 - x^14 - 8*x^12 - 3*x^8 + 27*x^6 - 25*x^4 + 8*x^2 - 1
  @test simplify(number_field(f)[1], canonical = true)[1].pol == g
  @test simplify(number_field(g)[1], canonical = true)[1].pol == g
  @test simplify(number_field(h)[1], canonical = true)[1].pol == g
end
