@testset "coercion between cyclotomic fields" begin
  F2, z2 = CyclotomicField(2)
  @test Hecke.force_coerce_cyclo(F2, z2) == z2

  F1, z1 = CyclotomicField(1)
  up = Hecke.force_coerce_cyclo(F2, z1)
  @test Hecke.force_coerce_cyclo(F1, up) == z1

  choices = fmpz[collect(-5:5)...]

  # coerce first up and then down
  for n in 1:15
    Fn, zn = CyclotomicField(n)
    for m in 1:15
      nm = n*m
      Fnm, znm = CyclotomicField(nm)
      x = rand(Fn, choices)
      x_up = Hecke.force_coerce_cyclo(Fnm, x)
      x_down = Hecke.force_coerce_cyclo(Fn, x_up)
      @test x_down == x
    end
  end

  # coerce first down and then up
  for n in 1:15
    Fn, zn = CyclotomicField(n)
    for g in divisors(n)
      Fg, zg = CyclotomicField(g)
      for m in 1:15
        gm = g*m
        Fgm, zgm = CyclotomicField(gm)
        x = rand(Fg, choices)
        x_up = Hecke.force_coerce_cyclo(Fgm, x)
        x_n = Hecke.force_coerce_cyclo(Fn, x_up)
        @test x_n == Hecke.force_coerce_cyclo(Fn, x)
      end
    end
  end

  # impossible coercions
  for n in 1:45
    Fn, zn = CyclotomicField(n)
    for m in 1:45
      if n % m != 0 && ! (isodd(n) && (2*n) % m == 0)
        Fm, zm = CyclotomicField(m)
        @test_throws ErrorException Hecke.force_coerce_cyclo(Fn, zm)
        @test Hecke.force_coerce_cyclo(Fn, zm, Val{false}) == nothing
      end
    end
  end

  # equality check requiring the construction of a common superfield
  F5, z5 = CyclotomicField(5)
  F3, z3 = CyclotomicField(3)
  @test z5^5 == z3^3

  # splitting field
  QQx, x = PolynomialRing(Hecke.rationals_as_number_field()[1], "x", cached = false)
  f = x^2 + 1
  K, r = splitting_field([f], do_roots = true)
  @test issetequal(r, [gen(K), -gen(K)])
end
