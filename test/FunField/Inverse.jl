@testset "Inverse" begin
  # The modular inverse agrees with AbstractAlgebra's generic inverse.
  generic_inv(a) = invoke(inv, Tuple{Generic.AbsSimpleFunctionFieldElem}, a)

  function test_inverses(F, elts)
    for a in elts
      is_zero(a) && continue
      b = inv(a)
      @test isone(a * b)
      @test b == generic_inv(a)
      @test is_zero(Hecke._inv_modular(a) - b)
    end
  end

  # prime fields: large p, non-monic f, denominators
  for (k, monic) in ((GF(10007), true), (GF(10007), false),
                     (Native.GF(2^62 - 57), true))
    kt, t = rational_function_field(k, :t)
    ktx, x = kt[:x]
    lc = monic ? one(kt) : t^2 + 1
    F, a = function_field(lc * x^3 + t * x^2 + (t^3 + 1) * x + t + 2, :a)
    test_inverses(F, [a, a + 1, (t^4 + 2) * a^2 + t * a + 1,
                      (a^2 + t) // F(t^2 + t + 1), F(t^5 + 1), F(3)])
  end
  # GF(3): F_3 has too few points, the generic algorithm is used
  kt, t = rational_function_field(GF(3), :t)
  ktx, x = kt[:x]
  F, a = function_field(x^3 + t * x + t^2 + 1, :a)
  @test Hecke._inv_modular(t^5 * a^2 + a + 1) === nothing
  @test isone((t^5 * a^2 + a + 1) * inv(t^5 * a^2 + a + 1))
  # non-prime finite fields are not covered
  kt, t = rational_function_field(GF(5, 2), :t)
  ktx, x = kt[:x]
  F, a = function_field(x^2 + t, :a)
  @test Hecke._inv_modular(a + 1) === nothing
  @test isone((a + 1) * inv(a + 1))

  # rationals, including coefficients needing many primes
  Qt, t = rational_function_field(QQ, :t)
  Qtx, x = Qt[:x]
  F, a = function_field(2 * x^4 + t * x - 1//3, :a)
  test_inverses(F, [a, (t^2 - 1//7) * a^2 + 5 * a,
                    (a + t) // F(t^3 + 2),
                    ZZ(10)^40 * a^2 + (ZZ(3)^50 * t - 1) * a + ZZ(7)^30])

  # the first prime of the multimodular algorithm divides lc_y(f)
  p = first(PrimesSet(Hecke.p_start, -1))
  F, a = function_field(p * x^4 + t * x - 1, :a)
  test_inverses(F, [a^2 + t * a + 1, (t^3 + 1) * a^3 + a])

  # extensions of Q(t) of degree <= 3 use the generic algorithm
  F, a = function_field(x^3 - t^3 - 1//2, :a)
  @test Hecke._inv_modular(a + t) === nothing
  @test isone((a + t) * inv(a + t))

  # number fields: monic integral defining polynomial, and a fallback
  Qs, s = QQ[:s]
  for g in (s^2 + 1, s^3 - 2)
    K, b = number_field(g, :b)
    Kt, t = rational_function_field(K, :t)
    Ktx, x = Kt[:x]
    F, a = function_field(x^3 + b * t * x + t^2 - b, :a)
    test_inverses(F, [a, (b * t + 1//2) * a^2 + a - b, (a + b) // F(t + b)])
  end
  K, b = number_field(2 * s^2 - 3, :b)
  Kt, t = rational_function_field(K, :t)
  Ktx, x = Kt[:x]
  F, a = function_field(x^2 + b * t, :a)
  @test Hecke._inv_modular(a + b) === nothing
  @test isone((a + b) * inv(a + b))

  # zero is passed on to the generic algorithm
  z = zero(F)
  outcome(f) = try f(z) catch e typeof(e) end
  @test outcome(inv) == outcome(generic_inv)
end
