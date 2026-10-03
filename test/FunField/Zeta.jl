@testset "L-polynomial" begin
  # counts of places of given degree is computed by sage:
  #   [len(F.places(i + 1)) for i in range(N)]
  # L polynomials are computed with sage when base field is the exact constants field:
  #   F.L_polynomial()
  # When base field is not the exact constants field, sage gives wrong answer

  Zt, t = polynomial_ring(ZZ, :t; cached = false)

  let (kx, x) = rational_function_field(GF(2), :x; cached = false),
      (ky, y) = polynomial_ring(kx, :y; cached = false)
    let (F, a) = function_field(y^3 - x^3 - 1; cached = false)
      counts = @inferred Hecke._fill_place_degree_counts(F, 6)
      @test counts == [3, 3, 2, 0, 6, 11]
      @test 2*t^2 + 1 == @inferred Hecke.L_polynomial(Zt, F)
    end

    let (F, a) = function_field(y^2 + y - x^5 - x; cached = false)
      counts = @inferred Hecke._fill_place_degree_counts(F, 6)
      @test counts == [5, 2, 0, 2, 4, 12]

      @test 4*t^4 + 4*t^3 + 4*t^2 + 2*t + 1 == @inferred Hecke.L_polynomial(Zt, F)
    end
  end

  let (kx, x) = rational_function_field(GF(5), :x; cached = false),
      (ky, y) = polynomial_ring(kx, :y; cached = false)
    let (F, a) = function_field(y^3 - x^2 - 1; cached = false)
      counts = @inferred Hecke._fill_place_degree_counts(F, 3)
      @test counts == [6, 15, 40]

      @test 5*t^2 + 1 == @inferred Hecke.L_polynomial(Zt, F)
    end

    let (F, a) = function_field(y^2 - x^6 - x - 1; cached = false)
      counts = @inferred Hecke._fill_place_degree_counts(F, 3)
      @test counts == [6, 15, 40]

      @test 25*t^4 + 5*t^2 + 1 == @inferred Hecke.L_polynomial(Zt, F)
    end

    let (F, a) = function_field(x^3 + x^2 + x*y^3 - x*y^2 + y^2 - y; cached = false)
      counts = @inferred Hecke._fill_place_degree_counts(F, 3)
      @test counts == [8, 10, 44]

      @test 125*t^6 + 50*t^5 + 15*t^4 + 8*t^3 + 3*t^2 + 2*t + 1 == @inferred Hecke.L_polynomial(Zt, F)
    end
  end

  let (kx, x) = rational_function_field(finite_field(2, 2)[1], :x; cached = false),
      (ky, y) = polynomial_ring(kx, :y; cached = false),
      (F, a) = function_field(y^5 - x^3 - 1; cached = false)
    counts = @inferred Hecke._fill_place_degree_counts(F, 4)
    @test counts == [5, 2, 20, 90]
    @test isempty(@inferred Hecke._fill_place_degree_counts(F, 0))

    @test 256*t^8 - 64*t^6 + 36*t^4 - 4*t^2 + 1 == @inferred Hecke.L_polynomial(Zt, F)
  end

  for K in [GF(5), GF(ZZ(5)), Native.GF(5), Native.GF(ZZ(5)),
            finite_field(5, 1, :a; cached = false)[1],
            finite_field(ZZ(5), 1, :a; cached = false)[1]]
    # we repeat the test above but now with varying base fields
    kx, x = rational_function_field(K, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    F, _ = function_field(y^3 - x^2 - 1; cached = false)

    counts = @inferred Hecke._fill_place_degree_counts(F, 3)
    @test counts == [6, 15, 40]

    @test 5*t^2 + 1 == @inferred Hecke.L_polynomial(Zt, F)
  end

  let (kx, x) = rational_function_field(GF(5), :x; cached = false),
      (ky, y) = polynomial_ring(kx, :y; cached = false)
    # F = F_{25}(x)
    let (F, a) = function_field(y^2 - 2; cached = false)
      @test one(Zt) == @inferred Hecke.L_polynomial(Zt, F)
    end

    # Consider k = F_q, k' = F_q(a) with a having minimal polynomial g of degree m,
    #   and hyperelliptic curve y^2 = a*f(x) over k'.
    # y is primitive, and g(y^2/f) = 0.
    # Substituting and clearing denominators we obtain monic of degree 2m over k(x)

    # g(t) = t^2 - 2, G = y^4 - 2*f^2
    # genus 1 over F_{25}
    # C(F_Q) = Q + 1 + c_1 => c_1 = C(F_Q) - 26 = -1
    let f = x^3 + x + 1,
        (F, a) = function_field(y^4 - 2*f^2; cached = false)
      @test constant_field_degree(F) == 2
      @test 25*t^2 - t + 1 == @inferred Hecke.L_polynomial(Zt, F)
    end

    # g(t) =  t^3 + t + 1, G = y^6 + f^2*y^2 + f^3
    # genus 1 over F_{125}
    # C(F_Q) = Q + 1 + c_1 => c_1 = C(F_Q) - 126 = -18
    let f = x^3 + x + 1,
        (F, a) = function_field(y^6 + f^2*y^2 + f^3; cached = false)
      @test constant_field_degree(F) == 3
      @test 125*t^2 - 18*t + 1 == @inferred Hecke.L_polynomial(Zt, F)
    end
  end
end
