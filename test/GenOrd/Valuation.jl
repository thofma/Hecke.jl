@testset "Valuations at prime ideals of orders over general PID" begin
  # Valuations via the valuation function of a prime (anti-uniformizer and
  #   representation matrix) agree with the valuation via ideal arithmetic,
  #   and satisfy the defining properties of a discrete valuation.

  function test_valuations(O, P, elts)
    a = anti_uniformizer(P)
    @test valuation(a, P) == -1
    @test valuation(inv(a), P) == 1
    for b in elts
      is_zero(b) && continue
      v = @inferred valuation(b, P)
      @test v == Hecke.valuation_naive(b, P)
      # negative powers of function field elements are not implemented
      c = v >= -1 ? b * a^(v + 1) : b * inv(a)^(-v - 1)
      @test valuation(c, P) == -1
      @test valuation(inv(b), P) == -v
      for c in elts
        is_zero(c) && continue
        @test valuation(b * c, P) == v + valuation(c, P)
        if !is_zero(b + c)
          @test valuation(b + c, P) >= min(v, valuation(c, P))
        end
      end
      bn = numerator(b, O)
      if !is_zero(bn)
        I = ideal(O, bn)
        @test @inferred(valuation(I, P)) == Hecke.valuation_naive(I, P)
        @test valuation(O(bn), P) == valuation(I, P)
      end
    end
  end

  function test_ideal_valuations(O, P, Q)
    e = ramification_index(P)
    p = minimum(P)
    @test valuation(p, P) == e
    @test valuation(p^3 * (p + 1), P) == 3 * e
    A = P^3 * Q
    @test valuation(A, P) == 3 + (P == Q ? 1 : 0)
    @test valuation(A, P) == Hecke.valuation_naive(A, P)
    # ideal given by a basis only
    B = ideal(O, basis_matrix(A))
    @test !Hecke.has_2_elem(B)
    @test valuation(B, P) == valuation(A, P)
    # fractional ideal
    C = fractional_ideal(A, p^2)
    @test valuation(C, P) == valuation(A, P) - 2 * e
    @test valuation(ideal(O, one(O)), P) == 0
  end

  function test_order(O, ps, elts)
    for p in ps
      lp = prime_decomposition(O, O.R(p))
      for (P, _) in lp
        test_valuations(O, P, elts)
        for (Q, _) in lp
          test_ideal_valuations(O, P, Q)
          Q === P && continue
          # the anti-uniformizer of P is a unit at the other primes over p
          @test valuation(anti_uniformizer(P), Q) == 0
        end
      end
    end
  end

  @testset "over F_2(x), ramified and inert primes" begin
    kx, x = rational_function_field(GF(2), :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    L, t = function_field(y^3 - x^3 - 1; cached = false)
    Ofin = finite_maximal_order(L)
    Oinf = infinite_maximal_order(L)
    elts = [L(x), t, t + 1, t^2 + t + 1, (t + x)//L(x^2 + x + 1),
            x^3*t^2//(t + 1)^2, L(1//x)]
    test_order(Ofin, [x, x + 1, x^2 + x + 1, x^4 + x + 1], elts)
    test_order(Oinf, [1//x], elts)
  end

  @testset "over F_7(x), hyperelliptic" begin
    kx, x = rational_function_field(GF(7), :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    L, t = function_field(y^2 - x^5 - 3*x + 1; cached = false)
    Ofin = finite_maximal_order(L)
    Oinf = infinite_maximal_order(L)
    elts = [L(x), t, t - 1, (t + x^2)//L(x - 2), t^3//L(x^2 + 1), L(x^3 + 1)]
    ps = [x, x - 2, x^2 + 1, x^5 + 4*x + 1]
    test_order(Ofin, ps, elts)
    test_order(Oinf, [1//x], elts)
  end

  @testset "over F_5(x), singular plane model" begin
    kx, x = rational_function_field(GF(5), :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    # x divides the index of the equation order: x splits completely in the
    #   first field and is totally ramified in the second
    for f in (y^3 - x^2*(x + 1)*y - x^5, y^3 + x^2*y^2 + x^5 + x^4)
      L, t = function_field(f; cached = false)
      Ofin = finite_maximal_order(L)
      Oinf = infinite_maximal_order(L)
      @test divides(Hecke.index(Ofin), Ofin.R(x))[1]
      elts = [L(x), t, t//L(x), t^2//L(x^3) + t, (t + 1)//L(x + 1)]
      test_order(Ofin, [x, x + 1, x + 2], elts)
      test_order(Oinf, [1//x], elts)
    end
  end

  @testset "over Q(x)" begin
    Qx, x = rational_function_field(QQ, :x; cached = false)
    Qxy, y = polynomial_ring(Qx, :y; cached = false)
    L, t = function_field(y^2 - x^3 + 2; cached = false)
    Ofin = finite_maximal_order(L)
    Oinf = infinite_maximal_order(L)
    elts = [L(x), t, (t + 3)//L(x - 3), t^3//L(x^2)]
    test_order(Ofin, [x, x - 3, x^3 - 2], elts)
    test_order(Oinf, [1//x], elts)
  end

  @testset "edge cases" begin
    kx, x = rational_function_field(GF(3), :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    L, t = function_field(y^2 - x^3 - x; cached = false)
    O = finite_maximal_order(L)
    P = prime_decomposition(O, O.R(x))[1][1]
    @test_throws ArgumentError valuation(zero(L), P)
    @test_throws ArgumentError valuation(zero(O.R), P)
    @test valuation(one(L), P) == 0
    @test valuation(L(x + 1), P) == 0
    # deepcopy does not copy the valuation function
    @test valuation(t, P) == 1
    Q = deepcopy(P)
    @test valuation(t, Q) == 1
    # non-maximal orders use the fallback
    OL = Hecke.GenOrd(O, identity_matrix(kx, 2), one(kx))
    @test !Hecke.is_maximal_known_and_maximal(OL)
    PL = prime_decomposition(OL, OL.R(x + 1))[1][1]
    @test !Hecke._has_valuation_function(PL)
    @test valuation(ideal(OL, OL(t)), PL) == 0
    @test valuation(ideal(OL, OL(x + 1)), PL) == ramification_index(PL)
  end
end
