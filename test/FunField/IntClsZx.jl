@testset "IntClsZx" begin
  function _test_integral_closure(O::Hecke.GenOrd{T, ZZPolyRing}, F::T) where T <: Field
    Zx = Hecke.Globals.Zx

    # basis rank
    b = basis(O, F)
    @test length(b) == degree(F)

    # basis elements are integral: check if minpoly is integral over Z[x]
    for bi in b
      f = minpoly(bi)
      @test all(c -> isone(denominator(c, Zx)), coefficients(f))
    end

    # discriminant(equation order) = square * discriminant(maximal order)
    kx = base_field(F)
    R_eq = parent(numerator(gen(kx)))
    O_eq = Hecke.GenOrd(R_eq, F)
    ef = discriminant(O_eq)
    of = kx( change_base_ring(QQ, discriminant(O), parent=R_eq) )
    @test is_square(divexact(ef, of))

    # For a in maximal order and b in equation order, ab is in maximal order,
    # so that Tr(ab) is in equation order and a is in the codifferent of equation order
    # Then a*f'(gen) is in equation order
    fp = derivative(defining_polynomial(F))(gen(F))
    for bi in b
      @test all(x -> isone(denominator(x, Zx)), coordinates(bi*fp, O_eq))
    end
  end

  kx, x = rational_function_field(QQ, :x; cached=false)
  ky, y = polynomial_ring(kx, :y; cached=false)
  X = gen(Hecke.Globals.Zx)

  # elliptic curve: y^2 = x^3+1
  F, a = function_field(y^2 - x^3 - 1, :a; cached=false)
  O = Hecke.integral_closure(Hecke.Globals.Zx, F)
  _test_integral_closure(O, F)
  # for elliptic curve the integral closure is "trivial" 1*Z[x] + y*Z[x]
  @test basis(O) == [O(one(F)), O(a)]
  # maximal order is equation order
  @test discriminant(O) == 4*(X^3 + 1)

  # hyperelliptic curve of genus 2: y^2 = x^6 + x + 1
  F, a = function_field(y^2 - x^6 - x - 1, :a; cached=false)
  O = Hecke.integral_closure(Hecke.Globals.Zx, F)
  _test_integral_closure(O, F)
  # x^6 + x + 1 is monic having squarefree discriminant -1 * 101 * 431
  # the integral closure is "trivial" 1*Z[x] + y*Z[x]
  @test basis(O) == [O(one(F)), O(a)]
  # maximal order is equation order
  @test discriminant(O) == 4*(X^6 + X + 1)

  # hyperelliptic curve of genus 1: y^2 = x^5 + x^3 + x^2
  # y^2 = x^2(x^3 + x + 1) -> y/x is integral; discriminant is -4*x^2(x^3+x+1)
  # we expect the basis [1, y/x], and discriminant 4(x^3+x+1)
  F, a = function_field(y^2 - x^5 - x^3 - x^2, :a; cached=false)
  O = Hecke.integral_closure(Hecke.Globals.Zx, F)
  _test_integral_closure(O, F)
  @test basis(O) == [O(one(F)), O(a//F(x))]
  @test discriminant(O) == 4*(X^3 + X + 1)

  # hyperelliptic curve of genus 2: y^2 = x^7 + x^3 + x^2
  # y^2 = x^2(x^5 + x + 1) -> y/x is integral; discriminant is -4*x^2(x^5+x+1)
  # we expect the basis [1, y/x], and discriminant 4(x^5+x+1)
  F, a = function_field(y^2 - x^7 - x^3 - x^2, :a; cached=false)
  O = Hecke.integral_closure(Hecke.Globals.Zx, F)
  _test_integral_closure(O, F)
  @test basis(O) == [O(one(F)), O(a//F(x))]
  @test discriminant(O) == 4*(X^5 + X + 1)

  F, a = function_field(y^6 + 27*x^2 + 108*x + 108, :a; cached=false)
  O = Hecke.integral_closure(Hecke.Globals.Zx, F)
  _test_integral_closure(O, F)

  F, a = function_field(y^6 + (140*x - 70)*y^3 + 8788*x^2 - 8788*x + 2197, :a; cached=false)
  O = Hecke.integral_closure(Hecke.Globals.Zx, F)
  _test_integral_closure(O, F)
end
