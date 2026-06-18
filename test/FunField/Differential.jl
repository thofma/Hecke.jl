import Hecke: divisor

@testset "Differentials" begin
  @testset "Differential basic operations" begin
    for base_field in [QQ, finite_field(2, 4)[1], finite_field(5, 2)[1], finite_field(101)[1]]
      kx, x = rational_function_field(base_field, :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)
      for poly in [y^3 - x - 1, y^3 - x^3 - 1, y^3 - x^17 - 1]
        F, a = function_field(poly; cached = false)
        @test is_zero(differential(one(F)))

        dx = @inferred differential(F(x))
        dy = @inferred differential(a)
        @test dx != dy
        @test is_one(dx.f)
        @test !is_zero(divisor(dx))
        @test !is_zero(divisor(dy))

        @test differential(F(x) + a)    == @inferred(dx + dy)
        @test differential(F(x) - a)    == @inferred(dx - dy)
        @test differential(F(x) * a)    == @inferred(a*dx + F(x)*dy)
        @test differential(F(x) // a)   == @inferred((a*dx - F(x)*dy) // a^2)
        @test differential(F(x)^3) // 3 == @inferred((F(x)^2)*dx)
        @test differential(F(x)^3)      == @inferred(3*(F(x)^2)*dx)
      end
    end
  end

  @testset "Elliptic Curve Differentials" begin
    # General idea: for elliptic curves we can compute invariant differential "by the book"
    # we test that it generates zero divisor
    # further, the space of differentials is one-dimensional
    # so we can check the basis in the same way, AND check that the ratio of
    #   basis element and invariant differential is a constant
    function _test_basis_of_differentials(F, w)
      B = @inferred basis_of_differentials(F)
      @test length(B) == 1
      @test is_zero(divisor(B[1]))

      mult = @inferred B[1] // w
      @test !is_zero(mult)
      # the current implementation of is_zero checks that the ideal is 1*O
      #   and will return false for ideals u*O for a *unit* u not equal to 1
      # thus we go through the support
      # TODO: fix is_zero implementation of Divisor
      # @test is_zero(divisor(mult))
      @test isempty(support(divisor(mult)))
    end

    BF, t = finite_field(2, 4)
    kx, x = rational_function_field(BF, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)

    # ordinary characteristic 2: w = dx/x
    F, a = function_field(y^2 + x*y + x^3 + x^2 + t^2+1; cached = false)

    dx = differential(F(x))
    @test !is_zero(divisor(dx))
    w = dx // F(x)
    @test is_zero(divisor(w))
    _test_basis_of_differentials(F, w)

    # supersingular characteristic 2: w = dx/a_3
    F, a = function_field(y^2 + (t^3+1)*y + x^3 + x + 1; cached = false)

    dx = differential(F(x))
    @test is_zero(divisor(dx))
    w = dx // F(t^3+1)
    @test is_zero(divisor(w))
    _test_basis_of_differentials(F, w)

    # characteristic 3: w = dx/(-y) = - dy/(a_2*x - a_4)
    BF, t = finite_field(3, 2)
    kx, x = rational_function_field(BF, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    F, a = function_field(y^2 - x^3 - t*x^2 - t^2*x - 1; cached = false)

    dx = differential(F(x))
    @test !is_zero(divisor(dx))
    dy = differential(a)
    @test !is_zero(divisor(dy))

    w = dx // (-a)
    @test is_zero(divisor(w))
    w = - dy // (F(t*x) - F(t^2))
    @test is_zero(divisor(w))
    _test_basis_of_differentials(F, w)

    # characteristic > 3: w = dx/(2*y) = dy/(3*x^2 + A)
    BF, t = finite_field(7, 2)
    kx, x = rational_function_field(BF, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    F, a = function_field(y^2 - x^3 - t^4*x - 1; cached = false)

    dx = differential(F(x))
    @test !is_zero(divisor(dx))
    dy = differential(a)
    @test !is_zero(divisor(dy))

    w = dx // (2*a)
    @test is_zero(divisor(w))
    _test_basis_of_differentials(F, w)
    w = dy // (3*F(x)^2 + F(t^4))
    @test is_zero(divisor(w))

    # characteristic = 0: w = dx/(2*y) = dy/(3*x^2 + A)
    kx, x = rational_function_field(QQ, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    F, a = function_field(y^2 - x^3 - 3*x - 1; cached = false)

    dx = differential(F(x))
    @test !is_zero(divisor(dx))
    dy = differential(a)
    @test !is_zero(divisor(dy))

    w = dx // (2*a)
    @test is_zero(divisor(w))
    w = dy // (3*F(x)^2 + 3)
    @test is_zero(divisor(w))
    _test_basis_of_differentials(F, w)
  end

  @testset "Curve Differentials and genus" begin
    # Check for the basis of differentials:
    # length should equal genus
    # elements of basis should be non-zero, give effective divisor of a specific degree
    function _test_basis_of_differentials(F, g)
      B = @inferred basis_of_differentials(F)
      @test length(B) == g
      for b in B
        @test !is_zero(b)
        D = @inferred divisor(b)
        @test degree(D) == 2*g - 2
        @test is_effective(D)
      end
    end

    # genus 1, ramification at infinity = 3
    let (kx, x) = rational_function_field(GF(5), :x; cached = false),
        (ky, y) = polynomial_ring(kx, :y; cached = false)
      F, a = function_field(y^3 - x^2 - 1; cached = false)
      @test genus(F) == 1
      _test_basis_of_differentials(F, 1)
    end

    # genus 1, ramification at infinity = 3 (wild)
    let (kx, x) = rational_function_field(GF(3), :x; cached = false),
        (ky, y) = polynomial_ring(kx, :y; cached = false)
      F, a = function_field(y^3 + y - x^2 - 1; cached = false)
      @test genus(F) == 1
      _test_basis_of_differentials(F, 1)
    end

    # genus 2
    for base_field in [QQ, finite_field(3, 3)[1], finite_field(7, 2)[1], finite_field(101)[1]]
      kx, x = rational_function_field(base_field, :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)
      F, a = function_field(y^2 - x^5 - 1; cached=false)
      @test genus(F) == 2
      _test_basis_of_differentials(F, 2)
    end

    # genus 2, unramified at infinity
    let (kx, x) = rational_function_field(QQ, :x; cached = false),
        (ky, y) = polynomial_ring(kx, :y; cached = false)
      F, a = function_field(y^2 - x^6 - 2; cached = false)
      @test genus(F) == 2
      @test degree(discriminant(infinite_maximal_order(F))) == 0
      _test_basis_of_differentials(F, 2)
    end

    # genus 3
    for base_field in [QQ, finite_field(3, 3)[1], finite_field(5, 2)[1], finite_field(101)[1]]
      kx, x = rational_function_field(base_field, :x; cached = false)
      ky, y = polynomial_ring(kx, :y; cached = false)
      F, a = function_field(y^2 - x^7 - 1; cached=false)
      @test genus(F) == 3
      _test_basis_of_differentials(F, 3)
    end

    # characteristic 2
    let (BF, t) = finite_field(2, 4),
        (kx, x) = rational_function_field(BF, :x; cached = false),
        (ky, y) = polynomial_ring(kx, :y; cached = false)
      for (p, g) in [(y^2 + y + x^5 + 1, 2), (y^2 + y + x^7 + 1, 3), (y^2 + (x + t)*y + x^5 + x^3, 2)]
        F, a = function_field(p; cached=false)
        @test genus(F) == g
        _test_basis_of_differentials(F, g)
      end
    end

    # non-monic defining polynomial
    let (kx, x) = rational_function_field(QQ, :x; cached = false),
        (ky, y) = polynomial_ring(kx, :y; cached = false)
      F, a = function_field(x^3 + x^2 + x*y^3 - x*y^2 + y^2 - y; cached = false)
      @test genus(F) == 3
      _test_basis_of_differentials(F, 3)
    end
  end
end
