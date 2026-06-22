import Hecke: divisor

in_RR(f, D) = is_zero(f) || is_effective(divisor(f) + D)

function test_rr_simple(D, RR)
  for f in RR
    @test in_RR(f, D)
  end
  # TODO: it might make sense to test linear independence

  g = genus(function_field(D))

  # Riemann-Roch: l(D) - l(K-D) = deg(D) - g + 1
  @test dimension(D) - index_of_speciality(D) == degree(D) + 1 - g

  if degree(D) < 0
    @test length(RR) == 0
  end

  if degree(D) > 2*g - 2
    @test length(RR) == degree(D) + 1 - g
  end
end

function test_RR_dim1_with_generator(RR, f)
  @test length(RR) == 1
  @test is_zero(divisor(f * inv(RR[1])))
end

function test_RR_for_one_place(P)
  for m in (-10, -2, 2, 10)
    D = m*P
    test_rr_simple(D, riemann_roch_space(D))
  end
end

function test_RR_for_principal_divisor(f)
  D = divisor(f)
  test_RR_dim1_with_generator(riemann_roch_space(D), inv(f))
end

function test_divisors_different_degree(Ofin, x, a, O)
  p1, _ = @inferred first(factor(ideal(Ofin, x - 1)))
  p2, _ = @inferred first(factor(ideal(Ofin, a + 1)))
  D1, D2 = divisor(p1), divisor(p2)

  D = -pole_divisor(inv(a))   # negative degree
  test_rr_simple(D, riemann_roch_space(D))
  D = 5*zero_divisor(a^2)     # degree bigger than 2g - 2
  test_rr_simple(D, riemann_roch_space(D))
  D = 3*D1 - D2 + 2*O         # mixed degree
  test_rr_simple(D, riemann_roch_space(D))
end

@testset "Riemann-Roch" begin
  @testset "Elliptic Curve over F_5" begin
    kx, x = rational_function_field(GF(5), :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    F, a = function_field(y^2 - x^3 - x - 1; cached = false)
    Ofin = @inferred finite_maximal_order(F)
    Oinf = @inferred infinite_maximal_order(F)

    @test genus(F) == 1
    @test dimension(canonical_divisor(F)) - dimension(trivial_divisor(F)) == 0

    pinf, _ = first(factor(ideal(Oinf, base_ring(Oinf)(1//x))))
    O = divisor(pinf)

    # (x)_inf = 2*O, (y)_inf = 3*O
    @test pole_divisor(F(x)) == 2*O
    @test pole_divisor(a) == 3*O

    # basis of L(mO) is {x^k, 2k <= m} + {x^k*y,  2k+3 <= m}
    for (m, d) in [(0, 1), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5)]
      D = m*O
      RR = riemann_roch_space(D)
      @test length(RR) == d
      test_rr_simple(D, RR)
    end

    # for P = (0, 1), Q = (0,4) we have (x) = P + Q - 2*O
    P = divisor(ideal(Ofin, x, Ofin(y-1)))
    Q = divisor(ideal(Ofin, x, Ofin(y-4)))

    # for elliptic curves: g = 1 and canonical divisor is trivial
    # giving for D with degree 0: l(D) = l(-D)
    # for principal D (tested above) this gives dimension 1
    # for non-principal this gives l(D) = 0
    @test dimension(P - O) == 0

    # L(2*O) = [1, x] and x(P) = 0
    D = 2*O - P
    RR = riemann_roch_space(D)
    test_RR_dim1_with_generator(RR, x)

    # L(3*O) = [1, x, y], vanishing at P gives [x, y-1]
    D = 3*O - P
    RR = riemann_roch_space(D)
    test_rr_simple(D, RR)
    @test length(RR) == 2

    test_divisors_different_degree(Ofin, x, a, O)
    test_RR_for_one_place(P)
    test_RR_for_principal_divisor(F(x))
  end

  @testset "Hyperelliptic Curve over F_3" begin
    kx, x = rational_function_field(GF(3), :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    # has no finite affine points
    F, a = function_field(y^2 - x^5 - 2*x^4 - 2*x^3 - x^2 - 2; cached = false)
    Ofin = @inferred finite_maximal_order(F)
    Oinf = @inferred infinite_maximal_order(F)

    @test genus(F) == 2
    @test dimension(canonical_divisor(F)) - dimension(trivial_divisor(F)) == 1

    pinf, _ = first(factor(ideal(Oinf, base_ring(Oinf)(1//x))))
    O = divisor(pinf)

    # (x)_inf = 2*O, (y)_inf = 5*O
    @test pole_divisor(F(x)) == 2*O
    @test pole_divisor(a) == 5*O

    # basis of L(mO) is {x^k, 2k <= m} + {x^k*y,  2k+5 <= m}
    for (m, d) in [(0, 1), (1, 1), (2, 2), (3, 2), (4, 3), (5, 4), (6, 5)]
      D = m*O
      RR = riemann_roch_space(D)
      @test length(RR) == d
      test_rr_simple(D, RR)
    end

    u = F(x^2) + 1

    # P1, P2 are conjugate degree 2 places
    # (x^2 + 1) = P1 + P2 - 4*O
    P1 = divisor(ideal(Ofin, x^2 + 1, Ofin(y - (x + 1))))
    P2 = divisor(ideal(Ofin, x^2 + 1, Ofin(y - (2*x + 2))))

    # L(2*O) = [1, x], no non-zero linear polynomial in x vanishes at P1
    @test dimension(2*O - P1) == 0

    # L(4*O) = [1, x, x^2], x^2+1 vanishes at P1
    D = 4*O - P1
    RR = riemann_roch_space(D)
    test_RR_dim1_with_generator(RR, u)

    test_divisors_different_degree(Ofin, x, a, O)
    test_RR_for_one_place(P1)
    test_RR_for_principal_divisor(u)
  end

  @testset "Hyperelliptic Curve over F_5" begin
    kx, x = rational_function_field(GF(5), :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    # has two points at infinity
    F, a = function_field(y^2 - x^6 - x - 1; cached = false)
    Ofin = @inferred finite_maximal_order(F)
    Oinf = @inferred infinite_maximal_order(F)

    @test genus(F) == 2
    @test dimension(canonical_divisor(F)) - dimension(trivial_divisor(F)) == 1

    # (x)_inf = O1 + O2
    inf_factor = collect(factor(ideal(Oinf, base_ring(Oinf)(1//x))))
    O1 = divisor(inf_factor[1][1])
    O2 = divisor(inf_factor[2][1])
    O = pole_divisor(F(x))
    @test O == O1 + O2

    # basis of L(m*(x)) is {x^k, k <= m} + {x^k*y,  k+3 <= m}
    for (m, d) in [(0, 1), (1, 2), (2, 3), (3, 5), (4, 7)]
      D = m*O
      RR = riemann_roch_space(D)
      @test length(RR) == d
      test_rr_simple(D, RR)
    end

    test_divisors_different_degree(Ofin, x, a, O1)
    test_RR_for_one_place(O2)
    test_RR_for_principal_divisor(F(x))
  end

  @testset "Non-monic Curve over F_5" begin
    kx, x = rational_function_field(GF(5), :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    F, a = function_field(x^3 + x^2 + x*y^3 - x*y^2 + y^2 - y; cached = false)
    Ofin = @inferred finite_maximal_order(F)
    Oinf = @inferred infinite_maximal_order(F)

    @test genus(F) == 3
    @test dimension(canonical_divisor(F)) - dimension(trivial_divisor(F)) == 2

    pinf, _ = first(factor(ideal(Oinf, base_ring(Oinf)(1//x))))
    O = divisor(pinf)
    Q = divisor(ideal(Ofin, x, Ofin(x*a + x + 1)))

    @test pole_divisor(F(x)) == 3*O
    @test pole_divisor(a) == 2*O + Q

    for (m, d) in [(0, 1), (1, 1), (2, 1), (3, 2), (4, 2), (5, 3), (6, 4), (7, 5)]
      D = m*O
      RR = riemann_roch_space(D)
      @test length(RR) == d
      test_rr_simple(D, RR)
    end

    b = F(x)^2*a
    @assert !(a in Ofin)
    @assert b in Ofin

    p1, _ = @inferred first(factor(ideal(Ofin, F(x) - 1)))
    p2, _ = @inferred first(factor(ideal(Ofin, b + 1)))
    D1, D2 = divisor(p1), divisor(p2)

    D = -pole_divisor(inv(F(x)))
    test_rr_simple(D, riemann_roch_space(D))
    D = 5*zero_divisor(F(x)^2)
    test_rr_simple(D, riemann_roch_space(D))
    D = 3*D1 - D2 + 2*O
    test_rr_simple(D, riemann_roch_space(D))

    test_RR_for_one_place(O)
    test_RR_for_principal_divisor(F(x))
  end

  @testset "Artin-Schreier Curve over F_2" begin
    kx, x = rational_function_field(GF(2), :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    # has wild ramification at infinity
    F, a = function_field(y^2 + y - x^5 - x; cached = false)
    Ofin = @inferred finite_maximal_order(F)
    Oinf = @inferred infinite_maximal_order(F)

    @test genus(F) == 2
    @test dimension(canonical_divisor(F)) - dimension(trivial_divisor(F)) == 1

    pinf, _ = first(factor(ideal(Oinf, base_ring(Oinf)(1//x))))
    O = divisor(pinf)

    # (x)_inf = 2*O, (y)_inf = 5*O
    @test pole_divisor(F(x)) == 2*O
    @test pole_divisor(a) == 5*O

    # basis of L(mO) is {x^k, 2k <= m} + {x^k*y,  2k+5 <= m}
    for (m, d) in [(0, 1), (1, 1), (2, 2), (3, 2), (4, 3), (5, 4), (6, 5)]
      D = m*O
      RR = riemann_roch_space(D)
      @test length(RR) == d
      test_rr_simple(D, RR)
    end

    test_divisors_different_degree(Ofin, x, a, O)
    test_RR_for_one_place(O)
    test_RR_for_principal_divisor(a)
  end

  @testset "Artin-Schreier Curve over F_3" begin
    kx, x = rational_function_field(GF(3), :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    # has wild ramification at infinity
    F, a = function_field(y^3 - y - x^4 - x^2 - x; cached = false)
    Ofin = @inferred finite_maximal_order(F)
    Oinf = @inferred infinite_maximal_order(F)

    @test genus(F) == 3
    @test dimension(canonical_divisor(F)) - dimension(trivial_divisor(F)) == 2

    pinf, _ = first(factor(ideal(Oinf, base_ring(Oinf)(1//x))))
    O = divisor(pinf)

    # (x)_inf = 3*O, (y)_inf = 4*O, canonical divisor is 4*O
    @test pole_divisor(F(x)) == 3*O
    @test pole_divisor(a) == 4*O
    @test canonical_divisor(F) == 4*O

    for (m, d) in [(0, 1), (1, 1), (2, 1), (3, 2), (4, 3), (5, 3), (6, 4), (7, 5)]
      D = m*O
      RR = riemann_roch_space(D)
      @test length(RR) == d
      test_rr_simple(D, RR)
    end

    test_divisors_different_degree(Ofin, x, a, O)
    test_RR_for_one_place(O)
    test_RR_for_principal_divisor(a-1)
  end

  @testset "Artin-Schreier Curve over F_5" begin
    kx, x = rational_function_field(GF(5), :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    # has wild ramification at infinity
    F, a = function_field(y^5 - y - x^3 - x; cached = false)
    Ofin = @inferred finite_maximal_order(F)
    Oinf = @inferred infinite_maximal_order(F)

    @test genus(F) == 4
    @test dimension(canonical_divisor(F)) - dimension(trivial_divisor(F)) == 3

    pinf, _ = first(factor(ideal(Oinf, base_ring(Oinf)(1//x))))
    O = divisor(pinf)

    # (x)_inf = 5*O, (y)_inf = 3*O, canonical divisor is 6*O
    @test pole_divisor(F(x)) == 5*O
    @test pole_divisor(a) == 3*O
    @test canonical_divisor(F) == 6*O

    for (m, d) in [(0, 1), (1, 1), (2, 1), (3, 2), (4, 2), (5, 3), (6, 4), (7, 4)]
      D = m*O
      RR = riemann_roch_space(D)
      @test length(RR) == d
      test_rr_simple(D, RR)
    end

    test_divisors_different_degree(Ofin, x, a, O)
    test_RR_for_one_place(O)
    test_RR_for_principal_divisor(a-1)
  end

  @testset "Superelliptic Curve over Q" begin
    kx, x = rational_function_field(QQ, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    F, a = function_field(y^3 - x^5 - 1; cached = false)
    Ofin = @inferred finite_maximal_order(F)
    Oinf = @inferred infinite_maximal_order(F)

    @test genus(F) == 4
    @test dimension(canonical_divisor(F)) - dimension(trivial_divisor(F)) == 3

    pinf, _ = first(factor(ideal(Oinf, base_ring(Oinf)(1//x))))
    O = divisor(pinf)

    p1, _ = @inferred first(factor(ideal(Ofin, x - 13)))
    p2, _ = @inferred first(factor(ideal(Ofin, a - 2)))
    D1, D2 = divisor(p1), divisor(p2)

    for (m, d) in [(0, 1), (1, 1), (2, 1), (3, 2), (4, 2), (5, 3), (6, 4), (7, 4)]
      D = m*O
      RR = riemann_roch_space(D)
      @test length(RR) == d
      test_rr_simple(D, RR)
    end

    test_divisors_different_degree(Ofin, x, a, O)
    test_RR_for_one_place(D2)
    test_RR_for_principal_divisor(a-1)
  end

  @testset "Superelliptic Curve over F_4" begin
    B = finite_field(2, 2; cached = false)[1]
    kx, x = rational_function_field(B, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    F, a = function_field(y^3 - x^5 - 1; cached = false)
    Ofin = @inferred finite_maximal_order(F)
    Oinf = @inferred infinite_maximal_order(F)

    @test genus(F) == 4
    @test dimension(canonical_divisor(F)) - dimension(trivial_divisor(F)) == 3

    pinf, _ = first(factor(ideal(Oinf, base_ring(Oinf)(1//x))))
    O = divisor(pinf)

    p1, _ = @inferred first(factor(ideal(Ofin, x - 1)))
    p2, _ = @inferred first(factor(ideal(Ofin, a - gen(B))))
    D1, D2 = divisor(p1), divisor(p2)

    for (m, d) in [(0, 1), (1, 1), (2, 1), (3, 2), (4, 2), (5, 3), (6, 4), (7, 4)]
      D = m*O
      RR = riemann_roch_space(D)
      @test length(RR) == d
      test_rr_simple(D, RR)
    end

    test_divisors_different_degree(Ofin, x, a, O)
    test_RR_for_one_place(D1)
    test_RR_for_principal_divisor(a-gen(B))
  end
end
