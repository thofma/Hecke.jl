@testset "GenOrd" begin
  # Test first the ring interface
  Qx, x = QQ["x"]
  K, _ = number_field(x^3 - 18, "a")
  O = @inferred order(ZZ, K)
  @test O isa Hecke.GenOrd
  ConformanceTests.test_Ring_interface(O)

  k = GF(5)
  kx, x = rational_function_field(k, "x")
  kt = parent(numerator(x))
  ky, y = polynomial_ring(kx, "y")
  F, a = function_field(y^3+(4*x^3 + 4*x^2 + 2*x +2)*y^2 + (3*x+3)*y +2)
  Ofin = integral_closure(kt, F)

  # Promotion
  @test Ofin(one(k)) == one(Ofin)
  @test Ofin(one(kt)) == one(Ofin)
  @test Ofin(one(ZZ)) == one(Ofin)
  @test one(Ofin) + 1 == Ofin(2)
  @test one(Ofin) + one(k) == Ofin(2)
  @test one(Ofin) + one(kt) == Ofin(2)

  u = canonical_unit(one(Ofin))
  @test parent(u) === Ofin
  @test is_unit(u)

  let # some weird rings
    Qt,t = rational_function_field(QQ, :t)
    Qtx, x= Qt[:x]
    f = x^2-4*t^3-1
    F, a = function_field(f)
    Zx, x = ZZ[:x]
    O = integral_closure(Zx, F)
    @test length(basis(O)) == 2
  end
end

@testset "Trace matrix and codifferent" begin
  # for equation order O = R[a], different(O) = (f'(a)) and codifferent(O) = (1/f'(a))
  function check_equation_order_different(O, f)
    @assert is_equation_order(O)
    K = Hecke.field(O)
    fp_alpha = derivative(f)(gen(K))
    @test inv(codifferent(O)) == ideal(O, O(fp_alpha))
    @test 1//fp_alpha in @inferred codifferent(O)

    # simplistic check for public trace matrix api to agree
    @test @inferred(trace_matrix(O)) == @inferred(trace_matrix(basis(O)))
  end

  # for every r in the radical Tr(r * basis(O)) is in pR
  function check_radical_basis_trace(O, p)
    M = Hecke.radical_basis_trace(O, p)
    n = degree(O)

    _, mR = residue_field(parent(p), p)
    B = basis(O)
    for i = 1:n
      r = O([M[i, j] for j = 1:n])
      for k = 1:n
        @test iszero(mR(trace(r * B[k])))
      end
    end
  end

  @testset "number field over ZZ" begin
    x = gen(Hecke.Globals.Qx)
    f = x^2 + 5
    K, _ = number_field(f, :a; cached = false)

    O = order(ZZ, K)
    @assert is_equation_order(O)
    check_equation_order_different(O, f)
    check_radical_basis_trace(O, ZZ(5)) # p = 5: bigger than the degree and divides disc(O)
  end

  @testset "number field localization" begin
    x = gen(Hecke.Globals.Qx)
    f = x^2 + 5
    K, _ = number_field(f, :a; cached = false)
    R = Hecke.localization(ZZ, ZZ(5); cached = false)

    O = integral_closure(R, K)
    @assert is_equation_order(O)
    check_equation_order_different(O, f)
    check_radical_basis_trace(O, R(5)) # p = 5 bigger than the degree and ramified

    R = Hecke.localization(ZZ, ZZ(7); cached = false)
    O = integral_closure(R, K)
    @assert is_equation_order(O)
    check_equation_order_different(O, f)
  end

  @testset "function field over Q(t)" begin
    kx, x = rational_function_field(QQ, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    f = y^3 + x*y + (x^2 + 1)
    L, t = function_field(f; cached = false)

    O = Hecke.GenOrd(parent(numerator(x)), L)
    @assert is_equation_order(O)
    check_equation_order_different(O, f)

    fac = collect(factor(discriminant(O)))
    check_radical_basis_trace(O, fac[1][1])
  end

  @testset "function field over F_2(x)" begin
    kx, x = rational_function_field(GF(2), :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    f = y^3 - x^3 - 1
    L, t = function_field(f; cached = false)

    O = Hecke.GenOrd(parent(numerator(x)), L)
    @assert is_equation_order(O)
    check_equation_order_different(O, f)
  end

  @testset "function field over F_5(t)" begin
    kx, x = rational_function_field(GF(5), :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    f = y^2 + x*y + (x^3 + 1)
    L, t = function_field(f; cached = false)

    O = Hecke.GenOrd(parent(numerator(x)), L)
    @assert is_equation_order(O)
    check_equation_order_different(O, f)

    fac = collect(factor(discriminant(O)))
    check_radical_basis_trace(O, fac[1][1])
  end
end
