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
    M = @inferred Hecke.radical_basis_trace(O, p)
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

@testset "pmaximal_overorder" begin
  function check_p_maximal(O, Op, p)
    # runtime type check (we will do @inferred in tests, so just to be safe)
    @test Op isa typeof(O)

    # Op contains O (overorder property)
    for b in basis(O)
      @test b in Op
    end

    # disc(Op) divides disc(O)
    @test iszero(mod(discriminant(O), discriminant(Op)))

    # Idempotent at p: applying pmaximal again is a no-op
    @test discriminant(Hecke.pmaximal_overorder(Op, p, true)) == discriminant(Op)
  end

  @testset "number field (trace-radical)" begin
    x = gen(Hecke.Globals.Qx)
    K, _ = number_field(x^2 - 18, :a; cached = false)
    # maximal order: Z[sqrt(2)]
    # equation order: Z[3*sqrt(2)] has index 3 in maximal order
    O = order(ZZ, K)
    @assert discriminant(O) == 72   # = 9 · 8

    Op = @inferred Hecke.pmaximal_overorder(O, ZZ(3), true)
    check_p_maximal(O, Op, ZZ(3))
    @test discriminant(Op) == 8     # 72 / 3^2 = 8 (= disc Q(sqrt(2)))

    Op_np = @inferred Hecke.pmaximal_overorder(O, ZZ(3), false)
    check_p_maximal(O, Op_np, ZZ(3))
    @test discriminant(Op_np) == 8
  end

  @testset "number field 2 (radical-by-power)" begin
    x = gen(Hecke.Globals.Qx)
    K, _ = number_field(x^2 - 12, :a; cached = false)
    # maximal order: Z[sqrt(3)]
    # equation order: Z[2*sqrt(3)] has index 2 in maximal order
    O = order(ZZ, K)
    @assert discriminant(O) == 48     # = 4 · 12

    Op = @inferred Hecke.pmaximal_overorder(O, ZZ(2), true)
    check_p_maximal(O, Op, ZZ(2))
    @test discriminant(Op) == 12      # 48 / 2^2 = 12 (= disc Q(sqrt(3)))

    Op_np = @inferred Hecke.pmaximal_overorder(O, ZZ(2), false)
    check_p_maximal(O, Op_np, ZZ(2))
    @test discriminant(Op_np) == 12
  end

  @testset "function field over Q(t) (trace-radical)" begin
    kx, x = rational_function_field(QQ, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    f = y^2 - x^2*(x + 1)           # disc = 4*x^2*(x+1)
    L, _ = function_field(f; cached = false)

    Zx = parent(numerator(x))
    O = Hecke.GenOrd(Zx, L)
    p = gen(Zx)                     # prime = x

    Op = @inferred Hecke.pmaximal_overorder(O, p, true)
    check_p_maximal(O, Op, p)
    # the x^2 factor in the equation-order discriminant goes away
    @test  iszero(mod(discriminant(O),  p^2))
    @test !iszero(mod(discriminant(Op), p^2))

    # TODO: results in
    #   function divrem is not implemented for arguments
    #   EuclideanRingResidueRingElem{QQPolyRingElem}: 1
    #   EuclideanRingResidueRingElem{QQPolyRingElem}: 1

    # Op_np = @inferred Hecke.pmaximal_overorder(O, p, false)
    # check_p_maximal(O, Op_np, p)
    # @test !iszero(mod(discriminant(Op_np), p^2))
  end

  @testset "function field over F_2(x) (radical-by-power)" begin
    kx, x = rational_function_field(GF(2), :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    f = y^3 + x*y + x^2             # disc = x^4, non-maximal equation order
    L, _ = function_field(f; cached = false)

    Zx = parent(numerator(x))
    O = Hecke.GenOrd(Zx, L)

    fac = collect(factor(discriminant(O)))
    p = fac[1][1]

    # discriminant Op is x^2
    Op = @inferred Hecke.pmaximal_overorder(O, p, true)
    check_p_maximal(O, Op, p)
    @test  iszero(mod(discriminant(O),  p^4))
    @test !iszero(mod(discriminant(Op), p^4))
    @test  iszero(mod(discriminant(Op), p^2))

    # TODO: results in
    #   function divrem is not implemented for arguments
    #   EuclideanRingResidueRingElem{QQPolyRingElem}: 1
    #   EuclideanRingResidueRingElem{QQPolyRingElem}: 1

    # Op_np = @inferred Hecke.pmaximal_overorder(O, p, false)
    # check_p_maximal(O, Op_np, p)
    # @test !iszero(mod(discriminant(Op_np), p^4))
    # @test  iszero(mod(discriminant(Op_np), p^2))
  end
end
