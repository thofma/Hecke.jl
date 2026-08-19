@testset "Residue rings of orders over general PID" begin
  # Basic ring axioms and consistency between quo, residue_ring, mod and lift
  function test_quo_common(O, I, rand_range = 0:10; ntests::Int = 10)
    Q, f = quo(O, I)
    @test domain(f) === O
    @test codomain(f) === Q
    @test base_ring(Q) === O
    @test Hecke.ideal(Q) === I

    @test isone(@inferred f(one(O)))
    @test iszero(@inferred f(zero(O)))
    @test isone(one(Q))
    @test iszero(zero(Q))

    R = residue_ring(O, I)
    @test elem_type(R) == elem_type(Q)
    @test isone(R(one(O)))

    rand_elem() = O([rand(base_ring(O), rand_range) for _ in 1:degree(O)])

    for _ in 1:ntests
      x = rand_elem()
      X = f(x)
      # preimage / lift agree with the canonical representative given by mod
      m = mod(x, I)
      @test f(preimage(f, X)) == X
      @test f(m) == X
      @test x - preimage(f, X) in I
      # copying and hashing
      @test deepcopy(X) == X
      @test hash(X) == hash(deepcopy(X))
    end
  end

  @testset "over F_3(t): unit ideal" begin
    k, t = rational_function_field(GF(3), :t; cached = false)
    K, a = function_field(polynomial(k, [t, 0, 1]); cached = false)
    OK = finite_maximal_order(K)

    # the original bug report: quo(OK, OK(2)*OK) used to throw an error
    I = OK(2)*OK
    @test isone(I)
    Q, f = @inferred quo(OK, I)

    ConformanceTests.test_Ring_interface(Q)
    # 2 is a unit in F_3, so I is the unit ideal and Q is the trivial ring
    @test isone(zero(Q))
    @test iszero(one(Q))
    test_quo_common(OK, I)
  end

  @testset "over F_3(t): prime ideal" begin
    k, t = rational_function_field(GF(3), :t; cached = false)
    K, a = function_field(polynomial(k, [t, 0, 1]); cached = false)
    OK = finite_maximal_order(K)
    kt = base_ring(OK)
    tt = gen(kt)
    I = prime_decomposition(OK, tt + 1)[1][1]
    Q, f = @inferred quo(OK, I)
    ConformanceTests.test_Ring_interface(Q)
    test_quo_common(OK, I)
  end

  @testset "over number field" begin
    x = gen(Hecke.Globals.Qx)
    K, a = number_field(x^2 - 2, :a)
    O = Hecke._integral_closure(ZZ, K)
    I = ideal(O, ZZ(3))
    Q, f = quo(O, I)
    ConformanceTests.test_Ring_interface(Q)
    test_quo_common(O, I)
  end
end
