@testset "Elements in algebras" begin
  Qx, x = QQ["x"]
  f = x^2 + 1
  A = StructureConstantAlgebra(f)

  @testset "divexact" begin
    for side in (:left, :right)
      @test divexact(A([1,1]), A([1,1]), side) == one(A)
      @test_throws ErrorException divexact(zero(A), zero(A), side)
    end
    @test_throws MethodError divexact(one(A), one(A))

    M = matrix_algebra(QQ, 2)
    a = M(QQ[1 1; 0 1])
    b = M(QQ[1 0; 1 1])
    @test divexact(a*b, a, :left) == b
    @test divexact(a*b, b, :right) == a
  end

  @testset "Is integral" begin
    @test Hecke.is_integral(A[1]) == true
    @test Hecke.is_integral(QQFieldElem(1, 2)*A[1]) == false

    B = group_algebra(QQ, small_group(2, 1))
    @test Hecke.is_integral(B[1]) == true
    @test Hecke.is_integral(QQFieldElem(1, 2)*B[1]) == false

    C = matrix_algebra(QQ, B, 2)
    @test Hecke.is_integral(C[1]) == true
    @test Hecke.is_integral(QQFieldElem(1, 2)*C[1]) == false
  end

  @testset "zero! for group algebra elements" begin
    # Check in-place zeroing for both representations, including infinite groups.
    for (n, sparse) in ((4, false), (4, true), (0, true))
      G = abelian_group([n])
      B = group_algebra(ZZ, G; sparse)
      b = B(zero(G) => 2, first(gens(G)) => -3)
      @test !iszero(b)
      @test zero!(b) === b
      @test iszero(b)
      @test zero!(b) === b
    end
  end

  let
    A = matrix_algebra(QQ, 2)
    @test is_idempotent(A(QQ[1 0; 0 0]))
    @test !is_central(A(QQ[1 0; 0 0]))
    @test is_central(A(QQ[2 0; 0 2]))
    @test !is_central_idempotent(A(QQ[1 0; 0 0]))
    @test is_central_idempotent(A(QQ[1 0; 0 1]))

    Qx, x = QQ["x"]
    f = (x + 1)*(x - 1)
    B = StructureConstantAlgebra(f)
    e = B([1//2, 1//2])
    @test is_central_idempotent(e)
  end


  @testset "Characteristic polynomial" begin
    f = x^2 + 1
    K, a = number_field(f, "a")
    A = StructureConstantAlgebra(f)

    b = rand(K, -10:10)
    c = A(coefficients(b))

    cpb = charpoly(b)
    cpc = charpoly(c)
    rcpc = reduced_charpoly(c)

    # We have to compare the polynomials by hand as they live in "different" polynomial rings...
    for p in [ cpc, rcpc ]
      for i = 0:2
        @test coeff(p, i) == coeff(cpb, i)
      end
    end

    mpb = minpoly(b)
    mpc = minpoly(c)

    @test degree(mpb) == degree(mpc)
    for i = 0:2
      @test coeff(mpb, i) == coeff(mpc, i)
    end
  end

  # Fix reduced char poly
  A = Hecke.QuaternionAlgebra(QQ, QQ(-1), QQ(-1))
  M = matrix_algebra(QQ, A, 2)
  a = A(QQFieldElem[0, -2, -1, 1])
  b = A(QQFieldElem[0, 1, -2, -1//2])
  m = M(matrix(A, 2, 2, [a, 0, 0, b]))
  @test normred(m) == 63//2
  @test normred(m) == normred(a * b) == normred(a) * normred(b)

  g = reduced_charpoly(m)
  x = gen(parent(g))
  @test g == x^4 + 45//4 * x^2 + 63//2

  # mul! for matrix algebra elements
  A = matrix_algebra(QQ, 2)
  @test isone(mul!(zero(A), one(A), ZZRingElem(1)))

  @testset "addmul! with scalars" begin
    A = quaternion_algebra(QQ, -1, -1)
    a = A([1, 2, 3, 4])
    c0 = A([5, 6, 7, 8])

    for s in (QQ(3), ZZ(3), 3)
      expected = c0 + a*s

      c = deepcopy(c0)
      @test addmul!(c, a, s, QQ()) === c
      @test c == expected

      c = deepcopy(c0)
      @test addmul!(c, s, a, QQ()) === c
      @test c == expected

      c = deepcopy(c0)
      @test addmul!(c, a, s) === c
      @test c == expected
    end

    c = deepcopy(a)
    @test addmul!(c, c, ZZ(2), QQ()) === c
    @test c == 3*a

    B = quaternion_algebra(QQ, -1, -2)
    @test_throws ArgumentError addmul!(zero(B), a, QQ(1), QQ())
    @test_throws ArgumentError addmul!(zero(B), a, ZZ(1), QQ())
  end

  # mul! and addmul! with integer scalars over base rings other than QQ
  let
    H = abelian_group([2, 3])
    Fx, x = GF(5)[:x]
    algs = [group_algebra(ZZ, H; sparse = false, cached = false),
            group_algebra(GF(5), H; sparse = false, cached = false),
            structure_constant_algebra(x^3 + x + 1),
            matrix_algebra(GF(5), 2)]
    for A in algs
      a = A(base_ring(A).(1:dim(A)))
      for s in (ZZ(3), 3)
        c = zero(A)
        @test mul!(c, a, s) === c
        @test c == 3 * a
        @test mul!(zero(A), s, a) == 3 * a
        @test addmul!(one(A), a, s) == one(A) + 3 * a
        b = deepcopy(a)
        @test mul!(b, b, s) == 3 * a
      end
    end
  end

  # Mutating arithmetic agrees with the non-mutating one, also if the
  # output is one of the inputs.
  @testset "Mutating arithmetic" begin
    H = quaternion_algebra(QQ, -1, -1)
    M = matrix_algebra(QQ, 2)
    G = small_group(6, 1)
    elems = [(H([2, 3, 4, 5]), H([1, -1, 2, 7])),
             (M(QQ[1 2; 3 4]), M(QQ[0 1; 1 1]))]
    for sparse in (false, true)
      QG = Hecke._group_algebra(QQ, G; sparse = sparse)
      push!(elems, (QG(G[1]) + 2*QG(G[2]), 3*QG(G[1]*G[2]) - QG(one(G))))
    end
    amul = (x, y, z) -> x + y*z
    for (a, b) in elems
      E = typeof(a)
      ConformanceTests.test_mutating_op_like_zero(zero, zero!, a)
      ConformanceTests.test_mutating_op_like_neg(-, neg!, a)
      ConformanceTests.test_mutating_op_like_add(+, add!, a, b)
      ConformanceTests.test_mutating_op_like_add(-, sub!, a, b)
      ConformanceTests.test_mutating_op_like_add(*, mul!, a, b)
      ConformanceTests.test_mutating_op_like_addmul(amul, addmul!, b, a, b)
      for s in (QQ(3), ZZ(3), 3)
        ConformanceTests.test_mutating_op_like_add(*, mul!, a, s, E)
        ConformanceTests.test_mutating_op_like_add(*, mul!, s, a, E)
        ConformanceTests.test_mutating_op_like_addmul(amul, addmul!, b, a, s, E)
        ConformanceTests.test_mutating_op_like_addmul(amul, addmul!, b, s, a, E)
      end
    end

    # == compares matrices, so check the cached coefficients separately
    c = M(QQ[1 2; 3 4])
    @test !iszero(coefficients(c))
    @test iszero(coefficients(zero!(c)))
  end

  # add! for matrix algebra elements
  # 1547
  let
    A = matrix_algebra(QQ, 2)
    b = A(matrix(QQ, [3 4; 5 6]))
    Hecke.add!(b,b)
    @test b == A(matrix(QQ, [6 8; 10 12]))
  end

  # fancy group algebra element constructor
  G = abelian_group([2, 2]); a = G([0, 1]);
  QG = Hecke._group_algebra(QQ, G; sparse = false);
  @test QG(Dict(a => 2, zero(G) => 1)) == 2 * QG(a) + 1 * QG(zero(G))
  @test QG(a => ZZ(2), zero(G) => QQ(1)) == 2 * QG(a) + 1 * QG(zero(G))
  QG = Hecke._group_algebra(QQ, G; sparse = true);
  @test QG(Dict(a => 2, zero(G) => 1)) == 2 * QG(a) + 1 * QG(zero(G))
  @test QG(a => ZZ(2), zero(G) => QQ(1)) == 2 * QG(a) + 1 * QG(zero(G))

  let
    # Jordan-Chevalley
    Qx, x = QQ[:x]
    A = associative_algebra((x^2 + 1)^2)
    alpha = basis(A)[2]
    u, v = Hecke.jordan_chevalley_decomposition(alpha)
    @test u == A(QQ.([0, 3//2, 0, 1//2]))
    @test v == A(QQ.([0, -1//2, 0, -1//2]))
    @test u + v == alpha
  end
end

# Reduced traces remain defined when the matrix degree vanishes in the field.
@testset "Reduced trace" begin
  for p in (2, 3)
    k = GF(p)
    B = matrix_algebra(k, p)
    b = B(diagonal_matrix(k, [one(k); fill(zero(k), p - 1)]))
    @test iszero(tr(b))
    @test trred(b) == one(k)

    K, t = rational_function_field(GF(p), :t; cached = false)
    A = matrix_algebra(K, p)
    a = A(diagonal_matrix(K, [one(K); fill(t, p - 1)]))
    @test iszero(tr(a))
    @test trred(a) == one(K) + (p - 1)*t
    @test trred(zero(A)) == zero(K)
    @test trred(one(A)) == zero(K)
    @test trred(a + one(A)) == trred(a)
  end
  kt, t = rational_function_field(GF(2), :t; cached = false)
  K, b = function_field(polynomial(kt, [t^3 + t + 1, 1, 1]); cached = false)
  A = matrix_algebra(K, 2)
  @test trred(A(K[1 b; 0 0])) == one(K)
  @test trred(A(K[b 1; 0 0])) == b

  for K in (QQ, GF(3))
    A = matrix_algebra(K, 2)
    @test trred(A(K[1 2; 3 4])) == K(5)
  end
end
