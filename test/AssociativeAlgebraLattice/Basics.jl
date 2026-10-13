@testset "Associative algebra lattice basics" begin
  @testset "PID" begin
    A = matrix_algebra(QQ, 2)
    b = basis(A)

    L = Hecke.lattice(A, ZZ, b[1:2])
    N = Hecke.embedded_module(ZZ, QQ, Hecke.coordinates(A, b[1:2]); overstructure = A)
    LN = Hecke.lattice(A, ZZ, N)
    @test algebra(L) === A
    @test base_ring(L) === ZZ
    @test Hecke.rank(L) == 2
    @test Hecke.ambient_rank(L) == dim(A)
    @test !Hecke.is_full_lattice(L)
    @test basis(L) == b[1:2]
    @test LN == L
    @test Hecke.underlying_module(LN) === N
    @test base_ring_type(typeof(L)) === ZZRing
    @test Hecke.algebra_type(typeof(L)) === typeof(A)
    @test Hecke.is_full_rank(L) == Hecke.is_full_lattice(L)

    B = basis_matrix(L)
    B[1, 1] = QQ(99)
    @test b[1] in L
    @test basis_matrix(L) == Hecke.coordinates(A, b[1:2])
    @test basis_matrix(L; copy = false) === basis_matrix(Hecke.underlying_module(L))
    PB = Hecke.pseudo_basis(L)
    @test Hecke.element.(PB) == basis(L)
    @test all(x -> Hecke.fractional_ideal(x) === nothing, PB)
    @test Hecke.is_full_rank(Hecke.lattice(A, ZZ, basis(A)))
    @test occursin("Lattice of rank 2", sprint(show, L))

    @test_throws ArgumentError Hecke.lattice(A, ZZ, identity_matrix(ZZ, dim(A)))
    @test_throws ArgumentError Hecke.lattice(A, ZZ, zero_matrix(QQ, 1, dim(A) - 1))
    @test_throws ArgumentError Hecke.lattice(A, ZZ, PB)

    A2 = matrix_algebra(QQ, 2)
    L2 = Hecke.lattice(A2, ZZ, basis(A2)[1:2])

    @test_throws ArgumentError Hecke.lattice(A, ZZ, basis(A2)[1:1])
    @test_throws ArgumentError Hecke.lattice(A, ZZ, Hecke.underlying_module(L2))

    wrong_rank = Hecke.embedded_module(ZZ, QQ, zero_matrix(QQ, 1, dim(A) - 1); overstructure = A)
    @test_throws ArgumentError Hecke.lattice(A, ZZ, wrong_rank)

    Z = Hecke.zero_lattice(A, ZZ)
    @test iszero(Z)
    @test Hecke.rank(Z) == 0
    @test Hecke.ambient_rank(Z) == dim(A)
    @test !Hecke.is_full_rank(Z)
    @test isempty(basis(Z))
    @test basis_matrix(Z) == zero_matrix(QQ, 0, dim(A))
    @test Hecke.lattice(A, ZZ, elem_type(A)[]) == Z
  end

  @testset "Degree localization" begin
    K, = rational_function_field(GF(13))
    R = localization(K, degree)
    A = group_algebra(K, small_group(2, 1))
    L = Hecke.lattice(A, R, basis(A))

    @test Hecke.is_full_lattice(L)
    @test basis_matrix(L) == identity_matrix(K, dim(A))

    P = K.fraction_field.base_ring
    LP = Hecke.lattice(A, P, basis(A))

    @test_throws ArgumentError Hecke.lattice(A, R, Hecke.underlying_module(LP))
  end

  @testset "Dedekind domain" begin
    K, = quadratic_field(5)
    O = maximal_order(K)
    A = group_algebra(K, small_group(2, 1))
    PM = pseudo_matrix(O, identity_matrix(K, dim(A)),
                       [fractional_ideal(O, one(O)) for _ in 1:dim(A)])
    L = Hecke.lattice(A, O, PM)
    LL = Hecke.lattice(A, O, PM; is_basis_matrix = true)
    LM = Hecke.lattice(A, O, identity_matrix(K, dim(A)))

    @test Hecke.rank(L) == dim(A)
    @test Hecke.is_full_lattice(L)
    @test LL == L
    @test LM == L

    @test matrix(basis_matrix(L)) == identity_matrix(K, dim(A))
    @test length(Hecke.pseudo_basis(L)) == dim(A)
    @test_throws ArgumentError basis(L)

    I2 = fractional_ideal(O, O(2))
    I1 = fractional_ideal(O, one(O))
    PB = [Hecke._pseudo_element(basis(A)[1], I2), Hecke._pseudo_element(basis(A)[2], I1)]
    LPB = Hecke.lattice(A, O, PB)
    LPM = Hecke.lattice(A, O, pseudo_matrix(O, identity_matrix(K, dim(A)), [I2, I1]))
    @test LPB == LPM

    @test Hecke.lattice(A, O, Hecke.pseudo_basis(LPB)) == LPB

    @test basis_matrix(LPB; copy = false) === basis_matrix(Hecke.underlying_module(LPB))
    copied = basis_matrix(LPB)
    matrix(copied)[1, 1] = K(99)
    Hecke.coefficient_ideals(copied)[1] = fractional_ideal(O, O(99))
    @test LPB == LPM

    @test_throws ArgumentError Hecke.lattice(A, ZZ, PM)
    @test_throws ArgumentError Hecke.lattice(A, O, pseudo_matrix(O, zero_matrix(K, 1, dim(A) + 1), [I1]))
    A2 = group_algebra(K, small_group(2, 1); cached = false)
    @test_throws ArgumentError Hecke.lattice(A, O, [Hecke._pseudo_element(basis(A2)[1], I1)])

    AQ = group_algebra(QQ, small_group(2, 1))
    @test_throws ArgumentError Hecke.lattice(AQ, O, PM)

    Z = Hecke.zero_lattice(A, O)
    @test iszero(Z)
  end

  @testset "Containment and equality" begin
    @testset "PID" begin
      A = matrix_algebra(QQ, 2)
      b = basis(A)

      L = Hecke.lattice(A, ZZ, b[1:2])

      @test b[1] in L
      @test !(b[3] in L)

      M = Hecke.lattice(A, ZZ, b[2:3])
      @test Hecke.is_compatible(L, M)

      @test hash(Hecke.lattice(A, ZZ, b[1:2])) == hash(L)

      A2 = matrix_algebra(QQ, 2)
      L2 = Hecke.lattice(A2, ZZ, basis(A2)[1:2])
      @test !Hecke.is_compatible(L, L2)

      @test_throws ArgumentError issubset(L, L2)
      @test L != L2

      @test_throws ArgumentError basis(A2)[1] in L

      Z = Hecke.zero_lattice(A, ZZ)

      @test issubset(Z, L)
    end

    @testset "PID hashing independent of the basis" begin
      F, t = rational_function_field(GF(7), "t")
      Rinf = localization(F, degree)
      for (R, K, u, a) in ((ZZ, QQ, ZZ(-1), QQ(1//2)),
                            (parent(numerator(t)), F, parent(numerator(t))(3), inv(t)),
                            (Rinf, F, Rinf(t/(t + 1)), t))
        A = matrix_algebra(K, 2)
        B = K[a 1 0 0; 0 3 1 0]
        C = K[K(u) 1; 0 1]*B
        L = Hecke.lattice(A, R, B; is_basis_matrix = true)
        N = Hecke.lattice(A, R, C; is_basis_matrix = true)
        M = Hecke.lattice(A, R, deepcopy(B))
        @test L == N == M
        @test (@inferred module_index(N, L)) == ideal(R, one(R))
        @test gen(module_index(N, L)) == one(R)
        @test (@inferred hash(L)) == hash(N) == hash(M)
        @test length(Set([L, N, M])) == 1
        @test Dict(L => 1)[N] == 1
        @test basis_matrix(L) == B
        @test basis_matrix(N) == C
      end
    end

    @testset "PID indices" begin
      F, t = rational_function_field(GF(7), "t")
      Rinf = localization(F, degree)
      for (R, K, s) in ((ZZ, QQ, ZZ(2)),
                        (parent(numerator(t)), F, numerator(t)),
                        (Rinf, F, Rinf(inv(t))))
        A = matrix_algebra(K, 2)
        B = basis(A)
        for r in (0, 2, dim(A))
          L = Hecke.lattice(A, R, B[1:r])
          N = s*L
          I = @inferred module_index(N, L)
          @test I == ideal(R, s^r)
          @test typeof(I) === ideal_type(typeof(R))
          @test module_index(N, L; check = false) == module_index(N, L)
          @test isone(module_index(L, L))
          @test base_ring(I) === R
          @test module_index(N, L) == module_index(Hecke.underlying_module(N),
                                                  Hecke.underlying_module(L))
        end
        L = Hecke.lattice(A, R, [K(1//2)*B[1], 3*B[2]])
        @test module_index(s*L, L) == ideal(R, s^2)
        @test module_index(s^2*L, L) == module_index(s^2*L, s*L)*module_index(s*L, L)
        @test_throws ArgumentError module_index(L, s*L)
        @test_throws ArgumentError module_index(Hecke.zero_lattice(A, R), L)
        @test_throws ArgumentError module_index(Hecke.lattice(A, R, B[3:4]), L)
        Aother = matrix_algebra(K, 2)
        @test_throws ArgumentError module_index(Hecke.lattice(Aother, R, basis(Aother)[1:2]), L)
      end
      A = matrix_algebra(F, 2)
      L = Hecke.lattice(A, parent(numerator(t)), basis(A))
      N = Hecke.lattice(A, Rinf, basis(A))
      @test_throws ArgumentError module_index(N, L)
    end

    @testset "Degree localization" begin
      K, = rational_function_field(GF(13))
      R = localization(K, degree)
      A = group_algebra(K, small_group(2, 1))
      L = Hecke.lattice(A, R, basis(A))

      @test all(x -> x in L, basis(A))

      P = K.fraction_field.base_ring
      LP = Hecke.lattice(A, P, basis(A))
      @test !Hecke.is_compatible(L, LP)
    end

    @testset "Dedekind domain" begin
      K, = quadratic_field(5)
      O = maximal_order(K)
      A = group_algebra(K, small_group(2, 1))
      PM = pseudo_matrix(O, identity_matrix(K, dim(A)),
                         [fractional_ideal(O, one(O)) for _ in 1:dim(A)])
      L = Hecke.lattice(A, O, PM)
      LL = Hecke.lattice(A, O, PM; is_basis_matrix = true)

      @test hash(LL) == hash(L)

      @test all(x -> x in L, basis(A))

      I2 = fractional_ideal(O, O(2))
      I1 = fractional_ideal(O, one(O))
      PB = [Hecke._pseudo_element(basis(A)[1], I2), Hecke._pseudo_element(basis(A)[2], I1)]
      LPB = Hecke.lattice(A, O, PB)

      @test !(basis(A)[1] in LPB)
      @test 2*basis(A)[1] in LPB
      @test basis(A)[2] in LPB
      @test PB[1] in LPB
      @test !(Hecke._pseudo_element(basis(A)[1], I1) in LPB)
      @test all(x -> x in LPB, Hecke.pseudo_basis(LPB))

      A2 = group_algebra(K, small_group(2, 1); cached = false)

      @test_throws ArgumentError Hecke._pseudo_element(basis(A2)[1], I1) in LPB

      M = 2*L

      @test issubset(M, L)
      @test !issubset(L, M)

      Z = Hecke.zero_lattice(A, O)

      @test issubset(Z, L)
    end
  end
end
