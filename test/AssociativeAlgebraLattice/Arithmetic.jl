@testset "Associative algebra lattice arithmetic" begin
  @testset "PID" begin
    A = matrix_algebra(QQ, 2)
    b = basis(A)

    L = Hecke.lattice(A, ZZ, b[1:2])

    M = Hecke.lattice(A, ZZ, b[2:3])

    S = L + M
    @test Hecke.rank(S) == 3
    @test all(x -> x in S, b[1:3])
    @test issubset(L, S)
    @test !issubset(S, L)

    T = 2*L
    @test T == L*2
    @test issubset(T, L)
    @test !issubset(L, T)
    @test 2*b[1] in T
    @test !(b[1] in T)

    I = intersect(Hecke.lattice(A, ZZ, 2 .* b[1:2]),
                  Hecke.lattice(A, ZZ, 3 .* b[2:3]))
    @test Hecke.rank(I) == 1
    @test 6*b[2] in I
    @test !(2*b[2] in I)
    @test !(3*b[2] in I)

    Lhalf = QQ(1//2)*Hecke.lattice(A, ZZ, [b[1]])
    Lthird = QQ(1//3)*Hecke.lattice(A, ZZ, [b[1]])
    @test intersect(Lhalf, Lthird) == Hecke.lattice(A, ZZ, [b[1]])

    E12 = A(QQ[0 1; 0 0])
    E21 = A(QQ[0 0; 1 0])
    E11 = E12*E21
    E22 = E21*E12
    L12 = Hecke.lattice(A, ZZ, [E12])
    L21 = Hecke.lattice(A, ZZ, [E21])
    @test L12*L21 == Hecke.lattice(A, ZZ, [E11])
    @test L21*L12 == Hecke.lattice(A, ZZ, [E22])
    @test L12*L12 == Hecke.zero_lattice(A, ZZ)
    @test E21*L12 == Hecke.lattice(A, ZZ, [E22])
    @test L12*E21 == Hecke.lattice(A, ZZ, [E11])
    @test E21*L12 != L12*E21

    A2 = matrix_algebra(QQ, 2)
    L2 = Hecke.lattice(A2, ZZ, basis(A2)[1:2])

    @test_throws ArgumentError L + L2

    @test_throws ArgumentError L*L2
    @test_throws ArgumentError intersect(L, L2)

    @test_throws ArgumentError basis(A2)[1]*L
    @test_throws ArgumentError L*basis(A2)[1]
    @test_throws ArgumentError GF(17)(1)*L

    Z = Hecke.zero_lattice(A, ZZ)

    @test Z*L == Z
    @test L*Z == Z
    @test E12*Z == Z
    @test Z*E12 == Z
    @test 0*L == Z
  end

  @testset "Degree localization" begin
    K, = rational_function_field(GF(13))
    R = localization(K, degree)
    A = group_algebra(K, small_group(2, 1))
    L = Hecke.lattice(A, R, basis(A))
    t = gen(R)

    @test t*L == L*t
    @test L*L == L

    P = K.fraction_field.base_ring
    LP = Hecke.lattice(A, P, basis(A))

    @test_throws ArgumentError L + LP
  end

  @testset "Polynomial PID" begin
    K, t = rational_function_field(GF(13))
    R = K.fraction_field.base_ring
    A = group_algebra(K, small_group(2, 1))
    L = Hecke.lattice(A, R, basis(A))
    M = t*L

    @test intersect(L, M) == M
    @test L*M == M
  end

  @testset "Dedekind domain" begin
    K, = quadratic_field(5)
    O = maximal_order(K)
    A = group_algebra(K, small_group(2, 1))
    PM = pseudo_matrix(O, identity_matrix(K, dim(A)),
                       [fractional_ideal(O, one(O)) for _ in 1:dim(A)])
    L = Hecke.lattice(A, O, PM)

    I2 = fractional_ideal(O, O(2))
    I1 = fractional_ideal(O, one(O))
    PB = [Hecke._pseudo_element(basis(A)[1], I2), Hecke._pseudo_element(basis(A)[2], I1)]
    LPB = Hecke.lattice(A, O, PB)

    @test 2*(K(1//2)*LPB) == LPB

    M = 2*L
    @test O(2)*L == M

    @test M + L == L
    @test intersect(M, L) == M
    @test M*M == 4*L
    @test basis(A)[2]*L == L

    I = fractional_ideal(O, one(O))
    L1 = Hecke.lattice(A, O, pseudo_matrix(O, matrix(K, 1, 2, [1, 0]), [I]))
    L2 = Hecke.lattice(A, O, pseudo_matrix(O, matrix(K, 1, 2, [0, 1]), [I]))
    @test iszero(intersect(L1, L2))
    @test intersect(L1, 2*L1) == 2*L1

    MA = matrix_algebra(K, 2)
    E12 = MA(K[0 1; 0 0])
    E21 = MA(K[0 0; 1 0])
    PM12 = pseudo_matrix(O, Hecke.coordinates(MA, [E12]), [I])
    ML12 = Hecke.lattice(MA, O, PM12)
    ML22 = Hecke.lattice(MA, O, pseudo_matrix(O, Hecke.coordinates(MA, [E21*E12]), [I]))
    ML11 = Hecke.lattice(MA, O, pseudo_matrix(O, Hecke.coordinates(MA, [E12*E21]), [I]))
    @test E21*ML12 == ML22
    @test ML12*E21 == ML11
    @test E21*ML12 != ML12*E21

    Z = Hecke.zero_lattice(A, O)

    @test Z*L == Z
    @test basis(A)[1]*Z == Z
  end
end
