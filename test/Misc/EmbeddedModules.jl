@testset "Embedded modules" begin
  @testset "ZZ-modules in QQ^n" begin
    ambient = Ref(:ambient)
    M = Hecke.embedded_module(ZZ, QQ, ZZ[2 0; 0 3]; overstructure = ambient)

    @test Hecke.ring(M) === ZZ
    @test Hecke.overring(M) === QQ
    @test Hecke.overstructure(M) === ambient
    @test Hecke.ambient_rank(M) == 2
    @test base_ring(Hecke.generator_matrix(M)) === QQ
    @test rank(M) == 2
    @test Hecke.has_full_rank(M)
    @test basis_matrix(M) == QQ[2 0; 0 3]
    @test Hecke.basis_matrix_components(M) == (ZZ[2 0; 0 3], ZZ(1))

    @test QQFieldElem[2, 3] in M
    @test QQFieldElem[4, -6] in M
    @test !(QQFieldElem[1, 3] in M)
    @test !(QQFieldElem[2, 1] in M)

    # Exercise the membership path using a cached inverse as well.
    @test basis_matrix_inverse(M) == QQ[1//2 0; 0 1//3]
    @test QQFieldElem[2, 3] in M
    @test !(QQFieldElem[1, 3] in M)

    N = Hecke.embedded_module(ZZ, QQ, QQ[4 0; 0 6])
    @test issubset(N, M)
    @test Hecke.index(N, M) == 4

    P = Hecke.embedded_module(ZZ, QQ, QQ[1 0; 0 3])
    @test !issubset(P, M)

    Q = Hecke.embedded_module(ZZ, QQ, QQ[4 0; 0 6]; is_basis_matrix = true)
    @test issubset(Q, M)
  end

  @testset "generators and rank" begin
    M = Hecke.embedded_module(ZZ, QQ, QQ[1//2 0; 0 3; 3//2 0])

    @test rank(M) == 2
    @test basis_matrix(M) == QQ[1//2 0; 0 3]
    @test QQFieldElem[5//2, -6] in M
    @test !(QQFieldElem[1//4, 0] in M)

    N = Hecke.embedded_module(ZZ, QQ, QQ[2 0 0; 0 3 0])
    @test rank(N) == 2
    @test Hecke.ambient_rank(N) == 3
    @test !Hecke.has_full_rank(N)
    @test QQFieldElem[4, 6, 0] in N
    @test !(QQFieldElem[4, 6, 1] in N)
    @test !(QQFieldElem[1, 3, 0] in N)

    P = Hecke.embedded_module(ZZ, QQ, QQ[4 0 0; 0 6 0])
    @test issubset(P, N)
    @test Hecke.index(P, N) == 4
  end

  @testset "cached data and coordinates" begin
    B = QQ[2 0; 0 3]
    Binv = QQ[1//2 0; 0 1//3]
    M = Hecke.embedded_module(ZZ, QQ, B; is_basis_matrix = true, inverse = Binv)

    @test basis_matrix(M) === B
    @test basis_matrix_inverse(M) === Binv
    @test Hecke.basis_matrix_numerator(M) == ZZ[2 0; 0 3]
    @test Hecke.index_multiple(M) == 6

    fl, c = Hecke._in(QQFieldElem[2, 3], M, Val(true))
    @test fl
    @test c == ZZRingElem[1, 1]

    N = Hecke.embedded_module(ZZ, QQ, QQ[2 0; 0 3])
    fl, c = Hecke._in(QQFieldElem[1, 0], N, Val(true))
    @test !fl
    @test c == ZZRingElem[1, 0]

    P = Hecke.embedded_module(ZZ, QQ, QQ[2 0 0; 0 3 0])
    fl, c = Hecke._in(QQFieldElem[0, 0, 1], P, Val(true))
    @test !fl
    @test c == ZZRingElem[0, 0, 0]

    fl, C = Hecke._in(QQ[0 0 1], P, Val(true))
    @test !fl
    @test C == zero_matrix(ZZ, 1, 2)
    @test !Hecke._in(QQ[0 0 1], P)

    fl, C = Hecke._in(QQ[4 0; 0 6], M, Val(true))
    @test fl
    @test C == ZZ[2 0; 0 2]

    T = Hecke._tmp_mat_overring(M, 3)
    @test size(T) == (3, 2)
    @test size(Hecke._tmp_mat_overring(M, 2)) == (2, 2)

    H = Hecke.embedded_module(ZZ, QQ, QQ[4 0; 0 6; 8 0])
    H.index_multiple = ZZ(24)
    @test Hecke.basis_matrix_numerator(H) == ZZ[4 0; 0 6]
  end

  @testset "zero module" begin
    M = Hecke.zero_embedded_module(ZZ, QQ, 3)

    @test rank(M) == 0
    @test Hecke.ambient_rank(M) == 3
    @test !Hecke.has_full_rank(M)
    @test basis_matrix(M) == zero_matrix(QQ, 0, 3)
    @test QQFieldElem[0, 0, 0] in M
    @test !(QQFieldElem[0, 1, 0] in M)
  end

  @testset "polynomial PID" begin
    K, x = rational_function_field(QQ, "x")
    R = parent(numerator(x))
    M = Hecke.embedded_module(R, K, K[x 0; 0 1])

    @test rank(M) == 2
    @test typeof(x)[x, x + 1] in M
    @test !(typeof(x)[K(1), K(0)] in M)
    @test !(typeof(x)[x, inv(x)] in M)
  end

  @testset "degree localization" begin
    K, x = rational_function_field(QQ, "x")
    R = localization(K, degree)
    M = Hecke.embedded_module(R, K, K[1//x 0; 0 1])

    @test Hecke.ring(M) === R
    @test Hecke.overring(M) === K
    @test basis_matrix(M) == K[1//x 0; 0 1]
    @test typeof(x)[inv(x), (x + 1)//x] in M
    @test typeof(x)[inv(x)^2, K(0)] in M
    @test !(typeof(x)[K(1), K(0)] in M)
    @test !(typeof(x)[inv(x), x] in M)
  end

  @testset "pseudo elements and Dedekind domains" begin
    p = Hecke._pseudo_element(QQ(2), ZZ)
    q = Hecke._pseudo_element(QQ(3), ZZ)
    pq = p*q
    @test Hecke.element(pq) == QQ(6)
    @test Hecke.fractional_ideal(pq) === nothing

    p_with_ideal = Hecke._pseudo_element(QQ(1), ZZ)
    @test Hecke.element(p_with_ideal) == QQ(1)
    @test Hecke.fractional_ideal(p_with_ideal) === nothing

    MZZ = Hecke.embedded_module(ZZ, QQ, QQ[2 0; 0 3])
    @test Hecke._pseudo_element(QQFieldElem[2, 3], ZZ) in MZZ

    K, = quadratic_field(5)
    O = maximal_order(K)
    M = Hecke.embedded_module(O, K, pseudo_matrix(identity_matrix(K, 2)))
    v = elem_type(K)[K(1), K(0)]
    w = elem_type(K)[K(1)//2, K(0)]

    @test Hecke.ambient_rank(M) == 2
    @test nrows(matrix(basis_matrix(M))) == 2
    @test Hecke._pseudo_element(v, O) in M
    @test !(Hecke._pseudo_element(w, O) in M)
  end
end
