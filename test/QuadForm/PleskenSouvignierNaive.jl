@testset "PleskenSouvignierNaive" begin

  # Helper to verify an automorphism: g^T * G * g == G
  function _is_auto(G::ZZMatrix, g::ZZMatrix)
    return transpose(g) * G * g == G
  end

  ############################################################################
  # Internal helper tests
  ############################################################################

  @testset "_zv_canon!" begin
    w1 = [0, -3, 1]
    s1 = Hecke._zv_canon!(w1)
    @test s1 == -1
    @test w1 == [0, 3, -1]

    w2 = [0, 3, -1]
    s2 = Hecke._zv_canon!(w2)
    @test s2 == 1
    @test w2 == [0, 3, -1]

    w3 = [0, 0, 0]
    s3 = Hecke._zv_canon!(w3)
    @test s3 == 1
    @test w3 == [0, 0, 0]

    w4 = [-5]
    s4 = Hecke._zv_canon!(w4)
    @test s4 == -1
    @test w4 == [5]

    w5 = [1, 2, 3]
    s5 = Hecke._zv_canon!(w5)
    @test s5 == 1
    @test w5 == [1, 2, 3]
  end

  @testset "_zm_divmod" begin
    # inv([1 0; 1 -1]) * [1 -1; 1 0] = [1 -1; 0 -1]
    A = [1 0; 1 -1]
    B = [1 -1; 1 0]
    C = Hecke._zm_divmod(A, B, 1009)
    @test C == [1 -1; 0 -1]
    @test A * C == B

    # Identity: inv(I) * B = B
    I2 = [1 0; 0 1]
    B2 = [3 -2; 1 4]
    @test Hecke._zm_divmod(I2, B2, 1009) == B2

    # inv(A) * A = I
    A3 = [2 1; 1 1]
    @test Hecke._zm_divmod(A3, A3, 1009) == I2
  end

  @testset "_matgen" begin
    V = [[1, 0], [0, 1], [1, 1]]
    per = [1, 2]

    # x = [1, 2]: column 1 = V[1], column 2 = V[2]
    M = Hecke._matgen([1, 2], per, V)
    @test M == [1 0; 0 1]

    # x = [-1, 3]: column 1 = -V[1], column 2 = V[3]
    M2 = Hecke._matgen([-1, 3], per, V)
    @test M2 == [-1 1; 0 1]

    # Permuted per
    M3 = Hecke._matgen([1, 2], [2, 1], V)
    @test M3 == [0 1; 1 0]
  end

  @testset "_operate and _orbit" begin
    G = matrix(ZZ, [2 -1; -1 2])
    qf = Hecke._init_qfauto(G)
    Vdict = Hecke._build_vdict(qf.V)

    # -Id should map each vector to its negative
    negI = [-1 0; 0 -1]
    for i in 1:length(qf.V)
      im = Hecke._operate(i, negI, qf.V, Vdict)
      @test im == -i
    end

    # Identity should be a no-op
    Id = [1 0; 0 1]
    for i in 1:length(qf.V)
      @test Hecke._operate(i, Id, qf.V, Vdict) == i
    end

    # Orbit of a single point under -Id has size 2
    orb = Hecke._orbit([1], [negI], qf.V, Vdict)
    @test length(orb) == 2
    @test Set(orb) == Set([1, -1])
  end

  @testset "_orbdelete!" begin
    orb1 = [1, 2, 3, 4, 5]
    Hecke._orbdelete!(orb1, [2, 4])
    @test orb1 == [1, 3, 5]

    orb2 = [1, -1, 2, -2]
    Hecke._orbdelete!(orb2, [1, -1])
    @test orb2 == [2, -2]
  end

  ############################################################################
  # End-to-end tests using lattices_and_aut_order from ZLatticeAutIso.jl
  ############################################################################

  # Test data: (flat gram matrix entries, expected automorphism group order)
  lattices_and_aut_order_naive = [
    # dim 1
    ([2], 2),
    # dim 2
    ([1, 0, 0, 2], 4),
    ([2, -1, -1, 2], 12),
    # dim 3
    ([2, 1, 0, 1, 2, 0, 0, 0, 26], 24),
    # dim 4
    ([1, 0, 0, 0, 0, 2, -1, 1, 0, -1, 3, -1, 0, 1, -1, 3], 16),
    # dim 5
    ([2, 1, 1, 1, -1, 1, 2, 1, 1, 0, 1, 1, 2, 1, -1, 1, 1, 1, 2, -1, -1, 0, -1, -1, 2], 3840),
    ([1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 3], 192),
    # dim 6 (E6)
    ([2, -1, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0, 0, -1, 2, -1, 0, -1, 0, 0, -1, 2, -1, 0, 0, 0, 0, -1, 2, 0, 0, 0, -1, 0, 0, 2], 103680),
    # dim 6
    ([1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 1, 3, 1, 1, 0, 0, 0, 1, 2, 1, 0, 0, 1, 1, 1, 3], 512),
  ]

  @testset "Automorphism group order (dim=$(isqrt(length(gdata))))" for (gdata, expected_order) in lattices_and_aut_order_naive
    n = isqrt(length(gdata))
    G = matrix(ZZ, n, n, gdata)
    order, gens = Hecke._autgrp_naive(G)
    @test order == expected_order
    @test all(g -> _is_auto(G, g), gens)
  end

  @testset "A16 lattice (dim=16)" begin
    G = matrix(ZZ, 16, 16, [i == j ? 2 : (abs(i - j) == 1 ? -1 : 0) for i in 1:16 for j in 1:16])
    order, gens = Hecke._autgrp_naive(G)
    @test order == 711374856192000
    @test all(g -> _is_auto(G, g), gens)
  end

  @testset "Trivial cases" begin
    # dim 0
    order0, gens0 = Hecke._autgrp_naive(zero_matrix(ZZ, 0, 0))
    @test order0 == 1
    @test isempty(gens0)

    # dim 1, identity Gram
    G1 = matrix(ZZ, 1, 1, [1])
    order1, gens1 = Hecke._autgrp_naive(G1)
    @test order1 == 2
  end

  @testset "LLL preprocessing" begin
    # Apply a basis change to make the Gram matrix non-reduced,
    # then check that _autgrp_naive still finds the right answer.
    G = matrix(ZZ, [2 -1; -1 2])  # A2
    U = matrix(ZZ, [1 3; 0 1])
    G_bad = transpose(U) * G * U
    order, gens = Hecke._autgrp_naive(G_bad)
    @test order == 12
    @test all(g -> _is_auto(G_bad, g), gens)
  end

  @testset "Diagonal lattices" begin
    # I_n for small n: the automorphism group is the hyperoctahedral group
    # of order 2^n * n!
    for n in 1:5
      G = identity_matrix(ZZ, n)
      order, gens = Hecke._autgrp_naive(G)
      @test order == ZZRingElem(2)^n * factorial(ZZRingElem(n))
      @test all(g -> _is_auto(G, g), gens)
    end
  end

  @testset "3(I+J)_26 lattice (rank 26)" begin
    # Gram matrix 3*(I + J) of rank 26, isomorphic to 3*A_26
    # Automorphism group order = 2 * 27!
    G = matrix(ZZ, 26, 26, [i == j ? 6 : 3 for i in 1:26 for j in 1:26])
    order, gens = Hecke._autgrp_naive(G)
    @test order == 2 * factorial(ZZRingElem(27))
    @test all(g -> _is_auto(G, g), gens)
  end
end
