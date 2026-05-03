using Printf

@testset "Flatter" begin
  # Helper: generate a q-ary lattice basis (common benchmark for lattice reduction)
  # Returns an n x n matrix where first k rows are random mod q, rest is q * I_n
  function _qary_lattice(n::Int, k::Int, bits::Int)
    q = rand_bits(ZZ, bits)
    M = zero_matrix(ZZ, n, n)
    for i in 1:k, j in 1:n
      M[i, j] = rand_bits(ZZ, bits)
    end
    for i in (k + 1):n
      M[i, i] = q
    end
    return M
  end

  # Helper: check that two matrices span the same row lattice
  function _same_lattice(A::ZZMatrix, B::ZZMatrix)
    return hnf(A) == hnf(B)
  end

  @testset "flatter correctness (small)" begin
    # 1x1
    M1 = matrix(ZZ, 1, 1, [42])
    @test Hecke.flatter(M1) == M1

    # 2x2
    M2 = ZZ[1 2; 3 4]
    R2 = Hecke.flatter(M2)
    @test _same_lattice(M2, R2)
    @test abs(det(R2)) == abs(det(M2))

    # 3x3
    M3 = ZZ[1 0 2; 0 1 -1; 3 2 1]
    R3 = Hecke.flatter(M3)
    @test _same_lattice(M3, R3)

    # 4x4
    M4 = ZZ[1 0 0 7; 0 1 0 -3; 0 0 1 5; 0 0 0 11]
    R4 = Hecke.flatter(M4)
    @test _same_lattice(M4, R4)

    # Identity should be returned unchanged
    I4 = identity_matrix(ZZ, 4)
    @test Hecke.flatter(I4) == I4

    # 2x2 already reduced
    M2r = ZZ[1 0; 0 1]
    L2r, T2r = Hecke.flatter_with_transform(M2r)
    @test L2r == M2r
    @test T2r == identity_matrix(ZZ, 2)

    # 5x5 with negative entries
    M5 = ZZ[3 -1 2 0 4; -2 5 -1 3 0; 1 0 -4 2 1; 0 3 1 -2 5; 4 -2 0 1 -3]
    R5 = Hecke.flatter(M5)
    @test _same_lattice(M5, R5)
    @test abs(det(R5)) == abs(det(M5))

    # 6x6 (first size that exercises the recursive split)
    M6 = ZZ[1 0 0 0 0 17; 0 1 0 0 0 -5; 0 0 1 0 0 8;
            0 0 0 1 0 -12; 0 0 0 0 1 3; 0 0 0 0 0 23]
    R6 = Hecke.flatter(M6)
    @test _same_lattice(M6, R6)
    @test abs(det(R6)) == abs(det(M6))
  end

  @testset "flatter_with_transform" begin
    M = ZZ[1 0 0 7; 0 1 0 -3; 0 0 1 5; 0 0 0 11]
    L, T = Hecke.flatter_with_transform(M)
    @test L == T * M
    @test _same_lattice(M, L)
    @test abs(det(T)) == 1

    # Already reduced
    I3 = identity_matrix(ZZ, 3)
    L3, T3 = Hecke.flatter_with_transform(I3)
    @test L3 == I3
    @test T3 == I3

    # Non-square-like: 6x6 with large off-diagonal
    M6 = ZZ[1 0 0 0 0 100; 0 1 0 0 0 200; 0 0 1 0 0 300;
            0 0 0 1 0 400; 0 0 0 0 1 500; 0 0 0 0 0 7]
    L6, T6 = Hecke.flatter_with_transform(M6)
    @test L6 == T6 * M6
    @test _same_lattice(M6, L6)
    @test abs(det(T6)) == 1

    # Random medium size
    M = _qary_lattice(12, 6, 30)
    L, T = Hecke.flatter_with_transform(M)
    @test L == T * M
    @test _same_lattice(M, L)
    @test abs(det(T)) == 1
  end

  @testset "flatter correctness (medium, q-ary)" begin
    # 8x8 q-ary lattice with 20-bit entries
    M = _qary_lattice(8, 4, 20)
    R = Hecke.flatter(M)
    @test _same_lattice(M, R)
    @test abs(det(R)) == abs(det(M))

    # 10x10 q-ary lattice with 50-bit entries
    M = _qary_lattice(10, 5, 50)
    R = Hecke.flatter(M)
    @test _same_lattice(M, R)

    # 10x10 with very small entries
    M = _qary_lattice(10, 5, 5)
    R = Hecke.flatter(M)
    @test _same_lattice(M, R)

    # 14x14 odd dimension
    M = _qary_lattice(14, 7, 40)
    R = Hecke.flatter(M)
    @test _same_lattice(M, R)
    @test abs(det(R)) == abs(det(M))
  end

  @testset "flatter correctness (larger, q-ary)" begin
    # 20x20 q-ary lattice
    M = _qary_lattice(20, 10, 100)
    R = Hecke.flatter(M)
    @test _same_lattice(M, R)
    @test abs(det(R)) == abs(det(M))
  end

  @testset "flatter_gram correctness" begin
    # Build a positive definite Gram matrix from a random basis
    B = ZZ[2 1 0; 1 3 1; 0 1 2]
    G = B * transpose(B)
    Gr = Hecke.flatter_gram(G)
    # Gr should be positive definite and have same determinant
    @test det(Gr) == det(G)
    @test Gr[1, 1] > 0  # positive definite check (first entry)

    # 1x1
    G1 = matrix(ZZ, 1, 1, [17])
    @test Hecke.flatter_gram(G1) == G1

    # 2x2
    G2 = ZZ[5 2; 2 3]
    Gr2 = Hecke.flatter_gram(G2)
    @test det(Gr2) == det(G2)

    # 5x5
    B5 = zero_matrix(ZZ, 5, 5)
    for i in 1:5, j in 1:5
      B5[i, j] = rand_bits(ZZ, 10) - ZZ(512)
    end
    # Make sure it's invertible
    while det(B5) == 0
      for i in 1:5, j in 1:5
        B5[i, j] = rand_bits(ZZ, 10) - ZZ(512)
      end
    end
    G5 = B5 * transpose(B5)
    Gr5 = Hecke.flatter_gram(G5)
    @test det(Gr5) == det(G5)

    # 8x8 from q-ary lattice
    M8 = _qary_lattice(8, 4, 20)
    G8 = M8 * transpose(M8)
    Gr8 = Hecke.flatter_gram(G8)
    @test det(Gr8) == det(G8)
  end

  @testset "flatter_gram_with_transform" begin
    B = ZZ[2 1 0 1; 1 3 1 0; 0 1 2 1; 1 0 1 3]
    G = B * transpose(B)
    T = Hecke.flatter_gram_with_transform(G)
    if T !== nothing
      Gr = T * G * transpose(T)
      @test det(Gr) == det(G)
      @test abs(det(T)) == 1
    end

    # Already reduced
    I3 = identity_matrix(ZZ, 3)
    @test Hecke.flatter_gram_with_transform(I3) === nothing

    # 6x6 Gram matrix
    B6 = zero_matrix(ZZ, 6, 6)
    for i in 1:6
      B6[i, i] = ZZ(1)
    end
    B6[1, 6] = ZZ(50)
    B6[2, 5] = ZZ(-30)
    G6 = B6 * transpose(B6)
    T6 = Hecke.flatter_gram_with_transform(G6)
    if T6 !== nothing
      Gr6 = T6 * G6 * transpose(T6)
      @test det(Gr6) == det(G6)
      @test abs(det(T6)) == 1
      @test Gr6 == transpose(Gr6)  # symmetric
    end
  end

  @testset "flatter vs LLL comparison" begin
    # Compare that flatter produces vectors of comparable or smaller norm
    M = _qary_lattice(15, 7, 40)
    R_flatter = Hecke.flatter(M)
    ctx = LLLContext(0.99, 0.51)
    R_lll = lll(M, ctx)

    @test _same_lattice(M, R_flatter)
    @test _same_lattice(M, R_lll)

    # Both should produce short first vector
    norm_flatter = sum(R_flatter[1, j]^2 for j in 1:ncols(R_flatter))
    norm_lll = sum(R_lll[1, j]^2 for j in 1:ncols(R_lll))
    # flatter should produce comparable quality
    @test nbits(norm_flatter) <= nbits(norm_lll) + ncols(M)
  end

  @testset "flatter and flatter_gram consistency" begin
    # Reducing a basis with flatter should give the same Gram matrix quality
    # as reducing the Gram matrix directly with flatter_gram
    M = _qary_lattice(10, 5, 30)
    G = M * transpose(M)

    R = Hecke.flatter(M)
    Gr_basis = R * transpose(R)

    Gr_gram = Hecke.flatter_gram(G)

    # Both should have the same determinant as the original
    @test det(Gr_basis) == det(G)
    @test det(Gr_gram) == det(G)

    # Both reduced Gram matrices should have reasonably small first diagonal entry
    # (not necessarily the same, but both reduced)
    @test Gr_basis[1, 1] > 0
    @test Gr_gram[1, 1] > 0
  end

  @testset "flatter with large entries" begin
    # Lattice with very large entries (500+ bits)
    M = _qary_lattice(8, 4, 500)
    R = Hecke.flatter(M)
    @test _same_lattice(M, R)
    @test abs(det(R)) == abs(det(M))

    L, T = Hecke.flatter_with_transform(M)
    @test L == T * M
    @test abs(det(T)) == 1
  end

  @testset "flatter idempotent" begin
    # Reducing an already-reduced matrix should not change it (much)
    M = _qary_lattice(10, 5, 30)
    R1 = Hecke.flatter(M)
    R2 = Hecke.flatter(R1)
    # The result should span the same lattice
    @test _same_lattice(R1, R2)
    # An already-reduced basis should ideally be unchanged
    @test R1 == R2
  end

  @testset "flatter diagonal and scaled identity" begin
    # Diagonal matrix
    D = diagonal_matrix(ZZ.([3, 7, 11, 5]))
    Rd = Hecke.flatter(D)
    @test _same_lattice(D, Rd)
    @test abs(det(Rd)) == abs(det(D))

    # Scaled identity
    S = ZZ(13) * identity_matrix(ZZ, 5)
    Rs = Hecke.flatter(S)
    @test Rs == S
  end

  @testset "flatter non-square matrices" begin
    # 2x3: two vectors in Z^3
    M = ZZ[1 2 3; 4 5 6]
    R = Hecke.flatter(M)
    @test _same_lattice(M, R)
    @test nrows(R) == 2
    @test ncols(R) == 3

    L, T = Hecke.flatter_with_transform(M)
    @test L == T * M
    @test size(T) == (2, 2)
    @test abs(det(T)) == 1

    # 1x5: single vector, should be unchanged
    M1 = ZZ[3 -7 2 11 -4]
    R1 = Hecke.flatter(M1)
    @test R1 == M1
    L1, T1 = Hecke.flatter_with_transform(M1)
    @test L1 == M1
    @test T1 == identity_matrix(ZZ, 1)

    # 3x5
    M35 = ZZ[1 0 0 7 -3; 0 1 0 -2 5; 0 0 1 4 8]
    R35 = Hecke.flatter(M35)
    @test _same_lattice(M35, R35)
    @test nrows(R35) == 3
    @test ncols(R35) == 5

    L35, T35 = Hecke.flatter_with_transform(M35)
    @test L35 == T35 * M35
    @test abs(det(T35)) == 1

    # 4x8 with larger entries
    M48 = zero_matrix(ZZ, 4, 8)
    for i in 1:4
      M48[i, i] = ZZ(1)
    end
    for i in 1:4, j in 5:8
      M48[i, j] = rand_bits(ZZ, 30) - ZZ(2)^29
    end
    R48 = Hecke.flatter(M48)
    @test _same_lattice(M48, R48)
    @test nrows(R48) == 4
    @test ncols(R48) == 8

    L48, T48 = Hecke.flatter_with_transform(M48)
    @test L48 == T48 * M48
    @test abs(det(T48)) == 1

    # 5x10 random
    M510 = zero_matrix(ZZ, 5, 10)
    for i in 1:5, j in 1:10
      M510[i, j] = rand_bits(ZZ, 20) - ZZ(2)^19
    end
    while rank(M510) < 5
      for i in 1:5, j in 1:10
        M510[i, j] = rand_bits(ZZ, 20) - ZZ(2)^19
      end
    end
    R510 = Hecke.flatter(M510)
    @test _same_lattice(M510, R510)

    L510, T510 = Hecke.flatter_with_transform(M510)
    @test L510 == T510 * M510
    @test abs(det(T510)) == 1

    # 6x12 larger non-square
    M612 = zero_matrix(ZZ, 6, 12)
    for i in 1:6
      M612[i, i] = ZZ(1)
    end
    for i in 1:6, j in 7:12
      M612[i, j] = rand_bits(ZZ, 50) - ZZ(2)^49
    end
    R612 = Hecke.flatter(M612)
    @test _same_lattice(M612, R612)

    L612, T612 = Hecke.flatter_with_transform(M612)
    @test L612 == T612 * M612
    @test abs(det(T612)) == 1
  end

  @testset "Timing: flatter vs LLL" begin
    println()
    println("=" ^ 70)
    println("  Flatter vs LLL Timing Comparison")
    println("=" ^ 70)
    println("  (Note: flatter excels for large dimensions with large entries)")
    println()

    for (n, k, bits) in [(20, 10, 100), (30, 15, 150), (40, 20, 200), (50, 25, 200)]
      M = _qary_lattice(n, k, bits)
      ctx = LLLContext(0.99, 0.51)

      # Warmup
      if n <= 20
        _ = lll(M, ctx)
        _ = Hecke.flatter(M)
      end

      t_lll = @elapsed R_lll = lll(M, ctx)
      t_flatter = @elapsed R_flatter = Hecke.flatter(M)

      norm_lll = sum(R_lll[1, j]^2 for j in 1:ncols(R_lll))
      norm_flatter = sum(R_flatter[1, j]^2 for j in 1:ncols(R_flatter))

      @printf("  n=%3d, k=%2d, bits=%3d | LLL: %8.3fs (|v1|²~2^%d) | flatter: %8.3fs (|v1|²~2^%d) | speedup: %.2fx\n",
              n, k, bits, t_lll, nbits(norm_lll), t_flatter, nbits(norm_flatter),
              t_lll / max(t_flatter, 1e-9))

      @test _same_lattice(M, R_flatter)
    end
    println("=" ^ 70)
  end
end
