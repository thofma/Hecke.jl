@testset "AbsAlgAss" begin

  @testset "Decomposition" begin
    Fp = GF(3)
    G = small_group(8, 4)
    FpG = group_algebra(Fp, G)

    dec = decompose(FpG)
    @test length(dec) == 5
    dim1 = 0
    dim4 = 0
    for (A, toFpG) in dec
      if dim(A) == 1
        dim1 += 1
      elseif dim(A) == 4
        dim4 += 1
      end
    end
    @test dim1 == 4
    @test dim4 == 1

    # Check whether the maps "work"
    A, toFpG = dec[1]
    e = toFpG(one(A))
    @test e^2 == e
    ee = toFpG\one(FpG)
    @test ee^2 == ee

    # And now the same for AlgAss
    FpG = AlgAss(FpG)[1]
    dec = decompose(FpG)
    @test length(dec) == 5
    dim1 = 0
    dim4 = 0
    for (A, toFpG) in dec
      if dim(A) == 1
        dim1 += 1
      elseif dim(A) == 4
        dim4 += 1
      end
    end
    @test dim1 == 4
    @test dim4 == 1

    # Check whether the maps "work"
    A, toFpG = dec[1]
    e = toFpG(one(A))
    @test e^2 == e
    ee = toFpG\one(FpG)
    @test ee^2 == ee

    # And now for AlgMat
    A = matrix_algebra(Fp, 2)

    dec = decompose(A)
    @test length(dec) == 1

    B, BtoA = dec[1]
    @test dim(B) == 4

    e = BtoA(one(B))
    @test e^2 == e
    ee = BtoA\one(A)
    @test ee^2 == ee

    A = matrix_algebra(Fp, [ matrix(Fp, [ 1 1; 0 1 ]) ]) # not semisimple!
    @test_throws AssertionError decompose(A)

    Qx, x = FlintQQ["x"]
    A = AlgAss((x^2 + 1)*(x^2 + 3))
    dec = Hecke.as_number_fields(A)

    @test length(dec) == 2
    @test degree(dec[1][1]) == 2
    @test degree(dec[2][1]) == 2

    K, AtoK = dec[1]
    e = AtoK(one(A))
    @test e^2 == e
    ee = AtoK\one(K)
    @test ee^2 == ee
  end

  @testset "Generators" begin
    Qx, x = FlintQQ["x"]
    A = AlgAss((x^2 + 1)*(x^2 + 3))
    g, full_basis, v = gens(A, Val{true})

    @test length(full_basis) == dim(A)

    M = zero_matrix(FlintQQ, dim(A), dim(A))
    for i = 1:dim(A)
      Hecke.elem_to_mat_row!(M, i, full_basis[i])
    end
    @test rank(M) == dim(A)

    for i = 1:dim(A)
      b = full_basis[i]
      a = one(A)
      for (j, k) in v[i]
        a *= g[j]^k
      end
      @test b == a
    end
  end

  @testset "Radical" begin
    Qx, x = FlintQQ["x"]
    # f = x^2 + 1
    # g = x^3 + 3x^2 + 5x - 5
    f2g3 = x^13 + 9x^12 + 44x^11 + 120x^10 + 205x^9 + 153x^8 + 32x^7 - 168x^6 - 5x^5 - 485x^4 + 500x^3 - 400x^2 + 375x - 125 # = f^2*g^3
    A = AlgAss(f2g3)
    fg = A(fmpq[-5, 5, -2, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0]) # = f*g
    J = radical(A)
    I = ideal(A, fg)
    @test I == J

    f = x^2 + 1
    K, a = number_field(f, "a")
    Ky, y = K["y"]
    # g = y^3 - 3y^2 - 3y + 2
    # h = y^2 + 5y + 5
    g2h3 = y^12 + 9y^11 + 3y^10 - 198y^9 - 603y^8 + 423y^7 + 4829y^6 + 8430y^5 + 4335y^4 - 2675y^3 - 3075y^2 + 500 # = g^2*h^3
    A = AlgAss(g2h3)
    gh = A(map(K, [10, -5, -28, -13, 2, 1, 0, 0, 0, 0, 0, 0])) # = g*h
    J = radical(A)
    I = ideal(A, gh)
    @test I == J

    G = small_group(8, 4)
    F2 = GF(2)
    A = group_algebra(F2, G)
    I = radical(A)
    @test nrows(basis_matrix(I, copy = false)) == 7
    A = AlgAss(A)[1]
    I = radical(A)
    @test nrows(basis_matrix(I, copy = false)) == 7

    F3 = GF(3)
    A = group_algebra(F3, G)
    I = radical(A)
    @test nrows(basis_matrix(I, copy = false)) == 0

    F4 = GF(2, 2)
    A = group_algebra(F4, G)
    I = radical(A)
    @test nrows(basis_matrix(I, copy = false)) == 7
    A = AlgAss(A)[1]
    I = radical(A)
    @test nrows(basis_matrix(I, copy = false)) == 7

    A = group_algebra(FlintQQ, G)
    I = radical(A)
    @test nrows(basis_matrix(I, copy = false)) == 0

    for K in [ F2, F4, FlintQQ ]
      A = matrix_algebra(K, [ matrix(K, 2, 2, [ 1, 0, 0, 0 ]), matrix(K, 2, 2, [ 0, 1, 0, 0 ]), matrix(K, 2, 2, [ 0, 0, 0, 1]) ]) # i. e. upper triangular matrices
      I = radical(A)
      @test nrows(basis_matrix(I, copy = false)) == 1
    end

  end

  @testset "rand" begin
    Fp = GF(3)
    G = small_group(8, 4)
    FpG = group_algebra(Fp, G)
    A = AlgAss(FpG)[1]
    @assert A isa Hecke.AbsAlgAss

    E = elem_type(A)
    @test rand(A) isa E
    @test rand(rng, A) isa E
    @test rand(A, 2, 3) isa Matrix{E}

    Random.seed!(rng, rand_seed)
    a = rand(rng, A)
    Random.seed!(rng, rand_seed)
    @test a == rand(rng, A)
  end

  K, a = quadratic_field(2)
  A = matrix_algebra(K, 3)
  Ares, = restrict_scalars(A, QQ)
  @test (@inferred Hecke.dimension_of_center(Ares)) == 2
  @test (@inferred Hecke.dimension_over_center(Ares)) == 9
  @test (@inferred Hecke.degree_as_central_simple_algebra(Ares)) == 3
end
