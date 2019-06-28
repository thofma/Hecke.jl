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

end
