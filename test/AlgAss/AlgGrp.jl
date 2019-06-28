@testset "Group algebras" begin
  G = small_group(8, 4)
  A = AlgGrp(FlintQQ, G)

  @testset "Regular matrix algebra" begin
    B, BtoA = Hecke.regular_matrix_algebra(A)

    @test dim(B) == dim(A)

    for i = 1:dim(A)
      for j = 1:dim(A)
        @test BtoA(B[i])*BtoA(B[j]) == BtoA(B[i]*B[j])
        @test (BtoA\A[i])*(BtoA\A[j]) == BtoA\(A[i]*A[j])
      end
    end
  end

  @testset "Generators" begin
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
