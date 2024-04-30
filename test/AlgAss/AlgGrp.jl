@testset "Group algebras" begin
  G = small_group(8, 4)
  A = GroupAlgebra(FlintQQ, G)

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
    g, full_basis, v = gens(A, Val(true))

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

  @testset "Decomposition for abelian group algebras" begin
    G = abelian_group([2,4,6])
    QG = QQ[G]
    d = decompose(QG)
    idem = [y(one(x)) for (x, y) in d]
    @test isone(sum(idem))
    @test all(e^2 == e for e in idem)
    @test all(is_simple(x) for (x, _) in d)

    G = abelian_group([2,4,6])
    F = GF(5)
    QG = F[G]
    d = decompose(QG)
    idem = [y(one(x)) for (x, y) in d]
    @test isone(sum(idem))
    @test all(e^2 == e for e in idem)
    @test all(is_simple(x) for (x, _) in d)
  end

  @testset "Refined Wedderburn decomposition" begin
    G = small_group(8, 3)
    QG = QQ[G]
    Hecke._assert_has_refined_wedderburn_decomposition(QG)
    C = decompose(QG)
    for (B, _) in C
      @test isdefined(B, :isomorphic_full_matrix_algebra)
      M, f = B.isomorphic_full_matrix_algebra
      @test f(one(B)) == one(M)
      @test f(zero(B)) == zero(M)
      for i in 1:100
        a = rand(B, -1:1)
        b = rand(B, -1:1)
        @test f(a * b) == f(a) * f(b)
        @test f(a + b) == f(a) + f(b)
      end
    end
  end
end
