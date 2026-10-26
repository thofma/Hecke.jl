@testset "Deprecated keyword `isbasis`" begin
  Qx, x = QQ[:x]
  K, a = number_field(x^2 + 5, :a)
  B = basis(maximal_order(K), K)
  @test_deprecated order(K, B; isbasis = true)
  @test_deprecated order(B; isbasis = true)
  @test_deprecated subfield(K, [one(K), a]; isbasis = true)

  A = group_algebra(QQ, abelian_group([2]))
  @test_deprecated order(A, basis(A); isbasis = true)
  @test_deprecated matrix_algebra(QQ, [identity_matrix(QQ, 2)]; isbasis = true)

  V = quadratic_space(QQ, 2)
  @test_deprecated lattice(V, QQ[2 0; 4 0]; isbasis = false)
  @test_deprecated lattice_in_same_ambient_space(lattice(V), QQ[1 0]; isbasis = true)
end
