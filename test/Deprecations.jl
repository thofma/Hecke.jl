# TODO: use `@test_deprecated` once `isbasis` emits a deprecation warning
@testset "Keyword `isbasis`" begin
  Qx, x = QQ[:x]
  K, a = number_field(x^2 + 5, :a)
  B = basis(maximal_order(K), K)
  @test order(K, B; isbasis = true) == order(K, B; is_basis = true)
  @test order(B; isbasis = true) == order(B; is_basis = true)
  @test degree(subfield(K, [one(K), a]; isbasis = true)[1]) == 2

  A = group_algebra(QQ, abelian_group([2]))
  @test order(A, basis(A); isbasis = true) == order(A, basis(A); is_basis = true)
  @test dim(matrix_algebra(QQ, [identity_matrix(QQ, 2)]; isbasis = true)) == 1

  V = quadratic_space(QQ, 2)
  G = QQ[2 0; 4 0]
  @test lattice(V, G; isbasis = false) == lattice(V, G; is_basis = false)
  @test lattice_in_same_ambient_space(lattice(V), G[1:1, :]; isbasis = true) == lattice(V, G[1:1, :])
end
