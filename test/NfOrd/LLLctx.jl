@testset "NfLat" begin
  Qx, x = QQ[:x]
  K, a = number_field(x^3 - 2, :a)
  O = maximal_order(K)
  L = Hecke.lattice(elem_in_nf.(basis(O)), discriminant(O))
  n = degree(K)

  @testset "minkowski_gram_mat_scaled" begin
    A = Hecke.minkowski_gram_mat_scaled(L, 200)

    # calls with at most the cached precision shift the cached matrix
    @test Hecke.minkowski_gram_mat_scaled(L, 200) == A

    B = Hecke.minkowski_gram_mat_scaled(L, 100)
    c = Hecke.minkowski_matrix(basis(L), 300)
    G = c * transpose(c)
    @test all(abs(B[i, j] - n * (i == j) - ZZ(2)^100 * G[i, j]) < 2 for i in 1:n, j in 1:n)
  end
end
