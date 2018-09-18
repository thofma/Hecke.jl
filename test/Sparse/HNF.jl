@testset "Hermite normal form" begin
  for i in 1:10
    r = 200
    c = 100
    A = matrix(FlintZZ, rand([0,0,0,0,0,0,0,0,0,0,1], r, c))
    As = sparse_matrix(A)
    @test sub(hnf(A), 1:c, 1:c) == fmpz_mat(hnf(As))
  end
end

