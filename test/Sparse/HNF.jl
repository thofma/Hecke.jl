@testset "Hermite normal form" begin
  for i in 1:10
    r = 200
    c = 100
    A = matrix(FlintZZ, rand([0,0,0,0,0,0,0,0,0,0,1], r, c))
    As = sparse_matrix(A)
    @test hnf(A) == fmpz_mat(hnf(As))

    H, T = Hecke.hnf_kannan_bachem(As, Val{true})
    B = deepcopy(As)

    for t in T
      Hecke.apply_left!(B, t)
    end

    @test fmpz_mat(B) == hnf(A)
  end
end

