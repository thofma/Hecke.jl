@testset "Sparse rref" begin
  M = sparse_matrix(zero_matrix(FlintQQ, 2, 2))
  @test rref(M) == (0, M)

  M = sparse_matrix(matrix(GF(5), 3, 3, [ 0, 1, 2, 0, 1, 3, 0, 0, 4 ]))
  @test rref(M) == (2, sparse_matrix(matrix(GF(5), 3, 3, [ 0, 1, 0, 0, 0, 1, 0, 0, 0, ])))

  for i in 1:10
    r = 20
    c = 10
    M = matrix(FlintQQ, rand([0,0,0,0,0,0,0,0,0,0,1], r, c))
    Ms = sparse_matrix(M)
    n, N = rref(M)
    ns, Ns = rref(Ms)
    @test n == ns
    @test matrix(Ns) == N
  end
end

@testset "Sparse kernel" begin
  M = sparse_matrix(zero_matrix(FlintQQ, 2, 2))
  @test nullspace(M) == (2, identity_matrix(FlintQQ, 2))

  M = sparse_matrix(matrix(GF(5), 3, 3, [ 0, 1, 2, 0, 1, 3, 0, 0, 4 ]))
  @test nullspace(M) == (1, matrix(GF(5), 3, 1, [ 1, 0, 0 ]))
  @test kernel(M, side = :left) == matrix(GF(5), 1, 3, [ 4, 1, 1 ])
  @test kernel(M, side = :right) == matrix(GF(5), 3, 1, [ 1, 0, 0 ])

  for i in 1:10
    r = 10
    c = 20
    M = matrix(FlintQQ, rand([0,0,0,0,0,0,0,0,0,0,1], r, c))
    @test kernel(sparse_matrix(M)) == kernel(M)
  end
end
