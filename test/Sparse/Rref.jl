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
  n, K = nullspace(M)
  N = sparse_matrix(FlintQQ)
  N.r = 2
  N.c = 2
  N.rows = K
  @test n == 2
  @test transpose(matrix(N)) == identity_matrix(FlintQQ, 2)

  M = sparse_matrix(matrix(GF(5), 3, 3, [ 0, 1, 2, 0, 1, 3, 0, 0, 4 ]))
  n, K = nullspace(M)
  N = sparse_matrix(GF(5))
  N.r = 1
  N.c = 3
  N.rows = K
  @test n == 1
  @test transpose(matrix(N)) == matrix(GF(5), 3, 1, [ 1, 0, 0 ])

  for i in 1:10
    r = 10
    c = 20
    M = matrix(FlintQQ, rand([0,0,0,0,0,0,0,0,0,0,1], r, c))
    Ms = sparse_matrix(M)
    ns, Ks = nullspace(Ms)
    n, K = nullspace(M)
    @test n == ns
    N = sparse_matrix(FlintQQ)
    N.r = ncols(K)
    N.c = nrows(K)
    N.rows = Ks
    @test transpose(matrix(N)) == K
  end
end
