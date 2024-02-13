@testset "Sparse solving" begin
  M = sparse_matrix(QQ, [ 1 0 0; 0 0 0; 0 0 1 ])
  b = sparse_matrix(QQ, [ 1 0 3 ])

  fl, sol = can_solve_with_solution(M, b, side = :left)
  @test fl
  @test matrix(sol)*matrix(M) == matrix(b)
  @test nnz(sol) == sum(length(sol.rows[i].values) for i = 1:nrows(sol))
  sol = solve(M, b, side = :left)
  @test matrix(sol)*matrix(M) == matrix(b)
  @test nnz(sol) == sum(length(sol.rows[i].values) for i = 1:nrows(sol))

  fl, sol = can_solve_with_solution(M, transpose(b), side = :right)
  @test fl
  @test matrix(M)*matrix(sol) == matrix(transpose(b))
  @test nnz(sol) == sum(length(sol.rows[i].values) for i = 1:nrows(sol))
  sol = solve(M, transpose(b), side = :right)
  @test matrix(M)*matrix(sol) == matrix(transpose(b))
  @test nnz(sol) == sum(length(sol.rows[i].values) for i = 1:nrows(sol))

  fl, sol = can_solve_with_solution(M, b.rows[1])
  @test fl
  @test sol * M == b.rows[1]

  for i in 1:10
    r = 10
    c = 20
    M = matrix(FlintQQ, rand([0,0,0,0,0,0,0,0,0,0,1], r, c))
    Ms = sparse_matrix(M)
    N = matrix(FlintQQ, rand([0,0,0,0,0,0,0,0,0,0,1], r, 2))
    Ns = sparse_matrix(N)
    fl, sol = can_solve_with_solution(Ms, Ns, side = :right)
    @test fl == can_solve(Ms, Ns, side = :right)
    @test nnz(sol) == sum(length(sol.rows[i].values) for i = 1:nrows(sol); init = 0)
    fl2, sol2 = can_solve_with_solution(M, N, side = :right)
    @test fl2 == can_solve(M, N, side = :right)
    @test fl == fl2
    if fl
      @test M*matrix(sol) == N
    end
  end
end
