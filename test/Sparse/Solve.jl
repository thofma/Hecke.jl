# Triangular solving must preserve its inputs and own the solution coefficients.
@testset "Sparse triangular solution ownership" begin
  function dense_triangular_solution(M, v, R)
    w = deepcopy(v)
    x = [zero(R) for _ in axes(M, 1)]
    pivots = [findfirst(!iszero, M[i, :]) for i in axes(M, 1)]
    for c in eachindex(w)
      iszero(w[c]) && continue
      j = findfirst(==(c), pivots)
      j === nothing && return false, x
      p = w[c] * inv(M[j, c])
      x[j] = p
      w = [w[k] - p * M[j, k] for k in eachindex(w)]
    end
    return true, x
  end

  function check_triangular_solution(A, g)
    local R = base_ring(A)
    A_before = deepcopy(A)
    g_before = deepcopy(g)
    dense_basis = [A_before[i, j] for i in 1:nrows(A), j in 1:ncols(A)]
    row_values = Vector(g_before, ncols(A))
    expected_fl, expected = dense_triangular_solution(dense_basis, row_values, R)

    fl, sol = Hecke._can_solve_ut(A, g)
    @test fl == expected_fl
    @test Vector(sol, nrows(A)) == expected
    @test A == A_before
    @test g == g_before
    @test sol !== g
    @test sol.pos !== g.pos
    @test sol.values !== g.values
    for a in A.rows
      @test sol.pos !== a.pos
      @test sol.values !== a.values
    end
    if fl
      @test dense_row(sol, nrows(A)) * matrix(A) == dense_row(g, ncols(A))
      @test Hecke._solve_ut(A, g) == sol
    else
      @test_throws AssertionError Hecke._solve_ut(A, g)
    end
    @test A == A_before
    @test g == g_before

    if !isempty(sol.values)
      sol.values[1] = add!(sol.values[1], sol.values[1], one(R))
      @test A == A_before
      @test g == g_before
    end
    push!(sol.pos, nrows(A) + 1)
    push!(sol.values, one(R))
    @test A == A_before
    @test g == g_before
  end

  M = [3 2 0 1 0; 0 3 2 0 1; 0 0 3 1 2]
  gap = [1 2 0 1 0; 0 0 3 2 1]
  square = [1 2 1; 0 1 2; 0 0 1]
  cases = ((M, [6, 7, 11, 5, 7]), (M, [6, 7, 11, 6, 7]),
           (M, zeros(Int, 5)), (gap, [1, 2, 3, 3, 1]),
           (gap, [0, 1, 0, 0, 0]), (gap, [1, 3, 3, 3, 1]),
           (square, [1, 2, 3]), (zeros(Int, 0, 5), [1, 0, 0, 0, 0]),
           (zeros(Int, 2, 5), zeros(Int, 5)),
           (zeros(Int, 0, 0), Int[]))
  F4 = GF(2, 2)
  rings = (QQ, GF(101), residue_ring(ZZ, 101)[1], GF(2), F4)
  @testset "R = $R" for R in rings
    for (N, v) in cases
      A = sparse_matrix(matrix(R, N))
      g = sparse_row(matrix(R, 1, length(v), v))
      check_triangular_solution(A, g)
    end

    A = sparse_matrix(R, square)
    check_triangular_solution(A, A[1])
    g = sparse_row(matrix(R, 1, 3, [2, 3, 1]))
    g.values[1] = A[1].values[end]
    @test g.values[1] === A[1].values[end]
    check_triangular_solution(A, g)
  end

  a = gen(F4)
  A = sparse_matrix(matrix(F4, [a F4(1) a + 1; F4(0) a + 1 a]))
  g = sparse_row(matrix(F4, 1, 3, [a^2, a + 1, F4(1)]))
  check_triangular_solution(A, g)
end

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
    M = matrix(QQ, rand([0,0,0,0,0,0,0,0,0,0,1], r, c))
    Ms = sparse_matrix(M)
    N = matrix(QQ, rand([0,0,0,0,0,0,0,0,0,0,1], r, 2))
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

@testset "Sparse solving requires matching base fields" begin
  k, _ = quadratic_field(2)
  l, _ = quadratic_field(3)
  A = sparse_matrix(k, [1 0; 0 1])
  B = sparse_matrix(l, [1 0; 0 1])
  for side in (:left, :right)
    @test_throws ArgumentError can_solve(A, B; side)
    @test_throws ArgumentError can_solve_with_solution(A, B; side)
    @test_throws ArgumentError solve(A, B; side)
  end
  @test_throws ArgumentError can_solve(A, B.rows[1])
  @test_throws ArgumentError can_solve_with_solution(A, B.rows[1])
  @test_throws ArgumentError solve(A, B.rows[1])
end
