function _test_elem(R::PadicField)
  p = prime(R)
  prec = rand(1:R.prec_max)
  r = ZZRingElem(0):p-1
  return R(sum(rand(r)*p^i for i in 0:prec))
end

function _test_elem(R::NonArchLocalField)
  d = degree(R)
  a = gen(R)
  x = R()
  for i in 0:d - 1
    if rand() < 0.5
      # Only fill every second coefficient
      continue
    end
    x += _test_elem(base_field(R))*a^i
  end
  return x
end

function test_elem(R::Hecke.LocalFieldValuationRingResidueRing)
  return R(_test_elem(Hecke._field(R)))
end

@testset "Conformance tests" begin
  # PadicField
  K = padic_field(17)
  R = valuation_ring(K)
  pi = uniformizer(R)
  S, RtoS = residue_ring(R, pi^3)
  test_Ring_interface(S)

  # the euclidean conformance test seems to assume that the ring is a domain
  S, RtoS = residue_ring(R, pi)
  test_EuclideanRing_interface(S)

  # QadicField
  K, a = qadic_field(17, 2)
  R = valuation_ring(K)
  pi = uniformizer(R)
  S, RtoS = residue_ring(R, pi^3)
  test_Ring_interface(S)

  # LocalField
  F, _ = cyclotomic_field(3)
  OF = maximal_order(F);
  K, toK = completion(F, 2*OF);
  R = valuation_ring(K)
  pi = uniformizer(R)
  S, RtoS = residue_ring(R, pi^3)
  test_Ring_interface(S)
end

@testset "Linear algebra" begin
  K, _ = qadic_field(2, 2)
  R = valuation_ring(K)
  pi = uniformizer(R)
  S, RtoS = residue_ring(R, pi^4)

  M = matrix(S, [1 2 3 4 5; 0 0 8 9 10; 0 0 0 14 15])

  for b in [ [ S(1), S(2), S(3) ],
            matrix(S, 3, 1, [ S(1), S(2), S(3) ]),
            matrix(S, 3, 2, [ S(1), S(2), S(3), S(4), S(5), S(6) ]) ]
    @test @inferred can_solve(M, b, side = :right)
    x = @inferred solve(M, b, side = :right)
    @test M*x == b
    fl, x = @inferred can_solve_with_solution(M, b, side = :right)
    @test fl
    @test M*x == b
    fl, x, K = @inferred can_solve_with_solution_and_kernel(M, b, side = :right)
    @test fl
    @test M*x == b
    @test is_zero(M*K)
    @test ncols(K) == 2
    K = @inferred kernel(M, side = :right)
    @test is_zero(M*K)
    @test ncols(K) == 2
  end

  for b in [ [ S(1), S(1), S(1), S(1), S(1) ],
            matrix(S, 1, 5, [ S(1), S(1), S(1), S(1), S(1) ]),
            matrix(S, 2, 5, [ S(1), S(1), S(1), S(1), S(1),
                             S(1), S(1), S(1), S(1), S(1) ]) ]
    @test_throws ArgumentError solve(M, b)
    @test @inferred !can_solve(M, b)
    fl, x = @inferred can_solve_with_solution(M, b)
    @test !fl
    fl, x, K = @inferred can_solve_with_solution_and_kernel(M, b)
    @test !fl
  end

  for b in [ [ S(1), S(2), S(3), S(4), S(5) ],
            matrix(S, 1, 5, [ S(1), S(2), S(3), S(4), S(5)]),
            matrix(S, 2, 5, [ S(1), S(2), S(3), S(4), S(5),
                             S(0), S(0), S(8), S(9), S(10) ]) ]
    @test @inferred can_solve(M, b)
    x = @inferred solve(M, b)
    @test x*M == b
    fl, x = @inferred can_solve_with_solution(M, b)
    @test fl
    @test x*M == b
    fl, x, K = @inferred can_solve_with_solution_and_kernel(M, b)
    @test fl
    @test x*M == b
    @test is_zero(K*M)
    @test nrows(K) == 0
    K = @inferred kernel(M)
    @test is_zero(K*M)
    @test nrows(K) == 0
  end

  N = zero_matrix(S, 2, 1)
  b = zeros(S, 2)
  fl, x, K = @inferred can_solve_with_solution_and_kernel(N, b, side = :right)
  @test fl
  @test N*x == b
  @test K == identity_matrix(S, 1)
  K = @inferred kernel(N, side = :right)
  @test K == identity_matrix(S, 1)

  N = zero_matrix(S, 1, 2)
  b = zeros(S, 1)
  fl, x, K = @inferred can_solve_with_solution_and_kernel(N, b, side = :right)
  @test fl
  @test N*x == b
  @test K == identity_matrix(S, 2) || K == swap_cols!(identity_matrix(S, 2), 1, 2)
  K = @inferred kernel(N, side = :right)
  @test K == identity_matrix(S, 2) || K == swap_cols!(identity_matrix(S, 2), 1, 2)

  N = matrix(S, 1, 1, [2])
  K = @inferred kernel(N)
  @test K == matrix(S, 1, 1, [8])
  K = @inferred kernel(N, side = :right)
  @test K == matrix(S, 1, 1, [8])
end

@testset "Linear solving context" begin
  K, _ = qadic_field(2, 2)
  R = valuation_ring(K)
  pi = uniformizer(R)
  S, RtoS = residue_ring(R, pi^4)

  M = matrix(S, [1 2 3 4 5; 0 0 8 9 10; 0 0 0 14 15])
  C = solve_init(M)

  @test C isa AbstractAlgebra.solve_context_type(elem_type(S))
  @test C isa AbstractAlgebra.solve_context_type(zero(S))
  @test C isa AbstractAlgebra.solve_context_type(typeof(S))
  @test C isa AbstractAlgebra.solve_context_type(S)
  @test C isa AbstractAlgebra.solve_context_type(typeof(M))
  @test C isa AbstractAlgebra.solve_context_type(M)

  @test_throws ErrorException solve(C, [ S(1) ])
  @test_throws ErrorException solve(C, [ S(1) ], side = :right)
  @test_throws ErrorException solve(C, matrix(S, 1, 1, [ S(1) ]))
  @test_throws ErrorException solve(C, matrix(S, 1, 1, [ S(1) ]), side = :right)
  @test_throws ArgumentError solve(C, [ S(1), S(2), S(3) ], side = :test)
  @test_throws ArgumentError solve(C, matrix(S, 3, 1, [ S(1), S(2), S(3) ]), side = :test)

  for b in [ [ S(1), S(2), S(3) ],
            matrix(S, 3, 1, [ S(1), S(2), S(3) ]),
            matrix(S, 3, 2, [ S(1), S(2), S(3), S(4), S(5), S(6) ]) ]
    @test @inferred can_solve(C, b, side = :right)
    x = @inferred solve(C, b, side = :right)
    @test M*x == b
    fl, x = @inferred can_solve_with_solution(C, b, side = :right)
    @test fl
    @test M*x == b
    fl, x, K = @inferred can_solve_with_solution_and_kernel(C, b, side = :right)
    @test fl
    @test M*x == b
    @test is_zero(M*K)
    @test ncols(K) == 2
    K = @inferred kernel(C, side = :right)
    @test is_zero(M*K)
    @test ncols(K) == 2
  end

  for b in [ [ S(1), S(1), S(1), S(1), S(1) ],
            matrix(S, 1, 5, [ S(1), S(1), S(1), S(1), S(1) ]),
            matrix(S, 2, 5, [ S(1), S(1), S(1), S(1), S(1),
                             S(1), S(1), S(1), S(1), S(1) ]) ]
    @test_throws ArgumentError solve(C, b)
    @test @inferred !can_solve(C, b)
    fl, x = @inferred can_solve_with_solution(C, b)
    @test !fl
    fl, x, K = @inferred can_solve_with_solution_and_kernel(C, b)
    @test !fl
  end

  for b in [ [ S(1), S(2), S(3), S(4), S(5) ],
            matrix(S, 1, 5, [ S(1), S(2), S(3), S(4), S(5)]),
            matrix(S, 2, 5, [ S(1), S(2), S(3), S(4), S(5),
                             S(0), S(0), S(8), S(9), S(10) ]) ]
    @test @inferred can_solve(C, b)
    x = @inferred solve(C, b)
    @test x*M == b
    fl, x = @inferred can_solve_with_solution(C, b)
    @test fl
    @test x*M == b
    fl, x, K = @inferred can_solve_with_solution_and_kernel(C, b)
    @test fl
    @test x*M == b
    @test is_zero(K*M)
    @test nrows(K) == 0
    K = @inferred kernel(C)
    @test is_zero(K*M)
    @test nrows(K) == 0
  end

  N = zero_matrix(S, 2, 1)
  C = solve_init(N)
  b = zeros(S, 2)
  fl, x, K = @inferred can_solve_with_solution_and_kernel(C, b, side = :right)
  @test fl
  @test N*x == b
  @test K == identity_matrix(S, 1)
  K = @inferred kernel(C, side = :right)
  @test K == identity_matrix(S, 1)

  N = zero_matrix(S, 1, 2)
  C = solve_init(N)
  b = zeros(S, 1)
  fl, x, K = @inferred can_solve_with_solution_and_kernel(C, b, side = :right)
  @test fl
  @test N*x == b
  @test K == identity_matrix(S, 2) || K == swap_cols!(identity_matrix(S, 2), 1, 2)
  K = @inferred kernel(C, side = :right)
  @test K == identity_matrix(S, 2) || K == swap_cols!(identity_matrix(S, 2), 1, 2)
end
