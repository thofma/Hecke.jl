@testset "Conformance tests" begin
  F, _ = cyclotomic_field(20)
  OF = maximal_order(F)
  P = prime_decomposition(OF, 2)[1][1]
  Kcomp, _ = completion(F, P)

  Ks = [
         padic_field(17), # PadicField
         qadic_field(17, 2)[1], # QadicField
         Kcomp, # LocalField
         laurent_series_field(GF(17), 64, "t")[1], # LaurentSeriesRing
       ]

  @testset "...for $K" for K in Ks
    O = valuation_ring(K)
    pi = uniformizer(O)
    R, _ = residue_ring(O, pi^3)
    # For Kcomp, we have valuation(pi) == 1//2
    @test Hecke._exponent(R) == 3
    @test !is_domain_type(elem_type(R))
    @test is_exact_type(elem_type(R))
    ConformanceTests.test_Ring_interface(R)

    p = uniformizer(R)
    @test p == R(pi)
    @test p == R(uniformizer(K))
    p = uniformizer(R, 2)
    @test p == R(pi^2)
    p = uniformizer(R, 3)
    @test is_zero(p)

    # the euclidean conformance test seems to assume that the ring is a domain
    R, _ = residue_ring(O, pi)
    ConformanceTests.test_EuclideanRing_interface(R)
  end
end

@testset "Map for $K" for K in [qadic_field(17, 2)[1], laurent_series_field(GF(17), 64, "t")[1]]
  R = valuation_ring(K)
  pi = uniformizer(R)
  S, RtoS = residue_ring(R, pi^3)

  @test is_zero(RtoS(R()))
  @test is_one(RtoS(R(1)))
  @test_throws ArgumentError RtoS(setprecision!(R(1), 1))

  for a in [ConformanceTests.generate_element(R) for i in 1:10]
    @test RtoS\RtoS(a) == a
    for b in [ConformanceTests.generate_element(R) for i in 1:10]
      @test RtoS\RtoS(b) == b
      @test RtoS(a + b) == RtoS(a) + RtoS(b)
      @test RtoS(a * b) == RtoS(a) * RtoS(b)
    end
  end
end

@testset "gcdxx" begin
  F, _ = cyclotomic_field(20)
  OF = maximal_order(F)
  P = prime_decomposition(OF, 2)[1][1]
  Kcomp, _ = completion(F, P)

  @testset "...for $K" for (k, K) in [(QQ, Kcomp), (GF(17), laurent_series_field(GF(17), 64, "t")[1])]
    R = valuation_ring(K)
    pi = uniformizer(R)
    S, RtoS = residue_ring(R, pi^3)

    for a in [zero(S), one(S), S(pi), S(pi + 1), inv(k(3))*S(pi^2)]
      for b in [zero(S), one(S), S(pi), S(pi + 1), inv(k(3))*S(pi^2)]
        g, u, v, s, t = Hecke.AbstractAlgebra.gcdxx(a, b)
        @test g == gcd(a, b)
        @test g == u*a + v*b
        @test is_zero(s*a + t*b)
        @test is_one(u*t - v*s)
      end
    end

    for a in [zero(S), one(S), S(pi), S(pi + 1), inv(k(3))*S(pi^2)]
      b = annihilator(a)
      @test is_zero(b*a)
      r = absolute_ramification_index(K)
      va = is_zero(a) ? Hecke._exponent(S) : r * valuation(lift(a))
      vb = is_zero(b) ? Hecke._exponent(S) : r * valuation(lift(b))
      @test (va + vb) == Hecke._exponent(S)
    end
  end
end

@testset "Linear algebra (characteristic 0)" begin
  F, _ = cyclotomic_field(20)
  OF = maximal_order(F)
  P = prime_decomposition(OF, 2)[1][1]
  K, toK = completion(F, P)
  R = valuation_ring(K)
  pi = uniformizer(R)
  S, RtoS = residue_ring(R, pi^8)

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
  @test is_zero(K*N)
  @test nrows(K) == 1
  K = @inferred kernel(N, side = :right)
  @test is_zero(N*K)
  @test ncols(K) == 1
end

@testset "Linear algebra (positive characteristic)" begin
  K, _ = laurent_series_field(GF(101), 10, "x")
  R = valuation_ring(K)
  pi = uniformizer(R)
  S, RtoS = residue_ring(R, pi^6)

  M = matrix(S, [1 2 + pi 3 + pi^2 4 + pi^3 5 + pi^4; 0 0 8 9 + pi 10 + pi^2; 0 0 0 14 15 + pi])

  for b in [ [S(1), S(2 + pi), S(3 + pi^2)],
            matrix(S, 3, 1, [S(1), S(2 + pi), S(3 + pi^2)]),
            matrix(S, 3, 2, [S(1), S(2), S(3 + pi), S(4 + pi), S(5 + pi^2), S(6 + pi^2)]) ]
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

  for b in [ [S(1), S(1 + pi), S(1 + pi^2), S(1 + pi^3), S(1 + pi^4)],
            matrix(S, 1, 5, [S(1), S(1 + pi), S(1 + pi^2), S(1 + pi^3), S(1 + pi^4)]),
            matrix(S, 2, 5, [S(1), S(1 + pi), S(1 + pi^2), S(1 + pi^3), S(1 + pi^4),
                             S(1), S(1 + pi), S(1 + pi^2), S(1 + pi^3), S(1 + pi^4)]) ]
    @test_throws ArgumentError solve(M, b)
    @test @inferred !can_solve(M, b)
    fl, x = @inferred can_solve_with_solution(M, b)
    @test !fl
    fl, x, K = @inferred can_solve_with_solution_and_kernel(M, b)
    @test !fl
  end

  for b in [ [S(1), S(2 + pi), S(3 + pi^2), S(4 + pi^3), S(5 + pi^4)],
            matrix(S, 1, 5, [S(1), S(2 + pi), S(3 + pi^2), S(4 + pi^3), S(5 + pi^4)]),
            matrix(S, 2, 5, [S(1), S(2 + pi), S(3 + pi^2), S(4 + pi^3), S(5 + pi^4),
                             S(0), S(0), S(8), S(9 + pi), S(10 + pi^2)]) ]
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

  N = matrix(S, 1, 1, [pi])
  K = @inferred kernel(N)
  @test is_zero(K*N)
  @test nrows(K) == 1
  K = @inferred kernel(N, side = :right)
  @test is_zero(N*K)
  @test ncols(K) == 1
end

@testset "Linear solving context (characteristic 0)" begin
  F, _ = cyclotomic_field(20)
  OF = maximal_order(F)
  P = prime_decomposition(OF, 2)[1][1]
  K, toK = completion(F, P)
  R = valuation_ring(K)
  pi = uniformizer(R)
  S, RtoS = residue_ring(R, pi^8)

  M = matrix(S, [1 2 3 4 5; 0 0 8 9 10; 0 0 0 14 15])
  C = solve_init(M)
  @test C isa AbstractAlgebra.solve_context_type(S)
  @test C isa AbstractAlgebra.solve_context_type(M)

  @test AbstractAlgebra.Solve.matrix_normal_form_type(C) === AbstractAlgebra.Solve.HowellFormTrait()

  @test C isa AbstractAlgebra.solve_context_type(AbstractAlgebra.Solve.HowellFormTrait(), elem_type(S))
  @test C isa AbstractAlgebra.solve_context_type(AbstractAlgebra.Solve.HowellFormTrait(), zero(S))
  @test C isa AbstractAlgebra.solve_context_type(AbstractAlgebra.Solve.HowellFormTrait(), typeof(S))
  @test C isa AbstractAlgebra.solve_context_type(AbstractAlgebra.Solve.HowellFormTrait(), S)
  @test C isa AbstractAlgebra.solve_context_type(AbstractAlgebra.Solve.HowellFormTrait(), typeof(M))
  @test C isa AbstractAlgebra.solve_context_type(AbstractAlgebra.Solve.HowellFormTrait(), M)

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

@testset "Linear solving context (positive characteristic)" begin
  K, _ = laurent_series_field(GF(101), 10, "x")
  R = valuation_ring(K)
  pi = uniformizer(R)
  S, RtoS = residue_ring(R, pi^6)

  M = matrix(S, [1 2 + pi 3 + pi^2 4 + pi^3 5 + pi^4; 0 0 8 9 + pi 10 + pi^2; 0 0 0 14 15 + pi])

  C = solve_init(M)
  @test C isa AbstractAlgebra.solve_context_type(S)
  @test C isa AbstractAlgebra.solve_context_type(M)

  @test AbstractAlgebra.Solve.matrix_normal_form_type(C) === AbstractAlgebra.Solve.HowellFormTrait()

  @test C isa AbstractAlgebra.solve_context_type(AbstractAlgebra.Solve.HowellFormTrait(), elem_type(S))
  @test C isa AbstractAlgebra.solve_context_type(AbstractAlgebra.Solve.HowellFormTrait(), zero(S))
  @test C isa AbstractAlgebra.solve_context_type(AbstractAlgebra.Solve.HowellFormTrait(), typeof(S))
  @test C isa AbstractAlgebra.solve_context_type(AbstractAlgebra.Solve.HowellFormTrait(), S)
  @test C isa AbstractAlgebra.solve_context_type(AbstractAlgebra.Solve.HowellFormTrait(), typeof(M))
  @test C isa AbstractAlgebra.solve_context_type(AbstractAlgebra.Solve.HowellFormTrait(), M)

  @test_throws ErrorException solve(C, [ S(1) ])
  @test_throws ErrorException solve(C, [ S(1) ], side = :right)
  @test_throws ErrorException solve(C, matrix(S, 1, 1, [ S(1) ]))
  @test_throws ErrorException solve(C, matrix(S, 1, 1, [ S(1) ]), side = :right)
  @test_throws ArgumentError solve(C, [ S(1), S(2 + pi), S(3 + pi^2) ], side = :test)
  @test_throws ArgumentError solve(C, matrix(S, 3, 1, [ S(1), S(2 + pi), S(3 + pi^2) ]), side = :test)

  for b in [ [S(1), S(2 + pi), S(3 + pi^2)],
            matrix(S, 3, 1, [S(1), S(2 + pi), S(3 + pi^2)]),
            matrix(S, 3, 2, [S(1), S(2), S(3 + pi), S(4 + pi), S(5 + pi^2), S(6 + pi^2)]) ]
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

  for b in [ [S(1), S(1 + pi), S(1 + pi^2), S(1 + pi^3), S(1 + pi^4)],
            matrix(S, 1, 5, [S(1), S(1 + pi), S(1 + pi^2), S(1 + pi^3), S(1 + pi^4)]),
            matrix(S, 2, 5, [S(1), S(1 + pi), S(1 + pi^2), S(1 + pi^3), S(1 + pi^4),
                             S(1), S(1 + pi), S(1 + pi^2), S(1 + pi^3), S(1 + pi^4)]) ]
    @test_throws ArgumentError solve(C, b)
    @test @inferred !can_solve(C, b)
    fl, x = @inferred can_solve_with_solution(C, b)
    @test !fl
    fl, x, K = @inferred can_solve_with_solution_and_kernel(C, b)
    @test !fl
  end

  for b in [ [S(1), S(2 + pi), S(3 + pi^2), S(4 + pi^3), S(5 + pi^4)],
            matrix(S, 1, 5, [S(1), S(2 + pi), S(3 + pi^2), S(4 + pi^3), S(5 + pi^4)]),
            matrix(S, 2, 5, [S(1), S(2 + pi), S(3 + pi^2), S(4 + pi^3), S(5 + pi^4),
                             S(0), S(0), S(8), S(9 + pi), S(10 + pi^2)]) ]
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

@testset "Matrix inversion" begin
  F, _ = cyclotomic_field(20)
  OF = maximal_order(F)
  P = prime_decomposition(OF, 2)[1][1]
  K, toK = completion(F, P)
  R = valuation_ring(K)
  pi = uniformizer(R)
  S, RtoS = residue_ring(R, pi^8)

  M = matrix(S, [1 2 3 4 5; 0 0 8 9 10; 0 0 0 14 15])
  @test_throws ErrorException inv(M)

  M = matrix(S, [2 0; 0 1])
  @test_throws ErrorException inv(M)
  M = matrix(S, [1 4; 0 1])
  N = inv(M)
  @test M * N == identity_matrix(S, 2)
  @test N * M == identity_matrix(S, 2)

  K, _ = laurent_series_field(GF(101), 10, "x")
  R = valuation_ring(K)
  pi = uniformizer(R)
  S, RtoS = residue_ring(R, pi^6)
  M = matrix(S, [1 pi^2; 0 3])
  N = inv(M)
  @test M * N == identity_matrix(S, 2)
  @test N * M == identity_matrix(S, 2)
end
