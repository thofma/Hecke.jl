@testset "Jordan and Rational canonical form" begin

  Qx, x = polynomial_ring(FlintQQ, "x")
  f = x^6 + rand(Qx, 1:5, -3:3)
  M = companion_matrix(f)
  @test minpoly(Qx, M) == f
  @test charpoly(Qx, M) == f

  ff = factor(f)
  g = first(keys(ff.fac))
  g = divexact(g, leading_coefficient(g))
  J = Hecke.jordan_block(g, 2)
  @test minpoly(Qx, J) == g^2
  @test charpoly(Qx, J) == g^2

  M = identity_matrix(FlintQQ, 6)
  for i = 1:6
    for j = i+1:6
      M[i, j] = rand(FlintQQ, -2:2)
    end
  end
  M1 = transpose(M)
  @test Hecke.is_similar(M, M1)
  MT = Hecke.conjugating_matrix(M, M1)
  @test MT*M1*inv(MT) == M
  J, S = jordan_normal_form(M)
  @test S*M*inv(S) == J
  for i = 1:6
    for j = 1:i-1
      @test iszero(J[i, j])
    end
  end
  for i = 1:5
    @test isone(J[i, i+1]) || iszero(J[i, i+1])
  end
  for i = 1:6
    for j = i+2:6
      @test iszero(J[i, i+2])
    end
  end


  f = x^3+ rand(Qx, 1:2, -2:2)
  g = x^3 + rand(Qx, 1:2, -2:2)
  f1 = f
  f2 = f*g
  C = zero_matrix(FlintQQ, 9, 9)
  Hecke._copy_matrix_into_matrix(C, 1, 1, companion_matrix(f1))
  Hecke._copy_matrix_into_matrix(C, 4, 4, companion_matrix(f2))
  CF, TM = rational_canonical_form(C)
  @test CF == C
  @test TM * C * inv(TM) == CF

  # Issue #1279
  K, _ = number_field(x^2 - 2)
  M = matrix(K, [ 0 1 1; 1//2 0 0 ; 1//2 0 0 ])
  J, S = jordan_normal_form(M)
  @test J == S*M*inv(S)
  @test Set([ J[1, 1], J[2, 2], J[3, 3] ]) == Set([ K(), K(1), K(-1) ])
end

@testset "Common eigenspaces" begin
  M = [ matrix(QQ, [ 0 1 0 0 0 0;
                    1 0 0 0 0 0;
                    0 0 1 0 0 0;
                    0 0 0 1 0 0;
                    0 0 0 0 1 0;
                    0 0 0 0 0 1; ]),
       matrix(QQ, [ 1 0 0 0 0 0;
                    0 1 0 0 0 0;
                    0 0 0 1 0 0;
                    0 0 1 0 0 0;
                    0 0 0 0 1 0;
                    0 0 0 0 0 1; ]),
       matrix(QQ, [ 1 0 0 0 0 0;
                    0 1 0 0 0 0;
                    0 0 1 0 0 0;
                    0 0 0 1 0 0;
                    0 0 0 0 0 1;
                    0 0 0 0 1 0; ]) ]

  Eig = common_eigenspaces(M, side = :right)
  V = zero_matrix(FlintQQ, 6, 0)
  for (e, v) in Eig
    @test length(e) == 3
    for i = 1:3
      @test M[i]*v == e[i]*v
    end
    V = hcat(V, v)
  end
  @test rref!(V) == 6

  Eig = common_eigenspaces(M, side = :left)
  V = zero_matrix(FlintQQ, 0, 6)
  for (e, v) in Eig
    @test length(e) == 3
    for i = 1:3
      @test v*M[i] == e[i]*v
    end
    V = vcat(V, v)
  end
  @test rref!(V) == 6

  N = [ matrix(QQ, [ 0 0 1 0 0 0;
                     1 0 0 0 0 0;
                     0 1 0 0 0 0;
                     0 0 0 1 0 0;
                     0 0 0 0 1 0;
                     0 0 0 0 0 1; ]),
        matrix(QQ, [ 1 0 0 0 0 0;
                     0 1 0 0 0 0;
                     0 0 1 0 0 0;
                     0 0 0 0 0 1;
                     0 0 0 1 0 0;
                     0 0 0 0 1 0; ]) ]

  @test_throws ErrorException Hecke.simultaneous_diagonalization(N)

  K, a = cyclotomic_field(3, "a")
  T, D = Hecke.simultaneous_diagonalization(N, K)
  for i = 1:length(N)
    @test T*N[i]*inv(T) == D[i]
    @test is_invertible(D[i])
    @test is_diagonal(D[i])
  end
end
