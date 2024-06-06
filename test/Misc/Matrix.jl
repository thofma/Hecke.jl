@testset "Misc/Matrix" begin
  A = ZZ[1 2; 3 4]
  B = ZZ[1;]
  Z = zero_matrix(ZZ, 3, 3)
  Hecke._copy_matrix_into_matrix(Z, 1, 1, A)
  Hecke._copy_matrix_into_matrix(Z, 3, 3, B)
  @test Z == diagonal_matrix(A, B)

  A = QQ[1 2; 3 4]
  B = QQ[1;]
  Z = zero_matrix(QQ, 3, 3)
  Hecke._copy_matrix_into_matrix(Z, 1, 1, A)
  Hecke._copy_matrix_into_matrix(Z, 3, 3, B)
  @test Z == diagonal_matrix(A, B)

  A = ZZ[1 2; 3 4]
  B = zero_matrix(ZZ, 2, 2)
  Hecke.transpose!(B, A)
  @test B == transpose(A)

  A = ZZ[1 2; 3 4; 5 6]
  B = zero_matrix(ZZ, 2, 3)
  Hecke.transpose!(B, A)
  @test B == transpose(A)

  A = QQ[1 2; 3 4]
  B = zero_matrix(QQ, 2, 2)
  Hecke.transpose!(B, A)
  @test B == transpose(A)

  A = QQ[1 2; 3 4; 5 6]
  B = zero_matrix(QQ, 2, 3)
  Hecke.transpose!(B, A)
  @test B == transpose(A)
end

@testset "Multiplicative order" begin
  L = direct_sum(root_lattice(:A, 7), root_lattice(:E, 8))[1]
  ao = automorphism_group_order(L)
  aag = automorphism_group_generators(L)
  for M in aag
    @test has_finite_multiplicative_order(M)
    n = multiplicative_order(M)
    @test divides(ao, n)[1]
  end
  @test_throws ArgumentError multiplicative_order(zero_matrix(QQ,1,1))
  @test_throws ArgumentError has_finite_multiplicative_order(aag[1][:, 1:end-1])
end

