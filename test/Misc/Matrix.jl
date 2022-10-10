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
  Hecke._copy_matrix_into_matrix!(Z, 1, 1, A)
  Hecke._copy_matrix_into_matrix!(Z, 3, 3, B)
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

