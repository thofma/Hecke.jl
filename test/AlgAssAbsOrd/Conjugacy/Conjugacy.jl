@testset "Conjugacy" begin
  a = fmpz[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
           1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
           0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
           0, -9604, -7056, -12076, -2392, -2253, 952, 46, -16, 0, 0, 0, 0, 0,
           0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4900, -140]

  b = fmpz[-4645900, -49391, -3848404, -16744, -15771, 6664, 17066, 470484,
           33488, 3779643, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1,
           0, -2, 0, -26, 0, -8, 0, 1, 0, 0, 1, 0, 9, -55750240, -592692,
           -46180848, -200928, -189252, 79969, 204792, 5645808, 396956,
           45355576, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -10, 0, -8, 0, 0, 0, 0, 1,
           0, 8, 101541620, 1079546, 84115116, 365984, 344709, -145656,
           -373022, -10283436, -692768, -82611077, -4, 0, 0, 0, 0, 0, 0, 0, 0,
           1, -18583040, -197564, -15393616, -66976, -63084, 26656, 68264,
           1881936, 129052, 15118432]

  A = matrix(ZZ, 10, 10, a)
  B = matrix(ZZ, 10, 10, b)

  fl, C = Hecke.isGLZ_conjugate(A, B)
  @test fl
  @test C * A == B * C

  A = matrix(QQ, 10, 10, a)
  B = matrix(QQ, 10, 10, b)

  fl, C = Hecke.isGLZ_conjugate(A, B)
  _C = map_entries(QQ, C)
  @test fl
  @test _C * A == B * _C

  A = fmpq(1, 10) * A
  B = fmpq(1, 10) * B
  fl, C = Hecke.isGLZ_conjugate(A, B)
  _C = map_entries(QQ, C)
  @test fl
  @test _C * A == B * _C

  fl, _ = Hecke.isGLZ_conjugate(QQ[1 2; 3 4], QQ[1 2 3; 4 5 6; 7 8 9])
  @test !fl

  R = ResidueRing(FlintZZ, fmpz(7))
  x, y = R(6), R(6)
  q, r = divrem(x, y)
  @test y * q + r == x
  @test iszero(r)
end
