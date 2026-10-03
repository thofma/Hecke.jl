@testset "quotients" begin
  M = Hecke.embedded_module(ZZ, QQ, QQ[2 0; 0 3])
  N = Hecke.embedded_module(ZZ, QQ, QQ[4 0; 0 6])

  Q, MtoQ = quo(M, N)
  x = Hecke._element_from_coordinates(M, ZZRingElem[1, 0])
  y = Hecke._element_from_coordinates(M, ZZRingElem[2, 0])
  @test !iszero(MtoQ(x))
  @test iszero(MtoQ(y))
  @test coordinates(preimage(MtoQ, MtoQ(x))) == coordinates(x)

  V, MtoV = Hecke.quotient_vector_space(M, N, ZZ(2))
  @test dim(V) == 2
  @test !iszero(MtoV(x))
  @test iszero(MtoV(y))
  @test coordinates(preimage(MtoV, MtoV(x))) == coordinates(x)

  Mline = Hecke.embedded_module(ZZ, QQ, QQ[1 0])
  Nline = Hecke.embedded_module(ZZ, QQ, QQ[0 1])
  @test_throws ArgumentError quo(Mline, Nline)
end
