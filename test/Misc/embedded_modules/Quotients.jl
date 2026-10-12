@testset "quotients" begin
  M = Hecke.embedded_module(ZZ, QQ, QQ[2 0; 0 3])
  N = Hecke.embedded_module(ZZ, QQ, QQ[4 0; 0 6])

  Q, MtoQ = quo(M, N)
  @test MtoQ isa Hecke.EmbeddedModuleMap
  x = Hecke._element_from_coordinates(M, ZZRingElem[1, 0])
  y = Hecke._element_from_coordinates(M, ZZRingElem[2, 0])
  @test !iszero(MtoQ(x))
  @test iszero(MtoQ(y))
  @test coordinates(preimage(MtoQ, MtoQ(x))) == coordinates(x)

  V, MtoV, RtoF = Hecke.quotient_vector_space(M, N, ZZ(2))
  @test MtoV isa Hecke.EmbeddedModuleMap
  @test domain(MtoV) === M
  @test codomain(MtoV) === V
  @test domain(RtoF) === ZZ
  @test codomain(RtoF) === base_ring(V)
  @test dim(V) == 2
  @test !iszero(MtoV(x))
  @test iszero(MtoV(y))
  @test coordinates(preimage(MtoV, MtoV(x))) == coordinates(x)

  Mline = Hecke.embedded_module(ZZ, QQ, QQ[1 0])
  Nline = Hecke.embedded_module(ZZ, QQ, QQ[0 1])
  @test_throws ArgumentError quo(Mline, Nline)
end

@testset "embedded quotient validation" begin
  M = Hecke.embedded_module(ZZ, QQ, identity_matrix(QQ, 2))
  for N in (Hecke.embedded_module(ZZ, QQ, QQ[2 0]),
            Hecke.embedded_module(ZZ, QQ, QQ[2 0; 0 3]))
    @test_throws ArgumentError Hecke.quotient_embedded_module(M, N)
  end
  larger = Hecke.embedded_module(ZZ, QQ, QQ[1//2 0])
  incompatible = Hecke.embedded_module(ZZ, QQ, QQ[1 0 0])
  @test_throws ArgumentError Hecke.quotient_embedded_module(M, larger)
  @test_throws ArgumentError Hecke.quotient_embedded_module(M, incompatible)
end

@testset "residue quotient validation" begin
  M = Hecke.embedded_module(ZZ, QQ, identity_matrix(QQ, 2))
  p = ZZ(3)
  free_part = Hecke.embedded_module(ZZ, QQ, QQ[1 0])
  higher_torsion = Hecke.embedded_module(ZZ, QQ, QQ[1 0; 0 9])
  larger = Hecke.embedded_module(ZZ, QQ, QQ[1//2 0; 0 1])
  incompatible = Hecke.embedded_module(ZZ, QQ, QQ[3 0 0; 0 3 0])
  for N in (free_part, higher_torsion)
    @test_throws ArgumentError Hecke.quotient_vector_space(M, N, p)
  end
  @test_throws ArgumentError Hecke.quotient_vector_space(M, larger, p)
  @test_throws ArgumentError Hecke.quotient_vector_space(M, incompatible, p)
  for q in (ZZ(0), ZZ(1), ZZ(9))
    @test_throws ArgumentError Hecke.quotient_vector_space(M, M, q)
  end
  _, t = polynomial_ring(QQ, "t")
  @test_throws ArgumentError Hecke.quotient_vector_space(M, M, t)
end
