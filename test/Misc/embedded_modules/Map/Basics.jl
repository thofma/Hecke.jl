@testset "map interface and printing" begin
  M = Hecke.embedded_module(ZZ, QQ, QQ[2 0; 0 3])
  N = Hecke.embedded_module(ZZ, QQ, QQ[1 0; 0 1])
  f = (@inferred hom(M, N, basis(N)))

  @test f isa Hecke.EmbeddedModuleMap
  @test (@inferred domain(f)) === M
  @test (@inferred codomain(f)) === N
  @test f(basis(M)[1]) == basis(N)[1]
  @test image(f, basis(M)[2]) == basis(N)[2]
  @test preimage(f, basis(N)[1]) == basis(M)[1]

  text = sprint(show, MIME"text/plain"(), f)
  @test occursin("Homomorphism of embedded modules", text)
  @test occursin("from embedded module of rank 2", text)
  @test occursin("to embedded module of rank 2", text)
  @test occursin("defined by", text)
  @test occursin(" -> ", text)
  @test startswith(sprint(show, f), "Map: ")
  @test (@inferred show(IOBuffer(), MIME"text/plain"(), f)) === nothing
  @test (@inferred show(IOBuffer(), f)) === nothing

  g = hom(M, ZZ, ZZRingElem[2, 3])
  x = Hecke._element_from_coordinates(M, ZZRingElem[4, -1])
  @test codomain(g) === ZZ
  @test (@inferred g(x)) == 5
  @test occursin("to integer ring", sprint(show, MIME"text/plain"(), g))
  @test_throws ErrorException preimage(g, ZZ(1))

  @test_throws ArgumentError hom(M, N, basis(N)[1:1])
  @test_throws ArgumentError hom(M, N, basis(M))
  @test_throws ArgumentError f(basis(N)[1])
  @test_throws ArgumentError preimage(f, basis(M)[1])

  h = hom(M, QQ, QQFieldElem[2, 3])
  @test codomain(h) === QQ
  @test h(x) == QQ(5)
  @test occursin("to rational field", sprint(show, MIME"text/plain"(), h))

  K, t = rational_function_field(QQ, "t")
  P = Hecke.embedded_module(parent(numerator(t)), K, identity_matrix(K, 2))
  @test_throws ArgumentError hom(M, P, basis(P))
end
