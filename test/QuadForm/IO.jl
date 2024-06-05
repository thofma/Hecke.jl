@testset "IO" begin
  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  f = x^2 - 2;
  K, a = number_field(f)
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 16]);
  gens = [[2, 0, 0], [2, 0, 0], [2, 2, 0], [a, a, 0], [a + 2, 1, 1//4], [3*a + 3, 3//2*a, 3//8*a]]
  L = quadratic_lattice(K, gens, gram = D)
  @test Hecke.to_hecke_string(L) isa String
  @test Hecke.to_magma_string(L) isa String

  Qx, x = polynomial_ring(FlintQQ, "x")
  f = x^4-x^3-4*x^2+4*x+1
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2+(a^3 - 1*a^2 - 4*a + 5)
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 3, 3, [(1), 0, 0, 0, (1), 0, 0, 0, (1)])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [(1), 0, 0]), map(E, [0, (1), 0]), map(E, [0, 0, (1)])]
  L = hermitian_lattice(E, gens, gram = D)
  @test Hecke.to_hecke_string(L) isa String
  @test Hecke.to_magma_string(L) isa String

  # For Zlattices
  B = matrix(FlintQQ, 6, 7 ,[1, -1, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 1, -1]);
  G = matrix(FlintQQ, 7, 7 ,[3, 2, 2, 2, 2, 2, 1, 2, 3, 2, 2, 2, 2, 1, 2, 2, 3, 2, 2, 2, 1, 2, 2, 2, 3, 2, 2, 1, 2, 2, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 1, 1, 1, 1, 1, 1, 1]);
  L = integer_lattice(B, gram = G)

  @test Hecke.to_hecke_string(L) isa String
  @test Hecke.to_magma_string(L) isa String
  @test Hecke.to_sage_string(L) isa String
  @test Hecke.to_sage_string(dual(L)) isa String

end
