@testset "GenusRep" begin

  #
  # A definite example (lattice 214 from the database)
  #
  
  Qx, x = PolynomialRing(FlintQQ, "x")
  f = x^2 - x - 1
  K, a = NumberField(f, "a", cached = false)
  Kt, t = PolynomialRing(K, "t")
  g = t^2 - a + 3
  E, b = NumberField(g, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  gene = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [1, 0, 0]), map(E, [0, 1, -1]), map(E, [0, -1//2*a*b - 1//2*a + 3//2, 0])]

  L = hermitian_lattice(E, generators = gene, gram_ambient_space = D)
  gens, def, P0 = @inferred Hecke.genus_generators(L)
  @test isempty(gens)
  @test def
  
  gen_rep = @inferred genus_representatives(L)
  @test length(gen_rep) == 2
  @test L in gen_rep
  @test !isisometric(gen_rep[1], gen_rep[2])[1]


  #
  # An indefinite example (see [Kir19, Page 9])
  #

  
  K, a = rationals_as_number_field()
  Kt, t = PolynomialRing(K, "t")
  g = t^2 + 17
  E, b = NumberField(g, "b", cached = false)
  D = matrix(E, 2, 2, [102, b, -b, 0])
  gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [1, 0]), map(E, [b, 0]), map(E, [0, 1]), map(E, [0, b])]

  L = hermitian_lattice(E, generators = gens, gram_ambient_space = D)
  gens, def, P0 = @inferred Hecke.genus_generators(L)
  @test !def
  @test length(gens) == 1
  P, e = gens[1]
  @test minimum(P) == 3*maximal_order(K)
  @test e == 4
  @test P0 == 1*maximal_order(E)

  gen_rep = @inferred genus_representatives(L)
  @test length(gen_rep) == 4
  @test L in gen_rep
  a = involution(L)
  PB = [pseudo_basis(LL) for LL in gen_rep]
  @test all(i -> PB[i][1][2] == P^(i-1) && PB[i][2][2]^-1 == a(P)^(i-1), 1:length(PB))

end

