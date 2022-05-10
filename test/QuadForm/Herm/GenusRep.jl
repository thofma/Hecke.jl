@testset "GenusRep" begin

  #
  # Some definite examples
  #
  
  # Lattice 214 from the database: `a(P) != P` in `_neighbours`
  
  Qx, x = PolynomialRing(FlintQQ, "x")
  f = x^2 - x - 1
  K, a = NumberField(f, "a", cached = false)
  Kt, t = PolynomialRing(K, "t")
  g = t^2 - a + 3
  E, b = NumberField(g, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  gene = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [1, 0, 0]), map(E, [0, 1, -1]), map(E, [0, -1//2*a*b - 1//2*a + 3//2, 0])]

  L = hermitian_lattice(E, gene, gram = D)
  gens, def, P0 = @inferred Hecke.genus_generators(L)
  @test isempty(gens)
  @test def
  
  gen_rep = @inferred genus_representatives(L)
  @test length(gen_rep) == 2
  @test L in gen_rep
  @test !is_isometric(gen_rep[1], gen_rep[2])[1]


  # Lattice 324 from the database: `special == true` in `_neighbours`

  Qx, x = PolynomialRing(FlintQQ, "x")
  f = x^2 - x - 1
  K, a = NumberField(f, "a", cached = false)
  Kt, t = PolynomialRing(K, "t")
  g = t^2 - a + 3
  E, b = NumberField(g, "b", cached = false)
  D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1])
  gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [2, 1, 0, 0]), map(E, [(a + 3//2)*b - 13//2*a + 2, 0, (1//2*a + 1//2)*b + 3*a - 33//2, 0]), map(E, [0, 0, 2, 1]), map(E, [(-92011//2*a - 62822)*b - 15049//2*a + 178467//2, 0, (-126700*a + 60200)*b + 160300*a - 109900, 0])]

  L = hermitian_lattice(E, gens, gram = D)
  gens, def, P0 = @inferred Hecke.genus_generators(L)
  @test isempty(gens)
  a = involution(L)
  @test a(P0) == P0
  ok, scale = is_modular(L,P0)
  if scale != 0 && is_ramified(base_ring(L), minimum(P0))
    special = isodd(scale)
  end
  @test special

  @test genus_representatives(L) == [L]

  # Lattice 441 from the database: `special == false` in `_neighbours`; calls `_all_row_span`

  Qx, x = PolynomialRing(FlintQQ, "x")
  f = x - 1
  K, a = NumberField(f, "a", cached = false)
  Kt, t = PolynomialRing(K, "t")
  g = t^2 + 11
  E, b = NumberField(g, "b", cached = false)
  D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1])
  gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [5//2*b + 121//2, 1//2*b + 55//2, 0, 0]), map(E, [-1, -3, -1, 0]), map(E, [987//2*b - 2407//2, 475//2*b - 679//2, 0, 2*b + 62]), map(E, [3906*b - 16305, 2074*b - 5477, 0, 70*b + 595])]

  L = hermitian_lattice(E, gens, gram = D)
  gens, def, P0 = @inferred Hecke.genus_generators(L)
  a = involution(L)
  @test a(P0) == P0
  ok, scale = is_modular(L,P0)
  @test scale == 0
  gen_rep = @inferred representatives(genus(L))
  @test any(LL -> is_isometric(LL,L)[1], gen_rep)
  @test !all(LL -> is_isometric(LL,L)[1], gen_rep)


  #
  # An indefinite example (see [Kir19, Page 9])
  #

  
  K, a = rationals_as_number_field()
  Kt, t = PolynomialRing(K, "t")
  g = t^2 + 17
  E, b = NumberField(g, "b", cached = false)
  D = matrix(E, 2, 2, [102, b, -b, 0])
  gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [1, 0]), map(E, [b, 0]), map(E, [0, 1]), map(E, [0, b])]

  L = hermitian_lattice(E, gens, gram = D)
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
  @test a(P) != P
  PB = [pseudo_basis(LL) for LL in gen_rep]
  @test all(i -> PB[i][1][2] == P^(i-1) && PB[i][2][2]^-1 == a(P)^(i-1), 1:length(PB))

  #
  # Other indefinite examples
  #

  Qx, x = FlintQQ["x"]
  K, a = NumberField(x - 1, "a")
  Kt, t = K["t"]
  E, b = NumberField(t^2 + 1, "b")
  p = prime_decomposition(maximal_order(K), 2)[1][1]
  G = genus(HermLat, E, p, [(0, 3, -1, 0)])
  L = @inferred representative(G)
  @test length(@inferred Hecke.genus_representatives(L)) == 1

  Qx, x = PolynomialRing(FlintQQ, "x")
  f = x^6 + x^5 + x^4 + x^3 + x^2 + x + 1
  K, a = NumberField(f, "a", cached = false)
  Kt, t = PolynomialRing(K, "t")
  g = t^2 + 47
  E, z_7 = NumberField(g, "b", cached = false)
  b = z_7
  D = matrix(E, 6, 6, [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1])
  gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [1, 0, 0, 0, 0, 0]), map(E, [z_7, 0, 0, 0, 0, 0]), map(E, [z_7^2, 0, 0, 0, 0, 0]), map(E, [z_7^3, 0, 0, 0, 0, 0]), map(E, [z_7^4, 0, 0, 0, 0, 0]), map(E, [z_7^5, 0, 0, 0, 0, 0]), map(E, [1//2*b + 1//2, 0, 0, 0, 0, 0]), map(E, [1//2*z_7*b + 1//2*z_7, 0, 0, 0, 0, 0]), map(E, [1//2*z_7^2*b + 1//2*z_7^2, 0, 0, 0, 0, 0]), map(E, [1//2*z_7^3*b + 1//2*z_7^3, 0, 0, 0, 0, 0]), map(E, [1//2*z_7^4*b + 1//2*z_7^4, 0, 0, 0, 0, 0]), map(E, [1//2*z_7^5*b + 1//2*z_7^5, 0, 0, 0, 0, 0]), map(E, [0, 1, 0, 0, 0, 0]), map(E, [0, z_7, 0, 0, 0, 0]), map(E, [0, z_7^2, 0, 0, 0, 0]), map(E, [0, z_7^3, 0, 0, 0, 0]), map(E, [0, z_7^4, 0, 0, 0, 0]), map(E, [0, z_7^5, 0, 0, 0, 0]), map(E, [0, 1//2*b + 1//2, 0, 0, 0, 0]), map(E, [0, 1//2*z_7*b + 1//2*z_7, 0, 0, 0, 0]), map(E, [0, 1//2*z_7^2*b + 1//2*z_7^2, 0, 0, 0, 0]), map(E, [0, 1//2*z_7^3*b + 1//2*z_7^3, 0, 0, 0, 0]), map(E, [0, 1//2*z_7^4*b + 1//2*z_7^4, 0, 0, 0, 0]), map(E, [0, 1//2*z_7^5*b + 1//2*z_7^5, 0, 0, 0, 0]), map(E, [0, 0, 1, 0, 0, 0]), map(E, [0, 0, z_7, 0, 0, 0]), map(E, [0, 0, z_7^2, 0, 0, 0]), map(E, [0, 0, z_7^3, 0, 0, 0]), map(E, [0, 0, z_7^4, 0, 0, 0]), map(E, [0, 0, z_7^5, 0, 0, 0]), map(E, [0, 0, 1//2*b + 1//2, 0, 0, 0]), map(E, [0, 0, 1//2*z_7*b + 1//2*z_7, 0, 0, 0]), map(E, [0, 0, 1//2*z_7^2*b + 1//2*z_7^2, 0, 0, 0]), map(E, [0, 0, 1//2*z_7^3*b + 1//2*z_7^3, 0, 0, 0]), map(E, [0, 0, 1//2*z_7^4*b + 1//2*z_7^4, 0, 0, 0]), map(E, [0, 0, 1//2*z_7^5*b + 1//2*z_7^5, 0, 0, 0]), map(E, [0, 0, 0, 1, 0, 0]), map(E, [0, 0, 0, z_7, 0, 0]), map(E, [0, 0, 0, z_7^2, 0, 0]), map(E, [0, 0, 0, z_7^3, 0, 0]), map(E, [0, 0, 0, z_7^4, 0, 0]), map(E, [0, 0, 0, z_7^5, 0, 0]), map(E, [0, 0, 0, 1//2*b + 1//2, 0, 0]), map(E, [0, 0, 0, 1//2*z_7*b + 1//2*z_7, 0, 0]), map(E, [0, 0, 0, 1//2*z_7^2*b + 1//2*z_7^2, 0, 0]), map(E, [0, 0, 0, 1//2*z_7^3*b + 1//2*z_7^3, 0, 0]), map(E, [0, 0, 0, 1//2*z_7^4*b + 1//2*z_7^4, 0, 0]), map(E, [0, 0, 0, 1//2*z_7^5*b + 1//2*z_7^5, 0, 0]), map(E, [0, 0, 0, 0, 1, 0]), map(E, [0, 0, 0, 0, z_7, 0]), map(E, [0, 0, 0, 0, z_7^2, 0]), map(E, [0, 0, 0, 0, z_7^3, 0]), map(E, [0, 0, 0, 0, z_7^4, 0]), map(E, [0, 0, 0, 0, z_7^5, 0]), map(E, [0, 0, 0, 0, 1//2*b + 1//2, 0]), map(E, [0, 0, 0, 0, 1//2*z_7*b + 1//2*z_7, 0]), map(E, [0, 0, 0, 0, 1//2*z_7^2*b + 1//2*z_7^2, 0]), map(E, [0, 0, 0, 0, 1//2*z_7^3*b + 1//2*z_7^3, 0]), map(E, [0, 0, 0, 0, 1//2*z_7^4*b + 1//2*z_7^4, 0]), map(E, [0, 0, 0, 0, 1//2*z_7^5*b + 1//2*z_7^5, 0]), map(E, [0, 0, 0, 0, 0, 1]), map(E, [0, 0, 0, 0, 0, z_7]), map(E, [0, 0, 0, 0, 0, z_7^2]), map(E, [0, 0, 0, 0, 0, z_7^3]), map(E, [0, 0, 0, 0, 0, z_7^4]), map(E, [0, 0, 0, 0, 0, z_7^5]), map(E, [0, 0, 0, 0, 0, 1//2*b + 1//2]), map(E, [0, 0, 0, 0, 0, 1//2*z_7*b + 1//2*z_7]), map(E, [0, 0, 0, 0, 0, 1//2*z_7^2*b + 1//2*z_7^2]), map(E, [0, 0, 0, 0, 0, 1//2*z_7^3*b + 1//2*z_7^3]), map(E, [0, 0, 0, 0, 0, 1//2*z_7^4*b + 1//2*z_7^4]), map(E, [0, 0, 0, 0, 0, 1//2*z_7^5*b + 1//2*z_7^5])]
  L = hermitian_lattice(E, gens, gram = D)
  @test length(Hecke.genus_representatives(L)) == 15

end

