@testset "Lattices" begin
  
  #
  # A maximal integral lattice
  #

  Qx, x = PolynomialRing(FlintQQ, "x")
  f = x^2 - 3
  K, a = NumberField(f, "a", cached = false)
  Kt, t = PolynomialRing(K, "t")
  g = t^2 + 1
  E, b = NumberField(g, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [1, 0, 0]), map(E, [0, 1, 0]), map(E, [0, 0, 1])]
  L = hermitian_lattice(E, generators = gens, gram_ambient_space = D)

  @test sprint(show, "text/plain", L) isa String
  @test get_attribute(L, :absolute_pseudo_matrix) === nothing
  PMabs = @inferred Hecke.absolute_pseudo_matrix(L)
  Eabs = nf(base_ring(PMabs))
  @test change_base_ring(Eabs, L.pmat.matrix) == PMabs.matrix
  @test get_attribute(L, :absolute_pseudo_matrix) === Hecke.absolute_pseudo_matrix(L)

  ok, L2 = @inferred Hecke.ismaximal_integral(L)
  @test ok
  @test isisometric(L, L2)[1]


  #
  # Construction of maximal/minimal integral overlattices
  #

  Qx, x = PolynomialRing(FlintQQ, "x")
  f = x - 1
  K, a = NumberField(f, "a", cached = false)
  Kt, t = PolynomialRing(K, "t")
  g = t^2 + 2
  E, b = NumberField(g, "b", cached = false)
  D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1])
  gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [-14*b - 18, -10, 0, 0]), map(E, [1//2*b - 1//2, b - 1//2, 1, 0]), map(E, [27*b + 85, -33//2*b + 28, -9//4*b - 3//2, -1//4*b - 2]), map(E, [-16*b - 92, 20*b - 24, 2*b + 2, 2])]
  L = hermitian_lattice(E, generators = gens, gram_ambient_space = D)

  Lmax = @inferred Hecke.maximal_integral_lattice(L)
  @test !isisometric(L, Lmax)[1]
  @test issublattice(Lmax, L)

  ok, LL = @inferred Hecke.ismaximal_integral(L)
  chain = typeof(L)[L]
  while !ok
    push!(chain, LL)
    ok, LL = Hecke.ismaximal_integral(chain[end])
  end
  @test all(issublattice(chain[j], chain[i]) for i=1:length(chain) for j=i:length(chain))
  @test all(!isisometric(chain[i+1], chain[i])[1] for i=1:length(chain)-1)
  @test isisometric(Lmax, chain[end])[1]


  #
  # Construction of maximal/minimal locally integral overlattices
  #

  Qx, x = PolynomialRing(FlintQQ, "x")
  f = x - 1
  K, a = NumberField(f, "a", cached = false)
  Kt, t = PolynomialRing(K, "t")
  g = t^2 + 3
  E, b = NumberField(g, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [11//2*b + 41//2, b - 5, 0]), map(E, [-107//2*b + 189//2, 18*b, -b - 9]), map(E, [-29*b + 105, 15*b - 9, -2*b - 6])]
  L = hermitian_lattice(E, generators = gens, gram_ambient_space = D)
  
  p = genus(L).LGS[1].p
  v = infinite_places(nf(base_ring(L)))[1]
  @test_throws ErrorException hasse_invariant(L,p)
  @test_throws ErrorException witt_invariant(L,p)
  
  Lpmax = @inferred Hecke.maximal_integral_lattice(L, p)
  @test !islocally_isometric(L, Lpmax, p)
  @test islocally_isometric(Lpmax, L, v)
  @test issublattice(Lpmax, L)

  ok, Lp = @inferred ismaximal(L, p)
  chain = typeof(L)[L]
  while !ok
    push!(chain, Lp)
    ok, Lp = ismaximal(Lp, p)
  end
  @test all(issublattice(chain[i+1], chain[i]) for i=1:length(chain)-1)
  @test all(!islocally_isometric(Lp1, Lp2, p) for Lp1 in chain for Lp2 in chain if Lp1 != Lp2)
  @test all(islocally_isometric(Lp1, Lp2, v) for Lp1 in chain for Lp2 in chain)
  @test isisometric(chain[end], Lpmax)[1]

end

