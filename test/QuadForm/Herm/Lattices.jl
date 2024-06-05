@testset "Lattices" begin

  #
  # Constructors
  #

  K, a = rationals_as_number_field()
  Kt, t = polynomial_ring(K, "t")
  g = t^2 + 5
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 2])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [b + 8, b + 9, 0]), map(E, [-25*b + 66, -51//2*b + 171//2, -5//2*b + 1]), map(E, [104*b + 150, 132*b + 145, 5//2*b + 35//2]), map(E, [529*b - 47, 1243//2*b - 437//2, 28*b + 95//2])]
  L = hermitian_lattice(E, gens, gram = D)

  L1 = @inferred hermitian_lattice(base_field(L), pseudo_matrix(L))
  @test pseudo_matrix(L1) == pseudo_matrix(L)
  @test ambient_space(L1) != ambient_space(L)

  L2 = @inferred hermitian_lattice(base_field(L), pseudo_matrix(L), gram = D)
  @test ambient_space(L2) === ambient_space(L)
  @test L == L2

  L3 = @inferred hermitian_lattice(base_field(L), matrix(pseudo_matrix(L)))
  @test matrix(pseudo_matrix(L3)) == matrix(pseudo_matrix(L))
  @test pseudo_matrix(L3) != pseudo_matrix(L)
  @test ambient_space(L3) != ambient_space(L)

  L4 = @inferred hermitian_lattice(base_field(L), generators(L))
  @test ambient_space(L4) != ambient_space(L)

  L5 = @inferred hermitian_lattice(base_field(L), generators(L), gram = D)
  @test ambient_space(L5) === ambient_space(L)

  #
  # Zero lattice
  #

  LL = @inferred lattice(ambient_space(L), [])
  @test ambient_space(LL) === ambient_space(L)
  @test rank(LL) == 0

  @test_throws AssertionError hermitian_lattice(base_field(L), [])

  LL = @inferred hermitian_lattice(base_field(L), [], gram = D)
  @test ambient_space(LL) === ambient_space(L)
  @test rank(LL) == 0

  D = matrix(E, 0, 0, [])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[]
  L = @inferred hermitian_lattice(E, gens, gram = D)
  @test is_definite(L)
  @test rank(L) == 0


  #
  # A maximal integral lattice
  #

  Qx, x = polynomial_ring(FlintQQ, "x")
  f = x^2 - 3
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2 + 1
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [1, 0, 0]), map(E, [0, 1, 0]), map(E, [0, 0, 1])]
  L = hermitian_lattice(E, gens, gram = D)

  @test sprint(show, "text/plain", L) isa String
  @test get_attribute(L, :absolute_pseudo_matrix) === nothing
  PMabs = @inferred Hecke.absolute_pseudo_matrix(L)
  Eabs = Hecke.nf(base_ring(PMabs))
  @test change_base_ring(Eabs, L.pmat.matrix) == PMabs.matrix
  @test get_attribute(L, :absolute_pseudo_matrix) === Hecke.absolute_pseudo_matrix(L)

  ok, L2 = @inferred Hecke.is_maximal_integral(L)
  @test ok
  @test is_isometric_with_isometry(L, L2)[1]


  #
  # Construction of maximal/minimal integral overlattices
  #

  Qx, x = polynomial_ring(FlintQQ, "x")
  f = x - 1
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2 + 2
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [-14*b - 18, -10, 0, 0]), map(E, [1//2*b - 1//2, b - 1//2, 1, 0]), map(E, [27*b + 85, -33//2*b + 28, -9//4*b - 3//2, -1//4*b - 2]), map(E, [-16*b - 92, 20*b - 24, 2*b + 2, 2])]
  L = hermitian_lattice(E, gens, gram = D)

  Lmax = @inferred Hecke.maximal_integral_lattice(L)
  @test !is_isometric_with_isometry(L, Lmax)[1]
  @test is_sublattice(Lmax, L)

  ok, LL = @inferred Hecke.is_maximal_integral(L)
  chain = typeof(L)[L]
  while !ok
    push!(chain, LL)
    ok, LL = Hecke.is_maximal_integral(chain[end])
  end
  @test all(is_sublattice(chain[j], chain[i]) for i=1:length(chain) for j=i:length(chain))
  @test all(!is_isometric_with_isometry(chain[i+1], chain[i])[1] for i=1:length(chain)-1)
  @test is_isometric_with_isometry(Lmax, chain[end])[1]


  #
  # Construction of maximal/minimal locally integral overlattices
  #

  Qx, x = polynomial_ring(FlintQQ, "x")
  f = x - 1
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2 + 3
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [11//2*b + 41//2, b - 5, 0]), map(E, [-107//2*b + 189//2, 18*b, -b - 9]), map(E, [-29*b + 105, 15*b - 9, -2*b - 6])]
  L = hermitian_lattice(E, gens, gram = D)

  p = genus(L).LGS[1].p
  v = infinite_places(Hecke.nf(base_ring(L)))[1]
  @test_throws ErrorException hasse_invariant(L,p)
  @test_throws ErrorException witt_invariant(L,p)

  Lpmax = @inferred Hecke.maximal_integral_lattice(L, p)
  @test !is_locally_isometric(L, Lpmax, p)
  @test is_locally_isometric(Lpmax, L, v)
  @test is_sublattice(Lpmax, L)

  ok, Lp = @inferred is_maximal(L, p)
  chain = typeof(L)[L]
  while !ok
    push!(chain, Lp)
    ok, Lp = is_maximal(Lp, p)
  end
  @test all(is_sublattice(chain[i+1], chain[i]) for i=1:length(chain)-1)
  @test all(!is_locally_isometric(Lp1, Lp2, p) for Lp1 in chain for Lp2 in chain if Lp1 != Lp2)
  @test all(is_locally_isometric(Lp1, Lp2, v) for Lp1 in chain for Lp2 in chain)
  @test is_isometric_with_isometry(chain[end], Lpmax)[1]

end

