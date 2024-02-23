@testset "Lattices" begin

  #
  # Constructors
  #

  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  f = x - 1;
  K, a = number_field(f, "a", cached = false)
  D = matrix(K, 3, 3, [4, 0, 0, 0, 10, 0, 0, 0, 20]);
  gens = Vector{AbsSimpleNumFieldElem}[map(K, [0, 1, 0]), map(K, [0, 1, 0]), map(K, [-5//4, 3//2, 3//4]), map(K, [-5//4, 3//2, 3//4]), map(K, [-5//4, -1//2, -1//4]), map(K, [-5//4, -1//2, -1//4])]
  L = quadratic_lattice(K, gens, gram = D)

  L1 = @inferred quadratic_lattice(base_field(L), pseudo_matrix(L))
  @test pseudo_matrix(L1) == pseudo_matrix(L)
  @test ambient_space(L1) != ambient_space(L)

  LL, inj = direct_sum(L1,L1)
  i, j = inj
  @inferred i(L1)
  @test i(L1)+j(L1) == LL

  L2 = @inferred quadratic_lattice(base_field(L), pseudo_matrix(L), gram = D)
  @test ambient_space(L2) === ambient_space(L)
  @test L == L2

  L3 = @inferred quadratic_lattice(base_field(L), matrix(pseudo_matrix(L)))
  @test matrix(pseudo_matrix(L3)) == matrix(pseudo_matrix(L))
  @test pseudo_matrix(L3) != pseudo_matrix(L)
  @test ambient_space(L3) != ambient_space(L)

  L4 = @inferred quadratic_lattice(base_field(L), generators(L))
  @test ambient_space(L4) != ambient_space(L)

  L5 = @inferred quadratic_lattice(base_field(L), generators(L), gram = D)
  @test ambient_space(L5) === ambient_space(L)

  #
  # Zero lattice
  #

  LL = @inferred lattice(ambient_space(L), [])
  @test ambient_space(LL) === ambient_space(L)
  @test rank(LL) == 0

  @test_throws AssertionError quadratic_lattice(base_field(L), [])

  LL = @inferred quadratic_lattice(base_field(L), [], gram = D)
  @test ambient_space(LL) === ambient_space(L)
  @test rank(LL) == 0

  D = matrix(K, 0, 0, [])
  gens = Vector{AbsSimpleNumFieldElem}[]
  L = @inferred quadratic_lattice(K, gens, gram = D)
  @test is_definite(L)
  @test rank(L) == 0


end

