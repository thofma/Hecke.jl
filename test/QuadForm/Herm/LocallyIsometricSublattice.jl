@testset "LocallyIsometricSublattice" begin

  K, a = rationals_as_number_field()
  Kt, t = polynomial_ring(K,"t")
  OK = maximal_order(K)

  #
  # Split case
  #

  E, b = number_field(t^2+7, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [3*b - 28, b + 14, 0]), map(E, [9, 3, 1]), map(E, [-21//2*b + 49//2, 5//2*b - 35//2, 0])]
  L = hermitian_lattice(E, gens, gram = D)

  G = genus(L)
  V = ambient_space(L)
  M = maximal_integral_lattice(V)
  g = G[2*OK]
  @test is_split(g)
  p = prime(g)
  Lp = representative(g)

  Mp = @inferred locally_isometric_sublattice(M, Lp, p)
  @test is_sublattice(M, Mp)
  @test Hecke._islocally_isometric_kirschmer(Mp, Lp, p)
  @test all(i -> Hecke._islocally_isometric_kirschmer(M, Mp, G.LGS[i].p), 1:2)


  #
  # Inert dyadic case
  #

  E, b = number_field(t^2+3, "b", cached = false)
  D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [b - 30, b - 6, 0, 0]), map(E, [-1, 1, 1, 0]), map(E, [0, 0, 0, -1]), map(E, [2*b + 15, 3, 0, 0])]
  L = hermitian_lattice(E, gens, gram = D)

  G = genus(L)
  V = ambient_space(L)
  M = maximal_integral_lattice(V)
  g = G[2*OK]
  @test is_inert(g)
  p = prime(g)
  @test is_dyadic(p)
  Lp = representative(g)

  @test !is_maximal(L,p)[1]
  @test_throws AssertionError locally_isometric_sublattice(L, Lp, p)
  Mp = @inferred locally_isometric_sublattice(M, Lp, p)
  @test is_sublattice(M, Mp)
  @test Hecke._islocally_isometric_kirschmer(Lp, Mp, p)
  @test !Hecke._islocally_isometric_kirschmer(M, Mp, p)
  @test Hecke._islocally_isometric_kirschmer(M, Mp, 3*OK)


  #
  # Inert non-dyadic case
  #

  E, b = number_field(t^2+1, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [3*b - 17, 5*b + 11, 0]), map(E, [74*b - 412, 241//2*b + 525//2, 1//2*b - 3//2]), map(E, [-886*b + 3051, -701*b - 2077, -5*b + 11])]
  L = hermitian_lattice(E, gens, gram = D)

  G = genus(L)
  V = ambient_space(L)
  M = maximal_integral_lattice(V)
  g = G[3*OK]
  @test is_inert(g)
  p = prime(g)
  @test !is_dyadic(p)
  Lp = representative(g)

  Mp = @inferred locally_isometric_sublattice(M, Lp, p)
  @test is_sublattice(M, Mp)
  @test Hecke._islocally_isometric_kirschmer(Lp, Mp, p)
  @test !Hecke._islocally_isometric_kirschmer(M, Mp, p)
  @test Hecke._islocally_isometric_kirschmer(M, Mp, 2*OK)
  @test genus(L) != genus(Mp) && genus(L,p) != genus(M,p) && genus(L,p) == genus(Mp,p)


  #
  # Ramified non-dyadic case
  #

  # 2 even scales less than 4

  E, b = number_field(t^2+3, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [-1//2*b - 3//2, 15//2*b + 33//2, 0]), map(E, [0, -1, -1]), map(E, [0, 3//2*b + 3//2, 0])]
  L = hermitian_lattice(E, gens, gram = D)

  G = genus(L)
  V = ambient_space(L)
  M = maximal_integral_lattice(V)
  g = G[3*OK]
  @test is_ramified(g)
  @test count(s in [0,2] for s in scales(g)) == 2
  p = prime(g)
  @test !is_dyadic(p)
  Lp = representative(g)

  Mp = @inferred locally_isometric_sublattice(M, Lp, p)
  @test is_sublattice(M, Mp)
  @test Hecke._islocally_isometric_kirschmer(Lp, Mp, p)
  @test !Hecke._islocally_isometric_kirschmer(M, Mp, p)
  @test Hecke._islocally_isometric_kirschmer(M, Mp, 5*OK)

  # 1 even scale less than 4

  E, b = number_field(t^2+7, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [3*b - 28, b + 14, 0]), map(E, [9, 3, 1]), map(E, [-21//2*b + 49//2, 5//2*b - 35//2, 0])]
  L = hermitian_lattice(E, gens, gram = D)

  G = genus(L)
  V = ambient_space(L)
  M = maximal_integral_lattice(V)
  g = G[7*OK]
  @test is_ramified(g)
  @test count(s in [0,2] for s in scales(g)) == 1
  p = prime(g)
  @test !is_dyadic(p)
  Lp = representative(g)

  Mp = @inferred locally_isometric_sublattice(M, Lp, p)
  @test is_sublattice(M, Mp)
  @test Hecke._islocally_isometric_kirschmer(Lp, Mp, p)
  @test !Hecke._islocally_isometric_kirschmer(M, Mp, p)
  @test Hecke._islocally_isometric_kirschmer(M, Mp, 3*OK)


  E, b = number_field(t^2+3, "b", cached = false)

  # 2 odd scales less than 4

  D = matrix(E, 5, 5, [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [-3*b - 6, -3//2*b - 9//2, 0, 0, 0]), map(E, [-1, -1, 1, 0, 0]), map(E, [-12*b + 45, -23//2*b + 39//2, 0, -15, 0]), map(E, [0, 0, 0, 0, 1]), map(E, [14*b - 66, 15*b - 30, 0, b + 21, 0])]
  L = hermitian_lattice(E, gens, gram = D)

  G = genus(L)
  V = ambient_space(L)
  M = maximal_integral_lattice(V)
  g = G[3*OK]
  @test is_ramified(g)
  @test count(s in [1,3] for s in scales(g)) == 2
  p = prime(g)
  @test !is_dyadic(p)
  Lp = representative(g)

  Mp = @inferred locally_isometric_sublattice(M, Lp, p)
  @test is_sublattice(M, Mp)
  @test Hecke._islocally_isometric_kirschmer(Lp, Mp, p)
  @test !Hecke._islocally_isometric_kirschmer(M, Mp, p)
  @test Hecke._islocally_isometric_kirschmer(M, Mp, 7*OK)

  # 1 odd scale less than 4

  D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [-1//2*b + 27//2, 3//2*b + 15//2, 0, 0]), map(E, [-1, -1, 1, 0]), map(E, [0, 0, 0, -1]), map(E, [-2*b - 30, -5*b - 15, 0, 0])]
  L = hermitian_lattice(E, gens, gram = D)

  G = genus(L)
  V = ambient_space(L)
  M = maximal_integral_lattice(V)
  g = G[3*OK]
  @test is_ramified(g)
  @test count(s in [1,3] for s in scales(g)) == 1
  p = prime(g)
  @test !is_dyadic(p)
  Lp = representative(g)

  Mp = @inferred locally_isometric_sublattice(M, Lp, p)
  @test is_sublattice(M, Mp)
  @test Hecke._islocally_isometric_kirschmer(Lp, Mp, p)
  @test !Hecke._islocally_isometric_kirschmer(M, Mp, p)
  @test Hecke._islocally_isometric_kirschmer(M, Mp, 2*OK)

  # 1 scale greater or equal to 4

  D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [3//2*b - 27//2, -1//2*b + 3//2, 0, 0]), map(E, [1, 1, -1, 0]), map(E, [-3, 0, 0, 3//2*b - 3//2]), map(E, [0, 0, 0, 1//2*b + 3//2])]
  L = hermitian_lattice(E, gens, gram = D)

  G = genus(L)
  V = ambient_space(L)
  M = maximal_integral_lattice(V)
  g = G[3*OK]
  @test is_ramified(g)
  @test count(s >= 4 for s in scales(g)) != 0
  p = prime(g)
  @test !is_dyadic(p)
  Lp = representative(g)

  Mp = @inferred locally_isometric_sublattice(M, Lp, p)
  @test is_sublattice(M, Mp)
  @test Hecke._islocally_isometric_kirschmer(Lp, Mp, p)
  @test !Hecke._islocally_isometric_kirschmer(M, Mp, p)
  @test Hecke._islocally_isometric_kirschmer(M, Mp, 2*OK)


  #
  # Ramified dyadic case
  #

  E, b = number_field(t^2+1, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [3*b - 17, 5*b + 11, 0]), map(E, [74*b - 412, 241//2*b + 525//2, 1//2*b - 3//2]), map(E, [-886*b + 3051, -701*b - 2077, -5*b + 11])]
  L = hermitian_lattice(E, gens, gram = D)

  G = genus(L)
  V = ambient_space(L)
  M = maximal_integral_lattice(V)
  g = G[2*OK]
  @test is_ramified(g)
  p = prime(g)
  @test is_dyadic(p)
  Lp = representative(g)

  Mp = @inferred locally_isometric_sublattice(M, Lp, p)
  @test is_sublattice(M, Mp)
  @test Hecke._islocally_isometric_kirschmer(Lp, Mp, p)
  @test !Hecke._islocally_isometric_kirschmer(M, Mp, p)
  @test Hecke._islocally_isometric_kirschmer(M, Mp, 5*OK)


  E, b = number_field(t^2+17, "b", cached = false)
  D = matrix(E, 2, 2, [102, b, -b, 0])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [1, 0]), map(E, [b, 0]), map(E, [0, 1]), map(E, [0, b])]
  L = hermitian_lattice(E, gens, gram = D)

end
