@testset "Locally free class group of group algebras" begin
  G = small_group(8, 4)
  A = GroupAlgebra(QQ, G)
  O = order(A, basis(A))
  C = locally_free_class_group(O)
  @test C.snf == ZZRingElem[ 2 ]

  M = maximal_order(O)
  f = Hecke._get_a_twosided_conductor(O, M)
  @inferred Hecke.K1_order_mod_conductor(O, M, f)
  @inferred Hecke.K1_order_mod_conductor(O, M, f; do_units = true)

  finfields = [GF(2), GF(ZZRingElem(2)), GF(2, 1), GF(ZZRingElem(2), 1), GF(3), GF(5), GF(7)]
  for F in finfields
    for n in 1:5
      @inferred Hecke._unit_group_generators(matrix_algebra(F, n))
    end
  end

  A = StructureConstantAlgebra(A)[1]
  O = order(A, basis(A))
  C = locally_free_class_group(O)
  @test C.snf == ZZRingElem[ 2 ]

  G = small_group(10, 2)
  A = GroupAlgebra(QQ, G)
  O = order(A, basis(A))
  C = locally_free_class_group(O)
  @test C.snf == ZZRingElem[]

  A = StructureConstantAlgebra(A)[1]
  O = order(A, basis(A))
  C = locally_free_class_group(O)
  @test C.snf == ZZRingElem[]

  G = small_group(12, 3)
  A = StructureConstantAlgebra(GroupAlgebra(QQ, G))[1]
  O = order(A, basis(A))
  C = locally_free_class_group(O)
  @test C.snf == ZZRingElem[]
end

@testset "Locally free class group of matrix algebras" begin
  Qx, x = QQ["x"]
  f = x^2 + 47
  K, a = number_field(f, "a")
  A = StructureConstantAlgebra(matrix_ring(K, 2))
  A, _ = Hecke.restrict_scalars(A, QQ)
  O = maximal_order(A)
  C = Hecke.locally_free_class_group(O) # == class_group(K)
  @test C.snf == ZZRingElem[ 5 ]

  f = x^2 + 26
  K, a = number_field(f, "a")
  A = StructureConstantAlgebra(matrix_ring(K, 2))
  A, _ = Hecke.restrict_scalars(A, QQ)
  O = maximal_order(A)
  C = Hecke.locally_free_class_group(O) # == class_group(K)
  @test C.snf == ZZRingElem[ 6 ]
end

@testset "Discrete logarithm of locally free class group" begin
  Qx, x = QQ["x"]
  f = x^12 - x^11 + x^9 - x^8 + x^6 - x^4 + x^3 - x + 1
  K, a = number_field(f, "a") # Gal(K/Q) = C2 x C6 (aka 12T2 aka small_group(12, 5))
  OK = maximal_order(K)
  G, mG = automorphism_group(K)
  V, KtoV = galois_module(K, mG, normal_basis_generator = a)
  A = algebra(V)
  ZG = integral_group_ring(A)
  I = KtoV(lll(OK))
  S, mS = locally_free_class_group_with_disc_log(ZG)
  @test S.snf == ZZRingElem[ 2, 2 ]
  @test iszero(mS(I))

  # Check whether one can also call it with StructureConstantAlgebra
  B, BtoA = StructureConstantAlgebra(A)
  Areg = Hecke.regular_module(A)
  AregToA = x -> A(coordinates(x))
  fl, VToAreg = Hecke.is_isomorphic_with_isomorphism(V, Areg)

  basisOK2 = [ BtoA\(AregToA(VToAreg(KtoV(K(b))))) for b in basis(lll(OK)) ]
  d2 = lcm([ denominator(b) for b in basisOK2 ])
  ZG = order(B, basis(B))
  I = Hecke.ideal_from_lattice_gens(B, ZG, [ d2*b for b in basisOK2 ])
  S, mS = locally_free_class_group_with_disc_log(ZG, check = false)
  @test S.snf == ZZRingElem[ 2, 2 ]
  @test iszero(mS(I))

  f = x^8 - 3*x^7 + 22*x^6 - 60*x^5 + 201*x^4 - 450*x^3 + 1528*x^2 - 3069*x + 4561
  K, a = number_field(f, "a") # Gal(K/Q) = Q8 (aka 8T5 aka small_group(8, 4))
  OK = maximal_order(K)
  G, mG = automorphism_group(K)
  V, KtoV = galois_module(K, mG, normal_basis_generator = a)
  A = algebra(V)
  ZG = integral_group_ring(A)
  S, mS = locally_free_class_group_with_disc_log(ZG)
  I = KtoV(lll(OK))
  @test S.snf == ZZRingElem[ 2 ]
  @test mS(I) == S[1]
end

@testset "Kernel group" begin
  test_data = [
     (8, 3) => [1],   # D_8
     (8, 4) => [2],   # Q_8
     (12, 1) => [2],  # Q_12
     (16, 9) => [2],  # Q_16
     (32, 1) => [2, 4, 4], # C_32
     (12, 3) => [1],  # A_4
     (24, 12) => [1], # S_4
  ]
  for (grpid, o) in test_data
    G = small_group(grpid...)
    QG = QQ[G]
    ZG = integral_group_ring(QG)
    @test is_isomorphic(kernel_group(ZG), abelian_group(o))[1]
  end
end

let
  A, = StructureConstantAlgebra(group_algebra(GF(2, 3), small_group(2, 1)))
  u = Hecke.K1(A; do_units = true)
  @test length(closure(u, *)) == 8 * 7

  A, = StructureConstantAlgebra(group_algebra(GF(2, 4), small_group(2, 1)))
  u = Hecke.K1(A; do_units = true)
  @test length(closure(u, *)) == 16 * 15
end
