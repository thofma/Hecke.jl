@testset "Locally free class group of group algebras" begin
  G = small_group(8, 4)
  A = AlgGrp(FlintQQ, G)
  O = Order(A, basis(A))
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

  A = AlgAss(A)[1]
  O = Order(A, basis(A))
  C = locally_free_class_group(O)
  @test C.snf == ZZRingElem[ 2 ]

  G = small_group(10, 2)
  A = AlgGrp(FlintQQ, G)
  O = Order(A, basis(A))
  C = locally_free_class_group(O)
  @test C.snf == ZZRingElem[]

  A = AlgAss(A)[1]
  O = Order(A, basis(A))
  C = locally_free_class_group(O)
  @test C.snf == ZZRingElem[]

  G = small_group(12, 3)
  A = AlgAss(AlgGrp(FlintQQ, G))[1]
  O = Order(A, basis(A))
  C = locally_free_class_group(O)
  @test C.snf == ZZRingElem[]
end

@testset "Locally free class group of matrix algebras" begin
  Qx, x = FlintQQ["x"]
  f = x^2 + 47
  K, a = number_field(f, "a")
  A = AlgAss(MatrixAlgebra(K, 2))
  A, _ = Hecke.restrict_scalars(A, FlintQQ)
  O = MaximalOrder(A)
  C = Hecke.locally_free_class_group(O) # == class_group(K)
  @test C.snf == ZZRingElem[ 5 ]

  f = x^2 + 26
  K, a = number_field(f, "a")
  A = AlgAss(MatrixAlgebra(K, 2))
  A, _ = Hecke.restrict_scalars(A, FlintQQ)
  O = MaximalOrder(A)
  C = Hecke.locally_free_class_group(O) # == class_group(K)
  @test C.snf == ZZRingElem[ 6 ]
end

@testset "Discrete logarithm of locally free class group" begin
  Qx, x = FlintQQ["x"]
  f = x^12 - x^11 + x^9 - x^8 + x^6 - x^4 + x^3 - x + 1
  K, a = number_field(f, "a") # Gal(K/Q) = C2 x C6 (aka 12T2 aka small_group(12, 5))
  OK = maximal_order(K)
  G, mG = automorphism_group(K)
  A, KtoA = galois_module(K, mG, normal_basis_generator = a)
  basisOK = [ KtoA(b.elem_in_nf) for b in basis(OK) ]
  d = lcm([ denominator(b) for b in basisOK ])
  ZG = Order(A, basis(A))
  I = Hecke.ideal_from_lattice_gens(A, ZG, [ d*b for b in basisOK ])
  S, mS = locally_free_class_group_with_disc_log(ZG)
  @test S.snf == ZZRingElem[ 2, 2 ]
  @test iszero(mS(I))

  # Check whether one can also call it with AlgAss
  B, BtoA = AlgAss(A)
  basisOK2 = [ BtoA\b for b in basisOK ]
  d2 = lcm([ denominator(b) for b in basisOK2 ])
  ZG = Order(B, basis(B))
  I = Hecke.ideal_from_lattice_gens(B, ZG, [ d*b for b in basisOK2 ])
  S, mS = locally_free_class_group_with_disc_log(ZG, check = false)
  @test S.snf == ZZRingElem[ 2, 2 ]
  @test iszero(mS(I))

  f = x^8 - 3*x^7 + 22*x^6 - 60*x^5 + 201*x^4 - 450*x^3 + 1528*x^2 - 3069*x + 4561
  K, a = number_field(f, "a") # Gal(K/Q) = Q8 (aka 8T5 aka small_group(8, 4))
  OK = maximal_order(K)
  G, mG = automorphism_group(K)
  A, KtoA = galois_module(K, mG, normal_basis_generator = a)
  basisOK = [ KtoA(b.elem_in_nf) for b in basis(OK) ]
  d = lcm([ denominator(b) for b in basisOK ])
  ZG = Order(A, basis(A))
  I = Hecke.ideal_from_lattice_gens(A, ZG, [ d*b for b in basisOK ])
  S, mS = locally_free_class_group_with_disc_log(ZG)
  @test S.snf == ZZRingElem[ 2 ]
  @test mS(I) == S[1]
  @test iszero(mS(I^2))
end
