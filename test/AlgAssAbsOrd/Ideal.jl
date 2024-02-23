@testset "AlgAssAbsOrdIdl" begin
  QG = group_algebra(FlintQQ, FinGenAbGroup([ 4 ]))

  @testset "Arithmetic" begin
    O = any_order(QG)
    I = 2*O
    J = 4*O

    @test I + J == I
    @test I*J == 8*O
    @test intersect(I, J) == J
    @test I^2 == J
    @test I^ZZRingElem(2) == J
    @test norm(I) == 16
  end

  @testset "Prime ideals" begin
    A = Hecke.quaternion_algebra2(-1, -1)
    OA = maximal_order(A)

    p = prime_ideals_over(OA, 2)
    @test length(p) == 1
    @test p[1] == pradical(OA, 2)

    p = prime_ideals_over(OA, 3)
    @test length(p) == 1
    @test p[1] == 3*OA
  end

  #=
  @testset "Locally free basis" begin
    Qx, x = FlintQQ["x"]
    f = x^4 - 5x^2 + 5
    K, a = number_field(f, "a", cached = false, check = false) # Gal(K/Q) == C_4
    OK = maximal_order(K)

    KtoQG, QGtoK = Hecke._find_isomorphism(K, QG)
    basisOK = [ KtoQG(b.elem_in_nf) for b in basis(OK) ]
    d = lcm([ denominator(b) for b in basisOK ])
    ZG = Order(QG, basis(QG))
    I = Hecke.ideal_from_lattice_gens(QG, ZG, [ d*b for b in basisOK ])

    g = Hecke.locally_free_basis(I, 3)
    ZGg = ZG*g
    t = det(basis_matrix(I, copy = false)*basis_mat_inv(ZGg, copy = false))
    @test valuation(t, 3) == 0

    @test_throws ErrorException  Hecke.locally_free_basis(I, 2)
  end
  =#

  @testset "rand" begin
    Qx, x = FlintQQ["x"]
    A = StructureConstantAlgebra(x^2 - QQFieldElem(1, 5))
    O = any_order(A)
    I = 2*O
    T = elem_type(A)

    @test rand(rng, I, 3) isa T
    @test rand(I, 3) isa T
    m = make(I, 3)
    @test Random.gentype(m) == T
    @test rand(m, 3) isa Vector{T}

    @test reproducible(I, 3)
  end

  @testset "Swan module" begin
    G = abelian_group([2, 2])
    QG = QQ[G]
    ZG = Order(QG, basis(QG))
    I = swan_module(ZG, 1)
    @test I == ZG * sum(basis(QG)) + ZG * 1
    I = swan_module(ZG, ZZ(1))
    @test I == ZG * sum(basis(QG)) + ZG * 1
    @test_throws ArgumentError swan_module(ZG, 2)
  end

  @testset "Local computations" begin
    G = small_group(10, 1) # D_5
    QG = QQ[G]
    ZG = Order(QG, basis(QG))
    O = pmaximal_overorder(ZG, 2) # not maximal
    M = maximal_order(QG)

    I = 2 * O
    J = QG(1//3) * O
    @test (@inferred is_subset_locally(I, J, 2))
    @test (@inferred is_subset_locally(I, J, ZZ(2)))
    @test (@inferred !is_subset_locally(J, I, 2))
    @test (@inferred is_subset_locally(I, J, 3))
    @test (@inferred is_subset_locally(I, J, ZZ(3)))
    @test (@inferred !is_subset_locally(J, I, 3))

    @test (@inferred is_equal_locally(I, J, 5))
    @test (@inferred is_equal_locally(I, J, ZZ(5)))
    @test (@inferred !is_equal_locally(I, J, 2))
    @test (@inferred !is_equal_locally(I, J, ZZ(2)))

    # Create something in a different algebra
    H = small_group(10, 2) # C_10
    QH = QQ[H]
    ZH = Order(QH, basis(QH))
    II = 1 * ZH

    @test_throws ArgumentError is_subset_locally(I, II, 2)
    @test_throws ArgumentError is_equal_locally(I, II, 2)

    K = rand(M, -1:1) * O
    MK = basis_matrix(K)
    while !is_square(MK) || is_zero(det(MK))
      K = rand(M, -1:1) * O
      MK = basis_matrix(K)
    end
    X = lattice_with_local_conditions(O, [2, 3, 13], [I, J, K])
    @test is_equal_locally(X, I, 2)
    @test is_equal_locally(X, J, 3)
    @test is_equal_locally(X, K, 13)
    T = basis_matrix(X) * basis_mat_inv(Hecke.FakeFmpqMat, O)
    for a in QQMatrix(T)
      @test issubset(prime_divisors(denominator(a)) , [2, 3, 13])
    end
    for a in QQMatrix(inv(T))
      @test issubset(prime_divisors(denominator(a)) , [2, 3, 13])
    end

    @test_throws ArgumentError lattice_with_local_conditions(O, [2, 3], [I])
    @test_throws ArgumentError lattice_with_local_conditions(O, [3, 3], [I])
    @test_throws ArgumentError lattice_with_local_conditions(O, [3], [I, J])
  end

  # issubset
  G = small_group(4, 2)
  QG = QQ[G]
  ZG = Order(QG, basis(QG), isbasis = true)
  M = maximal_order(ZG)
  @test is_subset(2 * ZG, ZG)
  @test is_subset(2 * ZG, M)
  I = Hecke.ideal_from_lattice_gens(QG, QG(1//2) .* basis(QG))
  @test !is_subset(I, ZG)
  @test !is_subset(I, M)

  # minimum
  G = small_group(10, 1) # D_5
  QG = QQ[G]
  ZG = Order(QG, basis(QG))
  @test minimum(12 * ZG) == 12
  @test minimum(4 * ZG) == 4

  # primary decomposition
  G = small_group(4, 2)
  QG = QQ[G]
  ZG = Order(QG, basis(QG), isbasis = true)
  M = maximal_order(ZG)
  I = 6 * ZG
  PD = primary_decomposition(I, ZG)
  @test prod(x[1] for x in PD) == I
  @test all(x -> all(y -> y[2] === x[2] || x[2] + y[2] == 1*ZG, PD), PD)

  PD = primary_decomposition(I)
  @test prod(x[1] for x in PD) == I
  @test all(x -> all(y -> y[2] === x[2] || x[2] + y[2] == 1*ZG, PD), PD)

  I = 16 * M 
  PD = primary_decomposition(I, M)
  @test prod(x[1] for x in PD) == I
  @test all(x -> all(y -> y[2] === x[2] || x[2] + y[2] == 1*M, PD), PD)
  PD = primary_decomposition(I, ZG)
  @test prod(x[1] for x in PD) == I
  @test all(x -> all(y -> y[2] === x[2] || x[2] + y[2] == 1*ZG, PD), PD)

  I = prime_ideals_over(ZG, 3)[1]
  PD = primary_decomposition(I, ZG)
  @test prod(x[1] for x in PD) == I
  @test all(x -> all(y -> y[2] === x[2] || x[2] + y[2] == 1*ZG, PD), PD)

  m1 = QQFieldElem[48 0 0 0; 0 96 0 0; 0 0 0 0; 0 0 0 0]
  m2 = [0 48 0 0; 48 0 0 0; 0 0 0 0; 0 0 0 0]
  m3 = [0 0 0 0; 0 0 0 0; 0 0 48 0; 0 0 0 96]
  m4 = [0 0 0 0; 0 0 0 0; 0 0 0 48; 0 0 48 0]
  m = Array{QQFieldElem}(undef, (4, 4, 4))
  m[:, :, 1] = m1
  m[:, :, 2] = m2
  m[:, :, 3] = m3
  m[:, :, 4] = m4
  A = StructureConstantAlgebra(QQ, m)
  basO = map(x -> A(x), Vector{QQFieldElem}[[1//24, 0, 0, 0], [0, 1//48, 0, 0], [1//48, 0, 1//48, 0], [0, 0, 0, 1//48]])
  O = Order(A, basO)
  I = A(48) * O
  PD = primary_decomposition(I, O)

  J = typeof(I)(A, Hecke.Hecke.FakeFmpqMat(identity_matrix(QQ, 4)))
  @test J * J == typeof(I)(A, Hecke.Hecke.FakeFmpqMat(48 * identity_matrix(QQ, 4)))

  # zero algebra

  A = zero_algebra(QQ)
  O = Order(A, elem_type(A)[])
  I = 1 * O
  @test Hecke.is_full_lattice(I)

end
