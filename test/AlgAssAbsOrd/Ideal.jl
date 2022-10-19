@testset "AlgAssAbsOrdIdl" begin
  QG = group_algebra(FlintQQ, GrpAbFinGen([ 4 ]))

  @testset "Arithmetic" begin
    O = any_order(QG)
    I = 2*O
    J = 4*O

    @test I + J == I
    @test I*J == 8*O
    @test intersect(I, J) == J
    @test I^2 == J
    @test I^fmpz(2) == J
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
    A = AlgAss(x^2 - fmpq(1, 5))
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
    while iszero(det(basis_matrix(K)))
      K = rand(M, -1:1) * O
    end
    X = lattice_with_local_conditions(O, [2, 3, 13], [I, J, K])
    @test is_equal_locally(X, I, 2)
    @test is_equal_locally(X, J, 3)
    @test is_equal_locally(X, K, 13)
    T = basis_matrix(X) * basis_mat_inv(O)
    for a in fmpq_mat(T)
      @test issubset(prime_divisors(denominator(a)) , [2, 3, 13])
    end
    for a in fmpq_mat(inv(T))
      @test issubset(prime_divisors(denominator(a)) , [2, 3, 13])
    end

    @test_throws ArgumentError lattice_with_local_conditions(O, [2, 3], [I])
    @test_throws ArgumentError lattice_with_local_conditions(O, [3, 3], [I])
    @test_throws ArgumentError lattice_with_local_conditions(O, [3], [I, J])
  end

  # minimum
  G = small_group(10, 1) # D_5
  QG = QQ[G]
  ZG = Order(QG, basis(QG))
  @test minimum(12 * ZG) == 12
  @test minimum(4 * ZG) == 4
end
