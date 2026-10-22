@testset "AlgAssAbsOrdIdl" begin
  QG = group_algebra(QQ, FinGenAbGroup([ 4 ]))

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

    # p below the degree of OA, as a ZZRingElem
    @test pradical(OA, ZZ(2)) == pradical(OA, 2)
    @test pradical(OA, ZZ(3)) == 3*OA
  end

  #=
  @testset "Locally free basis" begin
    Qx, x = QQ["x"]
    f = x^4 - 5x^2 + 5
    K, a = number_field(f, "a", cached = false, check = false) # Gal(K/Q) == C_4
    OK = maximal_order(K)

    KtoQG, QGtoK = Hecke._find_isomorphism(K, QG)
    basisOK = [ KtoQG(b.elem_in_nf) for b in basis(OK) ]
    d = lcm([ denominator(b) for b in basisOK ])
    ZG = order(QG, basis(QG))
    I = Hecke.ideal_from_lattice_gens(QG, ZG, [ d*b for b in basisOK ])

    g = Hecke.locally_free_basis(I, 3)
    ZGg = ZG*g
    t = det(basis_matrix(I, copy = false)*basis_mat_inv(ZGg, copy = false))
    @test valuation(t, 3) == 0

    @test_throws ErrorException  Hecke.locally_free_basis(I, 2)
  end
  =#

  @testset "rand" begin
    Qx, x = QQ["x"]
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
    ZG = order(QG, basis(QG))
    I = swan_module(ZG, 1)
    @test I == ZG * sum(basis(QG)) + ZG * 1
    I = swan_module(ZG, ZZ(1))
    @test I == ZG * sum(basis(QG)) + ZG * 1
    @test_throws ArgumentError swan_module(ZG, 2)
  end

  @testset "Local computations" begin
    G = small_group(10, 1) # D_5
    QG = QQ[G]
    ZG = order(QG, basis(QG))
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
    ZH = order(QH, basis(QH))
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
    T = basis_matrix(X) * basis_matrix_inverse(O)
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
  ZG = order(QG, basis(QG), isbasis = true)
  M = maximal_order(ZG)
  @test is_subset(2 * ZG, ZG)
  @test is_subset(2 * ZG, M)
  I = Hecke.ideal_from_lattice_gens(QG, QG(1//2) .* basis(QG))
  @test !is_subset(I, ZG)
  @test !is_subset(I, M)

  # minimum
  G = small_group(10, 1) # D_5
  QG = QQ[G]
  ZG = order(QG, basis(QG))
  @test minimum(12 * ZG) == 12
  @test minimum(4 * ZG) == 4

  # primary decomposition
  G = small_group(4, 2)
  QG = QQ[G]
  ZG = order(QG, basis(QG), isbasis = true)
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
  O = order(A, basO)
  I = A(48) * O
  PD = primary_decomposition(I, O)

  J = typeof(I)(A, ZZ, identity_matrix(QQ, 4))
  @test J * J == typeof(I)(A, ZZ, 48 * identity_matrix(QQ, 4))

  # zero algebra

  A = zero_algebra(QQ)
  O = order(A, elem_type(A)[])
  I = 1 * O
  @test Hecke.is_full_lattice(I)

  # parent
  let
    A = zero_algebra(QQ)
    O = order(A, elem_type(A)[])
    I = 1 * O
    @test parent(I) == parent(I)
    @test hash(parent(I)) == hash(parent(I))
  end

  let
    T = matrix(QQ, [0 1; 0 0])
    A = matrix_algebra(QQ, [T])
    O = order(A, [T])
    I = ideal(O, A(T))
    @test !Hecke.is_full_lattice(I)
    @test !Hecke.is_full_rank(I)
    @test is_zero(I^2)
  end

  let # maximal integral ideal
    ZG = integral_group_ring(QQ[small_group(36, 1)])
    P = Hecke.maximal_integral_ideal(ZG, 2; side = :left)
    @test ZG(2) in P
    @test !(ZG(3) in P)
    @test ZG * P == P
    P = Hecke.maximal_integral_ideal(ZG, 3; side = :right)
    @test ZG(3) in P
    @test !(ZG(2) in P)
    @test P * ZG == P

    ZG = integral_group_ring(QQ[small_group(20, 1)])
    Ps = Hecke.maximal_integral_ideals(ZG, 2; side = :left)
    @test allunique(Ps)
    for P in Ps
      @test ZG(2) in P
      @test !(ZG(3) in P)
      @test ZG * P == P
    end

    Ps = Hecke.maximal_integral_ideals(ZG, 3; side = :right)
    @test allunique(Ps)
    for P in Ps
      @test ZG(3) in P
      @test !(ZG(2) in P)
      @test P * ZG == P
    end

    # a quaternion algebra (I know the result)
    let
      a, b, bas = (-3, -1, Vector{QQFieldElem}[[1, 0, 0, 0], [1//2, 3//2, 0, 0], [0, 0, 3, 0], [0, 0, 3//2, 1//2]])
      A = quaternion_algebra(QQ, a, b)
      bO = A.(bas)
      O = order(A, bO)
      lP = Hecke.maximal_integral_ideals(O, 2; side = :right)
      @test allunique(lP) && length(lP) == 3
      @test all(P -> P * O == P, lP)
    end

    # a maximal order of the quaternion algebra ramified at 11, at 11: one
    # maximal ideal, returned as a vector like any other answer
    let
      A = quaternion_algebra(QQ, -1, -11)
      M = maximal_order(A)
      for side in [:right, :left]
        Ps = Hecke.maximal_integral_ideals(M, 11; side)
        @test Ps isa Vector && length(Ps) == 1
        @test normred(only(Ps), M) == 11
      end
    end
  end

  let
    A = matrix_algebra(QQ, 3)
    O = order(A, basis(A))
    P = Hecke.maximal_integral_ideal_containing(2*O, 2, :left)
    @test normred(P, O) == 2
  end

  @testset "Maximal ideal containing a nonzero residue ideal" begin
    Hecke.Random.seed!(2)
    A = matrix_algebra(QQ, 3)
    O = order(A, basis(A))
    I = ideal(O, A(diagonal_matrix(QQ, [2, 1, 2])), :left)
    P = Hecke.maximal_integral_ideal_containing(I, 2, :left)
    @test normred(P, O) == 2
    @test all(b in P for b in absolute_basis(I))
    @test O * P == P
  end

  @testset "Maximal integral ideals of a quaternion order at a split prime" begin
    # the l + 1 maximal right and left ideals containing l, for l not dividing
    # the reduced discriminant of O, against the route through O/P for any
    # order: the same ideals, each of reduced norm l with O as right (left)
    # order, and the same list on every call
    generic(O, l, side) = reduce(vcat,
      [Hecke.__maximal_integral_ideals(O, P, l, side)
       for P in prime_ideals_over(O, l)])
    key(I) = Hecke._hnf_integral(basis_matrix(I), :lowerleft)
    for (a, b) in [(-1, -11), (-2, -37)]
      A = quaternion_algebra(QQ, a, b)
      M = maximal_order(A)
      J = first(Hecke.maximal_integral_ideals(M, 2; side = :right))
      E = order(A, vcat([one(A)], basis(J)))
      Z3M = order(A, vcat([one(A)], [3 * elem_in_algebra(x) for x in basis(M)]))
      for O in [M, E, Z3M], l in [2, 3, 5, 7], side in [:right, :left]
        is_divisible_by(Hecke._reduced_disc(O), l) && continue
        Is = Hecke.maximal_integral_ideals(O, l; side)
        @test length(Is) == l + 1
        @test Set(key.(Is)) == Set(key.(generic(O, l, side)))
        @test all(I -> normred(I, O) == l, Is)
        # the right (left) order computed from the basis, not the one stored
        fresh(I) = ideal(A, basis_matrix(I))
        if side === :right
          @test all(I -> I * O == I && right_order(fresh(I)) == O, Is)
        else
          @test all(I -> O * I == I && left_order(fresh(I)) == O, Is)
        end
        @test key.(Is) == key.(Hecke.maximal_integral_ideals(O, l; side))
        @test key.(Is) == key.(Hecke.maximal_integral_ideals(O, ZZ(l); side))
      end
    end

    # Z<1, i, j, k> in (-1, -11) at 1019, where c1^2 + c2^2 = 0 mod 1019 has
    # only the trivial solution, so that no alpha in the span of 1 and i has
    # rank one: the same ideals as the route through O/P
    A = quaternion_algebra(QQ, -1, -11)
    O = order(A, basis(A))
    for side in [:right, :left]
      Is = Hecke.maximal_integral_ideals(O, 1019; side)
      @test length(Is) == 1020
      @test Set(key.(Is)) == Set(key.(generic(O, 1019, side)))
    end

    # p must be prime
    M = maximal_order(A)
    for n in [15, 9, 1, 0, -3]
      @test_throws ArgumentError Hecke.maximal_integral_ideals(M, n; side = :right)
    end
  end
end
