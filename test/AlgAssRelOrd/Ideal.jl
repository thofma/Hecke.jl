@testset "AlgAssRelOrdIdl" begin
  Qx, x = QQ["x"]
  f = x^2 - 10x - 8
  K, a = number_field(f, "a")
  KG = group_algebra(K, FinGenAbGroup([ 2 ]))

  @testset "Arithmetic" begin
    O = any_order(KG)
    I = 2*O
    J = 4*O

    @test I + J == I
    @test I*J == 8*O
    @test intersect(I, J) == J
    @test I^2 == J
    @test I^ZZRingElem(2) == J

    @test norm(I) == 4*base_ring(O)

    @test hash(I * J) == hash(8 * O)
  end

  @testset "Locally free basis" begin
    Ky, y = K["y"]
    OK = maximal_order(K)
    g = y^2 + 1
    L, b = number_field(g, "b") # Gal(L/K) == C_2
    OL = maximal_order(L)

    LtoKG, KGtoL = Hecke._find_isomorphism(L, KG)
    basisOL = Vector{elem_type(KG)}()
    for i = 1:degree(L)
      for b in basis(pseudo_basis(OL, copy = false)[i][2])
        push!(basisOL, LtoKG(b*pseudo_basis(OL, copy = false)[i][1]))
      end
    end
    d = lcm([ denominator(b) for b in basisOL ])
    OKG = order(KG, basis(KG))
    I = Hecke.ideal_from_lattice_gens(KG, OKG, [ d*b for b in basisOL ])

    p = prime_decomposition(OK, 3)[1][1]
    g = Hecke.locally_free_basis(I, p)
    OKGg = OKG*g
    mat_I = Hecke.coprime_bases(OKG, I, p)[4]
    mat_OKGg = Hecke.coprime_bases(OKG, OKGg, p)[4]
    t = det(mat_I*inv(mat_OKGg))
    @test valuation(t, p) == 0

    p = prime_decomposition(OK, 2)[1][1]
    @test_throws ErrorException  Hecke.locally_free_basis(I, p)
  end

  @testset "maximal integral ideal" begin
    K,z = cyclotomic_field(7)
    o = maximal_order(K)
    M = Hecke.zeros_array(K,2,2,2)
    M[1,1,1] = one(K)
    M[1,2,2] = one(K)
    M[2,1,2] = one(K)
    M[2,2,1] = K(-12)
    E = Hecke.StructureConstantAlgebra(K,M)
    OE = maximal_order(E)
    @test is_prime(numerator(norm(@inferred Hecke.maximal_integral_ideal(OE, 3*o, :left))))
  end

  @testset "Maximal ideal containing a nonzero residue ideal" begin
    # This seed produces a residue generator with an existing pivot in column 1.
    Hecke.Random.seed!(0)
    K, = rationals_as_number_field()
    A = matrix_algebra(K, 3)
    O = order(A, basis(A))
    p = 2 * base_ring(O)
    I = ideal(O, A(diagonal_matrix(K, [2, 1, 2])), :left)
    P = Hecke.maximal_integral_ideal_containing(I, p, :left)
    @test normred(P, O) == p
    @test all(b in P for b in absolute_basis(I))
    @test O * P == P
  end

  @testset "factor" begin
    K,z = cyclotomic_field(7);
    E = Hecke.quaternion_algebra2(K, K(-1), K(-1))
    OE = maximal_order(E)
    list_ideals = [rand(E)*OE for i=1:10]
    list_factors = factor.(list_ideals)
    @test prod.(list_factors) == list_ideals
  end

  let # maximal integral ideal
    K, = rationals_as_number_field()
    QG = K[small_group(36, 1)]
    ZG = order(QG, basis(QG))
    p, = prime_ideals_over(maximal_order(K), 2)
    P = Hecke.maximal_integral_ideal(ZG, p; side = :left)
    @test ZG(2) in P
    @test !(ZG(3) in P)
    @test ZG * P == P
    p, = prime_ideals_over(maximal_order(K), 3)
    P = Hecke.maximal_integral_ideal(ZG, p; side = :right)
    @test ZG(3) in P
    @test !(ZG(2) in P)
    @test P * ZG == P

    K, = rationals_as_number_field()
    QG = K[small_group(20, 1)]
    ZG = order(QG, basis(QG))
    p, = prime_ideals_over(maximal_order(K), 2)
    Ps = Hecke.maximal_integral_ideals(ZG, p; side = :left)
    @test allunique(Ps)
    for P in Ps
      @test ZG(2) in P
      @test !(ZG(3) in P)
      @test ZG * P == P
    end

    p, = prime_ideals_over(maximal_order(K), 3)
    Ps = Hecke.maximal_integral_ideals(ZG, p; side = :right)
    @test allunique(Ps)
    for P in Ps
      @test ZG(3) in P
      @test !(ZG(2) in P)
      @test P * ZG == P
    end

    # a quaternion algebra (I know the result)
    let
      K, = rationals_as_number_field()
      a, b, bas = (-3, -1, Vector{QQFieldElem}[[1, 0, 0, 0], [1//2, 3//2, 0, 0], [0, 0, 3, 0], [0, 0, 3//2, 1//2]])
      A = quaternion_algebra(K, a, b)
      bO = A.(bas)
      O = order(A, bO)
      p, = prime_ideals_over(base_ring(O), 2)
      lP = Hecke.maximal_integral_ideals(O, p; side = :right)
      @test allunique(lP) && length(lP) == 3
      @test all(P -> P * O == P, lP)
      @test all(P -> all(in(O), absolute_basis(P)), lP)
    end

    # (sqrt(5), -3) over Q(sqrt(5)) ramifies at the prime above 5: one maximal
    # ideal there, returned as a vector like any other answer
    let
      K, a = quadratic_field(5)
      A = quaternion_algebra(K, a, K(-3))
      M = maximal_order(A)
      p, = prime_ideals_over(base_ring(M), 5)
      for side in [:right, :left]
        Ps = Hecke.maximal_integral_ideals(M, p; side)
        @test Ps isa Vector && length(Ps) == 1
      end
    end

    # at a prime p not dividing the reduced discriminant: the N(p) + 1 maximal
    # ideals, as a set those of the route through O/P, of reduced norm p and
    # with O as right (left) order, and the same list on every call; primes
    # of degree 1 and 2, above 2 and 3, for a maximal order and R + qM
    let
      old(O, p, side) = reduce(vcat,
        [Hecke.__maximal_integral_ideals(O, P, p, side)
         for P in prime_ideals_over(O, p)])
      K, = quadratic_field(5)
      A = quaternion_algebra(K, -1, -1)
      M = maximal_order(A)
      R = base_ring(M)
      q, = prime_decomposition(R, 11)[1]
      one_row = pseudo_matrix(matrix(K, 1, 4, coefficients(one(A))), [1 * R])
      PM = q * basis_pmatrix(M)
      E = order(A, sub(pseudo_hnf(vcat(PM, one_row), :lowerleft), 2:5, 1:4))
      primes = [P for l in [2, 3, 11] for (P, _) in prime_decomposition(R, l)]
      for O in [M, E], p in primes, side in [:right, :left]
        valuation(Hecke._reduced_disc(O), p) == 0 || continue
        Ps = Hecke.maximal_integral_ideals(O, p; side)
        @test length(Ps) == norm(p) + 1 && allunique(Ps)
        old_Ps = old(O, p, side)
        @test all(P -> count(==(P), old_Ps) == 1, Ps)
        for P in Ps
          J = ideal(A, basis_pmatrix(P))
          @test (side === :right ? right_order(J) : left_order(J)) == O
          @test normred(J, O) == fractional_ideal(R, p)
        end
        Qs = Hecke.maximal_integral_ideals(O, p; side)
        @test basis_pmatrix.(Qs) == basis_pmatrix.(Ps)
      end
      @test_throws ArgumentError Hecke.maximal_integral_ideals(M, 11 * R;
                                                               side = :right)
    end
  end

  @testset "Quotients as algebras" begin
    Qx, x = polynomial_ring(QQ, :x, cached = false)
    K, a = number_field(x^2 + 12 * x - 92, :a)
    OK = maximal_order(K)
    Ky, y = polynomial_ring(K, :y, cached = false)
    L, b = number_field(y^3 - 54 * y - 74, :b)
    OL = maximal_order(L)
    pbOL = pseudo_basis(OL)
    p = prime_decomposition(OK, 2)[1][1]

    M = diagonal_matrix(K, [1, 1, 1//2])
    PM = pseudo_matrix(M, [p, p, p])
    J = ideal(OL, PM)

    # Quotient of order by ideal over F_2
    Q, OLtoQ = quo(OL, J, p)
    @test dim(Q) == 2
    @test order(base_ring(Q)) == 2
    @test is_one(OLtoQ(OL(pbOL[1][1])))
    @test !is_zero(OLtoQ(OL(pbOL[2][1])))
    @test is_zero(OLtoQ(OL(pbOL[3][1])))

    q = preimage(OLtoQ, Q[1])
    @test is_one(q)
    @test parent(q) === OL

    # Quotient of ideal by ideal over F_2
    I = 1 * OL
    pbI = pseudo_basis(I)
    Q, ItoQ = quo(I, J, p)
    @test dim(Q) == 2
    @test order(base_ring(Q)) == 2
    @test is_one(ItoQ(OL(pbI[1][1])))
    @test !is_zero(ItoQ(OL(pbI[2][1])))
    @test is_zero(ItoQ(OL(pbI[3][1])))

    q = preimage(ItoQ, Q[1])
    @test is_one(q)
    @test parent(q) === OL

    # There is a slight difference in the code depending on whether the first
    # ideal is (1) or not. So we run it again with 2 * I and 2 * J.
    I2 = 2 * OL
    J2 = 2 * J
    pbI2 = pseudo_basis(I2)
    Q, I2toQ = quo(I2, J2, p)
    @test dim(Q) == 2
    @test order(base_ring(Q)) == 2
    @test_throws ErrorException one(Q)
    @test I2toQ(OL(2 * pbI2[1][1])) == Q[1]
    @test is_zero(I2toQ(OL(pbI2[3][1])))

    q = preimage(I2toQ, Q[1])
    @test parent(q) === OL
    @test q in I2
    @test !(q in J2)

    # Edge cases: Order by ideal (1) and ideal by itself
    Q0, OLtoQ0 = quo(OL, 1 * OL, p)
    @test dim(Q0) == 0
    @test order(base_ring(Q0)) == 2
    @test is_zero(OLtoQ0(one(OL)))
    q = preimage(OLtoQ0, zero(Q0))
    @test is_zero(q)
    @test parent(q) === OL

    Q0, JtoQ0 = quo(J, J, p)
    @test dim(Q0) == 0
    @test order(base_ring(Q0)) == 2
    @test is_zero(JtoQ0(one(OL)))
    q = preimage(JtoQ0, zero(Q0))
    @test is_zero(q)
    @test parent(q) === OL
  end
end
