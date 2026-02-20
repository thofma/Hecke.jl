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
