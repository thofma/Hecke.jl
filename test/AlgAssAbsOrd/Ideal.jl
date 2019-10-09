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
    A = Hecke.quaternion_algebra(-1, -1)
    OA = maximal_order(A)

    p = prime_ideals_over(OA, 2)
    @test length(p) == 1
    @test p[1] == pradical(OA, 2)

    p = prime_ideals_over(OA, 3)
    @test length(p) == 1
    @test p[1] == 3*OA
  end

  @testset "Locally free basis" begin
    Qx, x = FlintQQ["x"]
    f = x^4 - 5x^2 + 5
    K, a = number_field(f, "a") # Gal(K/Q) == C_4
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

end
