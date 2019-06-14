@testset "AlgAssRelOrdIdl" begin

  @testset "Locally free basis" begin
    Qx, x = FlintQQ["x"]
    f = x^2 - 10x - 8
    K, a = number_field(f, "a")
    Ky, y = K["y"]
    OK = maximal_order(K)
    g = y^2 + 1
    L, b = number_field(g, "b") # Gal(L/K) == C_2
    OL = maximal_order(L)

    KG = group_algebra(K, GrpAbFinGen([ 2 ]))
    LtoKG, KGtoL = Hecke._find_isomorphism(L, KG)
    basisOL = Vector{elem_type(KG)}()
    for i = 1:degree(L)
      for b in basis(pseudo_basis(OL, copy = false)[i][2])
        push!(basisOL, LtoKG(b*pseudo_basis(OL, copy = false)[i][1]))
      end
    end
    d = lcm([ denominator(b) for b in basisOL ])
    OKG = Order(KG, basis(KG))
    I = Hecke.ideal_from_lattice_gens(OKG, [ d*b for b in basisOL ])

    p = prime_decomposition(OK, 3)[1][1]
    g = Hecke.locally_free_basis(I, p)
    OKGg = OKG*g
    t = det(basis_mat(I, copy = false)*basis_mat_inv(OKGg, copy = false))
    @test valuation(t, p) == 0

    p = prime_decomposition(OK, 2)[1][1]
    @test_throws ErrorException  Hecke.locally_free_basis(I, p)
  end

end
