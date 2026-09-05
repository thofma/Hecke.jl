@testset "G3 Invariants and reconstruction" begin

    R, (x, y, z) = polynomial_ring(QQ, [:x,:y,:z])
    f = 24*x^4 + 13*x^3*y + x^3*z + 21*x^2*y^2 + 22*x^2*y*z + 28*x^2*z^2+7*x*y^3 + 23*x*y^2*z +27*x*y*z^2 + 10*x*z^3 +4*y^4 + 24*y^3*z + 2*y^2*z^2 + 20*y*z^3 +3*z^4

    #DO_invs, ws = @inferred dixmier_ohno_invariants(f)
    #TODO: Type stability for Julia v1.10-v1.11. It is type stable for 1.12 and higher.
    DO_invs, ws = dixmier_ohno_invariants(f)

    @test weighted_equality(DO_invs,[QQ(-10643//4), QQ(-232789351//10368), QQ(28644032036970205//1492992), QQ(33598204438518145//2985984), QQ(-281343305965100915927//35831808), 
    QQ(-9100651428481744802615//214990848), QQ(1488374529239252586611662819//82556485632), QQ(-75125447549415147964293401//27518828544), 
    QQ(199959474616841973201970119463769//2641807540224), QQ(846062552900897854109202266252809//23776267862016), 
    QQ(-10265140054846738766406670344006240929//160489808068608), QQ(-1560364612621209466127267306887733624939//1711891286065152), 
    QQ(19741947255984030059126097580178044126062103//1099511627776) ], ws)

    @test weighted_equality(dixmier_ohno_invariants(@inferred reconstruct_from_dixmier_ohno_invariants(DO_invs))[1], DO_invs, ws)

    K = GF(43)
    R, (x, y, z) = polynomial_ring(K, [:x,:y,:z])
    f = 15*x^4 -5*x^3*y + x^3*z + 7*x^2*y^2 + 8*x^2*y*z + -3*x^2*z^2+7*x*y^3 + 14*x*y^2*z +15*x*y*z^2 + 36*x*z^3 + 5*y^4 + 23*y^3*z + 21*y^2*z^2 + 4*y*z^3 +2*z^4

    #DO_invs, ws = @inferred dixmier_ohno_invariants(f)
    #TODO: Type stability for Julia v1.10-v1.11. It is type stable for 1.12 and higher.
    DO_invs, ws = dixmier_ohno_invariants(f)

    @test weighted_equality(DO_invs, map(K, [38, 10, 38, 37, 16, 30, 8, 14, 42, 30, 12, 40, 21]), ws)
    @test weighted_equality(dixmier_ohno_invariants(@inferred reconstruct_from_dixmier_ohno_invariants(DO_invs))[1], DO_invs, ws)

end