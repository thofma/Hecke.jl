@testset "G2 Invariants" begin

    
    Qx, x = polynomial_ring(QQ, "x") 
    f1 = x^6+3*x+5
    h1 = x+2
    C = hyperelliptic_curve(f1, h1)

    cl_invs = @inferred clebsch_invariants(C)
    ig_cl_invs = @inferred igusa_clebsch_invariants(C)
    ig_invs = @inferred igusa_invariants(C)
    g2_invs = @inferred g2_invariants(C)

    @test cl_invs == clebsch_invariants(f1, h1)
    @test weighted_equality(cl_invs,[ QQ(192), QQ(6912032//1125), QQ(-221201408//1125), QQ(-5220510728192//3796875) ] ,[2,4,6,10])
    @test weighted_equality(ig_cl_invs,[ QQ(-23040), QQ(14930112), QQ(-106065874944), QQ(-374476383977472) ] ,[2,4,6,10])
    @test weighted_equality(ig_invs, [ QQ(-2880), QQ(190078), QQ(4428544), QQ(-12220963201), QQ(-91424898432) ] ,[2,4,6,8,10])
    @test g2_invs == [ QQ(171992678400000//79361891), QQ(563065344000//11337413), QQ(-31885516800//79361891) ]

    @test weighted_equality(igusa_clebsch_from_igusa(ig_invs), ig_cl_invs, [2,4,6,10])
    @test weighted_equality(clebsch_from_igusa_clebsch(ig_cl_invs), cl_invs, [2,4,6,10])
    @test weighted_equality(igusa_from_g2(g2_invs), ig_invs, [2,4,6,8,10])


    F = GF(37)
    Fx, x = polynomial_ring(F, "x")

    f1 = x^5+8*x^4-5*x^3+3*x^2+7
    C = hyperelliptic_curve(f1)
    @test weighted_equality(clebsch_invariants(C),[ F(9), F(18), F(26), F(24)] ,[2,4,6,10])
    @test weighted_equality(igusa_clebsch_invariants(C),[ F(30), F(21), F(29), F(9) ] ,[2,4,6,10])
    @test weighted_equality(igusa_invariants(C), [ F(13), F(18), F(20), F(21), F(16) ]  ,[2,4,6,8,10])
    @test g2_invariants(C) == [ F(23), F(25), F(17) ]


    @test weighted_equality(igusa_clebsch_from_igusa(igusa_invariants(C)), igusa_clebsch_invariants(C), [2,4,6,10])
    @test weighted_equality(clebsch_from_igusa_clebsch(igusa_clebsch_invariants(C)), clebsch_invariants(C), [2,4,6,10])
    @test weighted_equality(igusa_from_g2(g2_invariants(C)), igusa_invariants(C), [2,4,6,8,10])


    F = GF(2, 4)
    a = gen(F)
    Fx, x = polynomial_ring(F, "x")

    f1 = x^6+a^2*x^5 + (a+a^3)*x^4+(a+1)*x^2+a*x+1
    C = hyperelliptic_curve(f1, Fx(1))

    ig_invs = @inferred igusa_invariants(C)
    g2_invs = @inferred g2_invariants(C)

    @test weighted_equality(ig_invs,[ F(0), F(0), F(0), F(1), F(a^12)] ,[2,4,6,8,10])
    @test g2_invs == [ F(0), F(0), F(a^9) ]
    @test weighted_equality(igusa_from_g2(g2_invs), ig_invs, [2,4,6,8,10])


    F = GF(5)
    Fx, x = polynomial_ring(F, "x")

    f1 = x^6+3*x^5-4*x^4+3*x^2+2*x-1
    C = hyperelliptic_curve(f1)

    ig_cl_invs = @inferred igusa_clebsch_invariants(C)
    ig_invs = @inferred igusa_invariants(C)
    g2_invs = @inferred g2_invariants(C)

    @test weighted_equality(ig_cl_invs,[ F(2), F(3), F(0), F(3) ] ,[2,4,6,10])
    @test weighted_equality(ig_invs,[ F(4), F(1), F(2), F(3), F(3)] ,[2,4,6,8,10])
    @test g2_invs == [ F(3), F(3), F(4) ]
    @test weighted_equality(igusa_clebsch_from_igusa(ig_invs), ig_cl_invs, [2,4,6,10])
    @test weighted_equality(igusa_from_g2(g2_invs), ig_invs, [2,4,6,8,10])


    F = GF(7)
    Fx, x = polynomial_ring(F, "x")

    f1 = x^6+3*x^5-4*x^4+3*x^2+2*x-1
    C = hyperelliptic_curve(f1)
    @test weighted_equality(clebsch_invariants(C),[ F(0), F(2), F(2), F(0)] ,[2,4,6,10])
    @test weighted_equality(igusa_clebsch_invariants(C),[ F(0), F(4), F(1), F(3) ] ,[2,4,6,10])
    @test weighted_equality(igusa_invariants(C),[ F(0), F(2), F(3), F(6), F(3)] ,[2,4,6,8,10])
    @test g2_invariants(C) == [ F(0), F(2), F(2) ]

    @test weighted_equality(igusa_clebsch_from_igusa(igusa_invariants(C)), igusa_clebsch_invariants(C), [2,4,6,10])
    @test weighted_equality(clebsch_from_igusa_clebsch(igusa_clebsch_invariants(C)), clebsch_invariants(C), [2,4,6,10])
    @test weighted_equality(igusa_from_g2(g2_invariants(C)), igusa_invariants(C), [2,4,6,8,10])

    
  end
