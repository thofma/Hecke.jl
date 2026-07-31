@testset "Shioda Invariants" begin

    Qx, x = polynomial_ring(QQ, "x")
    f1 = x^8 + 3*x^6+2*x-10
    h1 = x^3 +x+2
    C = hyperelliptic_curve(f1, h1)
    sh_invs, ws = @inferred shioda_invariants(C)


    @test weighted_equality(sh_invs,[ QQ(-20091//70), QQ(-5977893//34300), QQ(268596389//19208), QQ(11348446619//672280), 
QQ(2608534188783//3764768), QQ(-14978466451393//32941720), QQ(-70451391241636141//4035360700), 
QQ(60439772266071897//7378945280), QQ(-21411689220544042960233//25309782310400) ] ,ws)

    F = GF(37)
    Fx, x = polynomial_ring(F, "x")

    f1 = x^8 + 3*x^7 -16*x^5 + 2*x+36
    C = hyperelliptic_curve(f1)
    @test weighted_equality(shioda_invariants(C)[1],[F(15), F(8), F(27), F(8), F(31), F(20), F(17), F(7), F(5) ] , ws)

  end
