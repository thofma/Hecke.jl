@testset "Unramified extension" begin
    Qx,x = FlintQQ["x"]
    f = Qx([1, 8, -40, -46, 110, 71, -113, -43, 54, 11, -12, -1, 1])
    L = number_field(f)[1]
    P = prime_decomposition(maximal_order(L),7)[1][1]
    lp, mp = Hecke.generic_completion(L,P)
    Qy,y = PolynomialRing(lp,"y")
    f, mf = ResidueField(lp)
    N = Hecke.unramified_extension(y^3+preimage(mf,(gen(f)))+4)[1]
    F, mF = ResidueField(N)
    @test order(F) == 7^6
    G, mG = automorphism_group(N)
    @test order(G) == 3
    @test mG(G[1]^2) == mG(G[1])^2
    b = rand(f)
    @test norm(Hecke.norm_equation(F, b)) == b
    for i = 1:3
        c = 1+uniformizer(lp)^i
        chk = norm(Hecke.norm_equation_unramified(N, c))*c^-1 -1
        @test iszero(chk) || Int(ee*valuation(chk)) >= precision(c)
    end
    n = Int(ceil(absolute_ramification_index(lp)//(Int(prime(lp))-1)))+1
    l = base_field(lp)
    ee = absolute_ramification_index(l)
    for i = n:n+2
        c = 1+uniformizer(l)^i
        chk = norm(Hecke.norm_equation(lp, c))*c^-1 -1
        @test iszero(chk) || Int(ee*valuation(chk)) >= precision(c)
    end

end
