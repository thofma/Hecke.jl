@testset "Power modulo" begin
    R = ResidueRing(ZZ,7)
    Rx,x = R["x"]
    f = Base.rand(Rx,10)
    g = x^4+x+1
    e = fmpz(10)^20
    @test powmod(f,e,g) == powmod(f,e%(7^degree(g)-1),g)
    @test powmod(f,fmpz(0),g) == 1
end
