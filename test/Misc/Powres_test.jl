@testset "Power Residue" begin
    R = ResidueRing(ZZ,7)
    Rx,x = R["x"]
    b = x^4+x+1 #irreducible
    a = rand(Rx, 1:10)
    a = div(a, gcd(a, b))
    d = fmpz(3)
    @test Hecke.power_residue(b^2,b,d,fmpz(7)) == 0
    @test Hecke.power_residue(a,b,d,fmpz(7)) == mod(a^(div(7^degree(b)-1, 3)), b)
end
