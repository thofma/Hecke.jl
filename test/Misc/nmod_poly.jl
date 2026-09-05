@testset "gcd_sircana" begin
    R = residue_ring(ZZ,9)[1]
    S, x = R[:x]
    f = x^2
    g = x^2-5*x+6

    a, u, v = Hecke.gcd_sircana(f,g)
    d = u*f + v*g
    @test is_zero(rem(d, a))

    F, = residue_ring(ZZ, 12); x = F[:x][2]
    d, u, v = Hecke.gcd_sircana((x+7)*(x+1), (x+7)*(2*x+1))
    @test d == x + 7

    F, = residue_ring(ZZ, 210); x = F[:x][2]
    d, u, v = Hecke.gcd_sircana(x^2+1, x+1)
    @test d*u == x^2+1
    @test d*v == x+1

    F, = residue_ring(ZZ, 12); x = F[:x][2]
    d, u, v = Hecke.gcd_sircana(x^2+1, x+1)
    @test d*u == x^2+1
    @test d*v == x+1

    F, = residue_ring(ZZ, 9); x = F[:x][2]
    d, u, v = Hecke.gcd_sircana(x^2, x*(x^2-5*x+6))
    @test d == x

#=
    g *= x
    a, u, v = Hecke.gcd_sircana(f,g)
    d = u*f + v*g
    @test is_zero(rem(d, a))
=#
end

