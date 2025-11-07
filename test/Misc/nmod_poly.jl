@testset "gcd_sircana" begin
    R = residue_ring(ZZ,9)[1]
    S, x = R[:x]
    f = x^2
    g = x^2-5*x+6

    a, u, v = Hecke.gcd_sircana(f,g)
    d = u*f + v*g
    @test is_zero(rem(d, a))

#=
    g *= x
    a, u, v = Hecke.gcd_sircana(f,g)
    d = u*f + v*g
    @test is_zero(rem(d, a))
=#
end

