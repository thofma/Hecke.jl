@testset "Power modulo" begin
    R = residue_ring(ZZ,7)[1]
    Rx,x = R["x"]
    f = rand(Rx, 1:10)
    g = x^4+x+1
    e = ZZRingElem(10)^20
    @test powermod(f,e,g) == powermod(f,e%(7^degree(g)-1),g)
    @test powermod(f,ZZRingElem(0),g) == 1
end
