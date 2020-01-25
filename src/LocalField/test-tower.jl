
EisensteinField = Hecke.EisensteinField

Qp = PadicField(7,10)
Rx, x = PolynomialRing(Qp,"x")
K,a = EisensteinField(x^6-7, "a")
Ry,y = PolynomialRing(K,"y")
L,b = EisensteinField(y^4-a, "b")

@testset "Towers" begin
    Qp = PadicField(7,10)
    Rx, x = PolynomialRing(Qp,"x")
    K,a = EisensteinField(x^6-7, "a")
    Ry,y = PolynomialRing(K,"y")
    L,b = EisensteinField(y^4-a, "b")

    Lsq, mp, mpinv = Hecke.squash(L)
    
    # Coercsion
    @test L(Qp(0)) == zero(L)

    @test Qp(zero(L)) == zero(Qp)

    # Squash
    @test gen(Lsq) == mp(gen(L))

    @test mp(zero(L)) == zero(Lsq)

    @test mpinv(zero(Lsq)) == zero(L)

    @test mpinv(mp(gen(L))) == gen(L)

    @test length(Hecke.roots(L.pol, L)) == 2

    @test length(Hecke.roots(K.pol, L)) == 6

    @test all(let a=rand(Qp); Qp(L(a))==a end for i=1:10)

    @test all(let a=rand(K); K(L(a))==a end for i=1:10)
end

@testset "Towers: Sharpening" begin
    Qp = PadicField(7,10)
    Rx, x = PolynomialRing(Qp,"x")
    K,a = EisensteinField(x^6-7, "a")
    Ry,y = PolynomialRing(K,"y")
    L,b = EisensteinField(y^4-a, "b")

    sharpen_base!(K, 20)
    sharpen_base!(L, 20)
    sharpen!(L, 20)

    @test precision(L) == 20

    @test precision(base_ring(L)) == 20

    @test precision(Qp) == 20
    
end

nothing
