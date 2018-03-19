@testset "NfRel" begin
  @testset "isisomorphic" begin
    Qx, x = QQ["x"]
    f = x^2 + 12x - 92
    K, a = NumberField(f, "a")
    Ky, y = K["y"]

    g = y^5 - 5
    L, b = NumberField(g, "b")
    bb = 5*b - 2
    h = minpoly(bb)
    L2, b2 = NumberField(h, "b2")

    c, LtoL2 = Hecke.isisomorphic(L, L2)
    @test c == true
    @test parent(LtoL2(b)) == L2

    i = g - 1
    L3, b3 = NumberField(i, "b3")
    d, LtoL3 = Hecke.isisomorphic(L, L3)
    @test d == false
  end
end
