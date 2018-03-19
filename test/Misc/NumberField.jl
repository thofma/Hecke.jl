@testset "Misc/NumberField" begin
  @testset "isisomorphic" begin
    Qx, x = QQ["x"]
    f = x^5 + 12x - 92
    K, a = NumberField(f, "a")

    b = rand(K, -10:10)
    g = minpoly(b)
    while degree(g) != 5
      b = rand(K, -10:10)
      g = minpoly(b)
    end

    K2, a2 = NumberField(g, "a2")

    c, KtoK2 = Hecke.isisomorphic(K, K2)
    @test c == true
    @test parent(KtoK2(a)) == K2

    h = f - 1
    K3, a3 = NumberField(h, "a3")
    d, KtoK3 = Hecke.isisomorphic(K, K3)
    @test d == false
  end
end
