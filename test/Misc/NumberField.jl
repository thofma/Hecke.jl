@testset "Misc/NumberField" begin
  @testset "issubfield" begin
    Qx, x = FlintQQ["x"]
    K, a = NumberField(x^2 + 1, "a")
    L, b = NumberField(x^4 + 1, "b")

    c, KtoL = Hecke.issubfield(K, L)
    @test c == true
    @test parent(KtoL(a)) == L
    
    c, KtoL = Hecke.issubfield_normal(K, L)
    @test c == true
    @test parent(KtoL(a)) == L
    
    OK = maximal_order(K)
    OL = maximal_order(L)
    c, KtoL = Hecke.issubfield(K, L)
    @test c == true
    @test parent(KtoL(a)) == L
  end

  @testset "isisomorphic" begin
    Qx, x = FlintQQ["x"]
    f = x^5 + 12x - 92
    K, a = NumberField(f, "a")

    g = x^5 - 172x^4 + 7024x^3 + 8656448x^2 + 55735552x + 45796197888
    K2, a2 = NumberField(g, "a2")

    c, KtoK2 = Hecke.isisomorphic(K, K2)
    @test c == true
    @test parent(KtoK2(a)) == K2

    OK = maximal_order(K)
    OK2 = maximal_order(K2)
    c, KtoK2 = Hecke.isisomorphic(K, K2)
    @test c == true
    @test parent(KtoK2(a)) == K2

    h = f - 1
     K3, a3 = NumberField(h, "a3")
    d, KtoK3 = Hecke.isisomorphic(K, K3)
    @test d == false
  end
end
