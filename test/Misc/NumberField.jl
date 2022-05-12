@testset "Misc/NumberField" begin
  @testset "is_subfield" begin
    Qx, x = FlintQQ["x"]
    K, a = NumberField(x^2 + 1, "a")
    L, b = NumberField(x^4 + 1, "b")

    c, KtoL = is_subfield(K, L)
    @test c == true
    @test parent(KtoL(a)) == L

    c, KtoL = Hecke.is_subfield_normal(K, L)
    @test c == true
    @test parent(KtoL(a)) == L

    OK = maximal_order(K)
    OL = maximal_order(L)
    c, KtoL = is_subfield(K, L)
    @test c == true
    @test parent(KtoL(a)) == L
  end

  @testset "is_isomorphic" begin
    Qx, x = FlintQQ["x"]
    f = x^5 + 12x - 92
    K, a = NumberField(f, "a")

    g = x^5 - 172x^4 + 7024x^3 + 8656448x^2 + 55735552x + 45796197888
    K2, a2 = NumberField(g, "a2")

    c, KtoK2 = is_isomorphic_with_map(K, K2)
    @test c == true
    @test parent(KtoK2(a)) == K2

    OK = maximal_order(K)
    OK2 = maximal_order(K2)
    c, KtoK2 = is_isomorphic_with_map(K, K2)
    @test c == true
    @test parent(KtoK2(a)) == K2

    h = f - 1
    K3, a3 = NumberField(h, "a3")
    @test !is_isomorphic(K, K3)
  end
end
