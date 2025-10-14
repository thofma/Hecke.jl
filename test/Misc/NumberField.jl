@testset "Misc/number_field" begin
  @testset "constructors" begin
    Qx, x = QQ["x"]

    # test number_field constructors with single polynomial
    K1, a = number_field(x^2 + 1)
    K2, a = number_field(x^2 + 1, "a")
    @test is_isomorphic(K1, K2)
    K3, a = number_field(x^2 + 1, :a)
    @test is_isomorphic(K1, K3)

    # test number_field constructors with vector of polynomials
    L1, b = number_field([x^3 - 2, x^2 + x + 1])
    S1, _ = absolute_simple_field(L1)

    L2, b = number_field([x^3 - 2, x^2 + x + 1], "b")
    S2, _ = absolute_simple_field(L2)
    @test is_isomorphic(S1, S2)

    L3, b = number_field([x^3 - 2, x^2 + x + 1], :b)
    S3, _ = absolute_simple_field(L3)
    @test is_isomorphic(S1, S3)

    L4, b = number_field([x^3 - 2, x^2 + x + 1], ["b1","b2"])
    S4, _ = absolute_simple_field(L4)
    @test is_isomorphic(S1, S4)

    L5, b = number_field([x^3 - 2, x^2 + x + 1], [:b1,:b2])
    S5, _ = absolute_simple_field(L5)
    @test is_isomorphic(S1, S5)
  end

  @testset "is_subfield" begin
    Qx, x = QQ["x"]
    K, a = number_field(x^2 + 1, "a")
    L, b = number_field(x^4 + 1, "b")

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
    Qx, x = QQ["x"]
    f = x^5 + 12x - 92
    K, a = number_field(f, "a")

    g = x^5 - 172x^4 + 7024x^3 + 8656448x^2 + 55735552x + 45796197888
    K2, a2 = number_field(g, "a2")

    c, KtoK2 = is_isomorphic_with_map(K, K2)
    @test c == true
    @test parent(KtoK2(a)) == K2

    OK = maximal_order(K)
    OK2 = maximal_order(K2)
    c, KtoK2 = is_isomorphic_with_map(K, K2)
    @test c == true
    @test parent(KtoK2(a)) == K2

    h = f - 1
    K3, a3 = number_field(h, "a3")
    @test !is_isomorphic(K, K3)
  end
end


@testset "Misc/modular_init" begin
  F2p,t2 = QQ[:t]
  f2 = 364500000*t2^12 - 736290000*t2^10 + 611460900*t2^8 - 265281750*t2^6 + 62955117*t2^4 - 7693776*t2^2 + 374003
  f2 = f2/leading_coefficient(f2)
  F3,c = number_field(f2, "c")
  F3p,t3 = F3[:t]
  f3 = 17559810*t3^2 - 16159500000*c^10 + 35436690000*c^8 - 29275389900*c^6 + 11410311150*c^4 - 2037830337*c^2 + 114317153
  f3 = f3/leading_coefficient(f3)
  F4,_ = number_field(f3, "d") #crash in modular_init by Oscar #5442
end

