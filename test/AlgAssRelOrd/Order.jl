@testset "AlgAssRelOrd" begin

  @testset "Maximal Orders" begin
    Qx, x = FlintQQ["x"]
    f = x^2 - 5x - 1
    K, a = number_field(f, "a")
    G = small_group(8, 4)
    KG = group_algebra(K, G)

    O1 = Hecke.maximal_order_via_absolute(KG)
    O2 = Hecke.maximal_order_via_relative(KG)
    @test discriminant(O1) == discriminant(O2)

    KG = AlgAss(KG)[1]

    O1 = Hecke.maximal_order_via_absolute(KG)
    O2 = Hecke.maximal_order_via_relative(KG)
    @test discriminant(O1) == discriminant(O2)
  end

end
