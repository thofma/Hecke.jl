@testset "LocalField" begin
  
  @testset "Creation" begin
    Qx, x = FlintQQ["x"]
    f = x^2+1
    K, a = local_field(f, 2, 10,  "a", check = false)
    @test precision(K) == 10
    @test characteristic(K) == 0
    @test prime(K) == 2

    Kt, t = PolynomialRing(K, "t")
    g = t^2+2
    L, b = local_field(g, "b", EisensteinLocalField, check = false)
    @test precision(L) == precision(g)
    @test precision(b) == precision(L)
    @test degree(L) == 2
    @test absolute_degree(L) == 4
    @test prime(L) == 2
    
    Q2 = PadicField(2, 10)
    Q2s, s = PolynomialRing(Q2, "s")
    f = s^2+s+1
    Ku, c = local_field(f, "s", UnramifiedLocalField)
    @test precision(Ku) == precision(f)
    @test precision(f) == precision(c)
    @test degree(Ku) == 2
    @test absolute_degree(Ku) == 2
    @test inertia_degree(Ku) == 2
    @test ramification_index(Ku) == 1
    @test absolute_ramification_index(Ku) == 1
    @test absolute_inertia_degree(Ku) == 2

    Lu, u = PolynomialRing(L, "u")
    Lu, d = local_field(u^2+u+1, "s", UnramifiedLocalField)
    @test absolute_degree(Lu) == 8
    @test ramification_index(Lu, K) == 2
    @test inertia_degree(Lu, K) == 2

  end


end