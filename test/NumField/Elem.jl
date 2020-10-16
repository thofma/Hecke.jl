@testset "NumField/Elem" begin
  Qx, x = PolynomialRing(FlintQQ, "x")
  QasNumberField, _ = NumberField(x - 1)
  Kt, t = PolynomialRing(QasNumberField, "t")
  K1, a1 = NumberField(x^3 - 2)
  K2, (a2, ) = NumberField([x^3 - 2])
  K3, a3 = NumberField(t^3 - 2)
  K4, (a4, ) = NumberField([t^3 - 2])

  @testset for (K, a) in [(K1, a1), (K2, a2), (K3, a3), (K4, a4)]
    b = one(K)
    fl = @inferred isintegral(b)
    @test fl
    fl = @inferred isintegral(a)


    B = @inferred basis(K)
    c = @inferred basis_matrix([one(K), a^4])
    @assert nrows(c) == 2
    @assert ncols(c) == 3
    @assert sum(B[i] * c[1, i] for i in 1:3) == one(K)
    @assert sum(B[i] * c[2, i] for i in 1:3) == a^4

    f = @inferred charpoly(one(K()))
    @test f == (gen(parent(f)) - 1)^3
    f = @inferred minpoly(one(K))
    @test f == (gen(parent(f)) - 1)

    f = @inferred charpoly(a)
    @test f == gen(parent(f))^3 - 2
    f = @inferred minpoly(a)
    @test f == gen(parent(f))^3 - 2

  end

  @testset "NumField/Component" begin
    Qx, x = PolynomialRing(FlintQQ, "x")
    QasNumberField, _ = NumberField(x - 1)
    Kt, t = PolynomialRing(QasNumberField, "t")
    K3, a3 = NumberField(t^3 - 2)
    K4, (a4, ) = NumberField([t^3 - 2])
    K41, mK4 = component(K4, 1)
    @test isisomorphic(K41, K3)[1]
    @test mK4(gen(K41)) == a4


    K1, a1 = NumberField(x^3 - 2)
    K2, (a2, ) = NumberField([x^3 - 2])
    K21, mK2 = component(K2, 1)
    @test isisomorphic(K21, K1)[1]
    @test mK2(gen(K21)) == a2
  end  

  @testset "NumField/Coordinates" begin
    Qx, x = PolynomialRing(FlintQQ, "x")
    K, a = number_field(x^2+1, cached = false)
    BK = basis(K)
    for i = 1:5
      el = rand(K, -5:5)
      v = coordinates(el)
      @test el == dot(v, BK)
    end
    Kns, gKns = number_field([x^2+1, x^2+2], check = false)
    BKns = basis(Kns)
    for i = 1:5
      el = rand(Kns, -5:5)
      v = coordinates(el)
      @test el == dot(v, BKns)
    end
    Kt, t = PolynomialRing(K, "t", cached = false)
    L, gL = number_field(t^2+3, cached = false)
    BL = basis(L)
    BLabs = absolute_basis(L)
    for i = 1:5
      el = rand(L, -5:5)
      v = coordinates(el)
      vabs = absolute_coordinates(el)
      @test el == dot(v, BL)
      @test el == dot(vabs, BLabs)
    end
    Lns, gLns = number_field([t^2+3, t^2+5], check = false, cached = false)
    BLns = basis(Lns)
    BLnsabs = absolute_basis(Lns)
    for i = 1:5
      el = rand(Lns, -5:5)
      v = coordinates(el)
      vabs = absolute_coordinates(el)
      @test el == dot(v, BLns)
      @test el == dot(vabs, BLnsabs)
    end
    Knsy, y = PolynomialRing(Kns, "y", cached = false)
    F, gF = number_field(y^2+7, cached = false)
    BF = basis(F)
    BFabs = absolute_basis(F)
    for i = 1:5
      el = rand(F, -5:5)
      v = coordinates(el)
      vabs = absolute_coordinates(el)
      @test el == dot(v, BF)
      @test el == dot(vabs, BFabs)
    end
    Fns, gFns = number_field([y^2+7, y^2+11], cached = false)
    BFns = basis(Fns)
    BFnsabs = absolute_basis(Fns)
    for i = 1:5
      el = rand(Fns, -5:5)
      v = coordinates(el)
      vabs = absolute_coordinates(el)
      @test el == dot(v, BFns)
      @test el == dot(vabs, BFnsabs)
    end
    Fnsz, z = PolynomialRing(Fns, "z", cached = false)
    N, gN = number_field([z^2+17, z^2+19], check = false, cached = false)
    BN = basis(N)
    BNabs = absolute_basis(N)
    for i = 1:5
      el = rand(N, -5:5)
      v = coordinates(el)
      vabs = absolute_coordinates(el)
      @test el == dot(v, BN)
      @test el == dot(vabs, BNabs)
    end
  end
end  
