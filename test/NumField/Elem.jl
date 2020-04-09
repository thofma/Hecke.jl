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
end  
