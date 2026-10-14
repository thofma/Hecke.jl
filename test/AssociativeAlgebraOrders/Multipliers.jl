@testset "Lattice multiplier orders" begin
  for (R, K, p) in algebra_order_test_rings()
    A = matrix_algebra(K, 2)
    E = lattice(A, R, basis(A))
    D = A(K[p 0; 0 1])
    L = D*E
    Ol = @inferred left_order(L)
    Or = @inferred right_order(L)
    @test Ol isa AlgebraOrders.AssociativeAlgebraOrder
    @test Or isa AlgebraOrders.AssociativeAlgebraOrder
    @test Ol !== Or
    @test Ol != Or
    @test AlgebraOrders.underlying_lattice(Ol) == D*E*inv(D)
    @test AlgebraOrders.underlying_lattice(Or) == E
    @test issubset(AlgebraOrders.underlying_lattice(Ol)*L, L)
    @test issubset(L*AlgebraOrders.underlying_lattice(Or), L)
    @test left_order(inv(p)*L) == Ol
    @test right_order(inv(p)*L) == Or
    @test_throws ArgumentError left_order(lattice(A, R, basis(A)[1:2]))
    @test_throws ArgumentError right_order(Hecke.zero_lattice(A, R))

    Z = Hecke.zero_lattice(zero_algebra(K), R)
    @test left_order(Z) == right_order(Z)
    @test iszero(left_order(Z))
  end
end
