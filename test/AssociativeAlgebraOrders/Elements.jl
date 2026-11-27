@testset "Order element representations" begin
  for (R, K, p) in algebra_order_test_rings()
    A = matrix_algebra(K, 2)
    O = AlgebraOrders.order(A, R, basis(A))
    a = A(K[1 2; 0 1])
    x = @inferred O(a)
    @test typeof(x) === elem_type(O) === elem_type(typeof(O))
    @test parent_type(typeof(x)) === typeof(O)
    @test Hecke.is_exact_type(typeof(x))
    @test !Hecke.is_domain_type(typeof(x))
    @test parent(x) === O
    @test parent(AlgebraOrders.elem_in_lattice(x)) === AlgebraOrders.underlying_lattice(O)
    @test parent(Hecke.elem_in_module(x)) === Hecke.underlying_module(O)
    @test (@inferred Hecke.elem_in_algebra(x)) == a
    @test isdefined(AlgebraOrders.elem_in_lattice(x), :elem_in_algebra)
    @test Hecke.elem_in_algebra(x; copy = false) !== a
    @test Hecke.elem_in_algebra(x; copy = false) === Hecke.elem_in_algebra(x; copy = false)
    @test O(coordinates(x)) == x
    @test O(AlgebraOrders.elem_in_lattice(x)) == x
    @test O(Hecke.elem_in_module(x)) == x
    @test O(x) == x
    @test O(2) == O(R(2)) == O(2*one(A))
    @test Hecke.ambient_coordinates(x) == coefficients(a)
    @test x in O
    @test sprint(show, x) == sprint(show, a)

    v = coordinates(x)
    v[1] += one(parent(v[1]))
    @test coordinates(x) != v
    aa = Hecke.elem_in_algebra(x)
    Hecke.add!(aa, aa, one(A))
    @test Hecke.elem_in_algebra(x) == a
    Hecke.add!(a, a, one(A))
    @test Hecke.elem_in_algebra(x) != a
    y = deepcopy(x)
    @test y == x
    @test parent(y) === O
    @test AlgebraOrders.elem_in_lattice(y) !== AlgebraOrders.elem_in_lattice(x)
    Hecke.zero!(y)
    @test !iszero(x)
    @test hash(x) == hash(O(coordinates(x)))
    @test length(Set([x, O(x)])) == 1
    @test_throws ArgumentError O([one(R)])
    @test_throws ArgumentError O(inv(p)*one(A))

    OO = AlgebraOrders.order(AlgebraOrders.underlying_lattice(O))
    y = OO(x)
    @test y != x
    @test y in O
    @test_throws ArgumentError x + y
    @test_throws ArgumentError x - y
    @test_throws ArgumentError x*y
    @test O(y) == x

    L2 = lattice(A, R, basis(A))
    @test_throws ArgumentError AlgebraOrders.AssociativeAlgebraOrderElem(O, L2(one(A)))
    @test_throws ArgumentError O(Hecke.elem_in_module(L2(one(A))))
  end
end
