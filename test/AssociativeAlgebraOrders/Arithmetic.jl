@testset "Order arithmetic" begin
  for (R, K, p) in algebra_order_test_rings()
    A = matrix_algebra(K, 2)
    O = AlgebraOrders.order(A, R, basis(A))
    Hecke.AbstractAlgebra.ConformanceTests.test_NCRing_interface(O)

    x = O(A(K[1 1; 0 1]))
    y = O(A(K[1 0; 1 1]))
    @test divexact(x*y, x; side = :left) == y
    @test divexact(x*y, y; side = :right) == x
    @test_throws UndefKeywordError divexact(x, y)
    @test_throws ArgumentError divexact(x, y; side = :invalid)
    @test_throws ArgumentError divexact_right(one(O), O(p*one(A)))
  end
end

@testset "Division and zero-divisors" begin
  for (R, K, p) in algebra_order_test_rings()
    A = matrix_algebra(K, 2)
    L = lattice(A, R, basis(A))
    for D in (one(A), A(K[p 0; 0 1]))
      Di = inv(D)
      O = AlgebraOrders.order(D*L*Di)
      x = O(A(K[1 0; 0 0]))
      y = O(D*A(K[p 1; 0 0])*Di)
      yy = O(D*A(K[p 0; 1 0])*Di)
      for check in (true, false)
        q = divexact_left(x, y; check)
        @test y*q == x
        q = divexact_right(x, yy; check)
        @test q*yy == x
      end
      @test y*divexact_left(zero(O), y) == zero(O)
      @test divexact_right(zero(O), yy)*yy == zero(O)
      @test_throws ArgumentError divexact_left(one(O), y)
      @test_throws ArgumentError divexact_right(one(O), yy)
      @test_throws ArgumentError divexact_left(x, zero(O))
      @test_throws ArgumentError divexact_right(x, zero(O))
    end

    O = AlgebraOrders.order(Hecke.zero_lattice(zero_algebra(K), R))
    for side in (:left, :right)
      @test iszero(divexact(zero(O), zero(O); side))
    end
  end
end
