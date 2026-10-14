@testset "Order invariants" begin
  for (R, K, _) in algebra_order_test_rings()
    A = matrix_algebra(K, 2)
    O = AlgebraOrders.order(A, R, basis(A))
    a = A(K[1 2; 0 3])
    x = O(a)
    for f in (tr, trred, norm, normred)
      @test f(x) == R(f(a))
      @test parent(f(x)) === R
    end
    for f in (charpoly, minpoly, Hecke.reduced_charpoly)
      g = f(x)
      @test base_ring(parent(g)) === R
      @test collect(coefficients(change_base_ring(K, g))) == collect(coefficients(f(a)))
      S, = polynomial_ring(R, "z")
      @test parent(f(S, x)) === S
      @test f(S, x) == change_base_ring(R, f(a); parent = S)
      T, = polynomial_ring(K, "z")
      @test parent(f(T, x)) === T
      @test collect(coefficients(f(T, x))) == collect(coefficients(f(a)))
    end

    B = basis_matrix(O)
    for side in (:left, :right)
      C = representation_matrix(x, side)
      @test base_ring(C) === R
      @test change_base_ring(K, C)*B == B*representation_matrix(a, side)
    end
    @test_throws ArgumentError representation_matrix(x, :invalid)
    @test Hecke.trace_matrix(O) == change_base_ring(base_ring(Hecke.trace_matrix(O)), Hecke.trace_matrix(A))
    @test Hecke.trred_matrix(O) == change_base_ring(base_ring(Hecke.trred_matrix(O)), Hecke.trred_matrix(basis(A)))
    @test (@inferred Hecke.trred_matrix(O)) == Hecke.trred_matrix(O)
    @test (@inferred discriminant(O)) == discriminant(O)
    T = Hecke.trred_matrix(O)
    T[1, 1] += one(base_ring(T))
    @test Hecke.trred_matrix(O)[1, 1] != T[1, 1]
    @test discriminant(O) == R(-1)
  end

  A = quaternion_algebra(QQ, -1, -1)
  O = AlgebraOrders.order(A, ZZ, basis(A))
  OO = Hecke.order(A, basis(A); isbasis = true)
  @test Hecke.trred_matrix(O) == Hecke.trred_matrix(OO)
  @test discriminant(O) == discriminant(OO)
  x = O(basis(A)[2])
  @test normred(x) == ZZ(1)
  @test x*x == -one(O)
end
