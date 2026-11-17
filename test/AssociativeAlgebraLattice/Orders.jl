@testset "Associative algebra lattice multiplier modules" begin
  F, t = rational_function_field(GF(7), "t")
  Rinf = localization(F, degree)
  for (R, K, p) in ((ZZ, QQ, QQ(2)),
                     (parent(numerator(t)), F, t),
                     (Rinf, F, inv(t)))
    @testset "Distinct left and right modules over $R" begin
      A = matrix_algebra(K, 2)
      E = Hecke.lattice(A, R, basis(A))
      D = A(K[p 0; 0 1])
      L = D*E
      Ml = @inferred Hecke._left_order_module(L)
      Mr = @inferred Hecke._right_order_module(L)
      left = Hecke.lattice(A, R, Ml)
      right = Hecke.lattice(A, R, Mr)
      @test Ml isa Hecke.EmbeddedModule && Mr isa Hecke.EmbeddedModule
      @test Hecke._left_order_module(L) === Ml
      @test Hecke._right_order_module(L) === Mr
      @test Ml !== Mr
      @test left == D*E*inv(D)
      @test right == E
      @test left != right
      @test left == colon(L, L)
      @test right == colon(L, L; side = :right)
      @test issubset(left*L, L)
      @test issubset(L*right, L)
      @test one(A) in Ml && one(A) in Mr
      @test left*left == left
      @test right*right == right
      for f in (Hecke._left_order_module, Hecke._right_order_module)
        M = f(L)
        @test Hecke.ring(M) === R
        @test Hecke.overring(M) === K
        @test Hecke.overstructure(M) === A
        @test Hecke.has_full_rank(M)
        @test f(inv(p^2)*L) == M
        @test f(Hecke.lattice(A, R, basis_matrix(L))) == M
        @test_throws ArgumentError f(Hecke.zero_lattice(A, R))
        @test_throws ArgumentError f(Hecke.lattice(A, R, basis(A)[1:2]))
      end

      if R === ZZ
        I = ideal(A, basis_matrix(L))
        @test left == Hecke.lattice(A, R, basis_matrix(left_order(I)))
        @test right == Hecke.lattice(A, R, basis_matrix(right_order(I)))
      end
    end

    @testset "Nonsemisimple algebra over $R" begin
      Kz, z = polynomial_ring(K, "z")
      A = associative_algebra(z^2)
      b = basis(A)
      L = Hecke.lattice(A, R, [b[1], p*b[2]])
      M = inv(p^2)*L
      @test colon(M, M) == L
      @test colon(M, M; side = :right) == L
      @test Hecke._left_order_module(M) == Hecke.underlying_module(L)
      @test Hecke._right_order_module(M) == Hecke.underlying_module(L)
    end

    @testset "Zero-dimensional algebra over $R" begin
      A = zero_algebra(K)
      L = Hecke.zero_lattice(A, R)
      for f in (Hecke._left_order_module, Hecke._right_order_module)
        M = @inferred f(L)
        @test iszero(Hecke.rank(M))
        @test Hecke.has_full_rank(M)
        @test M == Hecke.underlying_module(L)
        @test f(L) === M
      end
    end
  end

  K, = quadratic_field(5)
  O = maximal_order(K)
  A = matrix_algebra(K, 2)
  L = Hecke.lattice(A, O, identity_matrix(K, dim(A)))
  for f in (Hecke._left_order_module, Hecke._right_order_module)
    @test_throws ArgumentError f(L)
  end

  A = StructureConstantAlgebra(QQ, reshape(QQFieldElem[0], 1, 1, 1))
  L = Hecke.lattice(A, ZZ, basis(A))
  for f in (Hecke._left_order_module, Hecke._right_order_module)
    @test_throws ArgumentError f(L)
  end
end
