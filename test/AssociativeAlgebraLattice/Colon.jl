@testset "Associative algebra lattice colons" begin
  F, t = rational_function_field(GF(7), "t")
  Rinf = localization(F, degree)
  for (R, K, p) in ((ZZ, QQ, QQ(2)),
                     (parent(numerator(t)), F, t),
                     (Rinf, F, inv(t)))
    @testset "Scalar lattices over $R" begin
      for A in (matrix_algebra(K, 1), group_algebra(K, small_group(2, 1)))
        E = Hecke.lattice(A, R, basis(A))
        L, M = inv(p)*E, p^2*E
        for side in (:left, :right)
          C = @inferred colon(L, M; side)
          @test C == inv(p^3)*E
          @test algebra(C) === A
          @test base_ring(C) === R
          @test Hecke.is_full_lattice(C)
          @test Hecke.overstructure(Hecke.underlying_module(C)) === A
          @test basis_matrix(C)*Hecke.basis_matrix_inverse(Hecke.underlying_module(C)) ==
                identity_matrix(K, dim(A))
          @test issubset(side === :left ? C*M : M*C, L)
          @test !(inv(p^4)*one(A) in C)
        end
        @test colon(L, M) == colon(L, M; side = :left)
      end
    end

    @testset "Noncommutative lattices over $R" begin
      A = matrix_algebra(K, 2)
      E = Hecke.lattice(A, R, basis(A))
      D = A(K[p 1; 0 1])
      T = A(K[1 0; 1 p])
      L, M = inv(p)*D*E, p*T*E
      @test colon(L, M) == inv(p^2)*D*E*inv(T)
      for side in (:left, :right)
        C = colon(L, M; side)
        @test issubset(side === :left ? C*M : M*C, L)
        for b in basis(A), s in (zero(K), one(K), inv(p), inv(p^2), p)
          x = s*b
          products = side === :left ? (x*m for m in basis(M)) : (m*x for m in basis(M))
          @test (x in C) == all(y -> y in L, products)
        end
      end
      U = identity_matrix(K, dim(A))
      U[1, 2] = one(K)
      Lequal = Hecke.lattice(A, R, U*basis_matrix(L); is_basis_matrix = true)
      Mequal = Hecke.lattice(A, R, U*basis_matrix(M); is_basis_matrix = true)
      @test L == Lequal && M == Mequal
      @test colon(L, M) == colon(Lequal, Mequal)
      @test colon(L, M; side = :right) == colon(Lequal, Mequal; side = :right)

      if R === ZZ
        I = ideal(A, basis_matrix(L))
        J = ideal(A, basis_matrix(M))
        @test colon(L, M) == Hecke.lattice(A, R, basis_matrix(colon(I, J)))
        @test colon(L, M; side = :right) == Hecke.lattice(A, R, basis_matrix(divexact_left(I, J)))
      end
    end

    @testset "Invalid inputs over $R" begin
      A = matrix_algebra(K, 2)
      E = Hecke.lattice(A, R, basis(A))
      Z = Hecke.zero_lattice(A, R)
      N = Hecke.lattice(A, R, basis(A)[1:2])
      for (L, M) in ((Z, E), (E, Z), (N, E), (E, N))
        @test_throws ArgumentError colon(L, M)
      end
      @test_throws ArgumentError colon(E, E; side = :invalid)
      Aother = matrix_algebra(K, 2)
      Eother = Hecke.lattice(Aother, R, basis(Aother))
      @test_throws ArgumentError colon(E, Eother)
      @test_throws ArgumentError colon(Eother, E)
    end

    @testset "Zero-dimensional algebra over $R" begin
      A = zero_algebra(K)
      L = Hecke.zero_lattice(A, R)
      @test Hecke.is_full_lattice(L)
      @test colon(L, L) == L
      @test colon(L, L; side = :right) == L
    end
  end

  A = matrix_algebra(F, 2)
  L = Hecke.lattice(A, parent(numerator(t)), basis(A))
  M = Hecke.lattice(A, Rinf, basis(A))
  @test_throws ArgumentError colon(L, M)
  @test_throws ArgumentError colon(M, L)

  K, = quadratic_field(5)
  O = maximal_order(K)
  A = matrix_algebra(K, 2)
  L = Hecke.lattice(A, O, identity_matrix(K, dim(A)))
  @test_throws ArgumentError colon(L, L)

  A = StructureConstantAlgebra(QQ, reshape(QQFieldElem[0], 1, 1, 1))
  L = Hecke.lattice(A, ZZ, basis(A))
  @test !Hecke.has_one(A)
  @test_throws ArgumentError colon(L, L)
end
