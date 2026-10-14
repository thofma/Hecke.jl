@testset "Order construction and delegation" begin
  for (R, K, p) in algebra_order_test_rings()
    @testset "Orders over $R" begin
      A = matrix_algebra(K, 2)
      L = lattice(A, R, basis(A))
      @test @inferred Hecke.defines_order(L)
      O = @inferred AlgebraOrders.order(L)
      @test typeof(O) === AlgebraOrders.AssociativeAlgebraOrder{typeof(R), Hecke._ring_type(R), typeof(A)}
      @test Hecke.order_type(L) === typeof(O)
      @test base_ring_type(typeof(O)) === typeof(R)
      @test Hecke.algebra_type(typeof(O)) === typeof(A)
      @test algebra(O) === A
      @test base_ring(O) === R
      @test Hecke.rank(O) == Hecke.ambient_rank(O) == degree(O) == dim(A)
      @test Hecke.is_full_lattice(O) && Hecke.is_full_rank(O)
      @test characteristic(O) == characteristic(K)
      @test !is_commutative(O)
      @test !iszero(O)
      @test sprint(show, O) isa String

      B = basis_matrix(O)
      @test B == basis_matrix(L)
      @test basis_matrix(O; copy = false) === basis_matrix(L; copy = false)
      @test AlgebraOrders.order(A, R, B) == O
      @test AlgebraOrders.order(A, R, Hecke.underlying_module(L)) == O
      @test AlgebraOrders.order(A, R, basis(A)) == O
      @test AlgebraOrders.order(A, R, vcat(basis(A), basis(A))) == O
      @test AlgebraOrders.order(A, R, identity_matrix(K, dim(A)); is_basis_matrix = true) == O
      @test Hecke.element.(Hecke.pseudo_basis(O)) == Hecke.element.(Hecke.pseudo_basis(L))
      @test Hecke.fractional_ideal.(Hecke.pseudo_basis(O)) == Hecke.fractional_ideal.(Hecke.pseudo_basis(L))
      C = @inferred basis_matrix_inverse(O)
      @test C == identity_matrix(K, dim(A))
      C[1, 1] = K(99)
      @test basis_matrix_inverse(O)[1, 1] == one(K)
      @test basis_matrix_inverse(O; copy = false) === basis_matrix_inverse(Hecke.underlying_module(O))

      b = @inferred basis(O)
      @test all(x -> parent(x) === O, b)
      @test Hecke.elem_in_algebra.(b) == basis(L)
      @test basis(O; copy = false) === basis(O; copy = false)
      @test basis(O; copy = false) !== b
      @test basis(O; copy = false)[1] === b[1]
      b[1] = zero(O)
      @test !iszero(basis(O; copy = false)[1])
      @test basis(O, A) == Hecke.basis_alg(O) == basis(L)
      @test Hecke.module_index(O, O) == ideal(R, one(R))
      U = identity_matrix(K, dim(A))
      U[1, 2] = one(K)
      OO = AlgebraOrders.order(A, R, U; is_basis_matrix = true)
      @test OO == O
      @test hash(OO) == hash(O)
      @test length(Set([OO, O])) == 1
      @test_throws ArgumentError basis(O, matrix_algebra(K, 2))

      D = A(K[p 0; 0 1])
      OO = AlgebraOrders.order(D*L*inv(D))
      N = intersect(O, OO)
      @test issubset(N, O) && issubset(N, OO)
      @test AlgebraOrders.underlying_lattice(N) == intersect(L, AlgebraOrders.underlying_lattice(OO))
      @test Hecke.defines_order(AlgebraOrders.underlying_lattice(N))
      @test one(A) in O
      @test Hecke.is_compatible(O, OO)
      @test O == AlgebraOrders.order(L; check = false)

      for M in (Hecke.zero_lattice(A, R), lattice(A, R, basis(A)[1:2]), p*L, inv(p)*L)
        @test !Hecke.defines_order(M)
        @test_throws ArgumentError AlgebraOrders.order(M)
      end

      A2 = matrix_algebra(K, 2)
      OO = AlgebraOrders.order(A2, R, basis(A2))
      @test !Hecke.is_compatible(O, OO)
      @test O != OO
      @test_throws ArgumentError one(A2) in O
      @test_throws ArgumentError issubset(O, OO)
      @test_throws ArgumentError intersect(O, OO)
    end
  end

  A = StructureConstantAlgebra(QQ, reshape(QQFieldElem[0], 1, 1, 1))
  @test !Hecke.defines_order(lattice(A, ZZ, basis(A)))

  A = matrix_algebra(QQ, 2)
  O = AlgebraOrders.order(A, ZZ, basis(A))
  OO = Hecke.order(A, ZZ, identity_matrix(QQ, dim(A)))
  @test OO isa Hecke.AlgAssAbsOrd
  @test !(O isa Hecke.AlgAssAbsOrd)
  @test basis_matrix(OO) == basis_matrix(O)
  @test first(Hecke.defines_order(A, ZZ, basis_matrix(O)))
end

@testset "Zero-dimensional orders" begin
  for (R, K, _) in algebra_order_test_rings()
    A = zero_algebra(K)
    L = Hecke.zero_lattice(A, R)
    @test Hecke.defines_order(L)
    O = AlgebraOrders.order(L)
    @test iszero(O)
    @test degree(O) == 0
    @test iszero(O()) && isone(O())
    @test one(O) == zero(O)
    @test isempty(coordinates(O()))
    @test one(O)*zero(O) == zero(O)
    @test is_unit(zero(O))
    @test inv(zero(O)) == zero(O)
  end
end
