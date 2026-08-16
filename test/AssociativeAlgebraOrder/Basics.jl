@testset "AssociativeAlgebraOrder" begin
  # creation

  let
    F, = rational_function_field(GF(13))
    FR = F.fraction_field.base_ring
    FRR = localization(F, degree)
    examples = [(QQ, ZZ), (F, FR), (F, FRR)]
    for (K, R) in examples
      # Test with input being a matrix
      A = group_algebra(K, small_group(2, 1))
      O = Hecke.new_order(A, R, basis(A); is_basis = true)
      @test algebra(O) === A
      @test base_ring(O) === R
      @test_throws ArgumentError Hecke.new_order(A, R, basis(A)[1:1]; is_basis = true)
      @test_throws ArgumentError Hecke.new_order(R, basis(A)[1:0]; is_basis = true)

      O = Hecke.new_order(A, R, identity_matrix(K, 2); is_basis = true)
      @test algebra(O) === A
      @test base_ring(O) === R
      @test_throws ArgumentError Hecke.new_order(A, R, zero_matrix(K, 2, 2); is_basis = true)
      @test_throws ArgumentError Hecke.new_order(A, R, vcat(identity_matrix(K, 2), zero_matrix(K, 2, 2)); is_basis = true)

      M = Hecke._closure(A, R, basis(A))
      @test basis_matrix(M) == identity_matrix(K, 2)
    end
  end

  let # Dedekind interface
    K, = rationals_as_number_field()
    OK = maximal_order(K)
    A = matrix_algebra(K, 2)
    M = Hecke._closure(A, OK, 2 .* basis(A))
    @test nrows(matrix(basis_matrix(M))) == dim(A)
  end

  let # PID interface, non-commutative case
    A = matrix_algebra(QQ, 2)
    M = Hecke._closure(A, ZZ, basis(A))
    @test basis_matrix(M) == identity_matrix(QQ, dim(A))
    @test_throws ErrorException Hecke._closure(A, ZZ, [QQ(1//2)*basis(A)[1]])
  end

  let
    K = QQ
    R = ZZ
    A = group_algebra(K, small_group(2, 1))
    O = Hecke.new_order(A, R, basis(A); is_basis = true)
    OO = Hecke.new_order(A, R, 2*basis(A))
    @test @inferred issubset(OO, O)
    @test @inferred !issubset(O, OO)
    @test @inferred index(OO, O) == 2
    @test_throws ArgumentError index(O, OO)
  end
end
