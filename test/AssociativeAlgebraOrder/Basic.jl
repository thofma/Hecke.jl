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
    end
  end
end
