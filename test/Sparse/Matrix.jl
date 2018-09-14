@testset "Matrix" begin
  R = FlintZZ
  M = SMatSpace(R, 3, 3)

  @test R == @inferred base_ring(M)
  
  A = identity_matrix(FlintZZ, 3)
  Asparse = sparse_matrix(A)

  @test R == @inferred base_ring(Asparse)
  @test M == @inferred parent(Asparse)

  @test 3 == @inferred rows(Asparse)
  @test 3 == @inferred cols(Asparse)
  @test 3 == @inferred nnz(Asparse)
  @test (3, 3) == @inferred size(Asparse)

  B = identity_matrix(FlintZZ, 3)
  Bsparse = sparse_matrix(B)

  Csparse = sparse_matrix(FlintZZ)
  @test base_ring(Csparse) == FlintZZ
  @test rows(Csparse) == 0
  @test rows(Csparse) == 0

  # Hash

  @test hash(Asparse) == @inferred hash(Bsparse)

  # Equality

  @test @inferred ==(Asparse, Bsparse)

  B = zero_matrix(FlintZZ, 2, 3)
  Bsparse = sparse_matrix(B)
  @test rows(Bsparse) == 2
  @test cols(Bsparse) == 3
  @test nnz(Bsparse) == 0
  @test Asparse !== Bsparse

  # Sparsity

  @test isapprox(2/3, @inferred sparsity(Asparse))

  # Density

  @test isapprox(1/3, @inferred density(Asparse))

  # Copy

  Csparse = @inferred copy(Asparse)

  @test Csparse == Asparse
end

