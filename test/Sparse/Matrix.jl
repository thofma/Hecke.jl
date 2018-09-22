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
  @test cols(Csparse) == 0

  A = fmpz[1 2; 0 0; 3 4]

  Dsparse = sparse_matrix(A)
  @test base_ring(Dsparse) == FlintZZ
  @test rows(Dsparse) == 3
  @test cols(Dsparse) == 2
  @test nnz(Dsparse) == 4

  Esparse = sparse_matrix(FlintZZ)
  @test base_ring(Dsparse) == FlintZZ
  @test rows(Dsparse) == 0
  @test cols(Dsparse) == 0
  @test nnz(Dsparse) == 0

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

  # Entry access

  A = identity_matrix(FlintZZ, 3)
  Asparse = sparse_matrix(A)
  for i in 1:3
    for j in 1:3
      b = @inferred A[i, j]
      if i == j
        @test b == one(FlintZZ)
      else
        @test iszero(b)
      end
    end
  end

  # Row access

  D = sparse_matrix(FlintZZ, [1 5 3; 0 0 0; 0 1 0])
  @test sparse_row(FlintZZ, [1, 2, 3], fmpz[1, 5, 3]) == @inferred D[1]
  @test sparse_row(FlintZZ) == @infererd D[2]
  @test sparse_row(FlintZZ, [2], fmpz[1]) == @inferred D[3]

  D[1] = sparse_row(FlintZZ, [1], fmpz[1])
  D[2] = sparse_row(FlintZZ, [2], fmpz[1])
  D[3] = sparse_row(FlintZZ, [3], fmpz[1])
  @test D == sparse_matrix(identity_matrix(FlintZZ, 3))

  # Modular reduction

  D = sparse_matrix(FlintZZ, [1 5 3; 5 5 5; -4 1 1])
  D = mod_sym!(D)
  @test rows(D) == 3
  @test cols(D) == 3
  @test D.rows[1] == sparse_row(FlintZZ, [1, 3], fmpz[1, -2])
  @test D.rows[2] == sparse_row(FlintZZ)
  @test D.rows[3] == sparse_Row(FlintZZ, [1, 2, 3], fmpz[1, 1, 1])

  # Random row

  D = sparse_matrix(FlintZZ, [1 5 3; 5 5 5; -4 1 1])
  r = @inferred randomrow(D)
  @test any(isequal(r), D.rows)

  # Change of ring

  R = ResidueRing(FlintZZ, 5)
  D = sparse_matrix(FlintZZ, [1 5 3; 5 5 5; -4 1 1])
  D_R = @inferred change_ring(D, R)
  @test D_R = sparse_matrix(R, map(R, [1 0 3; 0 0 0; 1 1 1]))

  # Transpose
  D = sparse_matrix(FlintZZ, [1 5 3; 0 0 0; 0 1 0])
  Dt = @inferred transpose(D)
  @test Dt == sparse_matrix(FlintZZ, [1 0 0; 5 0 0; 3 0 0])
  @test Dt == D'

  # Iterator interface

  D = sparse_matrix(FlintZZ, [1 5 3; 0 0 0; 0 1 0])
  @test D.rows == [ r for r in D]
  @test D.rows == @inferred collect(D)

end

