using Hecke.SparseArrays

@testset "Matrix" begin
  R = FlintZZ
  M = SMatSpace(R, 3, 3)

  @test R == @inferred base_ring(M)

  A = identity_matrix(FlintZZ, 3)
  Asparse = sparse_matrix(A)

  @test R == @inferred base_ring(Asparse)
  @test M == @inferred parent(Asparse)

  @test 3 == @inferred nrows(Asparse)
  @test 3 == @inferred ncols(Asparse)
  @test 3 == @inferred nnz(Asparse)
  @test (3, 3) == @inferred size(Asparse)
  @test 3 == @inferred size(Asparse, 1)
  @test 3 == @inferred size(Asparse, 2)
  @test 1 == @inferred size(Asparse, 3)
  B = identity_matrix(FlintZZ, 3)
  Bsparse = sparse_matrix(B)

  Csparse = sparse_matrix(FlintZZ)
  @test base_ring(Csparse) == FlintZZ
  @test nrows(Csparse) == 0
  @test ncols(Csparse) == 0

  A = ZZRingElem[1 2; 0 0; 3 4]

  Dsparse = sparse_matrix(A)
  @test base_ring(Dsparse) == FlintZZ
  @test nrows(Dsparse) == 3
  @test ncols(Dsparse) == 2
  @test nnz(Dsparse) == 4

  Esparse = sparse_matrix(FlintZZ)
  @test base_ring(Esparse) == FlintZZ
  @test nrows(Esparse) == 0
  @test ncols(Esparse) == 0
  @test nnz(Esparse) == 0

  # Hash

  @test hash(Asparse) == @inferred hash(Bsparse)

  # Equality

  @test @inferred ==(sparse_matrix(FlintZZ, [0 0 0; 1 1 1]), sparse_matrix(FlintZZ, [0 0 0; 1 1 1]))

  B = zero_matrix(FlintZZ, 2, 3)
  Bsparse = sparse_matrix(B)
  @test nrows(Bsparse) == 2
  @test ncols(Bsparse) == 3
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
  @test sparse_row(FlintZZ, [1, 2, 3], ZZRingElem[1, 5, 3]) == @inferred D[1]
  @test sparse_row(FlintZZ) == @inferred D[2]
  @test sparse_row(FlintZZ, [2], ZZRingElem[1]) == @inferred D[3]

  D[1] = sparse_row(FlintZZ, [1], ZZRingElem[1])
  D[2] = sparse_row(FlintZZ, [2], ZZRingElem[1])
  D[3] = sparse_row(FlintZZ, [3], ZZRingElem[1])
  @test D == sparse_matrix(identity_matrix(FlintZZ, 3))

  # Modular reduction

  D = sparse_matrix(FlintZZ, [1 5 3; 5 5 5; -4 1 1])
  D = mod_sym!(D, ZZRingElem(5))
  @test nrows(D) == 3
  @test ncols(D) == 3
  @test D.rows[1] == sparse_row(FlintZZ, [1, 3], ZZRingElem[1, -2])
  @test D.rows[2] == sparse_row(FlintZZ)
  @test D.rows[3] == sparse_row(FlintZZ, [1, 2, 3], ZZRingElem[1, 1, 1])

  # Random row

  D = sparse_matrix(FlintZZ, [1 5 3; 5 5 5; -4 1 1])
  r = @inferred rand_row(D)
  @test any(isequal(r), D.rows)

  # Change of ring

  R = residue_ring(FlintZZ, 5)[1]
  D = sparse_matrix(FlintZZ, [1 5 3; 5 5 5; -4 1 1])
  D_R = @inferred change_base_ring(R, D)
  @test D_R == sparse_matrix(R, map(R, [1 0 3; 0 0 0; 1 1 1]))

  # Transpose

  D = sparse_matrix(FlintZZ, [1 5 3; 0 0 0; 0 1 0])
  Dt = @inferred transpose(D)
  @test Dt == sparse_matrix(FlintZZ, [1 0 0; 5 0 1; 3 0 0])
  @test Dt == transpose(D)

  # Iterator interface

  D = sparse_matrix(FlintZZ, [1 5 3; 0 0 0; 0 1 0])
  @test D.rows == [ r for r in D]
  @test D.rows == @inferred collect(D)

  # Multiplications

  D = sparse_matrix(FlintZZ, [1 5 3; 0 0 0; 0 1 0])
  v = ZZRingElem[1, 2, 3]
  w = @inferred D * v
  @test w == ZZRingElem[20, 0, 2]
  w = @inferred D * view(v, 1:3)
  @test w == ZZRingElem[20, 0, 2]

  v = ZZRingElem[1 2 3; 0 0 4; 0 0 0]
  w = @inferred D * v
  @test w == ZZRingElem[1 2 23; 0 0 0; 0 0 4]
  v = ZZRingElem[1 1 1; 1 2 3; 0 0 4; 0 0 0]
  w = @inferred D * view(v, 2:4, :)
  @test w == ZZRingElem[1 2 23; 0 0 0; 0 0 4]

  v = matrix(FlintZZ, ZZRingElem[1 2 3; 0 0 4; 0 0 0])
  w = @inferred D * v
  @test w == matrix(FlintZZ, ZZRingElem[1 2 23; 0 0 0; 0 0 4])

  v = sparse_row(FlintZZ, [2], ZZRingElem[1])
  w = @inferred v * D
  @test w == sparse_row(FlintZZ)

  # Addition

  D = sparse_matrix(FlintZZ, [1 5 3; 0 0 0; 0 1 0])
  E = sparse_matrix(FlintZZ, [0 0 0; 1 0 1; 0 0 1])
  DplusE = @inferred D + E
  @test DplusE == sparse_matrix(FlintZZ, [1 5 3; 1 0 1; 0 1 1])
  @test D + E == E + D

  # Subtraction

  D = sparse_matrix(FlintZZ, [1 5 3; 0 1 0; 0 1 0])
  E = sparse_matrix(FlintZZ, [1 5 0; 1 0 1; 0 0 0])
  DminusE = @inferred D - E
  @test DminusE == sparse_matrix(FlintZZ, [0 0 3; -1 1 -1; 0 1 0])

  minusD = @inferred -D
  @test minusD == sparse_matrix(FlintZZ, [-1 -5 -3; 0 -1 0; 0 -1 0])

  # Scalar multiplication

  D = sparse_matrix(FlintZZ, [1 5 3; 0 0 0; 0 1 0])
  E = @inferred 0 * D
  @test E == zero_matrix(SMat, FlintZZ, 3)
  @test E == sparse_matrix(FlintZZ, 3, 3)
  E = @inferred D * 0
  @test E == zero_matrix(SMat, FlintZZ, 3)
  @test E == sparse_matrix(FlintZZ, 3, 3)
  E = @inferred BigInt(2) * D
  @test E == sparse_matrix(FlintZZ, [2 10 6; 0 0 0; 0 2 0])
  E = @inferred D * BigInt(2)
  @test E == sparse_matrix(FlintZZ, [2 10 6; 0 0 0; 0 2 0])
  E = @inferred ZZRingElem(2) * D
  @test E == sparse_matrix(FlintZZ, [2 10 6; 0 0 0; 0 2 0])
  E = @inferred D * ZZRingElem(2)
  @test E == sparse_matrix(FlintZZ, [2 10 6; 0 0 0; 0 2 0])

  R = residue_ring(FlintZZ, 6)[1]
  D = sparse_matrix(R, [1 2 2; 0 0 1; 2 2 2])
  E = @inferred ZZRingElem(3) * D
  @test E == sparse_matrix(R, [3 0 0; 0 0 3; 0 0 0])
  E = @inferred D * ZZRingElem(3)
  @test E == sparse_matrix(R, [3 0 0; 0 0 3; 0 0 0])
  E = @inferred Int(3) * D
  @test E == sparse_matrix(R, [3 0 0; 0 0 3; 0 0 0])
  E = @inferred D * Int(3)
  @test E == sparse_matrix(R, [3 0 0; 0 0 3; 0 0 0])
  E = @inferred R(3) * D
  @test E == sparse_matrix(R, [3 0 0; 0 0 3; 0 0 0])
  E = @inferred D * R(3)
  @test E == sparse_matrix(R, [3 0 0; 0 0 3; 0 0 0])

  # Dot product

  D = sparse_matrix(ZZ, [4 -2; -2 2])
  E = sparse_matrix(ZZ, [3 0 0; 0 3 0])

  @test dot(sparse_row(ZZ, [1], [1]), D, sparse_row(ZZ, [1], [1])) == 4
  @test dot(sparse_row(ZZ, [1, 2], [1, 1]), D, sparse_row(ZZ, [1, 2], [1, 2])) == 2
  @test dot(sparse_row(ZZ, [1], [1]), D, sparse_row(ZZ, [2], [1])) == -2

  @test dot(sparse_row(ZZ, [1, 4], [1, 2]), D, sparse_row(ZZ, [2], [1])) == -2
  @test dot(sparse_row(ZZ, [1, 4], [1, 2]), E, sparse_row(ZZ, [2], [1])) == 0
  @test dot(sparse_row(ZZ, [1, 2], [1, 2]), E, sparse_row(ZZ, [2], [1])) == 6

  @test dot(ZZRingElem[1, 0], D, ZZRingElem[1, 0]) == 4
  @test dot(ZZRingElem[1, 1], D, ZZRingElem[1, 2]) == 2
  @test dot(ZZRingElem[1, 0], D, ZZRingElem[0, 1]) == -2
  @test dot(ZZRingElem[1, 0], E, ZZRingElem[0, 1, 2]) == 0
  @test dot(ZZRingElem[0, 1], E, ZZRingElem[0, 1, 2]) == 3

  @test dot(ZZ[1 0], D, ZZ[1 0]) == 4
  @test dot(ZZ[1; 1], D, ZZ[1 2]) == 2
  @test dot(ZZ[1 0], D, ZZ[0; 1]) == -2
  @test dot(ZZ[1 0], E, ZZ[0 1 2]) == 0
  @test dot(ZZ[0 1], E, ZZ[0 1 2]) == 3

  @test_throws ArgumentError dot(ZZRingElem[1], D, ZZRingElem[0, 1])
  @test_throws ArgumentError dot(ZZRingElem[1, 0], D, ZZRingElem[0])
  @test_throws ArgumentError dot(ZZRingElem[1, 0, 2], E, ZZRingElem[0, 1])

  @test_throws ArgumentError dot(ZZ[1 0 0], D, ZZ[1 0])
  @test_throws ArgumentError dot(ZZ[0 1 2], E, ZZ[0 1])
  @test_throws ArgumentError dot(ZZ[1 0; 0 0], D, ZZ[1 0 0 0])

  # Submatrix

  D = sparse_matrix(FlintZZ, [1 5 3; 0 0 0; 0 1 0])
  E = @inferred sub(D, 2:3, 2:3)
  @test base_ring(E) == FlintZZ
  @test nrows(E) == 2
  @test ncols(E) == 2
  @test E == sparse_matrix(FlintZZ, [0 0; 1 0])

  # Vertical concatenation
  D = sparse_matrix(FlintZZ, [1 5 3; 0 0 0; 0 1 0])
  E = @inferred vcat(D, D)
  @test base_ring(E) == FlintZZ
  @test nrows(E) == 6
  @test ncols(E) == 3
  @test E == sparse_matrix(FlintZZ, [1 5 3; 0 0 0; 0 1 0;
                                     1 5 3; 0 0 0; 0 1 0])
  # Horizontal concatenation

  D = sparse_matrix(FlintZZ, [1 5 3; 0 0 0; 0 1 0])
  E = @inferred hcat(D, D)
  @test base_ring(E) == FlintZZ
  @test nrows(E) == 3
  @test ncols(E) == 6
  @test E == sparse_matrix(FlintZZ, [1 5 3 1 5 3; 0 0 0 0 0 0; 0 1 0 0 1 0])

  # Hadamard bound

  D = sparse_matrix(FlintZZ, [1 5 3; 0 1 0; 0 1 0])
  h = @inferred hadamard_bound2(D)
  @test h == ZZRingElem(35)

  # Maximum/minimum
  D = sparse_matrix(FlintZZ, [1 5 3; 0 -10 0; 0 1 0])
  b = @inferred maximum(abs, D)
  @test b == ZZRingElem(10)
  D = sparse_matrix(FlintQQ, [1 2 QQFieldElem(9, 4); 0 -10 0; 0 1 0])
  b = @inferred maximum(D)
  @test b == QQFieldElem(9, 4)
  b = @inferred minimum(D)
  @test b == QQFieldElem(-10)

  D = sparse_matrix(FlintZZ, [0 2 0; 0 0 1; 0 0 0])
  @test @inferred is_upper_triangular(D)
  D = sparse_matrix(FlintZZ, [0 0 2; 0 0 1; 0 0 0])
  @test !is_upper_triangular(D)
  D = sparse_matrix(FlintZZ, [0 0 0; 0 0 0; 0 0 0])
  @test @inferred is_upper_triangular(D)

  # Zero and identity matrix

  D = @inferred identity_matrix(SMat, FlintZZ, 3)
  @test D == sparse_matrix(FlintZZ, [1 0 0; 0 1 0; 0 0 1]);
  D = @inferred zero_matrix(SMat, FlintZZ, 3)
  @test D == sparse_matrix(FlintZZ, [0 0 0; 0 0 0; 0 0 0]);
  @test D == sparse_matrix(FlintZZ, 3, 3)
  D = @inferred zero_matrix(SMat, FlintZZ, 4, 3)
  @test D == sparse_matrix(FlintZZ, [0 0 0; 0 0 0; 0 0 0; 0 0 0]);
  @test D == sparse_matrix(FlintZZ, 4, 3)

  # Block diag matrix

  D1 = sparse_matrix(FlintZZ, [1 5; 0 1])
  D2 = sparse_matrix(FlintZZ, [2 3 8; 4 0 0])
  D = @inferred block_diagonal_matrix([D1, D2])
  @test D == sparse_matrix(FlintZZ, [1 5 0 0 0; 0 1 0 0 0; 0 0 2 3 8; 0 0 4 0 0])
  D = @inferred diagonal_matrix([D1, D2])
  @test D == sparse_matrix(FlintZZ, [1 5 0 0 0; 0 1 0 0 0; 0 0 2 3 8; 0 0 4 0 0])
  D = @inferred diagonal_matrix(D1, D2)
  @test D == sparse_matrix(FlintZZ, [1 5 0 0 0; 0 1 0 0 0; 0 0 2 3 8; 0 0 4 0 0])

  # Concatenation syntax

  D = sparse_matrix(FlintZZ, [1 5 3; 0 -10 0; 0 1 0])
  E = [D D D]
  @test E == hcat(hcat(D, D), D)
  E = [D; D; D]
  @test E == vcat(vcat(D, D), D)

  # Is one

  D = sparse_matrix(FlintZZ, [1 5 3; 0 -10 0; 0 1 0])
  b = @inferred isone(D)
  @test !b
  D = sparse_matrix(FlintZZ, [1 0 0; 0 1 0; 0 0 1])
  b = @inferred isone(D)
  @test b
  D = sparse_matrix(FlintZZ, [1 0 0; 0 0 1; 0 1 0])
  b = @inferred isone(D)
  @test !b
  D = sparse_matrix(FlintZZ, [1 0 0; 0 1 0; 0 0 1; 0 0 0])
  b = @inferred isone(D)
  @test !b

  D = sparse_matrix(FlintZZ, [0 0 0; 0 0 0])
  b = @inferred iszero(D)
  @test b
  D = sparse_matrix(FlintZZ, [0 0 0; 0 0 1])
  b = @inferred iszero(D)
  @test !b
  D = sparse_matrix(FlintZZ, [0 0 1; 0 0 0])
  b = @inferred iszero(D)
  @test !b

  # Conversion to julia types
  D = sparse_matrix(FlintZZ, [1 5 3; 0 -10 0; 0 1 0])
  @test Matrix(D) == ZZRingElem[1 5 3; 0 -10 0; 0 1 0]
  @test Array(D) == ZZRingElem[1 5 3; 0 -10 0; 0 1 0]
  E = SparseArrays.sparse(D)
  @test Matrix(E) == ZZRingElem[1 5 3; 0 -10 0; 0 1 0]
  @test Array(E) == ZZRingElem[1 5 3; 0 -10 0; 0 1 0]

  # kronecker_product
  D1 = sparse_matrix(FlintZZ, [12 403 -23; 0 0 122; -1 2 99])
  D2 = sparse_matrix(FlintZZ, [81 0 2; 31 0 -5])
  E = @inferred kronecker_product(D1, D2)
  @test E == sparse_matrix(kronecker_product(matrix(D1), matrix(D2)))
end

@testset "Oscar #2128" begin
  S0 = sparse_matrix(QQ, [2 0; 0 0])
  @test size(5*S0) == (2, 2)
  @test 5*S0 == sparse_matrix(QQ, [10 0; 0 0])
end

@testset "Oscar #2135" begin
  S0 = sparse_matrix(ZZ,[1 0; 0 1])
  S1 = sparse_matrix(ZZ,[-1 0; 0 -1])
  @test S0 + S1 == sparse_matrix(ZZ, 2, 2)
end

@testset "Hecke #1227" begin
  A = sparse_matrix(FlintZZ, [2 0; 0 0])
  @test kronecker_product(A, A) == sparse_matrix(FlintZZ, [4 0 0 0; 0 0 0 0; 0 0 0 0; 0 0 0 0])
end

@testset "Hecke #1261" begin
  D1 = sparse_matrix(FlintZZ, [3 0 4 0; 0 3 0 4; 0 0 2 0; 0 0 0 2])
  D2 = identity_matrix(SMat, FlintZZ, 2)
  E = kronecker_product(D1, D2)
  @test E == sparse_matrix(kronecker_product(matrix(D1), matrix(D2)))
end
