@testset "Row" begin
  R = FlintZZ

  # Construction

  A = @inferred SRow{fmpz}()
  @test A isa SRow{fmpz}

  B = @inferred SRow(R)
  @test B isa SRow{fmpz}

  C = @inferred sparse_row(R)
  @test C isa SRow{fmpz}

  D = @inferred sparse_row(R, [(1, fmpz(1)), (2, fmpz(2))])
  @test D isa SRow{fmpz}

  E = @inferred sparse_row(R, [(1, 1), (2, 2)])
  @test E isa SRow{fmpz}

  F = @inferred sparse_row(R, [1, 2], [fmpz(1), fmpz(2)])
  @test F isa SRow{fmpz}

  # Equality

  @test @inferred ==(D, E)
  @test @inferred ==(E, F)

  # Hashing

  h = @inferred hash(D)
  @test h == hash(E)

  # Accesing elements

  @test fmpz(1) == @inferred D[1]
  @test fmpz(2) == @inferred D[2]
  @test fmpz(0) == @inferred D[3]
  @test fmpz(0) == @inferred D[1000]

  G = @inferred copy(F)
  @test G == F

  # Zero test

  @test @inferred iszero(A)
  @test !iszero(D)

  # Modular reduction

  for T in [Int, fmpz]
    G = sparse_row(FlintZZ, collect(1:5), map(fmpz, collect(1:5)))
    mod!(G, T(2))
    @test G == sparse_row(FlintZZ, [1, 3, 5], fmpz[1, 1, 1])

    G = sparse_row(FlintZZ, collect(1:5), map(fmpz, collect(1:5)))
    mod_sym!(G, T(3))
    @test G == sparse_row(FlintZZ, [1, 2, 4, 5], fmpz[1, -1, 1, -1])
  end

  # Change ring

  G = sparse_row(FlintZZ, collect(1:5), map(fmpz, collect(1:5)))

  f = x -> (x^2 - 4)
  H = @inferred map_entries(f, G)
  @test H == sparse_row(FlintZZ, [1, 3, 4, 5], fmpz[-3, 5, 12, 21])

  Rx, x = PolynomialRing(R, "x", cached = false)
  H = @inferred change_base_ring(Rx, G)
  @test H == sparse_row(Rx, collect(1:5), map(Rx, collect(1:5)))

  # Iterator interface

  @test [(i, fmpz(i)) for i in 1:5] == @inferred collect(G)

  # Dot product

  A = sparse_row(FlintZZ, [1, 3, 5], fmpz[1, 2, 3])
  B = sparse_row(FlintZZ, [3, 4, 6], fmpz[10, 1, 1])

  @test fmpz(20) == @inferred dot(A, B)

  # Inplace scaling

  A = sparse_row(FlintZZ, [1, 2, 4], fmpz[1, 2, 3])
  scale_row!(A, fmpz(2))
  @test A == sparse_row(FlintZZ, [1, 2, 4], fmpz[2, 4, 6])

  # Addition
  A = sparse_row(FlintZZ, [1, 2, 3, 5], fmpz[1, 2, 3, 5])
  B = sparse_row(FlintZZ, [2, 3, 4, 6], fmpz[-2, 4, 3, 1])
  @test sparse_row(FlintZZ, [1, 3, 4, 5, 6], fmpz[1, 7, 3, 5, 1]) == @inferred A + B

  # Subtraction

  A = sparse_row(FlintZZ, [1, 2, 3, 5], fmpz[1, 2, 3, 5])
  B = sparse_row(FlintZZ, [2, 3, 4, 6], fmpz[2, -4, -3, -1])
  @test sparse_row(FlintZZ, [1, 3, 4, 5, 6], fmpz[1, 7, 3, 5, 1]) == @inferred A - B

  # Scalar multiplication
  A = sparse_row(FlintZZ, [1, 2, 3, 5], fmpz[2, 4, 8, 6])
  for T in [Int, BigInt, fmpz]
    b = T(2)
    B = @inferred b * A
    @test B == map_entries(x -> T(2) * x, A)

    b = T(2)
    B = @inferred div(A, b)
    @test B == map_entries(x -> div(x, fmpz(2)), A)

    b = T(2)
    B = @inferred divexact(A, b)
    @test B == map_entries(x -> divexact(x, fmpz(2)), A)
  end

  # Elementary row operation
  A = sparse_row(FlintZZ, [1, 2, 3, 5], fmpz[1, 2, 3, 5])
  B = sparse_row(FlintZZ, [2, 3, 4, 6], fmpz[-1, 4, 3, 1])
  C = add_scaled_row(B, A, fmpz(2))

  @test C == sparse_row(FlintZZ, [1, 3, 4, 5, 6], fmpz[1, 11, 6, 5, 2])

  # Maximum

  A = sparse_row(FlintZZ, [1, 2, 3, 5], fmpz[-5, 2, 4, 10])
  @test 10 == @inferred maximum(A)

  # Minimum

  @test -5 == @inferred minimum(A)

  # Lifting

  S = ResidueRing(FlintZZ, 5)
  A = sparse_row(S, [1, 2, 3, 5], [1, 1, 2, 3])
  B = @inferred lift(A)
  @test sparse_row(R, [1, 2, 3, 5], [1, 1, 2, 3]) == B

  # 2-norm

  A = sparse_row(FlintZZ, [1, 2, 3, 5], fmpz[-5, 2, 4, 10])
  b = @inferred norm2(A)
  @test b == fmpz(25 + 4 + 16 + 100)

  S = ResidueRing(FlintZZ, 5)
  A = sparse_row(S, [1, 2, 3, 5], [1, 1, 2, 3])
  b = @inferred norm2(A)
  @test b == R(0)

  # Maximum/minimum

  A = sparse_row(FlintZZ, [1, 3, 4, 5], fmpz[-5, 2, -10, 1])
  @test maximum(abs, A) == fmpz(10)
  B = sparse_row(FlintQQ, [1, 2, 4, 5], map(fmpq, [1, 2, 9//4, 1]))
  @test maximum(B) == fmpq(9, 4)
  C = sparse_row(FlintZZ, [1, 2, 4, 5], fmpz[-10, 100, 1, 1])
  @test minimum(C) == fmpz(-10)


end
