@testset "Ring conformance tests" begin
  R, = finite_ring(matrix_algebra(GF(2), 1))
  AbstractAlgebra.ConformanceTests.test_Ring_interface(R)

  R, = finite_ring(matrix_algebra(GF(3), 2))
  AbstractAlgebra.ConformanceTests.test_NCRing_interface(R)
end

@testset "Rings" begin
  R = finite_ring([1], [zero_matrix(ZZ, 1, 1)])

  @test elementary_divisors(R) == []
  @test order(R) == 1
  @test characteristic(R) == 1
  @test is_finite(R) == 1
  @test is_zero(R)
  @test is_commutative(R)
  @test sprint(show, R) isa String
  @test sprint(show, "text/plain", R) isa String

  S, = finite_ring(matrix_algebra(GF(3), 2))
  @test elementary_divisors(S) == [3, 3, 3, 3]
  @test order(S) == 3^4
  @test characteristic(S) == 3
  @test is_finite(S)
  @test !is_zero(S)
  @test !is_commutative(S)
  @test sprint(show, S) isa String
  @test sprint(show, "text/plain", S) isa String

  # a non-ring
  @test_throws ArgumentError finite_ring([2, 2], [zero_matrix(ZZ, 1, 1)])
  @test_throws ArgumentError finite_ring([2, 2], [zero_matrix(ZZ, 2, 2)])
  @test_throws ArgumentError finite_ring([2, 2], [zero_matrix(ZZ, 1, 1), identity_matrix(ZZ, 2)])

  # more constructions
  Q = quaternion_algebra(GF(3), -1, -1)
  R, = finite_ring(Q)
  @test elementary_divisors(R) == [3, 3, 3, 3]

  R, = finite_ring(matrix_algebra(GF(3), 1))
  S, = finite_ring(matrix_ring(R, 1))

end
