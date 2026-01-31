@testset "FiniteRings/Ideal" begin
  R, = finite_ring(GF(2)[small_group(8, 3)])
  @test_throws UndefKeywordError ideal(R, one(R))
  @test_throws ArgumentError ideal(R, one(R); side = :blub)
  I1 = ideal(R, one(R); side = :twosided)
  I2 = ideal(R, one(R); side = :left)
  I3 = ideal(R, one(R); side = :right)
  I4 = ideal(R, R([1, 1, 1, 1, 1, 1, 1, 1]); side = :left)
  I5 = Hecke.FiniteRings._ideal_zgens(R, [zero(R)]; side = :twosided)
  I6 = R*ZZ(2)
  I7 = ideal(R, R([1, 1, 0, 0, 0, 0, 0, 0]); side = :left)
  I8 = ideal(R, R([1, 1, 0, 0, 0, 0, 0, 0]); side = :right)
  @test is_zero(I5)
  @test is_zero(I6)
  @test Hecke.FiniteRings._test_ideal_sidedness(I4, :left)
  @test Hecke.FiniteRings._test_ideal_sidedness(I4, :right)
  @test Hecke.FiniteRings._test_ideal_sidedness(I4, :twosided)
  @test Hecke.FiniteRings._test_ideal_sidedness(I7, :left)
  @test !Hecke.FiniteRings._test_ideal_sidedness(I7, :right)
  @test !Hecke.FiniteRings._test_ideal_sidedness(I8, :left)
  @test Hecke.FiniteRings._test_ideal_sidedness(I8, :right)

  @test I1 == I2 == I3

  @test !is_zero(I1)
  @test is_zero(ideal(R, zero(R); side = :left))

  @test is_subset(ideal(R, zero(R); side = :left), I1)
  @test is_subset(I1, I2)
  @test is_subset(radical(R), I1)

  @test sprint(show, I1) isa String
  @test sprint(show, "text/plain", I1) isa String

  @test I1 * I1 == I1
  @test one(R) * R == R * one(R)
  @test left_ideal(R, one(R)) == left_ideal(R, [one(R)]) ==
        twosided_ideal(R, one(R)) == twosided_ideal(R, [one(R)]) == one(R) * R
  @test right_ideal(R, one(R)) == right_ideal(R, [one(R)]) == one(R) * R

  J = radical(R)
  Q, RtoJ = quo(R, J)
  @test order(Q) == 2
  @test length(additive_generators(J)) == 7

  QQ, = quo(J, J * J)

  # radical
  RR, = quo(R, one(R) * R)
  J = radical(RR)
  @test order(J) == 1
  @test is_zero(rand(J))
  J = radical(R)
  @test order(J) == 2^7
  @test rand(J) in J

  let
    R, f = finite_ring(matrix_algebra(GF(2), 2))
    a = R([1, 0, 0, 0])
    I = ideal(R, a; side = :left)
    @test_throws ArgumentError quo(R, I)
    S, = finite_ring(matrix_algebra(GF(2), 3))
    @test_throws ArgumentError quo(S, I)
  end

end
