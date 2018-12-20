@testset "Change of ring" begin

  # Restrict from number field to Q
  Qx, x = FlintQQ["x"]
  f = x^3 - 2
  K, a = number_field(f, "a")

  A = AlgAss(MatrixAlgebra(K, 2))
  B, AtoB, BtoA = Hecke.restrict_scalars(A, FlintQQ)
  @test base_ring(B) == FlintQQ
  @test dim(B) == dim(A)*degree(K)

  @test iszero(AtoB(zero(A)))
  @test iszero(BtoA(zero(B)))
  @test isone(AtoB(one(A)))
  @test isone(BtoA(one(B)))

  for i = 1:5
    c = rand(A, -10:10)
    d = rand(A, -10:10)
    @test BtoA(AtoB(c)) == c
    @test BtoA(AtoB(d)) == d
    @test AtoB(c + d) == AtoB(c) + AtoB(d)
    @test AtoB(c*d) == AtoB(c)*AtoB(d)

    e = rand(B, -10:10)
    f = rand(B, -10:10)
    @test AtoB(BtoA(e)) == e
    @test AtoB(BtoA(f)) == f
    @test BtoA(e + f) == BtoA(e) + BtoA(f)
    @test BtoA(e*f) == BtoA(e)*BtoA(f)
  end

  # Extend to K again
  C, BtoC, CtoB = Hecke._as_algebra_over_center(B)
  @test isisomorphic(K, base_ring(C))[1]
  @test dim(C) == dim(A)

  @test iszero(BtoC(zero(B)))
  @test iszero(CtoB(zero(C)))
  @test isone(BtoC(one(B)))
  @test isone(CtoB(one(C)))

  for i = 1:5
    c = rand(B, -10:10)
    d = rand(B, -10:10)
    @test CtoB(BtoC(c)) == c
    @test CtoB(BtoC(d)) == d
    @test BtoC(c + d) == BtoC(c) + BtoC(d)
    @test BtoC(c*d) == BtoC(c)*BtoC(d)

    e = rand(C, -10:10)
    f = rand(C, -10:10)
    @test BtoC(CtoB(e)) == e
    @test BtoC(CtoB(f)) == f
    @test CtoB(e + f) == CtoB(e) + CtoB(f)
    @test CtoB(e*f) == CtoB(e)*CtoB(f)
  end

  # Restrict from number field to number field
  g = x^9 - 15x^6 - 87x^3 - 125
  L, b = number_field(g, "b")
  KtoL = NfToNfMor(K, L, -2//45*b^7 + 7//9*b^4 + 109//45*b)

  A = AlgAss(MatrixAlgebra(L, 2))
  B, AtoB, BtoA = Hecke.restrict_scalars(A, KtoL)
 
  @test base_ring(B) == K
  @test dim(B) == dim(A)*div(degree(L), degree(K))

  @test iszero(AtoB(zero(A)))
  @test iszero(BtoA(zero(B)))
  @test isone(AtoB(one(A)))
  @test isone(BtoA(one(B)))

  for i = 1:5
    c = rand(A, -10:10)
    d = rand(A, -10:10)
    @test BtoA(AtoB(c)) == c
    @test BtoA(AtoB(d)) == d
    @test AtoB(c + d) == AtoB(c) + AtoB(d)
    @test AtoB(c*d) == AtoB(c)*AtoB(d)

    e = rand(B, -10:10)
    f = rand(B, -10:10)
    @test AtoB(BtoA(e)) == e
    @test AtoB(BtoA(f)) == f
    @test BtoA(e + f) == BtoA(e) + BtoA(f)
    @test BtoA(e*f) == BtoA(e)*BtoA(f)
  end

  # Restrict from F_q to F_p
  Fp = ResidueRing(FlintZZ, 7)
  Fq, a = FiniteField(7, 3, "a")

  A = AlgAss(MatrixAlgebra(Fq, 2))
  B, AtoB, BtoA = Hecke.restrict_scalars(A, Fp)
  @test base_ring(B) == Fp
  @test dim(B) == dim(A)*degree(K)

  @test iszero(AtoB(zero(A)))
  @test iszero(BtoA(zero(B)))
  @test isone(AtoB(one(A)))
  @test isone(BtoA(one(B)))

  for i = 1:5
    c = rand(A)
    d = rand(A)
    @test BtoA(AtoB(c)) == c
    @test BtoA(AtoB(d)) == d
    @test AtoB(c + d) == AtoB(c) + AtoB(d)
    @test AtoB(c*d) == AtoB(c)*AtoB(d)

    e = rand(B)
    f = rand(B)
    @test AtoB(BtoA(e)) == e
    @test AtoB(BtoA(f)) == f
    @test BtoA(e + f) == BtoA(e) + BtoA(f)
    @test BtoA(e*f) == BtoA(e)*BtoA(f)
  end
end
