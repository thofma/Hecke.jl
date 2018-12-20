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

  # Restrict from number field to number field
  g = x^9 - 15x^6 - 87x^3 - 125
  L, b = number_field(g, "b")
  t, KtoL = issubfield(K, L)
  @assert t

  C = AlgAss(MatrixAlgebra(L, 2))
  D, CtoD, DtoC = Hecke.restrict_scalars(C, KtoL)
 
  @test base_ring(D) == K
  @test dim(D) == dim(C)*div(degree(L), degree(K))

  @test iszero(CtoD(zero(C)))
  @test iszero(DtoC(zero(D)))
  @test isone(CtoD(one(C)))
  @test isone(DtoC(one(D)))

  for i = 1:5
    c = rand(C, -10:10)
    d = rand(C, -10:10)
    @test DtoC(CtoD(c)) == c
    @test DtoC(CtoD(d)) == d
    @test CtoD(c + d) == CtoD(c) + CtoD(d)
    @test CtoD(c*d) == CtoD(c)*CtoD(d)

    e = rand(D, -10:10)
    f = rand(D, -10:10)
    @test CtoD(DtoC(e)) == e
    @test CtoD(DtoC(f)) == f
    @test DtoC(e + f) == DtoC(e) + DtoC(f)
    @test DtoC(e*f) == DtoC(e)*DtoC(f)
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
