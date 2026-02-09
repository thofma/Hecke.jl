function _test_morphism(f; bijective = false)
  R = domain(f)
  @test is_one(f(one(R)))
  @test is_zero(f(zero(R)))
  for i in 1:10
    x = rand(R)
    y = rand(R)
    @test f(x + y) == f(x) + f(y)
    @test f(x * y) == f(x) * f(y)
  end
  if bijective
    S = codomain(f)
    for i in 1:10
      x = rand(S)
      y = rand(S)
      @test f\(x + y) == (f\x) + (f\y)
      @test f\(x * y) == (f\x) * (f\y)
      @test f(f\x) == x
    end
  end
end

@testset "FiniteRings/Conversions" begin
  RR, = finite_ring(GF(2)[small_group(8, 3)])
  S = matrix_ring(RR, 2)
  R, = finite_ring(S)

  f = isomorphism(MatAlgebra, R)
  @test codomain(f) isa MatAlgebra
  @test domain(f) === R
  _test_morphism(f; bijective = true)

  f = isomorphism(StructureConstantAlgebra, R)
  @test codomain(f) isa StructureConstantAlgebra{FqFieldElem}
  @test domain(f) === R
  _test_morphism(f; bijective = true)

  for T in (fpFieldElem, FpFieldElem, FqFieldElem)
    f = isomorphism(StructureConstantAlgebra{T}, R)
    @test codomain(f) isa StructureConstantAlgebra{T}
    @test domain(f) === R
    _test_morphism(f; bijective = true)
  end

  let
    R = finite_ring([4], [identity_matrix(ZZ, 1)])
    @test_throws ArgumentError isomorphism(StructureConstantAlgebra, R)
    @test_throws ArgumentError isomorphism(MatAlgebra, R)

    R, = finite_ring(GF(next_prime(ZZ(2)^100))[small_group(8, 3)])
    @test_throws ArgumentError isomorphism(StructureConstantAlgebra{fpFieldElem}, R)
  end
end
