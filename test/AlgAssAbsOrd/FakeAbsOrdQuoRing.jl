@testset "FakeAbsOrdQuoRing" begin
  G = small_group(8, 3)
  QG = QQ[G]
  ZG = Order(QG, basis(QG))

  for L in [ZG, maximal_order(ZG)]
    x = rand(L, -1:1)
    while iszero(det(representation_matrix(x)))
      x = rand(L, -1:1)
    end
    I = x * L
    R = @inferred Hecke.FakeAbsOrdQuoRing(L, I)
    @test (@inferred isone(@inferred one(R)))
    o = one(R)
    for i in 1:100
      a = @inferred rand(L, -1:1)
      aR = @inferred R(a)
      @test lift(aR) - a in I
      b = @inferred rand(L, -1:1)
      bR = @inferred R(b)
      @test lift(bR) - b in I
      @test o * aR == aR
      @test aR * o == aR
      @test aR * bR == R(a * b)
    end
  end
end
