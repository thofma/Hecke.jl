@testset "collect" begin
  ZZ7 = residue_ring(ZZ, 7)[1]
  @test collect(ZZ7) == ZZ7.(0:6)
  ZZ7_fmpz = residue_ring(ZZ, ZZ(7))[1]
  @test collect(ZZ7_fmpz) == ZZ7_fmpz.(0:6)
  F7 = GF(7)
  @test collect(F7) == F7.(0:6)
end

@testset "#465" begin
  G, mG = unit_group(quo(ZZ, 8)[1]);
  H = collect(G)
  X = map(mG, H)
  @test H == map(x->preimage(mG, x), X)
end

@testset "primitive root" begin
  for T in [Int, BigInt, ZZRingElem]
    g = primitive_root(T(10))
    @test typeof(g) === T
    @test g^2 % 10 != 1
    g = primitive_root(T(1))
    @test g == 0
    g = primitive_root(T(2))
    @test g == 1
    g = primitive_root(T(4))
    @test g == 3
  end
  @test_throws ArgumentError primitive_root(8)
  @test_throws ArgumentError primitive_root(3*5)
  @test_throws ArgumentError primitive_root(8*5)
end
