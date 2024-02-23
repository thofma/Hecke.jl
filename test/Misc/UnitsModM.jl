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
