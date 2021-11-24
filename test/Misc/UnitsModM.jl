@testset "#465" begin
  G, mG = unit_group(quo(ZZ, 8)[1]);
  H = collect(G)
  X = map(mG, H)
  @test H == map(x->preimage(mG, x), X)
end
