@testset "Torsion" begin
  D4_gram = matrix(ZZ, [[2, 0, 0, -1],
                        [0, 2, 0, -1],
                        [0, 0, 2, -1],
                        [-1 ,-1 ,-1 ,2]])

  L = Zlattice(gram = D4_gram)
  T = discriminant_group(L)
  @test order(T) == 4

  TT, mTT = @inferred sub(T, [T([1, 1//2, 1//2, 1])])
  @test order(TT) == 2
end
