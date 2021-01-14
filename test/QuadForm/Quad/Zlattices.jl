@testset "Zlattices" begin
  G = matrix(ZZ, 2, 2, [2,1,1,2])
  B = matrix(ZZ, 1, 2, [1,0])
  L = Zlattice(B, gram=G)
  LL = orthogonal_sum(L,L)
  @test rank(LL) == 2*rank(L)  
end
