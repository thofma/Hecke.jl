@testset "Quaternion algebras" begin
  M = Array{QQFieldElem, 3}(undef, 4, 4, 4)
  M[:, :, 1] = [-2 4 -2 0; 0 0 -1 -3; 1 1 0 3; -3 3 -3 0]
  M[:, :, 2] = [ -4 0 -1 -3; 2 0 2 0; -3 2 -5//2 -3//2; -3 0 -3//2 -9//2]
  M[:, :, 3] = [-4 0 -2 -6; 4 -4 5 3; -4 4 -7//2 -9//2; 0 0 -3//2 -9//2]
  M[:, :, 4] = [4//3 -8//3 8//3 0; 4//3 4//3 -1//3 3; -4//3 -4//3 5//6 -3//2; 0 0 3//2 -3//2]
  A = StructureConstantAlgebra(QQ, M)
  B, f = Hecke.is_quaternion_algebra(A)
  for b in basis(B)
    for bb in basis(B)
      @test f(b) * f(bb) == f(b * bb)
    end
  end
end
