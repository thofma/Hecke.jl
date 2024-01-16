@testset "Integers" begin
    
#Line 7
@test is_commuatative(ZZ)==true
#Lines 26-35
@test modord(2,3) == 2
#Lines 15-24 
@test modord(ZZ(2),ZZ(3)) == ZZ(2)
#Lines 760-762
@test sort(euler_phi_inv(ZZ(4))) == [ZZ(5), ZZ(8), ZZ(10), ZZ(12)]
#Lines 172-179


end