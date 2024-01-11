@testset "Integers" begin
    
@test is_commuatative(ZZ)==true

@test modord(2,3) == 2

@test modord(ZZ(2),ZZ(3)) == ZZ(2)


end