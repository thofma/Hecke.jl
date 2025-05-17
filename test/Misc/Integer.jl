@testset "Integers" begin

    
    @test is_commutative(ZZ)

    @test modord(2,3) == 2

    @test modord(ZZ(2),ZZ(3)) == ZZ(2)

    @test sort(euler_phi_inv(ZZ(4))) == [ZZ(5), ZZ(8), ZZ(10), ZZ(12)]

    @test Hecke.is_prime_power(ZZ(8))

    @test Hecke.is_prime_power(8) 

    @test sort(euler_phi_inv(2)) == [3,4,6]

    @test euler_phi(ZZ(5)) == ZZ(4)

    @test carmichael_lambda(ZZ(8)) == ZZ(2)
   
    @test sort(evaluate.(Hecke.euler_phi_inv_fac_elem(ZZ(4)))) == ZZ.([5, 8 ,10 ,12])
    
    @test carmichael_lambda(ZZ(1*2^3)) == ZZ(2)

    @test carmichael_lambda(8) == 2

    @test sort(Hecke.squarefree_up_to(2)) == [1,2] 

    @test support(QQ(2)) == [2]

    @test issetequal(euler_phi_inv(1), [1, 2])
end
