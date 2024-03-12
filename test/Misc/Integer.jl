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

    @test sort(euler_phi_inv(2)) == ZZ.([3,4,6])

    @test radical(2) == ZZ(2)

    @test Hecke.ecm(ZZ(2)) == (0,2)

    @test string(FacElem(Hecke.factor(ZZ(2)))) == "2^1"

    @test carmichael_lambda(Hecke.factor(ZZ(2))) == 1

    @test string(factor(FacElem(factor(ZZ(2))))) == "1 * 2"

    @test string(Divisors(factor(ZZ(2)))) == "Divisors of 2 = MSet(2)\n"

    @test euler_phi(factor(FacElem(factor(ZZ(2))))) == 1

    @test carmichael_lambda(factor(FacElem(factor(ZZ(2))))) == 1

    @test string(sunit_group_fac_elem([2])) == "(GrpAb: Z/2 x Z, SUnits (in factored form) map of Factored elements over Rational field for ZZRingElem[-1, 2]\n)"



end

