@testset "Integers" begin


    @test is_commutative(ZZ)

    @test modord(3,1) == 1
    @test modord(2,-1) == 1
    @test modord(3,-1) == 1

    @test modord(2,3) == 2

    @test modord(1,0) == 1

    @test modord(-1,0) == 2

    @test_throws ErrorException modord(2, 0)

    @test modord(ZZ(2),ZZ(3)) == ZZ(2)
    @test modord(ZZ(2),ZZ(-1)) == 1

    @test modord(ZZ(1),ZZ(0)) == 1

    @test modord(ZZ(-1),ZZ(0)) == 2

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

    @testset "Squarefree numbers with prime restrictions" begin
      @test Hecke.squarefree_up_to(30; coprime_to = ZZ.([2]),
                                  prime_base = ZZ.([2, 3, 5])) == [1, 3, 5, 15]
      @test Hecke.squarefree_up_to(30; coprime_to = ZZ.([2, 3, 5]),
                                  prime_base = ZZ.([2, 3, 5])) == [1]

      restrictions = [(ZZ.([2]), ZZ.([2, 3, 5])),
                      (ZZ.([2, 3, 5]), ZZ.([2, 3, 5])),
                      (ZZ.([7]), ZZ.([2, 3, 5])),
                      (ZZ.([6, 35]), ZZ.([2, 3, 5, 7, 11])),
                      (ZZ.([2, 7]), ZZ.([7, 2, 3, 11])),
                      (ZZ.([2, 3]), ZZRingElem[]),
                      (ZZRingElem[], ZZ.([2, 3, 5]))]
      for n in (1, 2, 9, 30, 100), (coprime_to, prime_base) in restrictions
        expected = [m for m in 1:n if is_squarefree(ZZ(m)) &&
                    all(x -> isone(gcd(ZZ(m), x)), coprime_to) &&
                    (isempty(prime_base) || all(p -> p in prime_base, prime_divisors(ZZ(m))))]
        @test Hecke.squarefree_up_to(n; coprime_to, prime_base) == expected
      end
    end

    @test support(QQ(2)) == [2]

    @test issetequal(euler_phi_inv(1), [1, 2])

    let
      n = 100
      for n in [n, - n], T in [Int8, Int32, Int, BigInt, ZZRingElem]
        v = @inferred coprime_residues(T(n))
        @test length(v) == 40
        @test all(x -> gcd(x, n) == 1, v)
        @test coprime_residues(T(0)) == T[]
        @test coprime_residues(T(1)) == T[0]
        @test coprime_residues(T(-1)) == T[0]
      end
    end
end
