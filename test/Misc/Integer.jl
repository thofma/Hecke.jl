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

    @testset "Squarefree iterator" begin
      for n in (0, 1, 2, 3, 4, 8, 9, 16, 25, 49, 50, 65, 1000)
        expected = [k for k in 1:n if is_squarefree(ZZ(k))]
        for block_size in (1, 2, 7, 64)
          it = Hecke.squarefree_up_to_iterator(n; block_size = block_size)
          @test eltype(it) == Int
          @test Base.IteratorSize(typeof(it)) == Base.SizeUnknown()
          @test collect(it) == expected
          @test collect(it) == expected
        end
      end

      @test collect(Hecke.squarefree_up_to_iterator(100000)) == Hecke.squarefree_up_to(100000)

      # Taking the first few values must not sieve the whole range or generate
      # all primes up to the square root of the bound.
      it = Hecke.squarefree_up_to_iterator(typemax(Int))
      @test collect(Iterators.take(it, 10)) == [1, 2, 3, 5, 6, 7, 10, 11, 13, 14]

      # Independent iterations over the same iterator keep separate sieve state.
      it = Hecke.squarefree_up_to_iterator(30; block_size = 2)
      a, state_a = iterate(it)
      b, state_b = iterate(it)
      @test a == b == 1
      a, state_a = iterate(it, state_a)
      a, state_a = iterate(it, state_a)
      b, state_b = iterate(it, state_b)
      @test a == 3
      @test b == 2
      @test collect(it) == Hecke.squarefree_up_to(30)

      it = Hecke.squarefree_up_to_iterator(1)
      _, state = iterate(it)
      @test iterate(it, state) === nothing
      @test iterate(it, state) === nothing

      @test_throws ArgumentError Hecke.squarefree_up_to_iterator(-1)
      @test_throws ArgumentError Hecke.squarefree_up_to_iterator(10; block_size = 0)
      @test_throws ArgumentError Hecke.squarefree_up_to_iterator(10; block_size = -1)

      @testset "Coprimality and prime support" begin
        restrictions = [
          (ZZ.([2, 3]), ZZRingElem[]),
          (ZZ.([6, -35]), ZZRingElem[]),
          (ZZ.([1, -1]), ZZRingElem[]),
          (ZZ.([0]), ZZRingElem[]),
          (ZZRingElem[], ZZ.([2, 3, 5])),
          (ZZRingElem[], ZZ.([11, 7, 2])),
          (ZZRingElem[], ZZ.([2, 2, 3, 5])),
          (ZZRingElem[], ZZ.([1009])),
          (ZZ.([2, 7]), ZZ.([2, 3, 5, 7])),
          (ZZ.([2, 3, 5]), ZZ.([2, 3, 5])),
          (ZZ.([0]), ZZ.([2, 3, 5])),
        ]
        for n in (0, 1, 2, 4, 9, 25, 49, 65, 1100)
          squarefree = [k for k in 1:n if is_squarefree(ZZ(k))]
          for (coprime_to, prime_base) in restrictions
            expected = [k for k in squarefree
                        if all(m -> isone(gcd(ZZ(k), m)), coprime_to) &&
                           (isempty(prime_base) || all(p -> p in prime_base, prime_divisors(ZZ(k))))]
            for block_size in (1, 7, 64)
              it = Hecke.squarefree_up_to_iterator(n; coprime_to, prime_base, block_size)
              @test collect(it) == expected
            end
          end
        end

        for n in (1, 2, 65, 1000)
          for coprime_to in (ZZ.([2]), ZZ.([2, 3, 7]))
            @test collect(Hecke.squarefree_up_to_iterator(n; coprime_to)) ==
                  Hecke.squarefree_up_to(n; coprime_to)
          end
          for prime_base in (ZZ.([2, 3, 5]), ZZ.([11, 7, 2]))
            @test collect(Hecke.squarefree_up_to_iterator(n; prime_base)) ==
                  Hecke.squarefree_up_to(n; prime_base)
          end
        end

        @test collect(Hecke.squarefree_up_to_iterator(100; coprime_to = [2], prime_base = [2, 3, 5])) == [1, 3, 5, 15]
        @test collect(Hecke.squarefree_up_to_iterator(100; coprime_to = [6])) ==
              collect(Hecke.squarefree_up_to_iterator(100; coprime_to = ZZ.([2, 3])))
        @test collect(Hecke.squarefree_up_to_iterator(100; coprime_to = [typemin(Int)])) ==
              collect(Hecke.squarefree_up_to_iterator(100; coprime_to = [2]))

        # Preserve the caller's lists and snapshot their contents.
        coprime_to = ZZ.([2])
        prime_base = ZZ.([5, 2, 5, 3])
        it = Hecke.squarefree_up_to_iterator(100; coprime_to, prime_base)
        @test coprime_to == ZZ.([2])
        @test prime_base == ZZ.([5, 2, 5, 3])
        coprime_to[1] = ZZ(3)
        prime_base[4] = ZZ(7)
        @test collect(it) == [1, 3, 5, 15]
        @test collect(it) == [1, 3, 5, 15]

        # A finite prime base bounds the entire enumeration even when n is huge.
        @test collect(Hecke.squarefree_up_to_iterator(typemax(Int); prime_base = [2, 3, 5])) ==
              [1, 2, 3, 5, 6, 10, 15, 30]
        large_prime = next_prime(ZZ(typemax(Int)))
        @test collect(Hecke.squarefree_up_to_iterator(100; prime_base = [large_prime])) == [1]
        @test collect(Hecke.squarefree_up_to_iterator(100; coprime_to = [large_prime])) ==
              Hecke.squarefree_up_to(100)

        # The product of the base primes can exceed the machine integer range.
        prime_base = ZZ.([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53])
        it = Hecke.squarefree_up_to_iterator(typemax(Int); prime_base)
        @test collect(Iterators.take(it, 10)) == [1, 2, 3, 5, 6, 7, 10, 11, 13, 14]

        for prime_base in ([0], [1], [-2], [4])
          @test_throws ArgumentError Hecke.squarefree_up_to_iterator(100; prime_base)
        end
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
