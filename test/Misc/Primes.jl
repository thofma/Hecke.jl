@testset "Primes" begin
  @testset "Next prime" begin
    for T in [UInt32, UInt64, UInt128, Int32, Int64, Int128, BigInt, fmpz]
      @test @inferred next_prime(T(0)) == T(2)
      @test @inferred next_prime(T(2)) == T(3)
      @test @inferred next_prime(T(3)) == T(5)
    end

    for T in [Int32, Int64, Int128, BigInt, fmpz]
      @test_throws ErrorException next_prime(T(-1))
    end

    if Int == Int64
      @test_throws ErrorException next_prime(Int(9223372036854775783))
    elseif Int == Int32
      @test_throws ErrorException next_prime(Int32(2147483647))
    end

    for B in 1:100
      for i in 1:10
        z = rand(fmpz(10)^B:fmpz(10)^(B + 1))
        p = @inferred next_prime(z)
        @test @inferred isprime(p)
      end
    end
  end

  @testset "PrimesSet" begin
    for T in [Int, BigInt, fmpz]
      P = @inferred PrimesSet(T(0), T(100))
      PP = collect(P)
      @test length(PP) == 25
      @test all(isprime(p) for p in P)
      @test PP[1] == T(2)
      @test PP[end] == T(97)

      P = @inferred PrimesSet(T(2), T(100))
      PP = collect(P)
      @test length(PP) == 25
      @test all(isprime(p) for p in P)
      @test PP[1] == T(2)
      @test PP[end] == T(97)

      P = @inferred collect(PrimesSet(T(100), T(1000), T(5), T(1)))
      PP = collect(P)
      @test length(PP) == 35
      @test PP[1] == T(101)
      @test PP[end] == T(991)
      @test all(isprime(p) && iszero(mod(p - T(1), T(5))) for p in P) 

      P = @inferred PrimesSet(T(100), T(1000))
      PP = collect(P)
      @test length(PP) == 143
      @test PP[1] == T(101)
      @test PP[end] == T(997)

      for i in 1:10
        B = rand(100:200)
        modd = rand(1:20)
        a = rand(0:modd)
        while gcd(modd, a) != 1
          a = rand(0:modd)
        end
        P = @inferred PrimesSet(T(B), 2 * T(B), T(modd), T(a))
        @test all(isprime(p) && iszero(mod(p - T(a), T(modd))) for p in P) 
      end
    end

    for B in 20:25
      P = @inferred PrimesSet(fmpz(10)^B, fmpz(10)^B + fmpz(10)^5)
      @test all(isprime(p) for p in P)
    end
  end
end
