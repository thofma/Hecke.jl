@testset "Primes" begin
  @testset "Next prime" begin
    for T in [UInt32, UInt64, UInt128, Int32, Int64, Int128, BigInt, ZZRingElem]
      @test T(2) == @inferred next_prime(T(0))
      @test T(3) == @inferred next_prime(T(2))
      @test T(5) == @inferred next_prime(T(3))
    end

    if Int == Int64
      @test_throws InexactError next_prime(Int(9223372036854775783))
    elseif Int == Int32
      @test_throws InexactError next_prime(Int32(2147483647))
    end

    for B in 1:100
      for i in 1:10
        z = rand(ZZRingElem(10)^B:ZZRingElem(10)^(B + 1))
        p = @inferred next_prime(z)
        @test @inferred is_prime(p)
      end
    end
  end

  @testset "PrimesSet" begin
    for T in [Int, BigInt, ZZRingElem]
      P = @inferred PrimesSet(T(0), T(100))
      PP = collect(P)
      @test length(PP) == 25
      @test all(is_prime(p) for p in P)
      @test PP[1] == T(2)
      @test PP[end] == T(97)

      P = @inferred PrimesSet(T(2), T(100))
      PP = collect(P)
      @test length(PP) == 25
      @test all(is_prime(p) for p in P)
      @test PP[1] == T(2)
      @test PP[end] == T(97)

      P = @inferred collect(PrimesSet(T(100), T(1000), T(5), T(1)))
      PP = collect(P)
      @test length(PP) == 35
      @test PP[1] == T(101)
      @test PP[end] == T(991)
      @test all(is_prime(p) && iszero(mod(p - T(1), T(5))) for p in P)

      P = @inferred PrimesSet(T(100), T(1000))
      PP = collect(P)
      @test length(PP) == 143
      @test PP[1] == T(101)
      @test PP[end] == T(997)

      for i in 1:10
        B = rand(100:200)
        modd = rand(2:20)
        a = rand(0:modd)
        while gcd(modd, a) != 1
          a = rand(0:modd)
        end
        P = @inferred PrimesSet(T(B), 2 * T(B), T(modd), T(a))
        @test all(is_prime(p) && iszero(mod(p - T(a), T(modd))) for p in P)
      end
    end

    for B in 20:25
      P = @inferred PrimesSet(ZZRingElem(10)^B, ZZRingElem(10)^B + ZZRingElem(10)^5)
      @test all(is_prime(p) for p in P)
    end
  end

  @testset "Factorization" begin
    z = ZZRingElem(35406006584838250779859646288524045541522102721903852419351442034218745921487618213430210114517205290360200098727562436996683618008616544114512403804879033305568279270240314426184896768288124359592373197652123675245898751520012787598855558789031381024625387676970030570435823658379242400351150075732901033905965864786338976200877211640473166089014964716251974918808271240247178842792601062285288192064508461909781716550249247324239984258941121466497704357904580222495174166761944293422767709291135213610316677755849561319492135401953603941166886125617969544902674910709468700828636641323083845265496724211468938267526059318324623810616578510536586846196125620883078603703124017829344050945482120041075683588528213410512026977220472164498442361107233172928990996889702611643333700128616817177297106110731760700226123826960770570905079841104576624248095584085121616172787911816790002442329981176247943435649)
    fac = factor(z)
    @test unit(fac) * prod(p^e for (p, e) in fac) == z
  end
end
