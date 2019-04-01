@testset "PrimeIdealsSet" begin
  Qx, x = FlintQQ["x"]
  K, a = NumberField(x - 1, "a")
  O = maximal_order(K)

  S = @inferred PrimeIdealsSet(O, 2, 100)
  @test @inferred length(collect(S)) == 25

  S = @inferred PrimeIdealsSet(O, 2, 100, indexdivisors = false, ramified = false, degreebound = 100, coprimeto = 3*5*7)
  @test @inferred length(collect(S)) == 22

  K, a = NumberField(x^2 - 5, "a")
  O = maximal_order(K)

  S = @inferred PrimeIdealsSet(O, fmpz(2), fmpz(100))
  @test @inferred length(collect(S)) == 35
  S = @inferred PrimeIdealsSet(O, fmpz(2), fmpz(100), indexdivisors = false)
  @test @inferred length(collect(S)) == 34
  S = @inferred PrimeIdealsSet(O, fmpz(2), fmpz(100), indexdivisors = false, ramified = false)
  @test @inferred length(collect(S)) == 33
  S = @inferred PrimeIdealsSet(O, fmpz(2), fmpz(100), indexdivisors = false, ramified = false, degreebound = 1)
  @test @inferred length(collect(S)) == 20 

  K, a = NumberField(x^5 - x + 1, "a")
  O = maximal_order(K)

  S = @inferred PrimeIdealsSet(O, fmpz(2), fmpz(100))
  @test @inferred length(collect(S)) == 51 

  S = @inferred PrimeIdealsSet(O, fmpz(2), fmpz(100), degreebound = 1)
  @test @inferred length(collect(S)) == 18
  SS = collect(S)

  S = @inferred PrimeIdealsSet(O, fmpz(2), -1, degreebound = 1)
  z = 1
  T = NfOrdIdl[]
  for P in S
    push!(T, P)
    if z == 18
      break
    end
    z += 1
  end
  @test T == SS

  P = prime_decomposition(O, 2)[1][1]
  S = @inferred PrimeIdealsSet(O, fmpz(2), fmpz(100), coprimeto = P)
  @test @inferred length(collect(S)) == 50 
  
  el = Hecke.find_elem_of_valuation_1(P, P^2)
  @test valuation(el, P) == 1
  
  S = @inferred PrimeIdealsSet(O, fmpz(2), fmpz(100), coprimeto = 2)
  @test @inferred length(collect(S)) == 49

  S = @inferred PrimeIdealsSet(O, fmpz(2), fmpz(100), coprimeto = fmpz(6))
  @test @inferred length(collect(S)) == 48 

  S = @inferred PrimeIdealsSet(O, fmpz(2), fmpz(100), coprimeto = O(30))
  @test @inferred length(collect(S)) == 47 

  @test_throws ErrorException PrimeIdealsSet(O, fmpz(-1), fmpz(1))
  @test_throws ErrorException PrimeIdealsSet(O, fmpz(1), -2)
  @test_throws ErrorException PrimeIdealsSet(O, fmpz(1), 2, coprimeto = "bla")
  
  
  
end
