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


@testset "PrimeIdealsSet" begin
  l = Hecke.primes_up_to(20)
  for i = 2:length(l)
    d = l[i]
    K = quadratic_field(d)[1]
    OK = maximal_order(K)
    p = next_prime(fmpz(10)^70)
    while length(prime_decomposition_type(OK, p)) != 2
      p = next_prime(p)
    end
    P = prime_decomposition(OK, p)[1][1]
    @test valuation(P.gen_two, P) == 1
  end

  _, x = PolynomialRing(QQ, cached = false)
  K = number_field(x^4 + 2*x^3 - 35*x^2 - 36*x + 5, "a", cached = false)[1]
  OK = maximal_order(K)
  @assert length(prime_decomposition_type(OK, 3)) == 2
  @assert length(prime_decomposition_type(OK, 5)) == 4
end

Qx, x = FlintQQ["x"]
f = x^2 - 2
K, a = number_field([f], "a")
O = Order(K, [3*a[1]])
P = ZZ(7) * O + (O(3*a[1]) + 2) * O
@test minimum(P) == 7
@test norm(P) == 7

@test is_prime(P)
P = ZZ(5) * O + (O((3*a[1]))^2 + 2) * O
@test (@inferred norm(P)) == 5^2
@test (@inferred is_prime(P))
@test (@inferred minimum(P)) == 5
