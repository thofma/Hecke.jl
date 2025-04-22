@testset "PrimeIdealsSet" begin
  Qx, x = QQ["x"]
  K, a = number_field(x - 1, "a")
  O = maximal_order(K)

  S = @inferred PrimeIdealsSet(O, 2, 100)
  @test @inferred length(collect(S)) == 25

  S = @inferred PrimeIdealsSet(O, 2, 100, indexdivisors = false, ramified = false, degreebound = 100, coprimeto = 3*5*7)
  @test @inferred length(collect(S)) == 22

  K, a = number_field(x^2 - 5, "a")
  O = maximal_order(K)

  S = @inferred PrimeIdealsSet(O, ZZRingElem(2), ZZRingElem(100))
  @test @inferred length(collect(S)) == 35
  S = @inferred PrimeIdealsSet(O, ZZRingElem(2), ZZRingElem(100), indexdivisors = false)
  @test @inferred length(collect(S)) == 34
  S = @inferred PrimeIdealsSet(O, ZZRingElem(2), ZZRingElem(100), indexdivisors = false, ramified = false)
  @test @inferred length(collect(S)) == 33
  S = @inferred PrimeIdealsSet(O, ZZRingElem(2), ZZRingElem(100), indexdivisors = false, ramified = false, degreebound = 1)
  @test @inferred length(collect(S)) == 20

  K, a = number_field(x^5 - x + 1, "a")
  O = maximal_order(K)

  S = @inferred PrimeIdealsSet(O, ZZRingElem(2), ZZRingElem(100))
  @test @inferred length(collect(S)) == 51

  S = @inferred PrimeIdealsSet(O, ZZRingElem(2), ZZRingElem(100), degreebound = 1)
  @test @inferred length(collect(S)) == 18
  SS = collect(S)

  S = @inferred PrimeIdealsSet(O, ZZRingElem(2), -1, degreebound = 1)
  z = 1
  T = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[]
  for P in S
    push!(T, P)
    if z == 18
      break
    end
    z += 1
  end
  @test T == SS

  P = prime_decomposition(O, 2)[1][1]
  S = @inferred PrimeIdealsSet(O, ZZRingElem(2), ZZRingElem(100), coprimeto = P)
  @test @inferred length(collect(S)) == 50

  el = Hecke.find_elem_of_valuation_1(P, P^2)
  @test valuation(el, P) == 1

  S = @inferred PrimeIdealsSet(O, ZZRingElem(2), ZZRingElem(100), coprimeto = 2)
  @test @inferred length(collect(S)) == 49

  S = @inferred PrimeIdealsSet(O, ZZRingElem(2), ZZRingElem(100), coprimeto = ZZRingElem(6))
  @test @inferred length(collect(S)) == 48

  S = @inferred PrimeIdealsSet(O, ZZRingElem(2), ZZRingElem(100), coprimeto = O(30))
  @test @inferred length(collect(S)) == 47

  @test_throws ErrorException PrimeIdealsSet(O, ZZRingElem(-1), ZZRingElem(1))
  @test_throws ErrorException PrimeIdealsSet(O, ZZRingElem(1), -2)
  @test_throws ErrorException PrimeIdealsSet(O, ZZRingElem(1), 2, coprimeto = "bla")
end


@testset "PrimeIdealsSet" begin
  l = Hecke.primes_up_to(20)
  for i = 2:length(l)
    d = l[i]
    K = quadratic_field(d)[1]
    OK = maximal_order(K)
    p = next_prime(ZZRingElem(10)^70)
    while length(prime_decomposition_type(OK, p)) != 2
      p = next_prime(p)
    end
    P = prime_decomposition(OK, p)[1][1]
    @test valuation(P.gen_two, P) == 1
  end

  _, x = polynomial_ring(QQ, cached = false)
  K = number_field(x^4 + 2*x^3 - 35*x^2 - 36*x + 5, "a", cached = false)[1]
  OK = maximal_order(K)
  @assert length(prime_decomposition_type(OK, 3)) == 2
  @assert length(prime_decomposition_type(OK, 5)) == 4
end

Qx, x = QQ["x"]
f = x^2 - 2
K, a = number_field([f], "a")
O = order(K, [3*a[1]])
P = ZZ(7) * O + (O(3*a[1]) + 2) * O
@test minimum(P) == 7
@test norm(P) == 7

@test is_prime(P)
P = ZZ(5) * O + (O((3*a[1]))^2 + 2) * O
@test (@inferred norm(P)) == 5^2
@test (@inferred is_prime(P))
@test (@inferred minimum(P)) == 5

Qx, x = QQ["x"]
KK, aa = number_field(x^4 - 2*x^2 + 9, "a")
OK = maximal_order(KK)
@assert basis(OK) == [1, aa, 1//2*aa^2 + 1//2, 1//12*aa^3 + 1//4*aa^2 + 7//12*aa + 3//4]
bmat = matrix(ZZ, 4, 4, [3062080894710611593095893681253524719283529370074754326817842112259095266, 0, 0, 0, 2226206391202033181194975445109233654981588868319097648678658242539756242, 42119761475466602781011154, 0, 0, 2480886204347145855965895405611286703203844802620233651734473712254265826, 5012083264523823781687980, 18, 0, 1217443710347825388779640934405414891520873327569391386052802753448766412, 2506041632261911890843972, 0, 18])
A = ideal(OK, bmat)
lf = Hecke.factor_easy(A)
@test prod(x^y for (x, y) in lf) == A
@test Hecke.is_pairwise_coprime([x^y for (x, y) in lf])

Qx, x = QQ["x"]
K, a = number_field(x^2 - 2)
OK = maximal_order(K)
lp = prime_decomposition(OK, 2339986748637033487833953)
P1 = lp[1][1]
P2 = lp[2][1]
A = P1^2 * P2
lf = Hecke.factor_easy(A)
@test prod(x^y for (x, y) in lf) == A
@test Hecke.is_pairwise_coprime([x^y for (x, y) in lf])

# primary decomposition
K, a = quadratic_field(5)
O = equation_order(K)
I = prime_ideals_over(O, 11)[1]
PD = primary_decomposition(I)
@test prod(x[1] for x in PD) == I
@test all(x -> all(y -> y[2] === x[2] || x[2] + y[2] == 1*ZG, PD), PD)

I = 4 * O
PD = primary_decomposition(I)
@test prod(x[1] for x in PD) == I
@test all(x -> all(y -> y[2] === x[2] || x[2] + y[2] == 1*ZG, PD), PD)

# Non-maximal, locally maximal order
Qx, x = QQ["x"]
f = x^3 - x^2 + 1
K, a = number_field(f)
O = equation_order(K)
E = pmaximal_overorder(O, 23)
lp = prime_decomposition(E, 23)
@test length(lp) == 2

let
  # valuation for large degree, inert prime
  K, a = cyclotomic_real_subfield(101, :a)
  P, = prime_ideals_over(maximal_order(K), 10007)
  @test valuation(gen(K), P) == 0
end
