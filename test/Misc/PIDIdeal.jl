@testset "PIDIdeal" begin
  k, = quadratic_field(-1)
  for K in [QQ, k, GF(2)] 
    Kx, x = K["x"]

    I = ideal(Kx, x)
    @test base_ring(I) === Kx
    @test I == ideal(Kx, x, x^2, 0)
    @test I == ideal(Kx, [x, x^2, 0])
    @test ideal(Kx, one(Kx)) == ideal(Kx, x, 1)

    #@test x * I == ideal(Kx, x^2)
    #@test I * x == ideal(Kx, x^2)
    #@test I * x == ideal(Kx, x^2)

    #@test x * Kx == I
    #@test Kx * x == I

    @test sprint(show, "text/plain", I) isa String

    @test ideal(Kx, gen(I)) == I
    @test ideal(Kx, gens(I)) == I

    D = Dict()
    D[I] = 1
    J = ideal(Kx, x)
    D[J] = 2
    @test haskey(D, I)
    @test D[I] == 2
    @test !haskey(D, ideal(Kx, 1))

    J = ideal(Kx, x^2)

    @test gcd(I, J) == I
    @test +(I, J) == I
    @test lcm(I, J) == J
    @test intersect(I, J) == J
    @test I * J == ideal(Kx, x^3)

    @test !is_one(I)
    @test is_one(ideal(Kx, 3))
    @test !is_zero(I)
    @test is_zero(ideal(Kx, 0))
  end

  for K in [QQ, k, GF(2)]
    I = ideal(K, K(1))
    J = ideal(K, K(0))
    @test I == ideal(K, 2, 3, 0)
    @test I == ideal(K, [2, 3, 0])
    @test J == ideal(K, 0, 0)
    @test J == ideal(K, [0, 0])

    #@test I == K(1) * K
    #@test I == K * K(1)
    #@test I == 1 * K
    #@test I == K * 1
    #@test J == K(0) * K
    #@test J == K * K(0)
    #@test J == K * 0

    @test sprint(show, "text/plain", I) isa String
    
    @test ideal(K, gen(I)) == I
    @test ideal(K, gen(J)) == J
    @test ideal(K, gens(I)) == I
    @test ideal(K, gens(J)) == J

    D = Dict()
    D[I] = 1
    D[ideal(K, 3)] = 2
    @test haskey(D, I)
    @test D[I] == 2
    @test !haskey(D, J)

    @test gcd(I, I) == I
    @test gcd(I, J) == I
    @test gcd(J, J) == J
    @test +(I, I) == I
    @test +(I, J) == I
    @test lcm(I, J) == J
    @test intersect(I, J) == J
    @test I * I == I
    @test I * J == J

    @test is_one(I)
    @test !is_one(J)
    @test is_zero(J)
    @test !is_zero(I)
  end
end




