################################################################################
#
#  test/DrinfeldModule/carlitz_module.jl : Tests for the Carlitz module
#
################################################################################

@testset "Carlitz module" begin
  Fq = GF(2)
  A, T = polynomial_ring(Fq, "T")

  @testset "carlitz_module(A)" begin
    phi = carlitz_module(A)
    @test rank(phi) == 1
    # phi_T = gen(Fq) + tau = 1 + tau  (generator of GF(2) is 1)
    @test coefficients(phi) == [gen(Fq), one(Fq)]
  end

  @testset "carlitz_module(A, gamma_T)" begin
    K = GF(2, 2, "a")
    a = gen(K)
    phi = carlitz_module(A, a)
    @test rank(phi) == 1
    @test coefficients(phi) == [a, one(K)]
  end

  @testset "carlitz_factorial" begin
    # D_0 = 1
    @test isone(carlitz_factorial(A, 0))

    # Test over GF(3)
    Fq3 = GF(3)
    A3, T3 = polynomial_ring(Fq3, "T3")
    q3 = 3

    # E_1 = T^3 - T
    E1 = T3^3 - T3
    # carlitz_factorial(A3, 1) = E1^1 = T^3 - T   (since 1 = 0*3 + 1, so c_0=1, remaining=0)
    # Wait: remaining = 1, c = divrem(1, 3) = (0, 1), so E_1 = 1^3 * (T3^3 - T3) = T3^3 - T3, result = E1^1
    @test carlitz_factorial(A3, 1) == E1

    # carlitz_factorial(A3, 3) = E1^0 * E2^1   (3 = 0 + 1*3, so c_1=1)
    # E_2 = E1^3 * (T^9 - T)
    E2 = E1^3 * (T3^9 - T3)
    @test carlitz_factorial(A3, 3) == E2

    # carlitz_factorial(A3, 4) = carlitz_factorial(A3, 1) * carlitz_factorial(A3, 3)
    # 4 = 1 + 1*3, so c_0=1, remaining=1; then c_1=1, remaining=0
    # result = E1^1 * E2^1
    @test carlitz_factorial(A3, 4) == E1 * E2
  end
end
