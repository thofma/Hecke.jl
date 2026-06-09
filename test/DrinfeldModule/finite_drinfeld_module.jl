################################################################################
#
#  test/DrinfeldModule/finite_drinfeld_module.jl : Tests for finite Drinfeld modules
#
################################################################################

@testset "Finite Drinfeld module" begin
  # Rank-1 Drinfeld module (Carlitz) over GF(2)[T] with base GF(4)
  Fq2 = GF(2)
  A2, T2 = polynomial_ring(Fq2, "T2")
  K2 = GF(2, 2, "b2")
  b2 = gen(K2)
  gamma2 = b2  # image of T in K2

  phi2 = drinfeld_module(A2, [gamma2, one(K2)])  # Carlitz-like, rank 1

  @testset "frobenius_endomorphism" begin
    frob = frobenius_endomorphism(phi2)
    @test domain(frob) == phi2
    @test codomain(frob) == phi2
    # [K:Fq] = 2/1 = 2, so Frobenius ore poly = tau^2
    R = ore_polynomial_ring(phi2)
    tau = gen(R)
    @test ore_polynomial(frob) == tau^2
  end

  @testset "is_ordinary and is_supersingular rank 1" begin
    # For rank 1, height = 1, so always ordinary
    @test is_ordinary(phi2)
    @test is_supersingular(phi2)  # rank 1 = height 1
  end

  # Rank-2 module over GF(2) with base GF(4)
  Fq = GF(2)
  A, T = polynomial_ring(Fq, "T")
  K = GF(2, 4, "c")
  c = gen(K)

  # phi_T = c + tau + tau^2  (rank 2, height 1 if GCD works out)
  phi = drinfeld_module(A, [c, one(K), one(K)])

  @testset "frobenius_endomorphism rank 2" begin
    frob = frobenius_endomorphism(phi)
    @test domain(frob) == phi
    @test codomain(frob) == phi
    R = ore_polynomial_ring(phi)
    tau = gen(R)
    # [K:Fq] = degree(K)/degree(Fq) = 4/1 = 4, so tau^4
    @test ore_polynomial(frob) == tau^4
  end

  @testset "frobenius_charpoly" begin
    chi = frobenius_charpoly(phi)
    # chi is degree 2 (= rank) in X, with coefficients in Fq[T] = GF(2)[T]
    @test degree(chi) == 2
    # leading coeff should be 1
    @test isone(leading_coefficient(chi))
  end

  @testset "frobenius_trace and frobenius_norm" begin
    tr = frobenius_trace(phi)
    nm = frobenius_norm(phi)
    chi = frobenius_charpoly(phi)
    # trace = -coeff(chi, rank-1), norm = coeff(chi, 0)
    @test tr == -coeff(chi, rank(phi) - 1)
    @test nm == coeff(chi, 0)
  end

  @testset "is_ordinary and is_supersingular rank 2" begin
    h = height(phi)
    @test is_ordinary(phi) == (h == 1)
    @test is_supersingular(phi) == (h == 2)
  end

  @testset "is_isogenous" begin
    # A module is isogenous to itself
    @test is_isogenous(phi, phi)
    # Different rank modules are not isogenous
    phi1 = drinfeld_module(A, [c, one(K)])
    @test !is_isogenous(phi1, phi)
  end
end
