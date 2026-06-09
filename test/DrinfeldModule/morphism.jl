################################################################################
#
#  test/DrinfeldModule/morphism.jl : Tests for Drinfeld module morphisms
#
################################################################################

@testset "Morphisms" begin
  # Setup: rank-2 Drinfeld module over GF(4)
  Fq, a = finite_field(2, 2, "a")
  A, T = polynomial_ring(Fq, "T")
  K, b = finite_field(2, 4, "b")

  # Use a concrete gamma(T) in K
  gamma_T = b^3 + b  # some element of K

  phi = drinfeld_module(A, [gamma_T, one(K), one(K)])

  @testset "Endomorphisms" begin
    R = ore_polynomial_ring(phi)
    tau = gen(R)

    # tau is always an endomorphism of phi (Frobenius endomorphism for n=1 if [K:Fq]=1,
    # but here [K:Fq]=2, so tau is NOT necessarily an endomorphism)
    # The identity is always an endomorphism
    id_morph = drinfeld_module_morphism(phi, phi, one(R))
    @test is_identity(id_morph)
    @test is_isomorphism(id_morph)
    @test is_endomorphism(id_morph)
    @test !is_zero(id_morph)
    @test degree(id_morph) == 0
    @test domain(id_morph) == phi
    @test codomain(id_morph) == phi

    # Zero morphism
    zero_morph = drinfeld_module_morphism(phi, phi, zero(R))
    @test is_zero(zero_morph)
    @test !is_isomorphism(zero_morph)
    @test degree(zero_morph) == -1

    # Composition of identity with itself
    comp = id_morph * id_morph
    @test is_identity(comp)

    # Inverse of identity
    inv_id = inv(id_morph)
    @test is_identity(inv_id)
    @test domain(inv_id) == phi
    @test codomain(inv_id) == phi
  end

  @testset "Isomorphisms" begin
    # An isomorphism is given by u * phi_T * u^{-1} for nonzero u in K
    Fq2, a2 = finite_field(2, 2, "a2")
    A2, T2 = polynomial_ring(Fq2, "T2")
    K2, b2 = finite_field(2, 6, "b2")
    gamma_T2 = b2^2 + b2

    # Rank-1 module: phi_T = gamma_T + tau
    phi1 = drinfeld_module(A2, [gamma_T2, one(K2)])

    # Twist by u: psi_T = u * phi_T * u^{-1}
    # For rank 1: psi_T[1] = u^{1 - q} * phi_T[1]
    u = b2^4 + one(K2)
    q = ZZRingElem(order(Fq2))
    psi_coeffs = [gamma_T2, u^(1 - q)]  # isomorphic twist
    psi1 = drinfeld_module(A2, psi_coeffs)

    R2 = ore_polynomial_ring(phi1)
    f = R2(u)
    m = drinfeld_module_morphism(phi1, psi1, f)
    @test is_isomorphism(m)
    @test domain(m) == phi1
    @test codomain(m) == psi1

    # Inverse
    m_inv = inv(m)
    @test is_isomorphism(m_inv)
    @test domain(m_inv) == psi1
    @test codomain(m_inv) == phi1
  end

  @testset "Equality and hash" begin
    R = ore_polynomial_ring(phi)
    m1 = drinfeld_module_morphism(phi, phi, one(R))
    m2 = drinfeld_module_morphism(phi, phi, one(R))
    @test m1 == m2
    @test hash(m1) == hash(m2)
  end

  @testset "hom convenience" begin
    R = ore_polynomial_ring(phi)
    m = hom(phi, one(R))
    @test is_identity(m)
    @test domain(m) == phi
    @test codomain(m) == phi
  end
end
