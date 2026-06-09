@testset "DrinfeldModule" begin
  # Example: rank-2 Drinfeld module over F_25
  Fq, a = finite_field(5, 2, "a")
  A, T = polynomial_ring(Fq, "T")

  # Coefficients: [gamma(T), Delta_1, Delta_2] where Delta_2 != 0
  phi = drinfeld_module(A, [a, zero(Fq), one(Fq)])

  @test rank(phi) == 2
  @test function_ring(phi) === A
  @test base_ring(phi) === Fq
  @test constant_coefficient(phi) == a
  @test coefficient(phi, 0) == a
  @test coefficient(phi, 1) == zero(Fq)
  @test coefficient(phi, 2) == one(Fq)
  @test coefficients(phi) == [a, zero(Fq), one(Fq)]

  # Ore polynomial ring
  R = ore_polynomial_ring(phi)
  @test base_ring(R) === Fq

  # Evaluate phi at T: should give phi_T
  @test evaluate(phi, T) == gen(phi)

  # Evaluate phi at 1: should give the identity (constant 1 in K{tau})
  @test evaluate(phi, one(A)) == one(R)

  # Evaluate phi at 0
  @test evaluate(phi, zero(A)) == zero(R)

  # j_invariant for rank 2: Delta_1^{q+1} / Delta_2
  # Here Delta_1 = 0, so j = 0
  @test j_invariant(phi) == zero(Fq)

  # Another rank-2 example with nonzero Delta_1
  psi = drinfeld_module(A, [a, one(Fq), one(Fq)])
  q = ZZRingElem(order(Fq))
  @test j_invariant(psi) == one(Fq)^(q + 1) * inv(one(Fq))

  # jk_invariants for rank 2
  jk = jk_invariants(psi)
  @test haskey(jk, 1)
  @test jk[1] == j_invariant(psi)

  # Equality
  @test phi == phi
  @test phi != psi

  # Characteristic: gamma(T) = a, so characteristic = minpoly of a over Fq
  # But Fq itself, so minpoly of a over Fq = T - a (degree 1)
  chi = characteristic(phi)
  @test parent(chi) === A
  @test degree(chi) == 1  # a is in Fq = F_25, so [F_q(a) : F_q] = 1
  # phi_chi is generally nonzero; its tau-adic valuation is the height
  @test !iszero(evaluate(phi, chi))

  # Height: for prime characteristic (degree 1), height in 1..rank
  h = height(phi)
  @test 1 <= h <= rank(phi)

  # Velu isogeny: f = tau is a valid isogeny kernel for a suitable phi
  # Use a rank-1 module phi_T = gamma + tau (always has a trivial isogeny)
  phi1 = drinfeld_module(A, [a, one(Fq)])
  R1 = ore_polynomial_ring(phi1)
  _, tau1 = ore_polynomial_ring(Fq, ZZRingElem(order(Fq)))
  # The isogeny f = 1 (identity) should give an isomorphic module
  f_id = one(R1)
  psi1 = velu(phi1, f_id)
  @test psi1 == phi1

  # is_isomorphic: a module is isomorphic to itself
  @test is_isomorphic(phi, phi)
  @test is_isomorphic(psi, psi)
  # phi and psi differ in coefficient 1, check non-isomorphic case
  # (they may or may not be isomorphic depending on the field)
end
