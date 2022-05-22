@testset "Isogenies" begin
  K = GF(7)
  E1 = EllipticCurve(K, [1, 2, 3, 4, 5])
  E2 = EllipticCurve(K, [1, 2, 3, 1, 1])
  phi = @inferred isogeny_from_kernel(E1, division_polynomial_univariate(E1,3)[1])
  @test @inferred domain(phi) == E1
  @test @inferred codomain(phi) == E2
  @test is_isomorphic(E1, codomain(phi))
  @test @inferred image(phi, E1([1,1])) == E2([6,2])
  @test @inferred degree(phi) == 9
  
  K = GF(3)
  E1 = EllipticCurve(K, [1, 0, 1, 1, 0])
  E2 = EllipticCurve(K, [1, 0, 1, 0, 2])
  Kx, x = PolynomialRing(K);
  f = x+2
  phi = @inferred isogeny_from_kernel(E1, f)
  @test @inferred domain(phi) == E1
  @test @inferred codomain(phi) == E2
  @test @inferred is_infinite(image(phi, E1([1,2]))) 
  phihat = @inferred dual_isogeny(phi)
  P = points_with_x(E1, 0)[1]
  @test (phi * phihat)(P) == 2*P || (phi * phihat)(P) == -2*P 
  
  f = @inferred identity_isogeny(E1)
  f(P) == P
  
  E1 = EllipticCurve([1, 2, 3, 4, 5])
  E2 = EllipticCurve([1, 2, 3, 979//16, 19067//64])
  phi = @inferred isogeny_from_kernel(E1, division_polynomial_univariate(E1,2)[1])
  @test @inferred domain(phi) == E1
  @test @inferred codomain(phi) == E2
  @test is_isomorphic(E1, codomain(phi))
  P = points_with_x(E1, 1)[1]
  g = @inferred multiplication_by_m_map(E1, 32)
  g(P) == 32*P
  
  #multiplication by p map in char p
  p = 11
  E = EllipticCurve(GF(p), [1, 1])
  phi = @inferred multiplication_by_m_map(E, p)
  P = points_with_x(E, 4)[1]
  @test 11*P == phi(P)
  
  p = 2
  K = GF(2,4)
  a = gen(K)
  E = elliptic_curve_from_j_invariant(a)
  phi = @inferred multiplication_by_m_map(E, p)
  P = points_with_x(E, a^2)[1]
  @test 2*P == phi(P)
  
  K = GF(2,6)
  a = gen(K)
  E = elliptic_curve_from_j_invariant(zero(K))
  phi = @inferred multiplication_by_m_map(E, p)
  P = points_with_x(E, a^3)[1]
  @test 2*P == phi(P)
  
  
  K= GF(2,4)
  a = gen(K)
  E1 = EllipticCurve(K,[a^2,1-a,1,0,a])
  E2 = EllipticCurve(K,[a^2,1-a,1,a^8,1])
  f = division_polynomial_univariate(E1,5)[1]
  phi = @inferred isogeny_from_kernel(E1, f)
  @test @inferred domain(phi) == E1
  @test @inferred codomain(phi) == E2
  @test @inferred image(phi, E1([a^2,a^2])) == E2([1,a^14])
  
  K = GF(13,2)
  E = elliptic_curve_from_j_invariant(K(2))
  div30 = division_polynomial_univariate(E,30)[1]
  L = isogeny_from_kernel_factored(E,div30)
  P = points_with_x(E, 1)[1]
  image(L, P)
  
  f = @inferred frobenius_map(E)
  Kx, x = PolynomialRing(base_field(E),"x")
  @test isogeny_map_phi(f) == x^13
  f(f(P)) == P

  # is_kernel_polynomial
  E = EllipticCurve([0, -1, 1, -10, -20])
  Qx, x = QQ["x"]
  @test (@inferred is_kernel_polynomial(E, 5, x^2 + x - 29//5))
  @test (@inferred is_kernel_polynomial(E, 5, (x - 16) * (x - 5)))
  @test !is_kernel_polynomial(E, 3, x)

  # An example from
  # K. Tsukazaki, Explicit Isogenies of Elliptic Curves, PhD thesis, University of Warwick, 2013
  # where the 13-division polynomial splits into 14 factors each of degree 6,
  # but only two of these is a kernel polynomial for a 13-isogeny::
  F = GF(3, 1)
  E = EllipticCurve(F, [0, 0, 0, -1, 0])
  Fx, x = F["x"]
  @test is_kernel_polynomial(E, 2, x + 2)
  f13, = division_polynomial_univariate(E, 13)
  factors = [f for (f, e) in factor(f13)]
  @show degree.(factors)
  @test all(g -> degree(g) == 6, factors)
  kp = [is_kernel_polynomial(E, 13, f) for f in factors]
  count(kp) == 2
  
  E = EllipticCurve(F, [0, 1, 1, 1, 1])
  @test is_kernel_polynomial(E, 3, x + 1)

  F, o = FiniteField(47, 2, "o")
  E = EllipticCurve(F, [0, o])
  Fx, x = F["x"]
  f = x^3 + (7*o + 11)*x^2 + (25*o + 33)*x + 25*o
  @test !is_kernel_polynomial(E, 7, f)
  @test is_kernel_polynomial(E, 1, x^0)
  @test !is_kernel_polynomial(E, 7, f^2)

  @test_throws ArgumentError is_kernel_polynomial(E, 7, QQ["y"][2])
end
