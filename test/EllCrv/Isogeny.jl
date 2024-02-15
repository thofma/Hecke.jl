@testset "Isogenies" begin
  K = GF(7)
  E1 = elliptic_curve(K, [1, 2, 3, 4, 5])
  E2 = elliptic_curve(K, [1, 2, 3, 1, 1])
  phi = @inferred isogeny_from_kernel(E1, division_polynomial_univariate(E1,3)[1])
  @test @inferred domain(phi) == E1
  @test @inferred codomain(phi) == E2
  @test is_isomorphic(E1, codomain(phi))
  @test @inferred image(phi, E1([1,1])) == E2([6,2])
  @test @inferred degree(phi) == 9

  K = GF(3)
  E1 = elliptic_curve(K, [1, 0, 1, 1, 0])
  E2 = elliptic_curve(K, [1, 0, 1, 0, 2])
  Kx, x = polynomial_ring(K);
  f = x+2
  phi = @inferred isogeny_from_kernel(E1, f)
  @test @inferred domain(phi) == E1
  @test @inferred codomain(phi) == E2
  @test @inferred is_infinite(image(phi, E1([1,2])))
  phihat = @inferred dual_isogeny(phi)
  P = points_with_x_coordinate(E1, 0)[1]
  @test (phi * phihat)(P) == 2*P

  f = @inferred identity_isogeny(E1)
  f(P) == P

  E1 = elliptic_curve([1, 2, 3, 4, 5])
  E2 = elliptic_curve([1, 2, 3, 979//16, 19067//64])
  phi = @inferred isogeny_from_kernel(E1, division_polynomial_univariate(E1,2)[1])
  @test @inferred domain(phi) == E1
  @test @inferred codomain(phi) == E2
  @test is_isomorphic(E1, codomain(phi))
  P = points_with_x_coordinate(E1, 1)[1]
  g = @inferred multiplication_by_m_map(E1, 32)
  g(P) == 32*P

  #multiplication by p map in char p
  p = 11
  E = elliptic_curve(GF(p), [1, 1])
  phi = @inferred multiplication_by_m_map(E, p)
  P = points_with_x_coordinate(E, 4)[1]
  @test 11*P == phi(P)

  psi = frobenius_map(E)
  psihat = @inferred dual_of_frobenius(E)
  @test rational_maps(psi * psihat) ==  rational_maps(psihat *psi)
  @test 11*P == (psi*psihat)(P)

  p = 2
  K = GF(2,4)
  a = gen(K)
  E = elliptic_curve_from_j_invariant(a)
  phi = @inferred multiplication_by_m_map(E, p)
  P = points_with_x_coordinate(E, a^2)[1]
  @test 2*P == phi(P)

  K = GF(2,6)
  a = gen(K)
  E = elliptic_curve_from_j_invariant(zero(K))
  phi = @inferred multiplication_by_m_map(E, p)
  P = points_with_x_coordinate(E, a^3)[1]
  @test 2*P == phi(P)


  K= GF(2,4)
  a = gen(K)
  E1 = elliptic_curve(K,[a^2,1-a,1,0,a])
  E2 = elliptic_curve(K,[a^2,1-a,1,a^8,1])
  f = division_polynomial_univariate(E1,5)[1]
  phi = @inferred isogeny_from_kernel(E1, f)
  @test @inferred domain(phi) == E1
  @test @inferred codomain(phi) == E2
  @test @inferred image(phi, E1([a^2,a^2])) == E2([1,a^14])

  K = GF(13,2)
  E = elliptic_curve_from_j_invariant(K(2))
  div30 = division_polynomial_univariate(E,30)[1]
  L = isogeny_from_kernel_factored(E,div30)
  P = points_with_x_coordinate(E, 1)[1]
  image(L, P)

  f = @inferred frobenius_map(E)
  Kx, x = polynomial_ring(base_field(E),"x")
  @test isogeny_map_phi(f) == x^13
  f(f(P)) == P

  # is_kernel_polynomial
  E = elliptic_curve([0, -1, 1, -10, -20])
  Qx, x = QQ["x"]
  @test (@inferred is_kernel_polynomial(E, x^2 + x - 29//5))
  @test (@inferred is_kernel_polynomial(E, (x - 16) * (x - 5)))
  @test !is_kernel_polynomial(E, x)

  # An example from
  # K. Tsukazaki, Explicit Isogenies of Elliptic Curves, PhD thesis, University of Warwick, 2013
  # where the 13-division polynomial splits into 14 factors each of degree 6,
  # but only two of these are a kernel polynomial for a 13-isogeny::
  F = GF(3, 1)
  E = elliptic_curve(F, [0, 0, 0, -1, 0])
  Fx, x = F["x"]
  @test is_kernel_polynomial(E, x + 2)
  f13, = division_polynomial_univariate(E, 13)
  factors = [f for (f, e) in factor(f13)]
  @test all(g -> degree(g) == 6, factors)
  kp = [is_kernel_polynomial(E, f) for f in factors]
  count(kp) == 2

  phi5 = multiplication_by_m_map(E, 5)
  h = x^6 + x^4 + 2*x^3 + x^2 + x + 2
  pi = isogeny_from_kernel(E, h)

  kerpol = isogeny_map_psi(phi5*pi)

  #Composition is seen as a valid kernel polynomial
  @test is_kernel_polynomial(E, kerpol)


  @test !is_cyclic_kernel_polynomial(E, kerpol)

  E = elliptic_curve(F, [0, 1, 1, 1, 1])
  @test is_kernel_polynomial(E, x + 1)

  F, o = finite_field(47, 2, "o")
  E = elliptic_curve(F, [0, o])
  Fx, x = F["x"]
  f = x^3 + (7*o + 11)*x^2 + (25*o + 33)*x + 25*o
  @test !is_kernel_polynomial(E, f)
  @test is_kernel_polynomial(E, x^0)
  @test !is_kernel_polynomial(E, f^2)

  #Example from https://trac.sagemath.org/ticket/32484
  E = elliptic_curve(GF(71, 2), [0,1])
  R, x = polynomial_ring(base_field(E), "x")
  h = x^4 + 26*x^3 + 61*x^2 + 4*x + 19
  @test !is_kernel_polynomial(E, h)

end
