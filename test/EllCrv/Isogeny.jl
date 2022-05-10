@testset "Isogenies" begin
  K = GF(7)
  E1 = EllipticCurve(K, [1, 2, 3, 4, 5])
  E2 = EllipticCurve(K, [1, 2, 3, 1, 1])
  phi = @inferred isogeny_from_kernel(E1, division_polynomial_univariate(E1,3)[1])
  @test @inferred domain(phi) == E1
  @test @inferred codomain(phi) == E2
  @test is_isomorphic(E1, codomain(phi))
  @test @inferred image(phi, E1([1,1])) == E2([6,2])
  
  K = GF(3)
  E1 = EllipticCurve(K, [1, 0, 1, 1, 0])
  E2 = EllipticCurve(K, [1, 0, 1, 0, 2])
  Kx, x = PolynomialRing(K);
  f = x+2
  phi = @inferred isogeny_from_kernel(E1, f)
  @test @inferred domain(phi) == E1
  @test @inferred codomain(phi) == E2
  @test @inferred is_infinite(image(phi, E1([1,2]))) 
  
  E1 = EllipticCurve([1, 2, 3, 4, 5])
  E2 = EllipticCurve([1, 2, 3, 979//16, 19067//64])
  phi = @inferred isogeny_from_kernel(E1, division_polynomial_univariate(E1,2)[1])
  @test @inferred domain(phi) == E1
  @test @inferred codomain(phi) == E2
  @test is_isomorphic(E1, codomain(phi))
  
  K= GF(2,4)
  a = gen(K)
  E1 = EllipticCurve(K,[a^2,1-a,1,0,a])
  E2 = EllipticCurve(K,[a^2,1-a,1,a^8,1])
  f = division_polynomial_univariate(E1,5)[1]
  phi = @inferred isogeny_from_kernel(E1, f)
  @test @inferred domain(phi) == E1
  @test @inferred codomain(phi) == E2
  @test @inferred image(phi, E1([a^2,a^2])) == E2([1,a^14])
end

