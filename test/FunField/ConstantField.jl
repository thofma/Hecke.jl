function test_constant_field_embedding(F, elts)
  K, phi = constant_field(F)
  @test domain(phi) === K
  @test codomain(phi) === F
  for a in elts, b in elts
    @test phi(a + b) == phi(a) + phi(b)
    @test phi(a * b) == phi(a) * phi(b)
  end
  for a in elts
    @test preimage(phi, phi(a)) == a
  end
  @test_throws ArgumentError preimage(phi, gen(F) + F(gen(base_field(F))))
end

@testset "Exact constant field" begin
  @testset "Geometrically irreducible" begin
    k = GF(5)
    kx, x = rational_function_field(k, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    F, a = function_field(y^2 - x^3 - x - 1; cached = false)

    @test constant_field_degree(F) == 1
    K, phi = constant_field(F)
    @test K === k
    @test phi(k(3)) == F(3)
    @test preimage(phi, F(3)) == k(3)
    @test_throws ArgumentError preimage(phi, a)
    @test genus(F) == 1
  end

  @testset "Constant field extension, genus 0" begin
    # F = F_5(x)(sqrt(2)) = F_25(x)
    k = GF(5)
    kx, x = rational_function_field(k, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    F, a = function_field(y^2 - 2; cached = false)

    @test constant_field_degree(F) == 2
    @test genus(F) == 0
    K, phi = constant_field(F)
    @test absolute_degree(K) == 2
    test_constant_field_embedding(F, [rand(K) for _ in 1:5])
    @test phi(K(2)) == F(2)
  end

  @testset "Constant field extension, genus 1" begin
    # y^4 = 2 f(x)^2, so (y^2/f)^2 = 2 and F = F_25(x)(sqrt(sqrt(2) f))
    k = GF(5)
    kx, x = rational_function_field(k, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    f = x^3 + x + 1
    F, a = function_field(y^4 - 2*f^2; cached = false)

    @test constant_field_degree(F) == 2
    @test genus(F) == 1
    K, phi = constant_field(F)
    @test absolute_degree(K) == 2
    test_constant_field_embedding(F, [rand(K) for _ in 1:5])
    c = a^2//F(f)
    @test preimage(phi, c)^2 == K(2)
  end

  @testset "Characteristic 0" begin
    kx, x = rational_function_field(QQ, :x; cached = false)
    ky, y = polynomial_ring(kx, :y; cached = false)
    F, a = function_field(y^2 + 1; cached = false)

    @test constant_field_degree(F) == 2
    @test genus(F) == 0
    K, phi = constant_field(F)
    @test degree(K) == 2
    test_constant_field_embedding(F, [K(1), gen(K), 1 + 2*gen(K), gen(K)^2 - 3])
    @test preimage(phi, a)^2 == K(-1)
  end
end
