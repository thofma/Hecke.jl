@testset "inclusion maps" begin
  inclusion_map = Hecke.EmbeddedModules.inclusion_map
  ambient = nothing
  M = Hecke.embedded_module(ZZ, QQ, QQ[1//2 0 0; 0 3 0];
                           overstructure = ambient)
  N = Hecke.embedded_module(ZZ, QQ, QQ[2 0 0]; overstructure = ambient)
  f = (@inferred inclusion_map(N, M))
  x = Hecke._element_from_coordinates(N, ZZRingElem[3])
  y = f(x)

  @test domain(f) === N
  @test codomain(f) === M
  @test parent(y) === M
  @test coordinates(y) == ZZRingElem[12, 0]
  @test Hecke.ambient_coordinates(y) == Hecke.ambient_coordinates(x)
  @test Hecke.ambient_coordinates(y) !== Hecke.ambient_coordinates(x)
  z = (@inferred preimage(f, y))
  @test parent(z) === N
  @test z == x
  @test Hecke.ambient_coordinates(z) !== Hecke.ambient_coordinates(y)
  @test (@inferred image(f)) === N
  Z = @inferred kernel(f)
  @test rank(Z) == 0
  @test Hecke.ambient_rank(Z) == 3
  @test Hecke.overstructure(Z) === ambient
  @test (@inferred is_injective(f))
  @test !(@inferred is_surjective(f))
  @test !(@inferred is_bijective(f))
  @test occursin("defined by", sprint(show, MIME"text/plain"(), f))
  @test occursin(" -> ", sprint(show, MIME"text/plain"(), f))

  @test_throws ArgumentError preimage(f, basis(M)[1])
  @test_throws ArgumentError preimage(f, basis(M)[2])
  @test_throws ArgumentError f(basis(M)[1])
  @test_throws ArgumentError preimage(f, x)
  @test_throws ArgumentError inclusion_map(M, N)
  different_dimension = Hecke.embedded_module(ZZ, QQ, QQ[2 0];
                                              overstructure = ambient)
  @test_throws ArgumentError inclusion_map(different_dimension, M)

  # Equal modules can use different bases and still give a bijective inclusion.
  P = Hecke.embedded_module(ZZ, QQ, QQ[1//2 3 0; 0 3 0];
                           overstructure = ambient, is_basis_matrix = true)
  g = inclusion_map(P, M)
  p = basis(P)[1]
  @test coordinates(g(p)) == ZZRingElem[1, 1]
  @test preimage(g, g(p)) == p
  @test is_surjective(g)
  @test is_bijective(g)
  @test is_bijective(inclusion_map(M, M))

  from_zero = inclusion_map(Z, M)
  @test image(from_zero) === Z
  @test kernel(from_zero) == Z
  @test iszero(from_zero(zero(Z)))
  @test iszero(preimage(from_zero, zero(M)))
  @test_throws ArgumentError preimage(from_zero, basis(M)[1])
  @test is_injective(from_zero)
  @test !is_surjective(from_zero)
  @test is_bijective(inclusion_map(Z, Z))
  @test occursin("rank 0", sprint(show, MIME"text/plain"(), from_zero))
end

@testset "inclusions over function field PIDs" begin
  inclusion_map = Hecke.EmbeddedModules.inclusion_map
  K, x = rational_function_field(QQ, "x")
  for (R, t) in ((parent(numerator(x)), x), (localization(K, degree), inv(x)))
    M = Hecke.embedded_module(R, K, identity_matrix(K, 2))
    N = Hecke.embedded_module(R, K, K[t 0])
    f = inclusion_map(N, M)
    b = basis(N)[1]
    @test parent(f(b)) === M
    @test Hecke.ambient_coordinates(f(b)) == typeof(x)[t, K(0)]
    @test preimage(f, f(b)) == b
    @test_throws ArgumentError preimage(f, basis(M)[1])
    @test_throws ArgumentError preimage(f, basis(M)[2])
    @test image(f) === N
    @test rank(kernel(f)) == 0
    @test is_injective(f)
    @test !is_surjective(f)
    @test !is_bijective(f)
  end
end

@testset "inclusions over Dedekind domains" begin
  inclusion_map = Hecke.EmbeddedModules.inclusion_map
  K, = quadratic_field(5)
  O = maximal_order(K)
  I = fractional_ideal(O, O(2))
  J = fractional_ideal(O, one(O))
  ambient = nothing
  M = Hecke.embedded_module(O, K,
                            pseudo_matrix(O, identity_matrix(K, 2), [J, J]);
                            overstructure = ambient, is_basis_matrix = true)
  N = Hecke.embedded_module(O, K, pseudo_matrix(O, K[1 0], [I]);
                            overstructure = ambient, is_basis_matrix = true)
  f = inclusion_map(N, M)
  x = Hecke._element_from_ambient_coordinates(N, elem_type(K)[K(2), K(0)];
                                             check = false)
  y = f(x)
  @test parent(y) === M
  @test Hecke.ambient_coordinates(y) == Hecke.ambient_coordinates(x)
  @test preimage(f, y) == x
  for v in (elem_type(K)[K(1), K(0)], elem_type(K)[K(0), K(1)])
    z = Hecke._element_from_ambient_coordinates(M, v; check = false)
    @test_throws ArgumentError preimage(f, z)
  end
  @test image(f) === N
  Z = kernel(f)
  @test rank(Z) == 0
  @test Hecke.ambient_rank(Z) == 2
  @test Hecke.overstructure(Z) === ambient
  @test is_injective(f)
  @test !is_surjective(f)
  @test !is_bijective(f)
  @test is_bijective(inclusion_map(M, M))
  from_zero = inclusion_map(Z, M)
  @test iszero(from_zero(zero(Z)))
  @test iszero(preimage(from_zero, zero(M)))
  @test is_bijective(inclusion_map(Z, Z))
  @test occursin("Homomorphism of embedded modules", sprint(show, MIME"text/plain"(), f))
  @test show(IOBuffer(), MIME"text/plain"(), f) === nothing
end
