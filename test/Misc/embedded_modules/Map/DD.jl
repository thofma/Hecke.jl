# Dedekind matrix maps retain coefficient ideals when lifting and composing.
@testset "Dedekind matrix maps" begin
  function test_dedekind_matrix_maps(R, K, I, c)
    U = fractional_ideal(ideal(R, one(R)))
    J = inv(c)*I
    scalar = K(last(basis(R)))
    B = K[inv(c) 0 0; scalar 1 0]
    M = Hecke.embedded_module(R, K, pseudo_matrix(R, B, [J, U]);
                             is_basis_matrix = true)
    N = Hecke.embedded_module(R, K, K[1 1 0]; is_basis_matrix = true)
    f = @inferred Hecke.EmbeddedModules._hom(M, N, K[c; 1;;])
    b = K(first(basis(J)))
    x = Hecke._element_from_coordinates(M, elem_type(K)[b, one(K)])
    y = Hecke._element_from_coordinates(N, elem_type(K)[one(K)])
    z = @inferred preimage(f, y)
    @test f(z) == y
    @test Hecke.ambient_coordinates(z) in M
    @test coordinates(z)[1] in J && coordinates(z)[2] in U
    @test f(x + z) == f(x) + y
    @test f(R(c)*x) == R(c)*f(x)
    A = K[c^2 c^2 0; 1 - scalar*c^2 1 - scalar*c^2 0; 0 0 0]
    ff = @inferred Hecke._hom_from_ambient_matrix(M, N, A)
    @test ff(x) == f(x)
    @test image(f) == N
    @test !is_injective(f) && is_surjective(f) && !is_bijective(f)
    L = Hecke.embedded_module(R, K,
          pseudo_matrix(R, K[1 -c]*B, [J]))
    @test kernel(f) == L
    k = Hecke._element_from_coordinates(M, elem_type(K)[b, -c*b])
    @test iszero(f(k))
    @test Hecke.ambient_coordinates(k) in kernel(f)
    @test_throws ArgumentError f(y)
    @test_throws ArgumentError preimage(f, x)
    @test_throws ArgumentError Hecke.EmbeddedModules._hom(M, N, K[1;;])
    @test_throws ArgumentError Hecke.EmbeddedModules._hom(M, N,
                                                         K[0; inv(c);;])
    @test sprint(show, MIME"text/plain"(), f) isa String

    g = Hecke.EmbeddedModules._hom(N, N, K[c;;])
    h = @inferred compose(f, g)
    @test h(x) == g(f(x))
    @test h(preimage(h, h(x))) == h(x)
    @test_throws ArgumentError preimage(h, y)
    @test !is_surjective(h)
    @test kernel(h) == kernel(f)
    P = @inferred preimage(f, image(g))
    expected = Hecke.embedded_module(R, K,
      pseudo_matrix(R, K[1 -c; 0 c]*B, [J, U]))
    @test P == expected
    @test preimage(f, N) == M
    @test preimage(f, Hecke.zero_embedded_module(R, K, 3)) == kernel(f)
    hh, pM, pN = Hecke.addition_map(f, g)
    zz = preimage(hh, y)
    @test f(pM(zz)) + g(pN(zz)) == y
    @test_throws ArgumentError Hecke.addition_map(f,
      Hecke.EmbeddedModules.inclusion_map(M, M))
    inclusion = Hecke.EmbeddedModules.inclusion_map(N, N)
    @test compose(f, inclusion)(x) == f(x)
    @test compose(inclusion, g)(y) == g(y)

    S = Hecke.embedded_module(R, K,
          pseudo_matrix(R, K[1 1 0], [I]); is_basis_matrix = true)
    j = Hecke.EmbeddedModules._hom(S, N, K[1;;])
    @test is_injective(j) && !is_surjective(j)
    @test_throws ArgumentError preimage(j, y)
    @test iszero(preimage(j, zero(N)))
    @test image(j) == S

    Z = Hecke.zero_embedded_module(R, K, 3)
    for D in (M, Z), C in (N, Z)
      q = Hecke.EmbeddedModules._hom(D, C,
                                    zero_matrix(K, rank(D), rank(C)))
      @test iszero(q(zero(D)))
      @test iszero(preimage(q, zero(C)))
      @test kernel(q) == D
      @test iszero(rank(image(q)))
      @test is_injective(q) == iszero(rank(D))
      @test is_surjective(q) == iszero(rank(C))
      @test is_bijective(q) == (iszero(rank(D)) && iszero(rank(C)))
      !iszero(rank(C)) && (@test_throws ArgumentError preimage(q, y))
    end
  end

  K, a = quadratic_field(-5)
  R = maximal_order(K)
  I = fractional_ideal(R, ideal(R, 2, R(1 + a)))
  @test !is_principal(numerator(I))
  test_dedekind_matrix_maps(R, K, I, K(2))
  R = maximal_order(Hecke.GenOrd(ZZ, K))
  I = fractional_ideal(first(prime_decomposition(R, ZZ(2)))[1])
  test_dedekind_matrix_maps(R, K, I, K(2))

  kt, t = rational_function_field(GF(5), :t; cached = false)
  K, a = function_field(polynomial(kt, [-t^3 - t - 1, 0, 1]);
                         cached = false)
  R = finite_maximal_order(K)
  I = fractional_ideal(ideal(R, t, R(a - 1)))
  test_dedekind_matrix_maps(R, K, I, K(t))
  R = infinite_maximal_order(K)
  I = K(inv(t))*fractional_ideal(ideal(R, one(R)))
  test_dedekind_matrix_maps(R, K, I, K(inv(t)))
end
