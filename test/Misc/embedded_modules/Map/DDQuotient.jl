@testset "Dedekind quotient maps" begin
  function test_dedekind_quotient(R, K, I, c)
    U = one(K)*R
    i = first(basis(I))
    a = K(last(basis(R)))

    # Use a larger ambient space to exercise the change of coordinates.
    M = Hecke.embedded_module(R, K, Hecke.pseudo_matrix(R, K[1 0 0; 0 1 1], [I, U]))
    N = Hecke.embedded_module(R, K, Hecke.pseudo_matrix(R, K[c c c; 0 c c; c 0 0], [I, U, I]))
    V, f = quo(M, N)
    m = Hecke._element_from_ambient_coordinates(M, [i, one(K), one(K)])
    @test V isa Hecke.FPModuleDedekind
    @test f isa Hecke.EmbeddedModuleMap
    @test rank(V) == 0
    @test domain(f) === M
    @test codomain(f) === V
    @test kernel(f) === N
    @test image(f) === V
    @test M + N == M
    @test intersect(M, N) == N
    @test is_surjective(f)
    @test !is_injective(f)
    @test !is_bijective(f)
    @test !iszero(f(m))
    @test iszero(f(R(c)*m))
    @test f(R(a)*m + m) == R(a)*f(m) + f(m)
    @test f(preimage(f, f(m))) == f(m)
    @test Hecke.ambient_coordinates(m - preimage(f, f(m))) in N
    V2, g = quo(M, N)
    @test_throws ArgumentError preimage(f, g(m))
    @test_throws ArgumentError f(zero(N))
    @test_throws ArgumentError quo(N, M)
    @test_throws ArgumentError quo(M, Hecke.zero_embedded_module(R, K, 2))
    @test show(IOBuffer(), MIME"text/plain"(), f) === nothing

    ZM = Hecke.zero_embedded_module(R, K, 3)
    for (L, S) in ((M, M), (M, ZM), (ZM, ZM))
      W, q = quo(L, S)
      @test iszero(q(zero(L)))
      @test q(preimage(q, zero(W))) == zero(W)
      @test kernel(q) === S
      @test is_injective(q) == iszero(rank(S))
      @test rank(W) == rank(L) - rank(S)
    end
    W, q = quo(M, ZM)
    @test !iszero(q(m))
    @test preimage(q, q(m)) == m
    @test is_bijective(q)
    @test iszero(quo(M, M)[2](m))

    # A quotient with positive rank.
    L = Hecke.embedded_module(R, K, Hecke.pseudo_matrix(R, K[c 0 0], [I]))
    W, q = quo(M, L)
    @test rank(W) == 1
    @test !iszero(R(c)*q(m))
    @test q(preimage(q, q(m))) == q(m)
  end

  @testset "number field orders" begin
    K, a = quadratic_field(-5)
    R = maximal_order(K)
    I = fractional_ideal(R, ideal(R, 2, R(1 + a)))
    test_dedekind_quotient(R, K, I, K(2))

    _, t = polynomial_ring(QQ, :t)
    for polys in ([t^2 + 5], [t^2 + 5, t^2 + 7])
      K, a = number_field(polys)
      R = maximal_order(K)
      I = fractional_ideal(R, ideal(R, 2, R(1 + a[1])))
      test_dedekind_quotient(R, K, I, K(2))
    end
  end

  @testset "function field orders" begin
    for k in (GF(5), QQ)
      kt, t = rational_function_field(k, :t; cached = false)
      K, a = function_field(polynomial(kt, [-t^3 - t - 1, 0, 1]); cached = false)
      R = finite_maximal_order(K)
      I = fractional_ideal(ideal(R, t, R(a - 1)))
      test_dedekind_quotient(R, K, I, K(t))

      Rinf = infinite_maximal_order(K)
      Iinf = K(1//t)*Rinf
      test_dedekind_quotient(Rinf, K, Iinf, K(1//t))
    end
  end
end
