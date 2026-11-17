@testset "Dedekind domain reduction" begin
  K, a = quadratic_field(-5)
  O = maximal_order(K)
  I = fractional_ideal(O, ideal(O, 2, O(1 + a)))
  @test !is_principal(numerator(I))
  ambient = nothing

  # Include ramified, split, and inert primes. At split primes some normalized
  # coordinates are locally integral despite their denominators lying in p.
  primes = [first(prime_decomposition(O, q))[1] for q in (2, 3, 11)]
  for p in primes
    ideals = [inv(K(2))*I, inv(K(3))*fractional_ideal(p)]
    B = K[1//6 0 0; a 3 0]
    M = Hecke.embedded_module(O, K, pseudo_matrix(O, B, ideals);
                             overstructure = ambient, is_basis_matrix = true)
    result = Hecke.quotient_vector_space(M, p)
    @test length(result) == 2
    V, f = result
    OtoF = Hecke.ring_map(f)
    F = base_ring(V)
    @test f isa Hecke.EmbeddedModuleMap
    @test domain(f) === M
    @test codomain(f) === V
    @test domain(OtoF) === O
    @test codomain(OtoF) === F
    @test dim(V) == rank(M) == 2
    @test order(F) == norm(p)
    @test image(f) === V
    @test !is_injective(f)
    @test is_surjective(f)
    @test !is_bijective(f)

    N = kernel(f)
    @test N == Hecke.embedded_module(O, K, p * pseudo_matrix(O, B, ideals);
                                    overstructure = ambient)
    @test rank(N) == rank(M)
    @test Hecke.ambient_rank(N) == 3
    @test Hecke.overstructure(N) === ambient
    @test issubset(N, M)

    # Test every Z-basis generator of each ideal, not only a local basis.
    generators = elem_type(M)[]
    for i in 1:2, c in basis(ideals[i])
      v = Hecke.zeros_array(K, 2)
      v[i] = c
      x = Hecke._element_from_coordinates(M, v)
      push!(generators, x)
      @test Hecke.ambient_coordinates(x - preimage(f, f(x))) in N
      for t in basis(p)
        @test iszero(f(t*x))
      end
      for t in basis(O)
        @test f(t*x) == OtoF(t)*f(x)
      end
      y = Hecke._element_from_ambient_coordinates(M, Hecke.ambient_coordinates(x))
      @test f(y) == f(x)
    end
    @test f(sum(generators)) == sum(f(x) for x in generators)

    for c in (zero(F), one(F), gen(F))
      y = V([c, one(F)])
      x = preimage(f, y)
      @test parent(x) === M
      @test all(i -> coordinates(x)[i] in ideals[i], 1:2)
      @test Hecke.ambient_coordinates(x) in M
      @test f(x) == y
    end
    @test iszero(preimage(f, zero(V)))
    W, g = Hecke.quotient_vector_space(M, N, p)
    @test dim(W) == dim(V)
    @test all(f(preimage(g, g(x))) == f(x) for x in generators)
    @test kernel(g) === N
    @test_throws ArgumentError f(zero(N))
    @test_throws ArgumentError preimage(f, zero(W))
    @test_throws ArgumentError preimage(f, zero(M))
    @test occursin("Homomorphism of embedded modules", sprint(show, MIME"text/plain"(), f))
    @test show(IOBuffer(), f) === nothing
  end
end

@testset "Generic number field order reduction" begin
  K, a = quadratic_field(-5)
  O = Hecke.maximal_order(Hecke.GenOrd(ZZ, K))
  p = first(prime_decomposition(O, ZZ(3)))[1]
  J = inv(K(3))*fractional_ideal(p)
  M = Hecke.embedded_module(O, K, pseudo_matrix(O, identity_matrix(K, 2), [J, J]))
  N = Hecke.embedded_module(O, K, pseudo_matrix(O, K[1 1; 0 1], [J, p*J]))
  V, f = Hecke.quotient_vector_space(M, p)
  OtoF = Hecke.ring_map(f)
  W, g = Hecke.quotient_vector_space(M, N, p)
  @test dim(V) == 2
  @test dim(W) == 1
  @test order(base_ring(V)) == 3
  @test kernel(g) === N
  for (U, h) in ((V, f), (W, g))
    y = U([1 for _ in 1:dim(U)])
    x = preimage(h, y)
    @test Hecke.ambient_coordinates(x) in M
    @test h(x) == y
  end
  for c in basis(J)
    x = Hecke._element_from_coordinates(M, elem_type(K)[c, zero(K)])
    @test f(O(a)*x) == OtoF(O(a))*f(x)
    @test Hecke.ambient_coordinates(x - preimage(f, f(x))) in kernel(f)
  end
end

@testset "Dedekind domain reduction by a submodule" begin
  K, a = quadratic_field(-5)
  O = maximal_order(K)
  I = inv(K(2))*fractional_ideal(O, ideal(O, 2, O(1 + a)))
  B = K[1//2 0 0; a 1 0]
  ambient = nothing
  M = Hecke.embedded_module(O, K, pseudo_matrix(O, B, [I, I]);
                           overstructure = ambient, is_basis_matrix = true)
  for q in (2, 3, 11)
    p = first(prime_decomposition(O, q))[1]
    # N = I*(b1 + b2) + p*I*b2, so M/N is one-dimensional.
    C = K[1 1; 0 1]*B
    N = Hecke.embedded_module(O, K, pseudo_matrix(O, C, [I, p*I]);
                             overstructure = ambient)
    result = Hecke.quotient_vector_space(M, N, p)
    @test length(result) == 2
    V, f = result
    OtoF = Hecke.ring_map(f)
    F = base_ring(V)
    @test dim(V) == 1
    @test kernel(f) === N
    @test image(f) === V
    @test !is_injective(f)
    @test is_surjective(f)
    @test !is_bijective(f)
    @test any(!iszero(f(Hecke._element_from_coordinates(M, elem_type(K)[c, zero(K)])))
              for c in basis(I))
    for c in basis(I)
      x = Hecke._element_from_coordinates(M, elem_type(K)[c, zero(K)])
      y = Hecke._element_from_coordinates(M, elem_type(K)[zero(K), c])
      @test iszero(f(x + y))
      @test f(x) == -f(y)
      @test Hecke.ambient_coordinates(x - preimage(f, f(x))) in N
      for t in basis(O)
        @test f(t*x) == OtoF(t)*f(x)
      end
    end
    for c in (zero(F), one(F), gen(F))
      y = V([c])
      x = preimage(f, y)
      @test parent(x) === M
      @test Hecke.ambient_coordinates(x) in M
      @test f(x) == y
    end

    # Both zero-dimensional quotients and zero modules retain their ambient data.
    for L in (M, Hecke.zero_embedded_module(O, K, 3))
      W, g = Hecke.quotient_vector_space(L, L, p)
      @test dim(W) == 0
      @test iszero(g(zero(L)))
      @test iszero(preimage(g, zero(W)))
      @test kernel(g) === L
      @test is_surjective(g)
      @test is_injective(g) == iszero(rank(L))
      @test is_bijective(g) == iszero(rank(L))
    end
    Z = Hecke.zero_embedded_module(O, K, 3)
    W, g = Hecke.quotient_vector_space(Z, p)
    @test dim(W) == 0
    @test iszero(g(zero(Z)))
    @test iszero(preimage(g, zero(W)))
    @test kernel(g) == Z
    @test Hecke.ambient_rank(kernel(g)) == 3
    @test is_bijective(g)
  end
end

@testset "Dedekind reduction with nonconsecutive pivots" begin
  K, _ = quadratic_field(-5)
  O = maximal_order(K)
  p = first(prime_decomposition(O, 3))[1]
  U = fractional_ideal(ideal(O, one(O)))
  B = identity_matrix(K, 4)
  M = Hecke.embedded_module(O, K, B)
  # The relation rows have pivots in columns 2 and 4.
  C = K[0 0 0 1; 0 1 1 0; 1 0 0 0; 0 0 1 0]
  N = Hecke.embedded_module(O, K, pseudo_matrix(O, C, [U, U, p*U, p*U]))
  V, f = Hecke.quotient_vector_space(M, N, p)
  @test dim(V) == 2
  @test kernel(f) === N
  for i in 1:2
    @test iszero(f(Hecke._element_from_coordinates(M, C[i, :])))
  end
  for i in 1:4
    x = Hecke._element_from_coordinates(M, B[i, :])
    @test Hecke.ambient_coordinates(x - preimage(f, f(x))) in N
  end
  for y in (V([1, 0]), V([0, 1]))
    @test f(preimage(f, y)) == y
  end
end

@testset "Dedekind reduction at an index divisor" begin
  K, a = quadratic_field(5)
  O = maximal_order(K)
  p = first(prime_decomposition(O, 2))[1]
  @test Hecke.is_index_divisor(O, ZZ(2))
  M = Hecke.embedded_module(O, K, K[1//2 0; 0 3])
  V, f = Hecke.quotient_vector_space(M, p)
  OtoF = Hecke.ring_map(f)
  F = base_ring(V)
  @test dim(V) == 2
  @test order(F) == 4
  y = V([gen(F), one(F)])
  x = preimage(f, y)
  @test Hecke.ambient_coordinates(x) in M
  @test f(x) == y
  @test f(O((1 + a)//2)*x) == OtoF(O((1 + a)//2))*y
end

@testset "Dedekind domain reduction validation" begin
  K, a = quadratic_field(-5)
  O = maximal_order(K)
  M = Hecke.embedded_module(O, K, identity_matrix(K, 2))
  p = first(prime_decomposition(O, 2))[1]
  for bad in (ideal(O, 0), ideal(O, 1), p^2)
    @test_throws ArgumentError Hecke.quotient_vector_space(M, bad)
    @test_throws ArgumentError Hecke.quotient_vector_space(M, M, bad)
  end
  O2 = maximal_order(quadratic_field(-1)[1])
  p2 = first(prime_decomposition(O2, 2))[1]
  @test_throws ArgumentError Hecke.quotient_vector_space(M, p2)

  line = Hecke.embedded_module(O, K, K[1 0])
  higher = Hecke.embedded_module(O, K, p^2 * Hecke.basis_matrix(M))
  larger = Hecke.embedded_module(O, K, K[1//2 0; 0 1])
  incompatible = Hecke.embedded_module(O, K, identity_matrix(K, 3))
  for N in (line, higher, larger, incompatible)
    @test_throws ArgumentError Hecke.quotient_vector_space(M, N, p)
  end
end

@testset "Function field Dedekind domain reduction" begin
  function test_function_field_reduction(O, p, J, B)
    K = Hecke.field(O)
    ambient = nothing
    @test Hecke._ring_type(O) === Hecke._DD
    M = Hecke.embedded_module(O, K, pseudo_matrix(O, B, [J, J]);
                             overstructure = ambient, is_basis_matrix = true)
    N = Hecke.embedded_module(O, K, pseudo_matrix(O, K[1 1; 0 1]*B, [J, p*J]);
                             overstructure = ambient)
    V, f = Hecke.quotient_vector_space(M, p)
    OtoF = Hecke.ring_map(f)
    W, g = Hecke.quotient_vector_space(M, N, p)
    OtoG = Hecke.ring_map(g)
    F, G = base_ring(V), base_ring(W)
    @test dim(V) == 2
    @test dim(W) == 1
    @test domain(OtoF) === domain(OtoG) === O
    @test codomain(OtoF) === F
    @test codomain(OtoG) === G
    @test characteristic(F) == characteristic(G) == characteristic(K)
    @test domain(f) === domain(g) === M
    @test codomain(f) === V
    @test codomain(g) === W
    @test kernel(g) === N
    @test image(f) === V
    @test image(g) === W
    @test !is_injective(f) && !is_injective(g)
    @test is_surjective(f) && is_surjective(g)

    pM = kernel(f)
    expected = pseudo_matrix(O, B, [p*J, p*J])
    @test pM == Hecke.embedded_module(O, K, expected; overstructure = ambient)
    @test issubset(pM, N) && issubset(N, M)
    @test Hecke.overstructure(pM) === ambient
    @test Hecke.ambient_rank(pM) == 3
    for c in basis(J)
      x = Hecke._element_from_coordinates(M, elem_type(K)[c, zero(K)])
      y = Hecke._element_from_coordinates(M, elem_type(K)[zero(K), c])
      @test f(x + y) == f(x) + f(y)
      @test iszero(g(x + y))
      @test g(x) == -g(y)
      @test Hecke.ambient_coordinates(x - preimage(f, f(x))) in pM
      @test Hecke.ambient_coordinates(x - preimage(g, g(x))) in N
      z = Hecke._element_from_ambient_coordinates(M, Hecke.ambient_coordinates(x))
      @test f(z) == f(x)
      for u in basis(p)
        @test iszero(f(u*x))
      end
      for u in basis(O)
        @test f(u*x) == OtoF(u)*f(x)
        @test g(u*x) == OtoG(u)*g(x)
      end
    end
    for (U, h, OtoH) in ((V, f, OtoF), (W, g, OtoG))
      H = base_ring(U)
      for c in (zero(H), one(H), OtoH(last(basis(O))))
        y = U([c for _ in 1:dim(U)])
        x = preimage(h, y)
        @test parent(x) === M
        @test all(t -> t in J, coordinates(x))
        @test Hecke.ambient_coordinates(x) in M
        @test h(x) == y
      end
      @test iszero(preimage(h, zero(U)))
    end
    # Matrix input, empty modules, and their kernels use unit fractional ideals.
    L = Hecke.embedded_module(O, K, identity_matrix(K, 2))
    @test rank(L) == 2
    Z = Hecke.zero_embedded_module(O, K, 3)
    for T in (M, Z)
      U, h = Hecke.quotient_vector_space(T, T, p)
      @test dim(U) == 0
      @test iszero(h(zero(T)))
      @test iszero(preimage(h, zero(U)))
      @test kernel(h) === T
    end
    U, h = Hecke.quotient_vector_space(Z, p)
    @test dim(U) == 0
    @test iszero(h(zero(Z)))
    @test iszero(preimage(h, zero(U)))
    @test kernel(h) == Z
    @test is_bijective(h)
    inclusion = Hecke.EmbeddedModules.inclusion_map(N, M)
    @test rank(kernel(inclusion)) == 0
    for bad in (ideal(O, zero(O)), ideal(O, one(O)), p^2)
      @test_throws ArgumentError Hecke.quotient_vector_space(M, bad)
    end
    higher = Hecke.embedded_module(O, K, pseudo_matrix(O, B, [p^2*J, p^2*J]);
                                  overstructure = ambient)
    @test_throws ArgumentError Hecke.quotient_vector_space(M, higher, p)
  end

  for k in (GF(5), QQ)
    kt, t = rational_function_field(k, :t; cached = false)
    K, a = function_field(polynomial(kt, [-t^3 - t - 1, 0, 1]); cached = false)
    O = finite_maximal_order(K)
    for c in (0, 1)
      q = t - c
      p = first(prime_decomposition(O, base_ring(O)(q)))[1]
      J = inv(K(q))*fractional_ideal(p)
      test_function_field_reduction(O, p, J, K[inv(q) 0 0; a 1 0])
    end
    Oinf = infinite_maximal_order(K)
    p = first(prime_decomposition(Oinf, base_ring(Oinf)(inv(t))))[1]
    J = K(t)*fractional_ideal(p)
    test_function_field_reduction(Oinf, p, J, K[t 0 0; K(last(basis(Oinf))) 1 0])
    M = Hecke.embedded_module(O, K, identity_matrix(K, 1))
    @test_throws ArgumentError Hecke.quotient_vector_space(M, p)
  end
end
