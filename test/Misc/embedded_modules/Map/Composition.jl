# Composition preserves integral preimages and canonical inclusion maps.
@testset "PID map composition" begin
  inclusion_map = Hecke.EmbeddedModules.inclusion_map
  F, x = rational_function_field(GF(7), "x")
  Rinf = localization(F, degree)
  for (R, K, t) in ((ZZ, QQ, ZZ(2)),
                    (parent(numerator(x)), F, numerator(x)),
                    (Rinf, F, Rinf(inv(x))))
    source_ambient = Ref(:source)
    middle_ambient = Ref(:middle)
    target_ambient = Ref(:target)
    M = Hecke.embedded_module(R, K, K[1//2 0 0; 0 3 0];
                             overstructure = source_ambient)
    N = Hecke.embedded_module(R, K, identity_matrix(K, 2);
                             overstructure = middle_ambient)
    P = Hecke.embedded_module(R, K, K[0 1 0 0; 0 0 0 1];
                             overstructure = target_ambient)
    B, C, D = basis(M), basis(N), basis(P)
    f = hom(M, N, [t*C[1], C[2]])
    g = hom(N, P, [D[1] + D[2], D[2]])
    h = @inferred compose(f, g)
    a = 2*B[1] - 3*B[2]
    expected = 2*t*D[1] + (2*t - 3)*D[2]

    @test h isa Hecke.EmbeddedModuleMap
    @test domain(h) === M
    @test codomain(h) === P
    @test parent(h(a)) === P
    @test (@inferred h(a)) == expected == g(f(a))
    @test image(h, a) == expected
    @test (f*g)(a) == expected
    @test h(a + B[1]) == h(a) + h(B[1])
    @test h(t*a) == t*h(a)
    @test (@inferred preimage(h, expected)) == a
    @test h(preimage(h, expected)) == expected
    @test_throws ArgumentError preimage(h, D[1])
    @test_throws ArgumentError h(C[1])
    @test_throws ArgumentError preimage(h, B[1])
    s = image(Hecke.fraction_map(M), t)
    @test image(h) == Hecke.embedded_module(R, K, K[0 s 0 0; 0 0 0 1];
                                          overstructure = target_ambient)
    @test rank(kernel(h)) == 0
    @test Hecke.ambient_rank(kernel(h)) == 3
    @test Hecke.overstructure(kernel(h)) === source_ambient
    @test Hecke.overstructure(image(h)) === target_ambient
    @test is_injective(h)
    @test !is_surjective(h)
    @test !is_bijective(h)
    @test basis(M) == B
    @test basis(N) == C
    @test basis(P) == D
    coordinates(h(a); copy = false)[1] = R(99)
    @test h(a) == expected

    for id_M in (hom(M, M, B), inclusion_map(M, M))
      @test compose(id_M, f)(a) == f(a)
    end
    for id_N in (hom(N, N, C), inclusion_map(N, N))
      @test compose(f, id_N)(a) == f(a)
    end
    k = hom(P, M, [B[1] + B[2], B[1]])
    left = compose(compose(f, g), k)
    right = compose(f, compose(g, k))
    for b in (B[1], B[2], a)
      @test left(b) == right(b) == k(g(f(b)))
    end

    N_equal = Hecke.embedded_module(R, K, identity_matrix(K, 2);
                                   overstructure = middle_ambient)
    @test N_equal == N
    @test N_equal !== N
    g_equal = hom(N_equal, P, [D[1] + D[2], D[2]])
    @test_throws ArgumentError compose(f, g_equal)
    @test_throws ArgumentError f*g_equal
    @test_throws ArgumentError compose(g, f)
    @test occursin("Homomorphism of embedded modules",
                   sprint(show, MIME"text/plain"(), h))
  end
end

@testset "mixed homomorphism and inclusion composition" begin
  inclusion_map = Hecke.EmbeddedModules.inclusion_map
  M = Hecke.embedded_module(ZZ, QQ, QQ[2 0; 0 3])
  U = Hecke.embedded_module(ZZ, QQ, QQ[4 0])
  N = Hecke.embedded_module(ZZ, QQ, QQ[1 0; 0 1])
  P = Hecke.embedded_module(ZZ, QQ, QQ[1//2 1; 0 1];
                           is_basis_matrix = true)
  B, C = basis(M), basis(N)
  f = hom(M, N, [C[1] + C[2], C[1] - C[2]])
  before = @inferred compose(inclusion_map(U, M), f)
  after = @inferred compose(f, inclusion_map(N, P))
  u = basis(U)[1]
  a = 2*B[1] - B[2]
  @test domain(before) === U
  @test codomain(before) === N
  @test before(u) == 2*C[1] + 2*C[2]
  @test preimage(before, before(u)) == u
  @test rank(kernel(before)) == 0
  @test domain(after) === M
  @test codomain(after) === P
  @test Hecke.ambient_coordinates(after(a)) == QQFieldElem[1, 3]
  @test preimage(after, after(a)) == a
  @test image(after) == Hecke.embedded_module(ZZ, QQ, QQ[1 1; 1 -1])
end

@testset "preimages of a composite with a noninjective second map" begin
  M = Hecke.embedded_module(ZZ, QQ, identity_matrix(QQ, 1))
  N = Hecke.embedded_module(ZZ, QQ, identity_matrix(QQ, 2))
  P = Hecke.embedded_module(ZZ, QQ, identity_matrix(QQ, 1))
  b, C, d = basis(M)[1], basis(N), basis(P)[1]
  g = hom(N, P, [d, d])
  v = preimage(g, d)
  # Choose an image line that does not contain the particular lift chosen by g.
  c = iszero(coordinates(v)[2]) ? C[2] : C[1]
  f = hom(M, N, [c])
  @test !is_injective(g)
  @test_throws ArgumentError preimage(f, v)
  h = compose(f, g)
  @test h(b) == d
  @test preimage(h, d) == b
  @test h(preimage(h, 7*d)) == 7*d
  @test image(h) == P
  @test rank(kernel(h)) == 0
  @test is_bijective(h)
end

@testset "zero ranks in map composition" begin
  for r in 0:1, s in 0:1, t in 0:1
    M = Hecke.embedded_module(ZZ, QQ, identity_matrix(QQ, 1)[1:r, :])
    N = Hecke.embedded_module(ZZ, QQ, QQ[1 0][1:s, :])
    P = Hecke.embedded_module(ZZ, QQ, QQ[1 0 0][1:t, :])
    f = hom(M, N, elem_type(N)[zero(N) for _ in 1:r])
    g = hom(N, P, elem_type(P)[zero(P) for _ in 1:s])
    h = @inferred compose(f, g)
    @test domain(h) === M
    @test codomain(h) === P
    @test iszero(h(zero(M)))
    @test iszero(preimage(h, zero(P)))
    @test kernel(h) == M
    @test rank(image(h)) == 0
    @test Hecke.ambient_rank(image(h)) == 3
    @test is_injective(h) == iszero(r)
    @test is_surjective(h) == iszero(t)
    @test is_bijective(h) == (iszero(r) && iszero(t))
    if !iszero(t)
      @test_throws ArgumentError preimage(h, basis(P)[1])
    end
  end
end

@testset "composition of PID inclusions" begin
  inclusion_map = Hecke.EmbeddedModules.inclusion_map
  M = Hecke.embedded_module(ZZ, QQ, QQ[6 0 0])
  N = Hecke.embedded_module(ZZ, QQ, QQ[2 0 0; 0 3 0])
  P = Hecke.embedded_module(ZZ, QQ, identity_matrix(QQ, 3))
  f, g = inclusion_map(M, N), inclusion_map(N, P)
  h = @inferred compose(f, g)
  b = basis(M)[1]
  @test domain(h) === M
  @test codomain(h) === P
  @test h(b) == g(f(b))
  @test Hecke.ambient_coordinates(h(b)) == QQFieldElem[6, 0, 0]
  @test preimage(h, h(b)) == b
  @test_throws ArgumentError preimage(h, basis(P)[1])
  @test image(h) === M
  @test rank(kernel(h)) == 0
  @test is_injective(h)
  @test !is_surjective(h)
  @test !is_bijective(h)
  @test compose(inclusion_map(M, M), f)(b) == f(b)
  @test compose(f, inclusion_map(N, N))(b) == f(b)

  # Equal middle modules with different bases are still distinct parents.
  N_equal = Hecke.embedded_module(ZZ, QQ, QQ[2 3 0; 0 3 0];
                                 is_basis_matrix = true)
  @test N_equal == N
  @test_throws ArgumentError compose(f, inclusion_map(N_equal, P))
  Z = Hecke.zero_embedded_module(ZZ, QQ, 3)
  from_zero = compose(inclusion_map(Z, M), inclusion_map(M, P))
  @test image(from_zero) === Z
  @test iszero(from_zero(zero(Z)))
  @test iszero(preimage(from_zero, zero(P)))
  @test is_bijective(compose(inclusion_map(Z, Z), inclusion_map(Z, Z)))
end

@testset "composition of Dedekind inclusions" begin
  inclusion_map = Hecke.EmbeddedModules.inclusion_map
  K, a = quadratic_field(-5)
  O = maximal_order(K)
  J = ideal(O, 2, O(1 + a))
  @test !is_principal(J)
  I = fractional_ideal(O, J)
  unit = fractional_ideal(O, one(O))
  M = Hecke.embedded_module(O, K, pseudo_matrix(O, K[1 0], [ZZ(2)*I]);
                           is_basis_matrix = true)
  N = Hecke.embedded_module(O, K, pseudo_matrix(O, K[1 0], [I]);
                           is_basis_matrix = true)
  P = Hecke.embedded_module(O, K,
                           pseudo_matrix(O, identity_matrix(K, 2), [unit, unit]);
                           is_basis_matrix = true)
  f, g = inclusion_map(M, N), inclusion_map(N, P)
  h = @inferred compose(f, g)
  b = Hecke._element_from_ambient_coordinates(M, elem_type(K)[K(4), K(0)])
  @test domain(h) === M
  @test codomain(h) === P
  @test h(b) == g(f(b))
  @test Hecke.ambient_coordinates(h(b)) == Hecke.ambient_coordinates(b)
  @test preimage(h, h(b)) == b
  @test image(h) === M
  @test rank(kernel(h)) == 0
  @test is_injective(h)
  @test !is_surjective(h)
  @test !is_bijective(h)
  not_in_image = Hecke._element_from_ambient_coordinates(P, elem_type(K)[K(1), K(0)])
  @test_throws ArgumentError preimage(h, not_in_image)
  @test compose(inclusion_map(M, M), f)(b) == f(b)
  @test compose(f, inclusion_map(N, N))(b) == f(b)
  N_equal = Hecke.embedded_module(O, K, pseudo_matrix(O, K[1 0], [I]);
                                 is_basis_matrix = true)
  @test N_equal == N
  @test_throws ArgumentError compose(f, inclusion_map(N_equal, P))
  Z = kernel(h)
  from_zero = compose(inclusion_map(Z, M), inclusion_map(M, P))
  @test image(from_zero) === Z
  @test iszero(from_zero(zero(Z)))
  @test is_bijective(compose(inclusion_map(Z, Z), inclusion_map(Z, Z)))
end

@testset "Dedekind matrix map composition" begin
  K, a = quadratic_field(-5)
  R = maximal_order(K)
  I = fractional_ideal(R, ideal(R, 2, R(1 + a)))
  U = fractional_ideal(R, one(R))
  M = Hecke.embedded_module(R, K, pseudo_matrix(R, K[1 0], [I]);
                           is_basis_matrix = true)
  N = Hecke.embedded_module(R, K,
        pseudo_matrix(R, identity_matrix(K, 2), [I, U]);
        is_basis_matrix = true)
  P = Hecke.embedded_module(R, K, pseudo_matrix(R, K[0 0 1], [I]);
                           is_basis_matrix = true)
  f = Hecke.EmbeddedModules._hom(M, N, K[1 0])
  g = Hecke.EmbeddedModules._hom(N, P, K[1; 2;;])
  h = @inferred compose(f, g)
  x = Hecke._element_from_coordinates(M, elem_type(K)[K(2)])
  @test h(x) == g(f(x)) == (f*g)(x)
  @test preimage(h, h(x)) == x
  @test rank(kernel(h)) == 0
  @test image(h) == P
  @test is_bijective(h)
  @test !is_injective(g)
  @test_throws ArgumentError compose(g, f)
end

@testset "generic composition for other codomains" begin
  M = Hecke.embedded_module(ZZ, QQ, identity_matrix(QQ, 2))
  N = Hecke.embedded_module(ZZ, QQ, QQ[1//2 0; 0 3])
  B, C = basis(M), basis(N)
  f = hom(M, N, C)
  a = 4*B[1] - B[2]
  doubled = Hecke.embedded_module(ZZ, QQ, 2*basis_matrix(N))
  Q, q = quo(N, doubled)
  V, reduction = Hecke.quotient_vector_space(N, ZZ(3))
  scalar = hom(N, ZZ, ZZRingElem[2, 3])
  for g in (q, reduction, scalar)
    h = compose(f, g)
    @test !(h isa Hecke.EmbeddedModuleMap)
    @test domain(h) === M
    @test codomain(h) === codomain(g)
    @test h(a) == g(f(a))
    @test (f*g)(a) == h(a)
  end
end
