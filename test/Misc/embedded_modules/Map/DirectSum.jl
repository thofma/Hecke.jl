# Canonical direct sum maps and addition maps solve decompositions in modules.
@testset "Internal embedded module direct sums" begin
  function test_embedded_direct_sum(M, N, x, y)
    D, (iM, iN), (pM, pN) =
      @inferred Hecke.EmbeddedModules._direct_sum(M, N)
    z = iM(x) + iN(y)
    @test rank(D) == rank(M) + rank(N)
    @test Hecke.ambient_rank(D) ==
          Hecke.ambient_rank(M) + Hecke.ambient_rank(N)
    @test pM(z) == x && pN(z) == y
    @test iM(pM(z)) + iN(pN(z)) == z
    @test iszero(pM(iN(y))) && iszero(pN(iM(x)))
    @test preimage(iM, iM(x)) == x
    @test preimage(iN, iN(y)) == y
    @test pM(preimage(pM, x)) == x
    @test pN(preimage(pN, y)) == y
    @test compose(iM, pM)(x) == x
    @test compose(iN, pN)(y) == y
    @test is_injective(iM) && is_injective(iN)
    @test is_surjective(pM) && is_surjective(pN)
    @test image(pM) == M && image(pN) == N
    @test rank(kernel(pM)) == rank(N)
    @test rank(kernel(pN)) == rank(M)
    @test iszero(rank(kernel(iM))) && iszero(rank(kernel(iN)))
    @test Hecke.ambient_coordinates(z) ==
          vcat(Hecke.ambient_coordinates(x), Hecke.ambient_coordinates(y))
    !iszero(y) && (@test_throws ArgumentError preimage(iM, z))
    !iszero(x) && (@test_throws ArgumentError preimage(iN, z))
  end

  F, t = rational_function_field(GF(7), "t")
  K, a = quadratic_field(-5)
  R = maximal_order(K)
  I = fractional_ideal(R, ideal(R, 2, R(1 + a)))
  U = fractional_ideal(ideal(R, one(R)))
  for (R, K) in ((ZZ, QQ), (parent(numerator(t)), F),
                  (localization(F, degree), F))
    M = Hecke.embedded_module(R, K, K[1//2 0 0; 1 3 0];
                             is_basis_matrix = true)
    N = Hecke.embedded_module(R, K, K[0 1]; is_basis_matrix = true)
    x = Hecke._element_from_coordinates(M, elem_type(R)[R(2), R(-1)])
    y = Hecke._element_from_coordinates(N, elem_type(R)[R(3)])
    Z = Hecke.zero_embedded_module(R, K, 3)
    for (A, B, u, v) in ((M, N, x, y), (Z, N, zero(Z), y),
                          (M, Z, x, zero(Z)), (Z, Z, zero(Z), zero(Z)))
      test_embedded_direct_sum(A, B, u, v)
    end
  end
  R, K = order(I), Hecke.nf(order(I))
  M = Hecke.embedded_module(R, K,
        pseudo_matrix(R, K[1//2 0 0; a 1 0], [I, U]);
        is_basis_matrix = true)
  N = Hecke.embedded_module(R, K, pseudo_matrix(R, K[0 1], [inv(I)]);
                           is_basis_matrix = true)
  x = Hecke._element_from_coordinates(M, elem_type(K)[K(2), K(-1)])
  y = Hecke._element_from_coordinates(N, elem_type(K)[one(K)])
  Z = Hecke.zero_embedded_module(R, K, 3)
  for (A, B, u, v) in ((M, N, x, y), (Z, N, zero(Z), y),
                        (M, Z, x, zero(Z)), (Z, Z, zero(Z), zero(Z)))
    test_embedded_direct_sum(A, B, u, v)
  end
  @test_throws ArgumentError Hecke.EmbeddedModules._direct_sum(
    M, Hecke.embedded_module(ZZ, QQ, QQ[1;;]))
end

@testset "Embedded module addition maps" begin
  function test_embedded_addition(M, N, P, x)
    f, pM, pN = @inferred Hecke.addition_map(M, N, P)
    z = @inferred preimage(f, x)
    @test f(z) == x
    @test Hecke.ambient_coordinates(pM(z)) in M
    @test Hecke.ambient_coordinates(pN(z)) in N
    @test Hecke.ambient_coordinates(pM(z)) +
          Hecke.ambient_coordinates(pN(z)) == Hecke.ambient_coordinates(x)
    @test image(f) == P
    @test is_surjective(f)
    h, qM, qN = Hecke.addition_map(f, f)
    w = preimage(h, x)
    @test f(qM(w)) + f(qN(w)) == x
    @test rank(kernel(f)) == rank(M) + rank(N) - rank(P)
    g, _, _ = Hecke.addition_map(M, N)
    y = Hecke._element_from_ambient_coordinates(codomain(g),
                                               Hecke.ambient_coordinates(x))
    @test g(preimage(g, y)) == y
    @test is_surjective(g)
    @test sprint(show, MIME"text/plain"(), f) isa String
  end

  F, t = rational_function_field(GF(7), "t")
  for (R, K, p) in ((ZZ, QQ, QQ(2)),
                    (parent(numerator(t)), F, t),
                    (localization(F, degree), F, inv(t)))
    B = K[inv(p) 0 0; 1 p 0]
    P = Hecke.embedded_module(R, K, B; is_basis_matrix = true)
    M = Hecke.embedded_module(R, K, p*B; is_basis_matrix = true)
    N = Hecke.embedded_module(R, K, (p + 1)*B; is_basis_matrix = true)
    x = Hecke._element_from_coordinates(P, elem_type(R)[one(R), R(-1)])
    test_embedded_addition(M, N, P, x)
    Z = Hecke.zero_embedded_module(R, K, 3)
    test_embedded_addition(P, Z, P, x)
    test_embedded_addition(Z, P, P, x)
    test_embedded_addition(Z, Z, Z, zero(Z))
    f, _, _ = Hecke.addition_map(M, M, P)
    @test_throws ArgumentError preimage(f, x)
    @test !is_surjective(f)
    @test_throws ArgumentError Hecke.addition_map(M, N, M)
    @test_throws ArgumentError Hecke.addition_map(M,
      Hecke.zero_embedded_module(R, K, 4))
  end

  K, a = quadratic_field(-5)
  R = maximal_order(K)
  I = fractional_ideal(R, ideal(R, 2, R(1 + a)))
  U = fractional_ideal(ideal(R, one(R)))
  B = K[1//2 0 0; a 1 0]
  P = Hecke.embedded_module(R, K, pseudo_matrix(R, B, [I, U]);
                           is_basis_matrix = true)
  M = Hecke.embedded_module(R, K, pseudo_matrix(R, 2*B, [I, U]);
                           is_basis_matrix = true)
  N = Hecke.embedded_module(R, K, pseudo_matrix(R, 3*B, [I, U]);
                           is_basis_matrix = true)
  x = Hecke._element_from_coordinates(P, elem_type(K)[K(2), one(K)])
  test_embedded_addition(M, N, P, x)
  Z = Hecke.zero_embedded_module(R, K, 3)
  test_embedded_addition(P, Z, P, x)
  test_embedded_addition(Z, P, P, x)
  test_embedded_addition(Z, Z, Z, zero(Z))
  f, _, _ = Hecke.addition_map(M, M, P)
  @test_throws ArgumentError preimage(f, x)
  @test !is_surjective(f)
end
