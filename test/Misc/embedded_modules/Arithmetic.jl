# Embedded modules support arithmetic and conversion to integral ideals.
@testset "polynomial PID" begin
  K, x = rational_function_field(QQ, "x")
  R = parent(numerator(x))
  M = Hecke.embedded_module(R, K, K[x 0; 0 1])

  @test rank(M) == 2
  @test typeof(x)[x, x + 1] in M
  @test !(typeof(x)[K(1), K(0)] in M)
  @test !(typeof(x)[x, inv(x)] in M)

  N = Hecke.embedded_module(R, K, identity_matrix(K, 2))
  @test M + N == N
  @test intersect(M, N) == M
end

@testset "Ideal multiplication over Dedekind domains" begin
  function test_ideal_multiplication(O, p, q)
    K = parent(q)
    I = inv(K(q))*fractional_ideal(p)
    ambient = nothing
    M = Hecke.embedded_module(O, K, pseudo_matrix(O, K[1 0 0; 0 1 0], [I, I]);
                             overstructure = ambient, is_basis_matrix = true)
    for J in (p, I)
      N = J*M
      @test N == M*J
      @test Hecke.ring(N) === O
      @test Hecke.overring(N) === K
      @test Hecke.overstructure(N) === ambient
      @test Hecke.ambient_rank(N) == 3
      @test rank(N) == rank(M)
      @test (J*p)*M == J*(p*M)
      @test (J + p)*M == J*M + p*M
    end
    @test ideal(O, one(O))*M == M
    @test fractional_ideal(ideal(O, one(O)))*M == M
    for J in (ideal(O, zero(O)), fractional_ideal(ideal(O, zero(O))))
      Z = J*M
      @test iszero(rank(Z))
      @test Hecke.ambient_rank(Z) == 3
      @test Hecke.overstructure(Z) === ambient
      @test p*Z == Z
    end
    @test kernel(last(Hecke.quotient_vector_space(M, p))) == p*M
    L = Hecke.embedded_module(O, K, pseudo_matrix(O, K[1;;],
                             [fractional_ideal(p)]))
    @test (@inferred ideal(O, L)) == p
    @test ideal(O, Hecke.zero_embedded_module(O, K, 1)) == ideal(O, zero(O))
    @test_throws ArgumentError ideal(O, M)
    F = Hecke.embedded_module(O, K, K[inv(q);;])
    @test_throws ArgumentError ideal(O, F)
    L, _ = quadratic_field(-1)
    @test_throws ArgumentError ideal(maximal_order(L), 2)*M
  end

  K, _ = quadratic_field(-5)
  for O in (maximal_order(K), maximal_order(Hecke.GenOrd(ZZ, K)))
    p = first(prime_decomposition(O, ZZ(3)))[1]
    test_ideal_multiplication(O, p, K(3))
  end

  kt, t = rational_function_field(GF(5), :t; cached = false)
  K, _ = function_field(polynomial(kt, [-t^3 - t - 1, 0, 1]); cached = false)
  for O in (finite_maximal_order(K), infinite_maximal_order(K))
    q = base_ring(O) isa PolyRing ? t : inv(t)
    p = first(prime_decomposition(O, base_ring(O)(q)))[1]
    test_ideal_multiplication(O, p, K(q))
  end
end

@testset "PID modules as integral ideals" begin
  F, t = rational_function_field(GF(7), "t")
  for (R, K, c) in ((ZZ, QQ, QQ(2)), (parent(numerator(t)), F, t),
                    (localization(F, degree), F, inv(t)))
    M = Hecke.embedded_module(R, K, K[c;;])
    @test (@inferred ideal(R, M)) == ideal(R, R(c))
    @test ideal(R, Hecke.zero_embedded_module(R, K, 1)) == ideal(R, zero(R))
    @test_throws ArgumentError ideal(R,
      Hecke.embedded_module(R, K, K[inv(c);;]))
    @test_throws ArgumentError ideal(R,
      Hecke.embedded_module(R, K, identity_matrix(K, 2)))
    @test_throws ArgumentError ideal(K, M)
  end
end

@testset "degree localization" begin
  K, x = rational_function_field(QQ, "x")
  R = localization(K, degree)
  M = Hecke.embedded_module(R, K, K[1//x 0; 0 1])

  @test Hecke.ring(M) === R
  @test Hecke.overring(M) === K
  @test basis_matrix(M) == K[1//x 0; 0 1]
  @test typeof(x)[inv(x), (x + 1)//x] in M
  @test typeof(x)[inv(x)^2, K(0)] in M
  @test !(typeof(x)[K(1), K(0)] in M)
  @test !(typeof(x)[inv(x), x] in M)

  N = Hecke.embedded_module(R, K, identity_matrix(K, 2))
  @test M + N == N
  @test intersect(M, N) == M
end
