@testset "integer PID reduction" begin
  ambient = nothing
  M = Hecke.embedded_module(ZZ, QQ, QQ[1//6 0 0; 0 3 0];
                           overstructure = ambient, is_basis_matrix = true)
  V, f, RtoF = @inferred Hecke.quotient_vector_space(M, ZZ(3))
  F = base_ring(V)
  B = basis(M)
  x = 5*B[1] - 4*B[2]
  y = V([F(2), F(2)])

  @test f isa Hecke.EmbeddedModuleMap
  @test domain(f) === M
  @test codomain(f) === V
  @test dim(V) == rank(M) == 2
  @test order(F) == 3
  @test domain(RtoF) === ZZ
  @test codomain(RtoF) === F
  @test image(f, x) == y
  a = Hecke._element_from_ambient_coordinates(M, Hecke.ambient_coordinates(x);
                                             check = false)
  @test f(a) == y
  @test f(B[1]) == V([one(F), zero(F)])
  @test f(B[2]) == V([zero(F), one(F)])
  @test f(x + B[1]) == f(x) + f(B[1])
  @test f(ZZ(5)*x) == RtoF(ZZ(5))*f(x)
  @test parent(preimage(f, y)) === M
  @test f(preimage(f, y)) == y
  @test iszero(preimage(f, zero(V)))
  @test image(f) === V
  @test !is_injective(f)
  @test is_surjective(f)
  @test !is_bijective(f)

  K = kernel(f)
  @test K == Hecke.embedded_module(ZZ, QQ, QQ[1//2 0 0; 0 9 0];
                                  overstructure = ambient)
  @test rank(K) == rank(M)
  @test Hecke.ambient_rank(K) == 3
  @test Hecke.overstructure(K) === ambient
  @test issubset(K, M)
  @test all(iszero(f(3*b)) for b in B)
  for b in basis(K)
    k = Hecke._element_from_ambient_coordinates(M, Hecke.ambient_coordinates(b))
    @test iszero(f(k))
  end

  N = Hecke.embedded_module(ZZ, QQ, Hecke.basis_matrix(M);
                           overstructure = ambient)
  W, g, = Hecke.quotient_vector_space(N, ZZ(3))
  @test W !== V
  @test_throws ArgumentError f(basis(N)[1])
  @test_throws ArgumentError preimage(f, g(basis(N)[1]))
  @test_throws ArgumentError preimage(f, B[1])
  @test occursin("Homomorphism of embedded modules", sprint(show, MIME"text/plain"(), f))
  @test occursin("defined by", sprint(show, MIME"text/plain"(), f))
  @test show(IOBuffer(), MIME"text/plain"(), f) === nothing
  @test show(IOBuffer(), f) === nothing

  for p in (ZZ(0), ZZ(1), ZZ(9))
    @test_throws ArgumentError Hecke.quotient_vector_space(M, p)
  end
  P, t = polynomial_ring(QQ, "t")
  @test_throws ArgumentError Hecke.quotient_vector_space(M, t)
end

@testset "PID reduction by a submodule" begin
  ambient = nothing
  M = Hecke.embedded_module(ZZ, QQ, QQ[1//6 0 0; 0 3 0];
                           overstructure = ambient, is_basis_matrix = true)
  N = Hecke.embedded_module(ZZ, QQ, QQ[1//6 3 0; 0 9 0];
                           overstructure = ambient, is_basis_matrix = true)
  V, f, RtoF = @inferred Hecke.quotient_vector_space(M, N, ZZ(3))
  F = base_ring(V)
  B = basis(M)
  x = 2*B[1] + 3*B[2]

  @test f isa Hecke.EmbeddedModuleMap
  @test domain(f) === M
  @test codomain(f) === V
  @test dim(V) == 1
  @test iszero(f(B[1] + B[2]))
  @test f(B[1]) == -f(B[2])
  @test !iszero(f(B[1]))
  @test iszero(f(3*B[1]))
  @test image(f, x) == RtoF(ZZ(2))*f(B[1])
  @test f(x) == RtoF(ZZ(2))*f(B[1])
  @test f(x + B[1]) == f(x) + f(B[1])
  @test image(f) === V
  @test kernel(f) === N
  @test Hecke.ambient_coordinates(x - preimage(f, f(x))) in N
  @test !is_injective(f)
  @test is_surjective(f)
  @test !is_bijective(f)
  for a in (F(0), F(1), F(2))
    y = V([a])
    @test parent(preimage(f, y)) === M
    @test f(preimage(f, y)) == y
  end
  for b in basis(N)
    n = Hecke._element_from_ambient_coordinates(M, Hecke.ambient_coordinates(b))
    @test iszero(f(n))
  end

  W, g, = Hecke.quotient_vector_space(M, N, ZZ(3))
  @test W !== V
  @test_throws ArgumentError f(basis(N)[1])
  @test_throws ArgumentError preimage(f, g(B[1]))
  @test occursin("defined by", sprint(show, MIME"text/plain"(), f))

  U, h, = Hecke.quotient_vector_space(M, ZZ(3))
  T, k, = Hecke.quotient_vector_space(M, kernel(h), ZZ(3))
  @test dim(U) == dim(T) == 2
  @test all(coordinates(h(b)) == coordinates(k(b)) for b in B)
end

@testset "zero-dimensional residue quotients" begin
  for M in (Hecke.embedded_module(ZZ, QQ, identity_matrix(QQ, 2)),
            Hecke.zero_embedded_module(ZZ, QQ, 3))
    V, f, = Hecke.quotient_vector_space(M, M, ZZ(3))
    @test dim(V) == 0
    @test iszero(f(zero(M)))
    @test all(iszero(f(b)) for b in basis(M))
    @test parent(preimage(f, zero(V))) === M
    @test iszero(preimage(f, zero(V)))
    @test image(f) === V
    @test kernel(f) === M
    @test is_surjective(f)
    @test is_injective(f) == iszero(rank(M))
    @test is_bijective(f) == iszero(rank(M))
  end
end

@testset "zero PID reduction" begin
  M = Hecke.zero_embedded_module(ZZ, QQ, 3)
  V, f, = Hecke.quotient_vector_space(M, ZZ(2))
  @test dim(V) == 0
  @test iszero(f(zero(M)))
  @test iszero(preimage(f, zero(V)))
  @test image(f) === V
  @test kernel(f) == M
  @test Hecke.ambient_rank(kernel(f)) == 3
  @test is_injective(f)
  @test is_surjective(f)
  @test is_bijective(f)
end

@testset "function field PID reduction" begin
  K, x = rational_function_field(GF(3), "x")
  Rpoly = parent(numerator(x))
  Rinf = localization(K, degree)
  for (R, p) in ((Rpoly, numerator(x)^2 + 1), (Rinf, Rinf(inv(x))))
    s = R === Rpoly ? K(p) : inv(x)
    M = Hecke.embedded_module(R, K, K[inv(s) 0 0; 0 s 0];
                             is_basis_matrix = true)
    V, f, RtoF = Hecke.quotient_vector_space(M, p)
    F = base_ring(V)
    B = basis(M)
    @test dim(V) == 2
    @test order(F) == (R === Rpoly ? 9 : 3)
    @test f(B[1]) == V([one(F), zero(F)])
    @test f(B[2]) == V([zero(F), one(F)])
    @test iszero(f(p*B[1]))
    c = R === Rpoly ? numerator(x) : Rinf((x + 1)/(x + 2))
    v = c*B[1] + B[2]
    @test image(f, v) == V(elem_type(F)[RtoF(c), one(F)])
    @test f(c*v) == RtoF(c)*f(v)
    for a in (one(F), gen(F))
      y = V(elem_type(F)[a, one(F)])
      @test parent(preimage(f, y)) === M
      @test f(preimage(f, y)) == y
    end
    @test image(f) === V
    @test kernel(f) == Hecke.embedded_module(R, K, K[1 0 0; 0 s^2 0])
    @test !is_injective(f)
    @test is_surjective(f)
    @test !is_bijective(f)
    for q in (zero(R), one(R), p^2)
      @test_throws ArgumentError Hecke.quotient_vector_space(M, q)
    end
  end
end

@testset "function field reduction by a submodule" begin
  K, x = rational_function_field(GF(3), "x")
  Rpoly = parent(numerator(x))
  Rinf = localization(K, degree)
  for (R, p) in ((Rpoly, numerator(x)^2 + 1), (Rinf, Rinf(inv(x))))
    s = R === Rpoly ? K(p) : inv(x)
    M = Hecke.embedded_module(R, K, K[inv(s) 0 0; 0 s 0];
                             is_basis_matrix = true)
    N = Hecke.embedded_module(R, K, K[inv(s) s 0; 0 s^2 0];
                             is_basis_matrix = true)
    V, f, RtoF = Hecke.quotient_vector_space(M, N, p)
    F = base_ring(V)
    B = basis(M)
    @test dim(V) == 1
    @test kernel(f) === N
    @test image(f) === V
    @test f(B[1]) == -f(B[2])
    @test !iszero(f(B[1]))
    @test iszero(f(p*B[1]))
    c = R === Rpoly ? numerator(x) : Rinf((x + 1)/(x + 2))
    v = c*B[1] + B[2]
    @test image(f, c*v) == RtoF(c)*f(v)
    @test Hecke.ambient_coordinates(v - preimage(f, f(v))) in N
    for a in (zero(F), one(F), gen(F))
      y = V([a])
      @test parent(preimage(f, y)) === M
      @test f(preimage(f, y)) == y
    end
    @test !is_injective(f)
    @test is_surjective(f)
    @test !is_bijective(f)
  end
end
