@testset "torsion-free embedded quotient" begin
  ambient = nothing
  M = Hecke.embedded_module(ZZ, QQ, QQ[1//2 0 0; 0 3 0];
                           overstructure = ambient, is_basis_matrix = true)
  N = Hecke.embedded_module(ZZ, QQ, QQ[1 9 0];
                           overstructure = ambient)
  Q, f = @inferred Hecke.quotient_embedded_module(M, N)
  B = basis(M)

  @test Q isa Hecke.EmbeddedModule
  @test f isa Hecke.EmbeddedModuleMap
  @test Hecke.ring(Q) === ZZ
  @test Hecke.overring(Q) === QQ
  @test rank(Q) == Hecke.ambient_rank(Q) == 1
  @test basis_matrix(Q) == identity_matrix(QQ, 1)
  @test Hecke.overstructure(Q) === nothing
  @test domain(f) === M
  @test codomain(f) === Q
  @test kernel(f) == N
  @test image(f) == Q
  @test !is_injective(f)
  @test is_surjective(f)
  @test !is_bijective(f)
  @test iszero(f(2*B[1] + 3*B[2]))
  @test !iszero(f(B[1]))
  @test !iszero(f(B[2]))
  x = 5*B[1] - 4*B[2]
  @test image(f, x) == f(x)
  @test f(x + B[1]) == f(x) + f(B[1])
  @test f(ZZ(5)*x) == ZZ(5)*f(x)
  for y in (zero(Q), basis(Q)[1], 7*basis(Q)[1])
    z = preimage(f, y)
    @test parent(z) === M
    @test f(z) == y
  end
  z = preimage(f, f(x))
  @test Hecke.ambient_coordinates(x - z) in N
  @test_throws ArgumentError f(basis(N)[1])
  @test_throws ArgumentError preimage(f, B[1])
  other_Q, = Hecke.quotient_embedded_module(M, N)
  @test_throws ArgumentError preimage(f, basis(other_Q)[1])
  @test show(IOBuffer(), MIME"text/plain"(), f) === nothing
  @test show(IOBuffer(), f) === nothing
end

@testset "zero and identity embedded quotients" begin
  M = Hecke.embedded_module(ZZ, QQ, QQ[1//2 0 0; 0 3 0])
  Z = Hecke.zero_embedded_module(ZZ, QQ, 3)
  for (A, N) in ((M, Z), (M, M), (Z, Z))
    Q, f = Hecke.quotient_embedded_module(A, N)
    @test rank(Q) == Hecke.ambient_rank(Q) == rank(A) - rank(N)
    @test domain(f) === A
    @test codomain(f) === Q
    @test kernel(f) == N
    @test image(f) == Q
    @test is_surjective(f)
    @test is_injective(f) == iszero(rank(N))
    @test is_bijective(f) == iszero(rank(N))
    @test iszero(image(f, zero(A)))
    @test iszero(preimage(f, zero(Q)))
    for b in basis(A)
      y = f(b)
      z = preimage(f, y)
      @test f(z) == y
      if N === Z
        @test z == b
      else
        @test iszero(y)
      end
    end
    @test show(IOBuffer(), MIME"text/plain"(), f) === nothing
  end
end

@testset "embedded quotients over function field PIDs" begin
  K, x = rational_function_field(GF(3), "x")
  Rpoly = parent(numerator(x))
  Rinf = localization(K, degree)
  for (R, t) in ((Rpoly, x), (Rinf, inv(x)))
    M = Hecke.embedded_module(R, K, K[inv(t) 0 0; 0 t 0];
                             is_basis_matrix = true)
    N = Hecke.embedded_module(R, K, K[1 t 0])
    Q, f = Hecke.quotient_embedded_module(M, N)
    B = basis(M)
    c = R === Rpoly ? numerator(x) : Rinf(inv(x))
    @test Hecke.ring(Q) === R
    @test Hecke.overring(Q) === K
    @test rank(Q) == Hecke.ambient_rank(Q) == 1
    @test domain(f) === M
    @test codomain(f) === Q
    @test kernel(f) == N
    @test image(f) == Q
    @test is_surjective(f)
    @test !is_injective(f)
    @test !is_bijective(f)
    @test iszero(f(c*B[1] + B[2]))
    v = B[1] + c*B[2]
    @test image(f, c*v) == c*f(v)
    for y in (zero(Q), basis(Q)[1], c*basis(Q)[1])
      z = preimage(f, y)
      @test parent(z) === M
      @test f(z) == y
    end
    torsion = Hecke.embedded_module(R, K, K[1 0 0])
    @test_throws ArgumentError Hecke.quotient_embedded_module(M, torsion)
    zero_Q, zero_f = Hecke.quotient_embedded_module(M, M)
    @test rank(zero_Q) == Hecke.ambient_rank(zero_Q) == 0
    @test kernel(zero_f) == M
    @test image(zero_f) == zero_Q
    @test iszero(zero_f(B[1]))
    @test iszero(preimage(zero_f, zero(zero_Q)))
  end
end
