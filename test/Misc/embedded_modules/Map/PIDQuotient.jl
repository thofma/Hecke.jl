@testset "integer PID quotient maps" begin
  ambient = nothing
  M = Hecke.embedded_module(ZZ, QQ, QQ[1//6 0 0; 0 3 0];
                           overstructure = ambient, is_basis_matrix = true)
  N = Hecke.embedded_module(ZZ, QQ, QQ[1//3 3 0; 0 9 0];
                           overstructure = ambient, is_basis_matrix = true)
  Q, f = @inferred quo(M, N)
  B = basis(M)
  x = 5*B[1] - 4*B[2]

  @test f isa Hecke.EmbeddedModuleMap
  @test domain(f) === M
  @test codomain(f) === Q
  @test kernel(f) === N
  @test image(f) === Q
  @test !is_injective(f)
  @test is_surjective(f)
  @test !is_bijective(f)
  @test iszero(f(2*B[1] + B[2]))
  @test iszero(f(3*B[2]))
  @test iszero(f(6*B[1]))
  @test !iszero(f(3*B[1]))
  @test (@inferred image(f, x)) == f(x)
  @test f(x + B[1]) == f(x) + f(B[1])
  @test f(ZZ(5)*x) == ZZ(5)*f(x)
  a = Hecke._element_from_ambient_coordinates(M, Hecke.ambient_coordinates(x);
                                             check = false)
  @test f(a) == f(x)
  for v in (zero(M), B[1], x)
    y = f(v)
    z = preimage(f, y)
    @test parent(z) === M
    @test f(z) == y
    @test Hecke.ambient_coordinates(v - z) in N
  end
  for b in basis(N)
    n = Hecke._element_from_ambient_coordinates(M, Hecke.ambient_coordinates(b))
    @test iszero(f(n))
  end

  other_Q, g = quo(M, N)
  @test other_Q !== Q
  other_y = g(B[1])
  @test_throws ArgumentError preimage(f, other_y)
  @test_throws ArgumentError preimage(f, B[1])
  @test_throws ArgumentError f(basis(N)[1])
  @test_throws ArgumentError image(f, basis(N)[1])
  larger = Hecke.embedded_module(ZZ, QQ, QQ[1//12 0 0; 0 3 0];
                                overstructure = ambient)
  incompatible = Hecke.embedded_module(ZZ, QQ, QQ[1//3 3; 0 9])
  @test_throws ArgumentError quo(M, larger)
  @test_throws ArgumentError quo(M, incompatible)

  text = sprint(show, MIME"text/plain"(), f)
  @test occursin("Homomorphism of embedded modules", text)
  @test occursin("defined by", text)
  @test show(IOBuffer(), MIME"text/plain"(), f) === nothing
  @test show(IOBuffer(), f) === nothing
end

@testset "PID quotients with a free part" begin
  M = Hecke.embedded_module(ZZ, QQ, QQ[1//2 0 0; 0 3 0])
  N = Hecke.embedded_module(ZZ, QQ, QQ[1 0 0])
  Q, f = quo(M, N)
  B = basis(M)
  @test domain(f) === M
  @test codomain(f) === Q
  @test image(f) === Q
  @test kernel(f) === N
  @test !is_injective(f)
  @test is_surjective(f)
  @test !is_bijective(f)
  @test !iszero(f(B[1]))
  @test iszero(f(2*B[1]))
  @test !iszero(f(7*B[2]))
  x = B[1] + 7*B[2]
  y = image(f, x)
  z = preimage(f, y)
  @test f(z) == y
  @test Hecke.ambient_coordinates(x - z) in N
end

@testset "quotients by zero and by the whole module" begin
  ambient = nothing
  M = Hecke.embedded_module(ZZ, QQ, QQ[1//2 0 0; 0 3 0];
                           overstructure = ambient)
  Z = Hecke.embedded_module(ZZ, QQ, zero_matrix(QQ, 0, 3);
                           overstructure = ambient)
  for (A, N) in ((M, Z), (M, M), (Z, Z))
    Q, f = quo(A, N)
    @test domain(f) === A
    @test codomain(f) === Q
    @test image(f) === Q
    @test kernel(f) === N
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

@testset "quotient maps over function field PIDs" begin
  K, x = rational_function_field(GF(3), "x")
  Rpoly = parent(numerator(x))
  Rinf = localization(K, degree)
  for (R, p) in ((Rpoly, numerator(x)^2 + 1), (Rinf, Rinf(inv(x))))
    s = R === Rpoly ? K(p) : inv(x)
    M = Hecke.embedded_module(R, K, K[inv(s) 0 0; 0 s 0];
                             is_basis_matrix = true)
    N = Hecke.embedded_module(R, K, K[1 0 0])
    Q, f = quo(M, N)
    B = basis(M)
    @test domain(f) === M
    @test codomain(f) === Q
    @test image(f) === Q
    @test kernel(f) === N
    @test !is_injective(f)
    @test is_surjective(f)
    @test !is_bijective(f)
    @test !iszero(f(B[1]))
    @test iszero(f(p*B[1]))
    @test !iszero(f(p*B[2]))
    c = R === Rpoly ? numerator(x) : Rinf((x + 1)/(x + 2))
    v = c*B[1] + B[2]
    y = image(f, v)
    @test f(c*v) == c*y
    z = preimage(f, y)
    @test parent(z) === M
    @test f(z) == y
    @test Hecke.ambient_coordinates(v - z) in N
  end
end
