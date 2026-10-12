@testset "integer PID maps" begin
  source_ambient = Ref(:source)
  target_ambient = Ref(:target)
  M = Hecke.embedded_module(ZZ, QQ, QQ[1//2 0 0; 0 3 0];
                           overstructure = source_ambient)
  N = Hecke.embedded_module(ZZ, QQ, QQ[0 1//5];
                           overstructure = target_ambient)
  b = basis(N)[1]
  f = hom(M, N, [4*b, 6*b])
  x = Hecke._element_from_coordinates(M, ZZRingElem[3, -1])
  @test coordinates(f(x)) == ZZRingElem[6]
  @test Hecke.ambient_coordinates(f(x)) == QQFieldElem[0, 6//5]
  @test f(preimage(f, 2*b)) == 2*b
  @test_throws ArgumentError preimage(f, b)

  I = image(f)
  K = kernel(f)
  @test I isa Hecke.EmbeddedModule
  @test K isa Hecke.EmbeddedModule
  @test I == Hecke.embedded_module(ZZ, QQ, QQ[0 2//5];
                                  overstructure = target_ambient)
  @test K == Hecke.embedded_module(ZZ, QQ, QQ[-3//2 6 0];
                                  overstructure = source_ambient)
  @test Hecke.overstructure(I) === target_ambient
  @test Hecke.overstructure(K) === source_ambient
  @test issubset(I, N)
  @test issubset(K, M)
  k = Hecke._element_from_ambient_coordinates(M,
                         Hecke.ambient_coordinates(basis(K)[1]))
  @test iszero(f(k))
  @test !is_injective(f)
  @test !is_surjective(f)
  @test !is_bijective(f)

  g = hom(M, N, [2*b, 3*b])
  @test image(g) == N
  @test rank(kernel(g)) == 1
  @test !is_injective(g)
  @test is_surjective(g)
  @test !is_bijective(g)

  B = basis(M)
  doubled = hom(M, M, [2*B[1], 2*B[2]])
  @test is_injective(doubled)
  @test !is_surjective(doubled)
  @test !is_bijective(doubled)
  @test rank(kernel(doubled)) == 0

  iso = hom(M, M, [B[1] + 2*B[2], B[2]])
  @test is_injective(iso)
  @test is_surjective(iso)
  @test is_bijective(iso)
  @test preimage(iso, iso(x)) == x
  @test image(iso) == M
end

@testset "zero PID maps" begin
  M = Hecke.embedded_module(ZZ, QQ, QQ[1 0; 0 1])
  Z = Hecke.zero_embedded_module(ZZ, QQ, 3)
  to_zero = hom(M, Z, [zero(Z), zero(Z)])
  from_zero = hom(Z, M, elem_type(M)[])
  zero_iso = hom(Z, Z, elem_type(Z)[])
  zero_map = hom(M, M, [zero(M), zero(M)])

  @test image(to_zero) == Z
  @test kernel(to_zero) == M
  @test !is_injective(to_zero)
  @test is_surjective(to_zero)
  @test iszero(to_zero(basis(M)[1]))
  @test iszero(preimage(to_zero, zero(Z)))
  @test rank(image(from_zero)) == 0
  @test Hecke.ambient_rank(image(from_zero)) == 2
  @test kernel(from_zero) == Z
  @test is_injective(from_zero)
  @test !is_surjective(from_zero)
  @test iszero(from_zero(zero(Z)))
  @test iszero(preimage(from_zero, zero(M)))
  @test_throws ArgumentError preimage(from_zero, basis(M)[1])
  @test is_bijective(zero_iso)
  @test rank(image(zero_map)) == 0
  @test kernel(zero_map) == M
  @test !is_injective(zero_map)
  @test !is_surjective(zero_map)
  @test !is_bijective(zero_map)
  @test occursin("rank 0", sprint(show, MIME"text/plain"(), zero_iso))
end

@testset "function field PID maps" begin
  K, x = rational_function_field(QQ, "x")
  Rinf = localization(K, degree)
  for (R, t) in ((parent(numerator(x)), numerator(x)),
                 (Rinf, Rinf(inv(x))))
    M = Hecke.embedded_module(R, K, identity_matrix(K, 2))
    N = Hecke.embedded_module(R, K, K[1 0])
    B = basis(M)
    b = basis(N)[1]
    f = hom(M, M, [t*B[1], B[2]])
    v = B[1] + t*B[2]
    @test preimage(f, f(v)) == v
    @test is_injective(f)
    @test !is_surjective(f)
    @test !is_bijective(f)
    @test rank(kernel(f)) == 0
    s = image(Hecke.fraction_map(M), t)
    @test image(f) == Hecke.embedded_module(R, K, K[s 0; 0 1])

    g = hom(M, N, [t*b, b])
    @test image(g) == N
    @test kernel(g) == Hecke.embedded_module(R, K, K[-1 s])
    @test !is_injective(g)
    @test is_surjective(g)
    @test !is_bijective(g)
    @test g(preimage(g, b)) == b
  end
end

@testset "PID homomorphisms from generators" begin
  M = Hecke.embedded_module(ZZ, QQ, QQ[1//2 0 0; 0 3 0])
  N = Hecke.embedded_module(ZZ, QQ, identity_matrix(QQ, 2))
  B = basis(M)
  D = basis(N)
  v = D[1] + 2*D[2]
  w = 3*D[1] - D[2]
  imgs = [2*B[1] => 2*v, 3*B[1] => 3*v,
          2*B[2] => 2*w, 3*B[2] => 3*w,
          B[1] + B[2] => v + w, zero(M) => zero(N)]
  f = (@inferred hom(M, N, imgs))
  @test domain(f) === M
  @test codomain(f) === N
  @test all(f(x) == y for (x, y) in imgs)
  @test f(B[1]) == v
  @test f(B[2]) == w
  @test f(3*B[1] - 2*B[2]) == 3*v - 2*w

  @test_throws ArgumentError hom(M, N, [2*B[1] => 2*v, B[2] => w])
  @test_throws ArgumentError hom(M, N, [B[1] => v])
  @test_throws ArgumentError hom(M, N, Pair[])
  @test_throws ArgumentError hom(M, N,
                   [B[1] => v, B[2] => w, B[1] + B[2] => v + w + D[1]])
  @test_throws ArgumentError hom(M, N, [B[1] => v, B[2] => w,
                                        B[1] => v + D[1]])
  @test_throws ArgumentError hom(M, N, [B[1] => v, B[2] => w,
                                        zero(M) => D[1]])
  @test_throws ArgumentError hom(M, N, [D[1] => v, B[2] => w])
  @test_throws ArgumentError hom(M, N, [B[1] => B[1], B[2] => w])

  Z = Hecke.zero_embedded_module(ZZ, QQ, 3)
  for assignments in (Pair[], [zero(Z) => zero(N)])
    f = hom(Z, N, assignments)
    @test iszero(f(zero(Z)))
    @test domain(f) === Z
    @test codomain(f) === N
  end
  @test_throws ArgumentError hom(Z, N, [zero(Z) => D[1]])
  to_zero = hom(M, Z, [2*B[1] => zero(Z), 3*B[1] => zero(Z),
                       B[2] => zero(Z)])
  @test iszero(to_zero(B[1]))
  @test iszero(to_zero(B[2]))
end

@testset "generator images in generic codomains" begin
  M = Hecke.embedded_module(ZZ, QQ, identity_matrix(QQ, 2))
  B = basis(M)
  F, = residue_ring(ZZ, 6)
  for (X, a, b) in ((ZZ, ZZ(5), ZZ(-2)),
                    (QQ, QQ(1)//3, QQ(5)//7), (F, F(2), F(5)))
    f = hom(M, X, [2*B[1] => 2*a, 3*B[1] => 3*a, B[2] => b])
    @test f(B[1]) == a
    @test f(B[2]) == b
    @test f(4*B[1] - B[2]) == 4*a - b
    @test_throws ArgumentError hom(M, X, [B[1] => a, B[2] => b,
                                          zero(M) => one(X)])
  end
  @test_throws ArgumentError hom(M, ZZ, [B[1] => QQ(1), B[2] => QQ(2)])
end

@testset "generator images over function field PIDs" begin
  K, x = rational_function_field(QQ, "x")
  Rinf = localization(K, degree)
  for (R, t) in ((parent(numerator(x)), numerator(x)),
                 (Rinf, Rinf(inv(x))))
    M = Hecke.embedded_module(R, K, identity_matrix(K, 2))
    N = Hecke.embedded_module(R, K, K[1 0])
    B = basis(M)
    b = basis(N)[1]
    f = hom(M, N, [t*B[1] => t*b, (1-t)*B[1] => (1-t)*b,
                    B[2] => t*b])
    @test f(B[1]) == b
    @test f(B[2]) == t*b
    @test f(B[1] + t*B[2]) == b + t^2*b
    @test_throws ArgumentError hom(M, N, [t*B[1] => t*b, B[2] => t*b])
    @test_throws ArgumentError hom(M, N, [t*B[1] => t*b,
                                          (1-t)*B[1] => (1-t)*b + b,
                                          B[2] => t*b])
  end
end
