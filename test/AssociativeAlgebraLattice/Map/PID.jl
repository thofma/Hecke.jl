@testset "Generator assignments and coefficient rings" begin
  A = matrix_algebra(QQ, 2)
  B = basis(A)
  L = Hecke.lattice(A, ZZ, [QQ(1//2)*B[1], 3*B[2]])
  N = Hecke.lattice(A, ZZ, B[3:4])
  b, d = L.(basis(L)), N.(basis(N))
  v, w = d[1] + 2*d[2], 3*d[1] - d[2]
  assignments = [2*b[1] => 2*v, 3*b[1] => 3*v,
                 2*b[2] => 2*w, 3*b[2] => 3*w,
                 b[1] + b[2] => v + w, zero(L) => zero(N)]
  f = @inferred hom(L, N, assignments)
  @test all(f(x) == y for (x, y) in assignments)
  @test f(b[1]) == v && f(b[2]) == w
  mixed = Pair[Hecke.elem_in_algebra(b[1]) => v,
               b[2] => Hecke.elem_in_algebra(w)]
  g = @inferred hom(L, N, mixed)
  @test g(3*b[1] - 2*b[2]) == f(3*b[1] - 2*b[2])
  Lequal = Hecke.lattice(A, ZZ, basis(L))
  Nequal = Hecke.lattice(A, ZZ, basis(N))
  @test_throws ArgumentError hom(L, N, [Lequal(basis(L)[1]) => v, b[2] => w])
  @test_throws ArgumentError hom(L, N, [b[1] => Nequal(basis(N)[1]), b[2] => w])
  @test_throws ArgumentError hom(L, N, [B[3] => v, b[2] => w])
  @test_throws ArgumentError hom(L, N, [b[1] => B[1], b[2] => w])
  @test_throws ArgumentError hom(L, N, [2*b[1] => 2*v, b[2] => w])
  @test_throws ArgumentError hom(L, N, [b[1] => v])
  @test_throws ArgumentError hom(L, N, Pair[])
  @test_throws ArgumentError hom(L, N, [b[1] => v, b[2] => w,
                                        b[1] + b[2] => v + w + d[1]])
  @test_throws ArgumentError hom(L, N, [b[1] => v, b[2] => w, zero(L) => d[1]])

  F, t = rational_function_field(GF(7), "t")
  R = parent(numerator(t))
  C = group_algebra(F, small_group(2, 1))
  P = Hecke.lattice(C, R, basis(C))
  @test_throws ArgumentError hom(L, P, P.(basis(P)))
  @test_throws ArgumentError hom(L, P, [b[1] => P(basis(C)[1])])
  @test_throws ArgumentError Hecke.AssociativeAlgebraLatticeMap(L, P, Hecke.underlying_map(f))
  for S in (R, localization(F, degree))
    V = Hecke.lattice(C, S, basis(C))
    e = V.(basis(V))
    s = S === R ? numerator(t) : S(inv(t))
    h = hom(V, V, [s*e[1] => s*e[2], (1-s)*e[1] => (1-s)*e[2], e[2] => s*e[1]])
    @test h(e[1] + s*e[2]) == e[2] + s^2*e[1]
  end
end

@testset "General codomains" begin
  A = matrix_algebra(QQ, 2)
  B = basis(A)
  L = Hecke.lattice(A, ZZ, [QQ(1//2)*B[1], 3*B[2]])
  b = L.(basis(L))
  x = 4*b[1] - b[2]
  F, = residue_ring(ZZ, 6)
  V = free_module(ZZ, 2)
  v = gens(V)
  Q, q = quo(L, 6*L)
  for (X, a, c) in ((ZZ, ZZ(5), ZZ(-2)),
                    (QQ, QQ(1)//3, QQ(5)//7),
                    (F, F(2), F(5)),
                    (V, v[1] + 2*v[2], 3*v[1] - v[2]),
                    (Q, q(b[1]), q(b[2])))
    f = hom(L, X, [a, c])
    assignments = Pair[2*b[1] => 2*a, 3*b[1] => 3*a,
                       Hecke.elem_in_algebra(b[2]) => c, zero(L) => zero(X)]
    g = hom(L, X, assignments)
    @test f isa Hecke.AssociativeAlgebraLatticeMap
    @test domain(f) === L && codomain(f) === X
    @test domain(Hecke.underlying_map(f)) === Hecke.underlying_module(L)
    @test codomain(Hecke.underlying_map(f)) === X
    @test parent(f(x)) === X
    @test image(f, x) == f(x) == g(x) == 4*a - c
    @test all(g(y) == z for (y, z) in assignments if y isa Hecke.AssociativeAlgebraLatticeElem)
    @test f(x + b[1]) == f(x) + a
    @test f(2*x) == 2*f(x)
    h = compose(id_hom(L), f)
    @test domain(h) === L && codomain(h) === X
    @test h(x) == (id_hom(L)*f)(x) == f(x)
    @test occursin("Homomorphism from an associative algebra lattice", sprint(show, MIME"text/plain"(), f))
    @test occursin(" -> ", sprint(show, MIME"text/plain"(), g))
    @test_throws ArgumentError hom(L, X, [a])
    @test_throws ArgumentError hom(L, X, [2*b[1] => 2*a, b[2] => c])
    @test_throws ArgumentError hom(L, X, Pair[])
    @test_throws ArgumentError hom(L, X, [b[1] => a, b[2] => c,
                                          b[1] + b[2] => a + c + a])
    @test_throws ErrorException preimage(f, zero(X))
  end
  Lequal = Hecke.lattice(A, ZZ, basis(L))
  f = hom(L, ZZ, ZZRingElem[5, -2])
  @test_throws ArgumentError f(Lequal(Hecke.elem_in_algebra(x)))
  @test_throws ArgumentError preimage(f, QQ(0))
  @test_throws ArgumentError hom(L, ZZ, QQFieldElem[1, 2])
  @test_throws ArgumentError hom(L, ZZ, [b[1] => QQ(1), b[2] => QQ(2)])
  @test_throws ArgumentError hom(L, ZZ, [Lequal(basis(L)[1]) => ZZ(1), b[2] => ZZ(2)])
  @test_throws ArgumentError hom(L, ZZ, [B[3] => ZZ(1), b[2] => ZZ(2)])
  @test_throws ArgumentError hom(L, ZZ, [b[1] => ZZ(1), b[2] => ZZ(2), zero(L) => ZZ(1)])

  Z = Hecke.zero_lattice(A, ZZ)
  for assignments in (ZZRingElem[], Pair[], [zero(Z) => ZZ(0)], [zero(A) => ZZ(0)])
    h = hom(Z, ZZ, assignments)
    @test domain(h) === Z && codomain(h) === ZZ
    @test h(zero(Z)) == zero(ZZ)
  end
  @test_throws ArgumentError hom(Z, ZZ, [zero(Z) => ZZ(1)])

  K, t = rational_function_field(GF(7), "t")
  Rinf = localization(K, degree)
  C = group_algebra(K, small_group(2, 1))
  for (R, s) in ((parent(numerator(t)), numerator(t)), (Rinf, Rinf(inv(t))))
    P = Hecke.lattice(C, R, basis(C))
    e = P.(basis(P))
    for X in (R, K)
      a, c = X(s), one(X)
      h = hom(P, X, [a, c])
      g = hom(P, X, [s*e[1] => s*a, (1-s)*e[1] => (1-s)*a, e[2] => c])
      @test h(e[1] + s*e[2]) == g(e[1] + s*e[2]) == a + s*c
      @test h(s*e[1]) == s*h(e[1])
    end
  end
end

@testset "Embedded module codomains" begin
  A = matrix_algebra(QQ, 2)
  B = basis(A)
  L = Hecke.lattice(A, ZZ, [QQ(1//2)*B[1], 3*B[2]])
  b = L.(basis(L))
  P = Hecke.embedded_module(ZZ, QQ, QQ[0 1//5]; overstructure = Ref(:target))
  expected_image = Hecke.embedded_module(ZZ, QQ, QQ[0 2//5];
                                        overstructure = Hecke.overstructure(P))
  d = basis(P)[1]
  f = hom(L, P, [4*d, 6*d])
  g = hom(L, P, [2*b[1] => 8*d, 3*b[1] => 12*d, b[2] => 6*d])
  x = 3*b[1] - b[2]
  @test parent(f(x)) === P
  @test f(x) == g(x) == 6*d
  @test f(preimage(f, 2*d)) == 2*d
  @test parent(preimage(f, 2*d)) === L
  @test_throws ArgumentError preimage(f, d)
  @test rank(kernel(f)) == rank(image(f)) == 1
  @test kernel(f) == Hecke.lattice(A, ZZ, [Hecke.elem_in_algebra(-3*b[1] + 2*b[2])])
  @test image(f) == expected_image
  @test image(f) isa Hecke.EmbeddedModule
  @test Hecke.overstructure(image(f)) === Hecke.overstructure(P)
  @test !is_injective(f) && !is_surjective(f) && !is_bijective(f)
  onto = hom(L, P, [2*d, 3*d])
  @test is_surjective(onto) && image(onto) == P

  u = hom(L, L, [2*b[1], b[2]])
  @test u(x) == 6*b[1] - b[2]
  h = compose(u, f)
  @test h isa Hecke.AssociativeAlgebraLatticeMap
  @test domain(h) === L && codomain(h) === P
  @test h(x) == f(u(x)) == 18*d
  @test h(preimage(h, 2*d)) == 2*d
  @test image(h) == expected_image && rank(kernel(h)) == 1
  @test compose(id_hom(L), f)(x) == f(x)

  Pequal = Hecke.embedded_module(ZZ, QQ, basis_matrix(P); overstructure = Hecke.overstructure(P))
  @test Pequal == P && Pequal !== P
  @test_throws ArgumentError preimage(f, basis(Pequal)[1])
  @test_throws ArgumentError hom(L, P, [basis(Pequal)[1], d])
  @test_throws ArgumentError hom(L, P, [b[1] => basis(Pequal)[1], b[2] => d])
  K, t = rational_function_field(GF(7), "t")
  S = Hecke.embedded_module(parent(numerator(t)), K, identity_matrix(K, 1))
  @test_throws ArgumentError hom(L, S, [basis(S)[1], basis(S)[1]])
  @test_throws ArgumentError hom(L, S, [b[1] => basis(S)[1], b[2] => basis(S)[1]])
end
