@testset "Composition and composite preimages" begin
  A = matrix_algebra(QQ, 2)
  B = basis(A)
  L = Hecke.lattice(A, ZZ, B[1:2])
  N = Hecke.lattice(A, ZZ, B[2:3])
  P = Hecke.lattice(A, ZZ, [QQ(1//2)*B[4]])
  b, c = L.(basis(L)), N.(basis(N))
  d = P(basis(P)[1])
  f = hom(L, N, [2*c[1], c[2]])
  g = hom(N, P, [d, 3*d])
  x = 3*b[1] - b[2]
  @test g(f(x)) == 3*d
  h = @inferred compose(f, g)
  @test h isa Hecke.AssociativeAlgebraLatticeMap
  @test domain(h) === L && codomain(h) === P
  @test (@inferred h(x)) == g(f(x)) == (f*g)(x)
  @test h(preimage(h, d)) == d
  @test image(h) == P && rank(kernel(h)) == 1
  @test !is_injective(h) && is_surjective(h)
  @test compose(id_hom(L), f)(x) == compose(f, id_hom(N))(x) == f(x)
  k = hom(P, L, [b[1] + b[2]])
  @test compose(compose(f, g), k)(x) == compose(f, compose(g, k))(x)
  Nequal = Hecke.lattice(A, ZZ, Hecke.underlying_module(N))
  @test Nequal !== N && Hecke.underlying_module(Nequal) === Hecke.underlying_module(N)
  gequal = hom(Nequal, P, [d, 3*d])
  @test_throws ArgumentError compose(f, gequal)
  @test_throws ArgumentError f*gequal
  @test_throws ArgumentError compose(g, f)

  U = Hecke.lattice(A, ZZ, [4*B[1]])
  V = QQ(1//2)*N
  before = compose(Hecke.inclusion_map(U, L), f)
  after = compose(f, Hecke.inclusion_map(N, V))
  @test before(U(4*B[1])) == N(8*B[2])
  @test after(x) == V(Hecke.elem_in_algebra(f(x)))
  inc = compose(Hecke.inclusion_map(U, L), Hecke.inclusion_map(L, QQ(1//2)*L))
  @test is_injective(inc)

  S = Hecke.lattice(A, ZZ, [B[1]])
  T = Hecke.lattice(A, ZZ, B[2:3])
  W = Hecke.lattice(A, ZZ, [B[4]])
  e, v, w = S(B[1]), T.(basis(T)), W(B[4])
  gg = hom(T, W, [w, w])
  lift = preimage(gg, w)
  chosen = iszero(coordinates(lift)[2]) ? v[2] : v[1]
  ff = hom(S, T, [chosen])
  @test_throws ArgumentError preimage(ff, lift)
  hh = compose(ff, gg)
  @test preimage(hh, w) == e
  @test is_bijective(hh)
end

@testset "Zero ranks" begin
  A = matrix_algebra(QQ, 2)
  B = basis(A)
  for r in 0:1, s in 0:1, t in 0:1
    L = Hecke.lattice(A, ZZ, B[1:r])
    N = Hecke.lattice(A, ZZ, B[2:1+s])
    P = Hecke.lattice(A, ZZ, B[3:2+t])
    f = hom(L, N, [zero(N) for _ in 1:r])
    g = hom(N, P, [zero(P) for _ in 1:s])
    h = @inferred compose(f, g)
    @test iszero(f(zero(L))) && iszero(h(zero(L)))
    @test iszero(preimage(f, zero(N))) && iszero(preimage(h, zero(P)))
    @test kernel(f) == L && kernel(h) == L
    @test iszero(image(f)) && iszero(image(h))
    @test algebra(image(f)) === A && base_ring(image(f)) === ZZ
    @test Hecke.ambient_rank(kernel(f)) == Hecke.ambient_rank(image(f)) == dim(A)
    @test is_injective(f) == is_injective(h) == iszero(r)
    @test is_surjective(f) == iszero(s)
    @test is_surjective(h) == iszero(t)
    @test is_bijective(f) == (iszero(r) && iszero(s))
    @test show(IOBuffer(), MIME"text/plain"(), f) === nothing
    from_pairs = hom(L, N, [x => zero(N) for x in L.(basis(L))])
    @test iszero(from_pairs(zero(L)))
  end
  Z = Hecke.zero_lattice(A, ZZ)
  L = Hecke.lattice(A, ZZ, [B[1]])
  for assignments in (Pair[], [zero(Z) => zero(L)], [zero(A) => zero(A)])
    f = hom(Z, L, assignments)
    @test domain(f) === Z && codomain(f) === L
    @test iszero(f(zero(Z)))
  end
  @test_throws ArgumentError hom(Z, L, [zero(Z) => L(B[1])])
  inc = Hecke.inclusion_map(Z, L)
  @test is_injective(inc) && !is_surjective(inc)
  @test iszero(preimage(inc, zero(L)))
  @test_throws ArgumentError preimage(inc, L(B[1]))
  @test is_bijective(id_hom(Z))
end
