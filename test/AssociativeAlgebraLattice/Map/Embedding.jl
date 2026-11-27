@testset "Inclusions and identities" begin
  A = matrix_algebra(QQ, 2)
  B = basis(A)
  L = Hecke.lattice(A, ZZ, [QQ(1//2)*B[1], 3*B[2]])
  N = Hecke.lattice(A, ZZ, [2*B[1]])
  f = @inferred Hecke.inclusion_map(N, L)
  x = N(6*B[1])
  @test f(x) == L(6*B[1])
  @test (@inferred preimage(f, f(x))) == x
  @test Hecke.elem_in_algebra(f(x)) == Hecke.elem_in_algebra(x)
  @test image(f) == N && iszero(kernel(f))
  @test Hecke.underlying_module(image(f)) === Hecke.underlying_module(N)
  @test is_injective(f) && !is_surjective(f) && !is_bijective(f)
  @test_throws ArgumentError preimage(f, L(QQ(1//2)*B[1]))
  @test_throws ArgumentError preimage(f, L(3*B[2]))
  @test_throws ArgumentError Hecke.inclusion_map(L, N)

  P = Hecke.lattice(A, ZZ, Hecke.coordinates(A, [QQ(1//2)*B[1] + 3*B[2], 3*B[2]]);
                    is_basis_matrix = true)
  g = Hecke.inclusion_map(P, L)
  y = P(basis(P)[1])
  @test coordinates(g(y)) == ZZRingElem[1, 1]
  @test preimage(g, g(y)) == y
  @test is_bijective(g)
  id = @inferred id_hom(L)
  @test domain(id) === codomain(id) === L
  @test id(L(basis(L)[1])) == L(basis(L)[1])
  @test is_bijective(id) && image(id) == L && iszero(kernel(id))
  Aother = matrix_algebra(QQ, 2)
  other = Hecke.lattice(Aother, ZZ, basis(Aother))
  @test_throws ArgumentError Hecke.inclusion_map(L, other)
end

@testset "Dedekind inclusions with nonprincipal ideals" begin
  K, a = quadratic_field(-5)
  O = maximal_order(K)
  J = ideal(O, 2, O(1 + a))
  @test !is_principal(J)
  I = fractional_ideal(O, J)
  A = matrix_algebra(K, 2)
  B = basis(A)
  L = Hecke.lattice(A, O, pseudo_matrix(O, Hecke.coordinates(A, B[1:2]), [I, I]);
                    is_basis_matrix = true)
  N = Hecke.lattice(A, O, pseudo_matrix(O, Hecke.coordinates(A, [B[1]]), [ZZ(2)*I]);
                    is_basis_matrix = true)
  U = 2*N
  f = @inferred Hecke.inclusion_map(N, L)
  x = N(2*(1 + a)*B[1])
  @test f(x) == L(2*(1 + a)*B[1])
  @test preimage(f, f(x)) == x
  @test_throws ArgumentError preimage(f, L((1 + a)*B[1]))
  @test image(f) == N && iszero(kernel(f))
  @test algebra(kernel(f)) === algebra(image(f)) === A
  @test base_ring(kernel(f)) === base_ring(image(f)) === O
  @test is_injective(f) && !is_surjective(f) && !is_bijective(f)
  @test_throws ArgumentError Hecke.inclusion_map(L, N)
  id = @inferred id_hom(L)
  @test is_bijective(id) && id(f(x)) == f(x)
  @test compose(f, id)(x) == f(x)
  g = @inferred compose(Hecke.inclusion_map(U, N), f)
  y = U(4*(1 + a)*B[1])
  @test g(y) == L(Hecke.elem_in_algebra(y))
  @test preimage(g, g(y)) == y
  @test image(g) == U && iszero(kernel(g))

  P = Hecke.lattice(A, O, pseudo_matrix(O, Hecke.coordinates(A, [B[1], B[1] + B[2]]), [I, I]);
                    is_basis_matrix = true)
  equal_inc = Hecke.inclusion_map(P, L)
  z = P((1 + a)*(B[1] + B[2]))
  @test is_bijective(equal_inc)
  @test coordinates(equal_inc(z)) == elem_type(K)[1 + a, 1 + a]
  @test preimage(equal_inc, equal_inc(z)) == z
  @test_throws ArgumentError hom(L, L, [f(x)])
  @test_throws ArgumentError hom(L, L, [f(x) => f(x)])
  @test_throws ArgumentError hom(L, O, [O(1)])
  @test_throws ArgumentError hom(L, O, [f(x) => O(1)])
  @test occursin("Homomorphism of associative algebra lattices", sprint(show, MIME"text/plain"(), f))
  @test !occursin("\ndefined by\n", sprint(show, MIME"text/plain"(), f))
  @test (@inferred show(IOBuffer(), MIME"text/plain"(), f)) === nothing
  Z = Hecke.zero_lattice(A, O)
  zero_inc = Hecke.inclusion_map(Z, L)
  @test iszero(zero_inc(zero(Z))) && iszero(preimage(zero_inc, zero(L)))
  @test iszero(image(zero_inc)) && iszero(kernel(zero_inc))
  @test is_bijective(id_hom(Z))
end
