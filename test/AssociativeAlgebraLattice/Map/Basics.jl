@testset "PID homomorphisms and module interface" begin
  F, t = rational_function_field(GF(7), "t")
  Rinf = localization(F, degree)
  for (R, K, s) in ((ZZ, QQ, ZZ(2)),
                    (parent(numerator(t)), F, numerator(t)),
                    (Rinf, F, Rinf(inv(t))))
    A = matrix_algebra(K, 2)
    C = group_algebra(K, small_group(2, 1))
    B, D = basis(A), basis(C)
    L = Hecke.lattice(A, R, Hecke.coordinates(A, [K(1//2)*B[1], 3*B[2]]);
                      is_basis_matrix = true)
    N = Hecke.lattice(C, R, [D[1]])
    b = L.(basis(L))
    d = N(D[1])
    f = @inferred hom(L, N, [2*s*d, 3*s*d])
    x = 3*b[1] - b[2]

    @test f isa Hecke.AssociativeAlgebraLatticeMap
    @test !applicable(matrix, f)
    @test (@inferred domain(f)) === L
    @test (@inferred codomain(f)) === N
    mf = @inferred Hecke.underlying_map(f)
    @test domain(mf) === Hecke.underlying_module(L)
    @test codomain(mf) === Hecke.underlying_module(N)
    @test (@inferred image(f, x)) == 3*s*d
    @test (@inferred f(x)) == 3*s*d
    @test parent(f(x)) === N
    @test f(x + b[1]) == f(x) + f(b[1])
    @test f(s*x) == s*f(x)
    @test f(preimage(f, s*d)) == s*d
    @test parent(@inferred preimage(f, s*d)) === L
    @test f(f \ (s*d)) == s*d
    @test_throws ArgumentError preimage(f, d)
    @test_throws ArgumentError f(d)
    @test_throws ArgumentError preimage(f, b[1])

    I = @inferred image(f)
    Z = @inferred kernel(f)
    @test I == Hecke.lattice(C, R, [K(s)*D[1]])
    @test Z == Hecke.lattice(A, R, [Hecke.elem_in_algebra(-3*b[1] + 2*b[2])])
    @test algebra(I) === C && base_ring(I) === R
    @test algebra(Z) === A && base_ring(Z) === R
    @test issubset(I, N) && issubset(Z, L)
    @test rank(I) == rank(Z) == 1
    @test all(iszero(f(L(z))) for z in basis(Z))
    @test !(@inferred is_injective(f))
    @test !(@inferred is_surjective(f))
    @test !(@inferred is_bijective(f))

    onto = hom(L, N, Any[2*d, 3*D[1]])
    @test onto(x) == 3*d
    @test is_surjective(onto) && !is_injective(onto)
    iso = hom(L, L, [b[1] + s*b[2], b[2]])
    @test is_injective(iso) && is_surjective(iso) && is_bijective(iso)
    @test (@inferred preimage(iso, iso(x))) == x
    @test image(iso) == L && iszero(kernel(iso))
    wrapped = @inferred Hecke.AssociativeAlgebraLatticeMap(L, N, mf)
    @test wrapped(x) == f(x)
    @test Hecke.underlying_map(wrapped) === mf
    coordinates(f(x); copy = false)[1] = R(99)
    @test f(x) == 3*s*d
    @test x == 3*b[1] - b[2]

    text = sprint(show, MIME"text/plain"(), f)
    @test occursin("Homomorphism of associative algebra lattices", text)
    @test occursin("defined by", text) && occursin(" -> ", text)
    @test startswith(sprint(show, f), "Map: ")
    @test (@inferred show(IOBuffer(), MIME"text/plain"(), f)) === nothing
    @test (@inferred show(IOBuffer(), f)) === nothing

    Lequal = Hecke.lattice(A, R, basis(L))
    Nequal = Hecke.lattice(C, R, basis(N))
    @test Lequal == L && Lequal !== L
    @test Nequal == N && Nequal !== N
    @test_throws ArgumentError f(Lequal(Hecke.elem_in_algebra(x)))
    @test_throws ArgumentError preimage(f, Nequal(2*D[1]))
    @test_throws ArgumentError hom(L, N, [Nequal(D[1]), d])
    @test_throws ArgumentError hom(L, N, [D[2], D[1]])
    @test_throws ArgumentError hom(L, N, [d])
    @test_throws ArgumentError hom(L, N, [B[1], B[2]])
    @test_throws ArgumentError Hecke.AssociativeAlgebraLatticeMap(Lequal, N, mf)
    @test_throws ArgumentError Hecke.AssociativeAlgebraLatticeMap(L, Nequal, mf)
    Aother = matrix_algebra(K, 2)
    @test_throws ArgumentError hom(L, L, [basis(Aother)[1], basis(Aother)[2]])
  end
end
