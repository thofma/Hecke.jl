@testset "Associative algebra lattice quotients" begin
  @testset "Residue vector spaces over PIDs" begin
    Kfun, t = rational_function_field(GF(3), "t")
    Rpoly = parent(numerator(t))
    Rinf = localization(Kfun, degree)
    for (R, K, p) in ((ZZ, QQ, ZZ(3)),
                      (Rpoly, Kfun, numerator(t)^2 + 1),
                      (Rinf, Kfun, Rinf(inv(t))))
      A = matrix_algebra(K, 2)
      B = basis(A)
      s = K(p)
      L = Hecke.lattice(A, R, Hecke.coordinates(A, [inv(s)*B[1], s*B[2]]);
                        is_basis_matrix = true)
      b = L.(basis(L))
      N = Hecke.lattice(A, R, [Hecke.elem_in_algebra(b[1] + b[2]),
                              Hecke.elem_in_algebra(p*b[2])])
      V, f, RtoF = @inferred Hecke.quotient_vector_space(L, p)
      W, g, RtoG = @inferred Hecke.quotient_vector_space(L, N, p)
      F, G = base_ring(V), base_ring(W)
      x = 5*b[1] - 4*b[2]
      c = R === Rpoly ? numerator(t) : R === Rinf ? Rinf((t + 1)/(t + 2)) : ZZ(5)

      @test dim(V) == 2 && dim(W) == 1
      @test order(F) == order(G) == (R === Rpoly ? 9 : 3)
      @test (@inferred f(x)) == V([F(2), F(2)])
      @test f(b[1]) == V([one(F), zero(F)])
      @test f(b[2]) == V([zero(F), one(F)])
      @test g(b[1]) == -g(b[2]) && !iszero(g(b[1]))
      @test iszero(g(b[1] + b[2]))
      for (Q, q, RtoH, D) in ((V, f, RtoF, p*L), (W, g, RtoG, N))
        @test q isa Hecke.AssociativeAlgebraLatticeMap
        @test (@inferred domain(q)) === L
        @test (@inferred codomain(q)) === Q
        @test !applicable(matrix, q)
        uq = @inferred Hecke.underlying_map(q)
        @test domain(uq) === Hecke.underlying_module(L)
        @test codomain(uq) === Q
        @test domain(RtoH) === R && codomain(RtoH) === base_ring(Q)
        @test (@inferred image(q, x)) == uq(Hecke.elem_in_module(x))
        @test q(x + b[1]) == q(x) + q(b[1])
        @test q(c*x) == RtoH(c)*q(x)
        @test iszero(q(p*x))
        @test (@inferred image(q)) === Q
        Dq = @inferred kernel(q)
        @test Dq == D
        @test algebra(Dq) === A && base_ring(Dq) === R
        @test Hecke.ambient_rank(Dq) == dim(A)
        @test all(iszero(q(L(a))) for a in basis(Dq))
        @test !(@inferred is_injective(q))
        @test (@inferred is_surjective(q))
        @test !(@inferred is_bijective(q))
        for y in (zero(Q), q(x), base_ring(Q)(1)*q(b[1]))
          z = @inferred preimage(q, y)
          @test parent(z) === L
          @test q(z) == y
          @test q(q \ y) == y
        end
        @test x - preimage(q, q(x)) in Dq
        @test iszero(preimage(q, zero(Q)))
        @test occursin("Homomorphism from an associative algebra lattice", sprint(show, MIME"text/plain"(), q))
        @test occursin(" -> ", sprint(show, MIME"text/plain"(), q))
        @test (@inferred show(IOBuffer(), MIME"text/plain"(), q)) === nothing
        @test (@inferred show(IOBuffer(), q)) === nothing

        Lequal = Hecke.lattice(A, R, basis(L))
        @test_throws ArgumentError q(Lequal(Hecke.elem_in_algebra(x)))
        @test_throws ArgumentError preimage(q, x)
        @test_throws ArgumentError Hecke.AssociativeAlgebraLatticeMap(Lequal, Q, uq)
        other_Q, = Hecke.quotient_vector_space(L, p)
        @test_throws ArgumentError preimage(q, zero(other_Q))
        @test_throws ArgumentError Hecke.AssociativeAlgebraLatticeMap(L, other_Q, uq)

        h = compose(id_hom(L), q)
        @test domain(h) === L && codomain(h) === Q
        @test h(x) == (id_hom(L)*q)(x) == q(x)
        first = hom(L, L, [b[1] + b[2], b[2]])
        @test compose(first, q)(x) == q(first(x))
        @test_throws ArgumentError compose(id_hom(Lequal), q)
      end
      @test Hecke.underlying_module(kernel(g)) === Hecke.underlying_module(N)
      for badp in (zero(R), one(R), p^2)
        @test_throws ArgumentError Hecke.quotient_vector_space(L, badp)
        @test_throws ArgumentError Hecke.quotient_vector_space(L, N, badp)
      end
    end
  end

  @testset "Module quotients, torsion, and free parts" begin
    Kfun, t = rational_function_field(GF(3), "t")
    Rpoly = parent(numerator(t))
    Rinf = localization(Kfun, degree)
    for (R, K, p) in ((ZZ, QQ, ZZ(3)), (Rpoly, Kfun, numerator(t)),
                      (Rinf, Kfun, Rinf(inv(t))))
      A = matrix_algebra(K, 2)
      B = basis(A)
      L = Hecke.lattice(A, R, [B[1], B[2]])
      b = L.(basis(L))
      N = Hecke.lattice(A, R, [K(p)*B[1]])
      Q, q = @inferred quo(L, N)
      @test domain(q) === L && codomain(q) === Q
      @test image(q) === Q && kernel(q) == N
      @test Hecke.underlying_module(kernel(q)) === Hecke.underlying_module(N)
      @test !iszero(q(b[1])) && iszero(q(p*b[1]))
      @test !iszero(q(p*b[2]))
      @test q(2*b[1] + b[2]) == R(2)*q(b[1]) + q(b[2])
      @test !is_injective(q) && is_surjective(q) && !is_bijective(q)
      x = b[1] + p*b[2]
      z = @inferred preimage(q, q(x))
      @test parent(z) === L && q(z) == q(x)
      @test x - z in N
      @test image(q, x) == Hecke.underlying_map(q)(Hecke.elem_in_module(x))
      @test compose(id_hom(L), q)(x) == q(x)
      @test occursin("Homomorphism from an associative algebra lattice", sprint(show, MIME"text/plain"(), q))
      other_Q, other_q = quo(L, N)
      @test_throws ArgumentError preimage(q, other_q(x))
      @test_throws ArgumentError preimage(q, b[1])
      @test_throws ArgumentError q(N(K(p)*B[1]))
    end
  end

  @testset "Zero quotients and zero lattices" begin
    A = matrix_algebra(QQ, 2)
    L = Hecke.lattice(A, ZZ, basis(A)[1:2])
    Z = Hecke.zero_lattice(A, ZZ)
    for (M, N) in ((L, Z), (L, L), (Z, Z))
      Q, q = @inferred quo(M, N)
      @test domain(q) === M && codomain(q) === Q
      @test image(q) === Q && kernel(q) == N
      @test iszero(q(zero(M))) && iszero(preimage(q, zero(Q)))
      @test is_injective(q) == iszero(N)
      @test is_surjective(q) && is_bijective(q) == iszero(N)
      @test show(IOBuffer(), MIME"text/plain"(), q) === nothing
    end
    for (V, f, _) in (Hecke.quotient_vector_space(L, L, ZZ(3)),
                       Hecke.quotient_vector_space(Z, ZZ(3)),
                       Hecke.quotient_vector_space(Z, Z, ZZ(3)))
      M = domain(f)
      @test dim(V) == 0
      @test codomain(f) === V && image(f) === V
      @test kernel(f) == M
      @test iszero(f(zero(M))) && iszero(preimage(f, zero(V)))
      @test is_surjective(f) && is_injective(f) == iszero(M)
      @test is_bijective(f) == iszero(M)
      @test Hecke.ambient_rank(kernel(f)) == dim(A)
      @test show(IOBuffer(), MIME"text/plain"(), f) === nothing
    end
  end

  @testset "Delegated validation" begin
    A = matrix_algebra(QQ, 2)
    B = basis(A)
    L = Hecke.lattice(A, ZZ, B[1:2])
    larger = QQ(1//2)*L
    outside = Hecke.lattice(A, ZZ, [B[3]])
    other_A = matrix_algebra(QQ, 2)
    incompatible = Hecke.lattice(other_A, ZZ, basis(other_A)[1:2])
    for N in (larger, outside, incompatible)
      @test_throws ArgumentError quo(L, N)
      @test_throws ArgumentError Hecke.quotient_vector_space(L, N, ZZ(3))
    end
    for N in (Hecke.lattice(A, ZZ, [B[1]]),
              Hecke.lattice(A, ZZ, [B[1], 9*B[2]]))
      @test_throws ArgumentError Hecke.quotient_vector_space(L, N, ZZ(3))
    end
    K, t = rational_function_field(GF(3), "t")
    R = parent(numerator(t))
    C = matrix_algebra(K, 2)
    P = Hecke.lattice(C, R, basis(C))
    @test_throws ArgumentError quo(L, P)
    @test_throws ArgumentError Hecke.quotient_vector_space(L, P, ZZ(3))
    @test_throws ArgumentError Hecke.quotient_vector_space(L, numerator(t))
    @test_throws ArgumentError Hecke.quotient_vector_space(L, L, numerator(t))
  end
end
