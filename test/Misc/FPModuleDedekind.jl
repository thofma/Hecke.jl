@testset "Finitely presented modules over Dedekind domains" begin
  function test_dedekind_module(R, K, I, c)
    U = one(K)*R
    i = first(basis(I))
    a = K(last(basis(R)))
    C = K[c c; c 0; 0 c]
    A, B = [I, U], [I, I, U]
    Q = Hecke.FPModuleDedekind(R, A, C, B)
    x, y = Q([i, one(K)]), Q([zero(K), a])

    @test Q isa Hecke.AbstractAlgebra.Module{elem_type(R)}
    @test x isa Hecke.FPModuleDedekindElem
    @test base_ring(Q) === R
    @test Hecke.ring(Q) === R
    @test Hecke.overring(Q) === K
    @test base_ring_type(typeof(Q)) === typeof(R)
    @test elem_type(Q) === typeof(x)
    @test parent_type(typeof(x)) === typeof(Q)
    @test parent(x) === Q
    @test rank(Q) == 0
    @test Q(x) === x
    @test iszero(Q())
    @test iszero(zero(Q))
    @test iszero(zero(x))
    @test !iszero(x)
    @test iszero(R(c)*x)
    @test x + zero(Q) == x
    @test iszero(x - x)
    @test -(-x) == x
    @test R(a)*(x + y) == R(a)*x + R(a)*y
    @test x*R(a) == R(a)*x
    @test (2*x) + x == 3*x
    @test Q(matrix(K, 1, 2, [i, one(K)])) == x

    T = Hecke.FPModuleDedekind(R, [U], ZZ[2;;], [U])
    @test iszero(T([K(2)]))

    # Every ideal multiple of every relation must vanish. Equality and hashing
    # must also hold for representatives shifted by those multiples.
    for j in 1:nrows(C), b in basis(B[j])
      v = b .* C[j, :]
      @test iszero(Q(v))
      z = Q([i, one(K)] + v)
      @test z == x
      @test isequal(z, x)
      @test hash(z) == hash(x)
      @test length(Set([x, z])) == 1
    end

    @test deepcopy(x) == x
    @test parent(deepcopy(x)) === Q
    @test copy(x) == x
    v = coordinates(x)
    v[1] += i
    @test Q([i, one(K)]) == x
    v = [i, one(K)]
    z = Q(v)
    v[2] += one(K)
    @test z == x

    # Copy the matrix and ideal vectors, while sharing the ideals themselves.
    @test Hecke.coefficient_ideals(Q; copy = false)[1] === I
    @test Hecke.coefficient_ideals(relations(Q; copy = false))[1] === I
    C[1, 1] = zero(K)
    A[1] = U
    @test Hecke.matrix(relations(Q))[1, 1] == c
    ideals = Hecke.coefficient_ideals(Q)
    @test ideals !== Hecke.coefficient_ideals(Q; copy = false)
    @test ideals[1] === I
    ideals[1] = U
    @test Hecke.coefficient_ideals(Q; copy = false)[1] === I
    P = relations(Q)
    @test P !== relations(Q; copy = false)
    @test Hecke.coefficient_ideals(P) !== Hecke.coefficient_ideals(relations(Q; copy = false))
    @test Hecke.coefficient_ideals(P)[1] === I
    Hecke.matrix(P)[1, 1] = zero(K)
    Hecke.coefficient_ideals(P)[1] = U
    @test Hecke.matrix(relations(Q))[1, 1] == c
    @test Hecke.coefficient_ideals(relations(Q; copy = false))[1] === I

    @test_throws ArgumentError Q([i])
    @test_throws ArgumentError Q(identity_matrix(K, 2))
    @test_throws ArgumentError Hecke.FPModuleDedekind(R, [I], zero_matrix(K, 0, 2), typeof(I)[])
    @test_throws ArgumentError Hecke.FPModuleDedekind(R, [I], K[1;;], typeof(I)[])
    @test_throws ArgumentError Hecke.FPModuleDedekind(R, [c*I], K[1;;], [I])
    @test_throws ArgumentError Q([one(K), one(K)])
    other = Hecke.FPModuleDedekind(R, [I, U], K[c c; c 0; 0 c], [I, I, U])
    @test x != other([i, one(K)])
    @test_throws ArgumentError x + other([i, one(K)])
    @test_throws ArgumentError Q(other([i, one(K)]))

    # The projective part need not be free; fractional numerator ideals and
    # rectangular presentations must retain it.
    J = inv(c)*I
    F = Hecke.FPModuleDedekind(R, [J, U], K[c 0], [J])
    @test rank(F) == 1
    @test iszero(F([c*first(basis(J)), zero(K)]))
    @test !iszero(R(c)*F([zero(K), one(K)]))
    z = F([first(basis(J)), one(K)])
    w = F([first(basis(J)) + c*last(basis(J)), one(K)])
    @test z == w
    @test hash(z) == hash(w)

    # Skip zero rows and reduce a late pivot without changing free coordinates.
    G = Hecke.FPModuleDedekind(R, [J, U, U], K[0 c c; 0 0 0], [U, I])
    @test rank(G) == 2
    @test coordinates(G([first(basis(J)), zero(K), c])) == [first(basis(J)), -c, zero(K)]
    @test iszero(G([zero(K), c, c]))

    E = Hecke.FPModuleDedekind(R, [J], zero_matrix(K, 0, 1), typeof(J)[])
    e = E([first(basis(J))])
    @test rank(E) == 1
    @test coordinates(e) == [first(basis(J))]
    @test !iszero(R(c)*e)
    E = Hecke.FPModuleDedekind(R, [J], zero_matrix(ZZ, 0, 1), typeof(J)[])
    @test coordinates(E([first(basis(J))])) == [first(basis(J))]
    Z = Hecke.FPModuleDedekind(R, typeof(I)[], zero_matrix(K, 0, 0), typeof(I)[])
    @test rank(Z) == 0
    @test iszero(Z())
    @test coordinates(Z()) == elem_type(K)[]
    Z = Hecke.FPModuleDedekind(R, typeof(I)[], zero_matrix(K, 2, 0), [I, U])
    @test rank(Z) == 0
    @test iszero(Z())
    @test iszero(Hecke.FPModuleDedekind(R, [U], K[0;;], [U])([zero(K)]))
    @test !iszero(Hecke.FPModuleDedekind(R, [U], K[0;;], [U])([one(K)]))

    # A non-diagonal projective presentation with equal nonprincipal row ideals.
    D = K[1 1; 1 -1]
    T = Hecke.FPModuleDedekind(R, [I, I], D, [I, I])
    t = T([i, zero(K)])
    @test rank(T) == 0
    for b in basis(I), row in 1:2
      @test iszero(T(b .* D[row, :]))
      @test hash(t + T(b .* D[row, :])) == hash(t)
    end

    @test occursin("Finitely presented module", sprint(show, Q))
    @test show(IOBuffer(), x) === nothing
  end

  @testset "number-field order with nonprincipal ideals" begin
    K, a = quadratic_field(-5)
    R = maximal_order(K)
    I = fractional_ideal(R, ideal(R, 2, R(1 + a)))
    @test !is_principal(numerator(I))
    test_dedekind_module(R, K, I, K(2))
    U = fractional_ideal(R, 1)
    Q = Hecke.FPModuleDedekind(R, Hecke.pseudo_matrix(K[1;;], [I]))
    @test iszero(Q([K(2)]))
    @test Q([a]) == Q([K(1)])
    @test !iszero(Q([K(1)]))
    integral_Q = Hecke.FPModuleDedekind(R, [ideal(R, 1)], K[1;;], [numerator(I)])
    @test !iszero(integral_Q([K(1)]))
    @test iszero(integral_Q([K(2)]))
    for D in (ZZ[2;;], QQ[2;;])
      T = Hecke.FPModuleDedekind(R, [U], D, [U])
      @test !iszero(T([K(1)]))
      @test iszero(T([K(2)]))
    end
    T = Hecke.FPModuleDedekind(R, [U], QQ[1//2;;], [K(2)*U])
    @test iszero(T([K(1)]))
    for s in (1//1, QQ(1), 2//1, QQ(2))
      @test s*integral_Q([K(1)]) == Int(s)*integral_Q([K(1)])
      @test integral_Q([K(1)])*s == Int(s)*integral_Q([K(1)])
    end
    for s in (1//2, QQ(1, 2))
      @test_throws ErrorException s*integral_Q([K(1)])
      @test_throws ErrorException integral_Q([K(1)])*s
    end
    # Coprime relation ideals combine to the whole numerator.
    Q = Hecke.FPModuleDedekind(R, [U], K[1; 1;;], [I, fractional_ideal(R, 3)])
    @test iszero(Q([K(1)]))
    R2 = maximal_order(quadratic_field(-1)[1])
    @test_throws ArgumentError Hecke.FPModuleDedekind(R, [fractional_ideal(R2, 1)], zero_matrix(K, 0, 1), typeof(I)[])
    O = equation_order(quadratic_field(5)[1])
    @test_throws ArgumentError Hecke.FPModuleDedekind(O, [fractional_ideal(O, 1)], zero_matrix(Hecke.nf(O), 0, 1), Hecke.fractional_ideal_type(O)[])
  end

  @testset "non-simple number-field orders" begin
    _, t = polynomial_ring(QQ, :t)
    for polys in ([t^2 + 5], [t^2 + 5, t^2 + 7])
      K, a = number_field(polys)
      R = maximal_order(K)
      I = fractional_ideal(R, ideal(R, 2, R(1 + a[1])))
      test_dedekind_module(R, K, I, K(2))
    end
  end

  @testset "relative number-field order" begin
    k, a = quadratic_field(5)
    kx, x = polynomial_ring(k, :x)
    K, b = number_field(x^2 + 1, :b)
    R = maximal_order(K)
    U = K(1)*R
    @test Hecke.field(R) === K
    @test fractional_ideal(U) === U
    I = ideal(R, 1)
    @test fractional_ideal(I) == U
    T = Hecke.FPModuleDedekind(R, [I], K[2;;], [I])
    @test !iszero(T([K(1)]))
    @test iszero(T([K(2)]))
    Q = Hecke.FPModuleDedekind(R, [U], K[2;;], [U])
    @test Hecke.coefficient_ideals(Q; copy = false)[1] === U
    @test Hecke.coefficient_ideals(relations(Q; copy = false))[1] === U
    @test base_ring(Q) === R
    @test rank(Q) == 0
    @test !iszero(Q([K(1)]))
    @test iszero(Q([K(2)]))
    @test Q([b + 2]) == Q([b])
    @test hash(Q([b + 2])) == hash(Q([b]))
    @test iszero(R(b)*Q([K(2)]))
    for D in (ZZ[2;;], QQ[2;;])
      T = Hecke.FPModuleDedekind(R, [U], D, [U])
      @test !iszero(T([K(1)]))
      @test iszero(T([K(2)]))
    end
    for s in (1//1, QQ(1), 2//1, QQ(2))
      @test s*Q([K(1)]) == Int(s)*Q([K(1)])
      @test Q([K(1)])*s == Int(s)*Q([K(1)])
    end
    for s in (1//2, QQ(1, 2))
      @test_throws ErrorException s*Q([K(1)])
      @test_throws ErrorException Q([K(1)])*s
    end
    E = Hecke.FPModuleDedekind(R, [U], zero_matrix(ZZ, 0, 1), typeof(U)[])
    @test rank(E) == 1
    @test coordinates(E([b])) == [b]
    Q = Hecke.FPModuleDedekind(R, Hecke.pseudo_matrix(R, K[2;;], [U]))
    @test !iszero(Q([K(1)]))
    @test iszero(Q([K(2)]))
  end

  @testset "function-field orders over finite and infinite constant fields" begin
    for k in (GF(5), QQ)
      kt, t = rational_function_field(k, :t; cached = false)
      K, a = function_field(polynomial(kt, [-t^3 - t - 1, 0, 1]); cached = false)
      R = finite_maximal_order(K)
      I = fractional_ideal(ideal(R, t, R(a - 1)))
      test_dedekind_module(R, K, I, K(t))
      U = one(K)*R
      Q = Hecke.FPModuleDedekind(R, [U], K[1; 1;;], [I, fractional_ideal(ideal(R, t + 1))])
      @test iszero(Q([K(1)]))
      Q = Hecke.FPModuleDedekind(R, Hecke.pseudo_matrix(K[1;;], [I]))
      @test iszero(Q([K(t)]))
      @test Q([a]) == Q([K(1)])
      @test !iszero(Q([K(1)]))
      @test hash(Q([a])) == hash(Q([K(1)]))
      # Include the order at infinity, whose coefficient PID uses degree
      # localization rather than polynomial division.
      Rinf = infinite_maximal_order(K)
      Iinf = K(1//t)*Rinf
      test_dedekind_module(Rinf, K, Iinf, K(1//t))
    end
  end
end
