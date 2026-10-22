# Integral ideals delegate module operations to lattices and track sidedness.
@testset "Integral order ideals" begin
  for (R, K, p) in algebra_order_test_rings()
    @testset "Ideals over $R" begin
      A = matrix_algebra(K, 2)
      O = AlgebraOrders.order(A, R, basis(A))
      Lo = AlgebraOrders.underlying_lattice(O)
      e = A(K[1 0; 0 0])
      f = A(K[0 0; 0 1])
      u = A(K[0 1; 0 0])
      v = A(K[0 0; 1 0])
      Il = @inferred left_ideal(O, e)
      Ir = @inferred right_ideal(O, O(e))
      U = twosided_ideal(O, one(O))
      Z = twosided_ideal(O, zero(A))

      @test Il isa AlgebraOrders.AssociativeAlgebraOrderIdeal
      @test base_ring(Il) == O
      @test algebra(Il) == A
      @test Hecke.ideal_type(O) == Hecke.ideal_type(typeof(O)) == typeof(Il)
      @test base_ring_type(typeof(Il)) == typeof(O)
      @test Hecke.algebra_type(typeof(Il)) == typeof(A)
      @test is_left_ideal(Il) && !is_right_ideal(Il)
      @test is_right_ideal(Ir) && !is_left_ideal(Ir)
      @test is_left_ideal(U) && is_right_ideal(U)
      @test is_left_ideal(Z) && is_right_ideal(Z)
      @test v in Il && O(v) in Il
      @test !(u in Il) && !(O(u) in Il)
      @test u in Ir && O(u) in Ir
      @test !(v in Ir) && !(O(v) in Ir)
      @test zero(A) in Z && zero(O) in Z
      @test !(one(A) in Z)
      @test !(inv(p)*e in Il)
      @test isone(U) && !iszero(U)
      @test iszero(Z) && !isone(Z)
      @test !iszero(Il) && !isone(Il)
      @test Hecke.rank(Il) == 2
      @test Hecke.ambient_rank(Il) == 4
      @test !Hecke.is_full_lattice(Il) && !Hecke.is_full_rank(Il)
      @test Hecke.is_full_lattice(U) && Hecke.is_full_rank(U)
      @test sprint(show, Il) isa String
      @test sprint(show, "text/plain", Il) isa String

      L = lattice(A, R, [e, v])
      @test AlgebraOrders.underlying_lattice(Il) == L
      @test basis_matrix(Il) == basis_matrix(L)
      @test basis(Il) == basis(L)
      @test all(x -> x in Il, basis(Il))
      @test Hecke.element.(Hecke.pseudo_basis(Il)) ==
            Hecke.element.(Hecke.pseudo_basis(L))
      @test Hecke.underlying_module(Il) == Hecke.underlying_module(L)
      for check in (true, false)
        @test ideal(O, L; side = :left, check) == Il
        @test ideal(O, [e, O(v)]; side = :left, check) == Il
      end
      @test_throws ArgumentError ideal(O, L; side = :right)
      @test_throws ArgumentError ideal(O, L; side = :twosided)
      @test ideal(O, [e]; side = :left) == Il == O*e == O*O(e)
      @test ideal(O, [e]; side = :right) == Ir == e*O == O(e)*O
      @test ideal(O, [e]; side = :twosided) == U
      @test ideal(O, view([e, v], :); side = :left) == Il
      @test left_ideal(O, e, v) == Il
      @test right_ideal(O, e, u) == Ir
      @test twosided_ideal(O, e, u) == U
      @test twosided_ideal(O, 1) == U
      @test left_ideal(O, 0) == right_ideal(O, 0) == Z
      @test left_ideal(O, elem_type(A)[]) == Z
      @test right_ideal(O, elem_type(O)[]) == Z
      @test twosided_ideal(O, Any[]) == Z
      @test_throws ArgumentError ideal(O, lattice(A, R, [e]); side = :left)
      @test_throws UndefKeywordError ideal(O, L)
      @test_throws UndefKeywordError ideal(O, [e])
      @test_throws UndefKeywordError ideal(O, e)
      @test_throws ArgumentError ideal(O, L; side = :invalid)
      @test_throws ArgumentError ideal(O, [e]; side = :invalid)

      F = inv(p)*Lo
      for check in (true, false), side in (:left, :right, :twosided)
        @test_throws ArgumentError ideal(O, F; side, check)
        @test_throws ArgumentError AlgebraOrders.AssociativeAlgebraOrderIdeal(
          O, F; side, check)
        @test_throws ArgumentError ideal(O, [inv(p)*e]; side, check)
        @test_throws ArgumentError ideal(O, inv(p)*e; side, check)
        @test_throws ArgumentError ideal(O, inv(p); side, check)
      end
      @test_throws ArgumentError O*(inv(p)*e)
      @test_throws ArgumentError (inv(p)*e)*O

      P = twosided_ideal(O, p*e)
      @test AlgebraOrders.underlying_lattice(P) == p*Lo
      @test O(p*one(A)) in P && !(one(A) in P)
      @test Hecke.module_index(P, U) == ideal(R, R(p)^dim(A))
      @test p*O == O*p == P
      @test issubset(P, U) && !issubset(U, P)

      Jl = left_ideal(O, f)
      Jr = right_ideal(O, f)
      @test !is_right_ideal(Jl) && !is_left_ideal(Jr)
      for (I, J) in ((Il, Jl), (Ir, Jr))
        S = I + J
        T = intersect(I, J)
        @test S == U && T == Z
        @test is_left_ideal(S) && is_right_ideal(S)
        @test is_left_ideal(T) && is_right_ideal(T)
        @test issubset(I, S) && issubset(J, S)
        @test issubset(T, I) && issubset(T, J)
        Li = AlgebraOrders.underlying_lattice(I)
        Lj = AlgebraOrders.underlying_lattice(J)
        @test AlgebraOrders.underlying_lattice(S) == Li + Lj
        @test AlgebraOrders.underlying_lattice(T) ==
              intersect(Li, Lj)
        @test hash(S) == hash(U)
        @test length(Set([S, U])) == 1
      end
      @test Il + Il == intersect(Il, Il) == Il
      @test Ir + Ir == intersect(Ir, Ir) == Ir
      @test_throws ArgumentError Il + Ir
      @test_throws ArgumentError intersect(Il, Ir)
      Zr = right_ideal(O, Hecke.zero_lattice(A, R))
      @test Il + Zr == Il
      @test intersect(Il, Zr) == Z
      @test intersect(U, P) == P
      @test U + P == U

      D = A(K[p 0; 0 1])
      OO = AlgebraOrders.order(D*Lo*inv(D))
      J = left_ideal(OO, e)
      @test inv(p)*v in J && OO(inv(p)*v) in J
      @test issubset(AlgebraOrders.underlying_lattice(J),
                     AlgebraOrders.underlying_lattice(OO))
      @test_throws ArgumentError ideal(O, OO(inv(p)*v); side = :left)
      @test !Hecke.is_compatible(Il, J)
      @test Il != J
      @test_throws ArgumentError Il + J
      @test_throws ArgumentError intersect(Il, J)
      @test_throws ArgumentError issubset(Il, J)
      @test_throws ArgumentError Hecke.module_index(Il, J; check = false)

      AA = matrix_algebra(K, 2)
      @test_throws ArgumentError one(AA) in Il
      @test_throws ArgumentError ideal(O, one(AA); side = :left)
      L = lattice(AA, R, basis(AA))
      @test_throws ArgumentError ideal(O, L; side = :left, check = false)
    end
  end
end

@testset "Ideal arithmetic and sampling" begin
  for (R, K, p) in algebra_order_test_rings()
    A = matrix_algebra(K, 2)
    O = AlgebraOrders.order(A, R, basis(A))
    e = O(A(K[1 0; 0 0]))
    f = one(O) - e
    u = O(A(K[0 1; 0 0]))
    v = O(A(K[0 0; 1 0]))
    Il, Ir = O*e, e*O
    U, Z = one(Il), zero(Il)
    P = R(p)*U

    @test U == twosided_ideal(O, one(O))
    @test Z == twosided_ideal(O, zero(O))
    @test copy(Il) == Il && base_ring(copy(Il)) === O
    @test is_left_ideal(copy(Il)) && !is_right_ideal(copy(Il))
    @test U*Il == Il && Il*U == U
    @test Ir*U == Ir && U*Ir == U
    @test Il*Ir == U
    @test_throws ArgumentError Ir*Il
    @test Z*Il == Ir*Z == Z
    @test Il*u == O*f
    @test v*Ir == f*O
    @test Il*Il == Il && Ir*Ir == Ir
    @test Il*e == Il
    @test e*Ir == Ir
    @test_throws ArgumentError e*Il
    @test_throws ArgumentError Ir*e
    @test Il*Hecke.elem_in_algebra(u) == Il*u
    @test Hecke.elem_in_algebra(v)*Ir == v*Ir
    for n in (0, 1, 2, 5, BigInt(3), ZZ(3))
      @test Il^n == (iszero(n) ? U : Il)
      @test P^n == R(p)^Int(n)*U
    end
    @test_throws ArgumentError Il^(-1)
    @test_throws ArgumentError P^ZZ(-1)
    @test 2*Il == Il*2 == R(2)*Il == ZZ(2)*Il
    @test R(p)*Il == Il*R(p)
    @test is_left_ideal(R(p)*Il) && !is_right_ideal(R(p)*Il)
    @test 0*Il == Z && Il*R(0) == Z
    @test_throws ArgumentError inv(p)*P
    @test_throws ArgumentError P*inv(p)
    @test_throws ArgumentError P*(inv(p)*one(A))
    @test Hecke.module_index(P, O) == ideal(R, R(p)^dim(A))
    @test left_order(P) == right_order(P) == O

    rng = Hecke.Random.MersenneTwister(42)
    for I in (Il, Ir, U, Z, P)
      for x in (rand(rng, I, 4), rand(I, 4), rand(rng, I, 0:3))
        @test parent(x) === A
        @test x in I
      end
      @test iszero(rand(rng, I, 0))
    end
    @test_throws ArgumentError rand(rng, Il, -1)

    OO = AlgebraOrders.order(AlgebraOrders.underlying_lattice(O))
    J = left_ideal(OO, OO(e))
    @test_throws ArgumentError Il*J
    @test_throws ArgumentError Hecke.module_index(Il, OO)
  end
end

@testset "Reduction and modular powers" begin
  for (R, K, p) in algebra_order_test_rings()
    A = matrix_algebra(K, 2)
    O = AlgebraOrders.order(A, R, basis(A))
    e = O(A(K[1 0; 0 0]))
    x = O(A(K[1 + p p; 1 p^2]))
    U = twosided_ideal(O, one(O))
    Z = zero(U)
    P = R(p)*U
    Il, Ir = O*e, e*O
    for I in (U, Z, P, Il, Ir)
      y = mod(x, I)
      @test parent(y) === O
      @test x - y in I
      @test mod(y, I) == y
      @test mod(x + O(rand(I, 3)), I) == y
      z = deepcopy(x)
      coordinates(z)
      Hecke.elem_in_algebra(z; copy = false)
      mod!(z, I)
      @test z == y
      @test coordinates(z) == coordinates(y)
      @test Hecke.elem_in_algebra(z) == Hecke.elem_in_algebra(y)
    end
    @test mod(x, U) == zero(O)
    @test mod(x, Z) == x
    for n in (0, 1, 2, 7, BigInt(11), ZZ(13))
      @test powermod(x, n, P) == mod(x^Int(n), P)
      @test iszero(powermod(x, n, U))
    end
    y = one(O) + O(A(K[0 1; 0 0]))
    z = @inferred invmod(y, P)
    @test y*z - one(O) in P && z*y - one(O) in P
    @test mod(z, P) == z
    @test invmod(y, Z) == inv(y)
    @test iszero(invmod(y, U))
    for n in (-1, -3, BigInt(-5), ZZ(-7), typemin(Int))
      @test powermod(y, n, P) == mod(O(A(K[1 K(n); 0 1])), P)
    end
    @test_throws ArgumentError powermod(e, -1, P)
    @test_throws ArgumentError invmod(e, P)
    @test_throws ArgumentError invmod(y, Il)
    @test_throws ArgumentError invmod(y, Ir)
    @test_throws ArgumentError powermod(x, 2, Il)
    @test_throws ArgumentError powermod(x, 2, Ir)
    @test_throws ArgumentError powermod(x, 0, Il)

    OO = AlgebraOrders.order(AlgebraOrders.underlying_lattice(O))
    @test_throws ArgumentError mod(OO(x), P)
    @test_throws ArgumentError mod!(OO(x), P)
    @test_throws ArgumentError powermod(OO(x), 2, P)
    @test_throws ArgumentError invmod(OO(x), P)
  end

  A = matrix_algebra(QQ, 2)
  O = AlgebraOrders.order(A, ZZ, basis(A))
  I = twosided_ideal(O, 5)
  @test mod(O(A(QQ[-1 6; 7 -3])), I) == O(A(QQ[4 1; 2 2]))
  x = O(A(QQ[2 0; 0 3]))
  @test !is_unit(x)
  y = invmod(x, I)
  @test powermod(x, -1, I) == y
  @test mod(x*y, I) == mod(y*x, I) == mod(one(O), I)
  @test powermod(x, -3, I) == powermod(y, 3, I)
end

@testset "Contraction, coprimality and change of order" begin
  for (R, K, p) in algebra_order_test_rings()
    A = matrix_algebra(K, 2)
    O = AlgebraOrders.order(A, R, basis(A))
    Lo = AlgebraOrders.underlying_lattice(O)
    e = O(A(K[1 0; 0 0]))
    f = one(O) - e
    U = twosided_ideal(O, one(O))
    P = R(p)*U
    Q = R(p + 1)*U
    Il, Jl = O*e, O*f
    for (I, J) in ((P, Q), (Il, Jl), (e*O, f*O), (U, zero(U)))
      @test is_coprime(I, J)
      a, b = idempotents(I, J)
      @test parent(a) === parent(b) === O
      @test a in I && b in J
      @test a + b == one(O)
      if is_right_ideal(I) && is_left_ideal(I) &&
         is_right_ideal(J) && is_left_ideal(J)
        T = intersect(I, J)
        @test a*a - a in T && b*b - b in T
        @test a*b in T && b*a in T
      end
    end
    @test !is_coprime(P, P)
    @test_throws ArgumentError idempotents(P, P)
    @test !is_coprime(Il, f*O)
    @test_throws ArgumentError idempotents(Il, f*O)

    for (I, c) in ((P, R(p)), (U, one(R)), (zero(U), zero(R)),
                    (Il, zero(R)))
      C = contract(I, R)
      @test C == ideal(R, c)
      @test intersect(I, R) == intersect(R, I) == C
      @test O(c) in I
      if R === ZZ
        @test minimum(I) == abs(c)
      end
    end
    @test_throws ArgumentError contract(P, K)

    OO = AlgebraOrders.order(A, R,
                            [Hecke.elem_in_algebra(e),
                             Hecke.elem_in_algebra(f),
                             A(K[0 p; 0 0]), A(K[0 0; p 0])])
    J = twosided_ideal(OO, R(p)*Lo)
    @test contract(P, OO) == intersect(P, OO) == intersect(OO, P) == J
    @test base_ring(contract(P, OO)) === OO
    @test extend(J, O) == P
    for side in (:left, :right, :twosided)
      E = extend(J, O; side)
      @test E == P && base_ring(E) === O
      @test all(b -> b in E, basis(J))
    end
    @test O*J == J*O == P
    @test is_left_ideal(extend(left_ideal(OO, OO(e)), O; side = :left))
    @test extend(left_ideal(OO, OO(e)), O; side = :left) == Il
    @test extend(right_ideal(OO, OO(e)), O; side = :right) == e*O
    @test is_left_ideal(contract(Il, OO))
    @test is_right_ideal(contract(e*O, OO))
    for I in (P, U, zero(U), Il, e*O)
      H = @inferred contract(I, OO)
      @test base_ring(H) === OO
      @test AlgebraOrders.underlying_lattice(H) ==
            intersect(AlgebraOrders.underlying_lattice(I),
                      AlgebraOrders.underlying_lattice(OO))
    end
    @test contract(contract(P, OO), R) == contract(P, R)
    @test_throws ArgumentError extend(J, O; side = :invalid)
    @test_throws ArgumentError extend(P, OO)
    @test_throws ArgumentError contract(J, O)
    @test_throws ArgumentError is_coprime(P, J)
    @test_throws ArgumentError idempotents(P, J)
  end
end

@testset "Idempotents, contraction and modular powers over Dedekind rings" begin
  function test_dedekind_idempotents(R, K, I, c)
    U = fractional_ideal(ideal(R, one(R)))
    A = matrix_algebra(K, 2)
    C = [U, inv(I), I, U]
    L = lattice(A, R, pseudo_matrix(R, identity_matrix(K, 4), C))
    O = AlgebraOrders.order(L)
    e = A(K[1 0; 0 0])
    f = one(A) - e
    V = twosided_ideal(O, L)
    P = twosided_ideal(O, c*L)
    Q = twosided_ideal(O, (c + 1)*L)
    left = (left_ideal(O, L*e), left_ideal(O, L*f))
    right = (right_ideal(O, e*L), right_ideal(O, f*L))
    for (J, H) in ((P, Q), left, right, (V, zero(V)))
      @test is_coprime(J, H)
      u, v = @inferred idempotents(J, H)
      @test u in J && v in H && u + v == one(O)
      if is_left_ideal(J) && is_right_ideal(J) &&
         is_left_ideal(H) && is_right_ideal(H)
        T = intersect(J, H)
        @test u*u - u in T && v*v - v in T
        @test u*v in T && v*u in T
      end
    end
    @test_throws ArgumentError idempotents(P, P)

    for (J, C) in ((P, ideal(R, R(c))), (Q, ideal(R, R(c + 1))),
                    (V, ideal(R, one(R))), (zero(V), ideal(R, zero(R))),
                    (left[1], ideal(R, zero(R))),
                    (right[1], ideal(R, zero(R))))
      @test (@inferred contract(J, R)) == C
      @test intersect(J, R) == intersect(R, J) == C
    end
    central = twosided_ideal(O, lattice(A, R, I*Hecke.underlying_module(O)))
    @test contract(central, R) == numerator(I)

    S = lattice(A, R, [Hecke._pseudo_element(one(A), U)])
    OO = AlgebraOrders.order(S + c*L)
    @test OO != O && issubset(OO, O)
    for J in (P, V, zero(V), left[1], right[1], central)
      H = @inferred contract(J, OO)
      @test base_ring(H) === OO
      @test AlgebraOrders.underlying_lattice(H) ==
            intersect(AlgebraOrders.underlying_lattice(J),
                      AlgebraOrders.underlying_lattice(OO))
      is_left_ideal(J) && (@test is_left_ideal(H))
      is_right_ideal(J) && (@test is_right_ideal(H))
    end
    H = contract(P, OO)
    @test intersect(P, OO) == intersect(OO, P) == H
    @test AlgebraOrders.underlying_lattice(H) == c*L
    @test isone(contract(V, OO))
    @test iszero(contract(zero(V), OO))
    @test contract(contract(central, OO), R) == contract(central, R)
    W = twosided_ideal(OO, AlgebraOrders.underlying_lattice(OO))
    @test_throws ArgumentError contract(W, O)

    u = O(A(K[1 c; 0 1]))
    for n in (-1, -3, BigInt(-5), ZZ(-7), typemin(Int))
      @test powermod(u, n, P) == mod(O(A(K[1 K(n)*c; 0 1])), P)
    end
    w = O((c + 1)*one(A))
    v = @inferred invmod(w, P)
    @test w*v - one(O) in P && v*w - one(O) in P
    @test mod(v, P) == v
    @test powermod(w, -1, P) == v
    @test powermod(w, -3, P) == powermod(v, 3, P)
    @test powermod(u, -1, zero(V)) == inv(u)
    @test iszero(powermod(u, -1, V))
    @test invmod(u, zero(V)) == inv(u)
    @test iszero(invmod(u, V))
    @test_throws ArgumentError powermod(O(c*one(A)), -1, P)
    @test_throws ArgumentError powermod(O(c*one(A)), -1, zero(V))
    @test_throws ArgumentError powermod(O(e), -1, P)
    @test_throws ArgumentError powermod(u, -1, left[1])
    @test_throws ArgumentError invmod(O(c*one(A)), P)
    @test_throws ArgumentError invmod(O(e), P)
    @test_throws ArgumentError invmod(u, left[1])
    @test_throws ArgumentError invmod(u, right[1])

    ZO = AlgebraOrders.order(Hecke.zero_lattice(zero_algebra(K), R))
    Z = twosided_ideal(ZO, AlgebraOrders.underlying_lattice(ZO))
    @test idempotents(Z, Z) == (zero(ZO), zero(ZO))
    @test contract(Z, R) == ideal(R, one(R))
    ZOO = AlgebraOrders.order(AlgebraOrders.underlying_lattice(ZO))
    @test iszero(contract(Z, ZOO)) && isone(contract(Z, ZOO))
    @test iszero(powermod(zero(ZO), -1, Z))
    @test iszero(invmod(zero(ZO), Z))
    return O
  end

  K, a = quadratic_field(-5)
  R = maximal_order(K)
  I = fractional_ideal(R, ideal(R, 2, R(1 + a)))
  @test !is_principal(numerator(I))
  O = test_dedekind_idempotents(R, K, I, K(2))
  p = first(prime_decomposition(R, 2))[1]
  q = first(prime_decomposition(R, 3))[1]
  J = twosided_ideal(O, lattice(algebra(O), R, p*Hecke.underlying_module(O)))
  H = twosided_ideal(O, lattice(algebra(O), R, q*Hecke.underlying_module(O)))
  x, y = idempotents(J, H)
  @test x in J && y in H && x + y == one(O)

  R = maximal_order(Hecke.GenOrd(ZZ, K))
  I = fractional_ideal(first(prime_decomposition(R, ZZ(2)))[1])
  test_dedekind_idempotents(R, K, I, K(2))

  kt, t = rational_function_field(GF(5), :t; cached = false)
  K, a = function_field(polynomial(kt, [-t^3 - t - 1, 0, 1]);
                         cached = false)
  R = finite_maximal_order(K)
  I = fractional_ideal(ideal(R, t, R(a - 1)))
  test_dedekind_idempotents(R, K, I, K(t))
  R = infinite_maximal_order(K)
  I = K(inv(t))*fractional_ideal(ideal(R, one(R)))
  test_dedekind_idempotents(R, K, I, K(inv(t)))
end

@testset "Ideals of zero-dimensional orders" begin
  for (R, K, _) in algebra_order_test_rings()
    A = zero_algebra(K)
    O = AlgebraOrders.order(Hecke.zero_lattice(A, R))
    for side in (:left, :right, :twosided)
      I = ideal(O, elem_type(A)[]; side)
      @test iszero(I) && isone(I)
      @test is_left_ideal(I) && is_right_ideal(I)
      @test zero(A) in I && zero(O) in I
      @test isempty(basis(I))
      @test I + I == intersect(I, I) == I
      @test zero(I) == one(I) == copy(I) == I*I == I^0 == I^2
      @test Hecke.module_index(I, O) == ideal(R, one(R))
      @test iszero(rand(I, 3))
      @test iszero(mod(zero(O), I))
      @test iszero(powermod(zero(O), -1, I))
      @test iszero(invmod(zero(O), I))
      @test iszero(powermod(zero(O), 0, I))
      @test contract(I, R) == ideal(R, one(R))
      @test is_coprime(I, I)
      @test idempotents(I, I) == (zero(O), zero(O))
    end
  end
end

@testset "Coprime ideals with noncommuting products" begin
  for (R, K, _) in algebra_order_test_rings()
    M = [zero(K) for _ in 1:3, _ in 1:3, _ in 1:3]
    M[1, 1, 1] = M[1, 2, 2] = M[2, 3, 2] = M[3, 3, 3] = one(K)
    A = StructureConstantAlgebra(K, M)
    O = AlgebraOrders.order(A, R, basis(A))
    e, u, f = basis(O)
    I = twosided_ideal(O, [u, f])
    J = twosided_ideal(O, [e, u])
    T = intersect(I, J)
    @test is_coprime(I, J)
    @test iszero(I*J) && !iszero(J*I)
    @test J*I == T
    a, b = idempotents(I, J)
    @test a in I && b in J && a + b == one(O)
    @test a*a - a in T && b*b - b in T
    @test a*b in T && b*a in T
    @test contract(I, R) == contract(J, R) == ideal(R, zero(R))
    x = e + u
    @test !is_unit(x)
    y = powermod(x, -1, I)
    @test mod(x*y, I) == mod(y*x, I) == mod(one(O), I)
  end
end
