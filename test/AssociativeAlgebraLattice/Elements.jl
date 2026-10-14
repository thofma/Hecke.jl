@testset "Associative algebra lattice elements" begin
  @testset "PID construction and arithmetic" begin
    F, = rational_function_field(GF(13))
    P = F.fraction_field.base_ring
    R = localization(F, degree)
    for (K, C) in [(QQ, ZZ), (F, P), (F, R)]
      A = group_algebra(K, small_group(2, 1))
      b = basis(A)
      L = Hecke.lattice(A, C, Hecke.coordinates(A, [2*b[1]]); is_basis_matrix = true)
      a = 6*b[1]
      x = @inferred L(a)
      y = @inferred L([C(-2)])

      @test typeof(x) === elem_type(L) === elem_type(typeof(L))
      @test parent_type(typeof(x)) === typeof(L)
      @test parent(x) === L
      @test @inferred(Hecke.elem_in_algebra(x)) == a
      @test coordinates(x) == elem_type(C)[C(3)]
      @test L(coordinates(x)) == x
      @test L(Hecke.elem_in_module(x)) == x
      @test L(x) == x
      @test Hecke.ambient_coordinates(x) == coefficients(a)
      @test parent(Hecke.elem_in_module(x)) === Hecke.underlying_module(L)
      @test Hecke.elem_in_algebra(x) === Hecke.elem_in_algebra(x)
      acopy = deepcopy(Hecke.elem_in_algebra(x))
      coefficients(acopy; copy = false)[1] = K(99)
      @test Hecke.elem_in_algebra(x) == a
      @test hash(x) == hash(L(coordinates(x)))
      @test length(Set([x, L(a), y])) == 2
      @test x in L

      @test parent(x + y) === L
      @test Hecke.elem_in_algebra(x + y) == 2*b[1]
      @test Hecke.elem_in_algebra(x - y) == 10*b[1]
      @test Hecke.elem_in_algebra(-x) == -a
      @test Hecke.elem_in_algebra(2*x) == 2*a
      @test x*2 == 2*x
      @test ZZ(2)*x == 2*x
      @test C(2)*x == 2*x
      if C !== ZZ
        s = gen(C)
        @test Hecke.elem_in_algebra(s*x) == K(s)*a
        @test x*s == s*x
      end
      @test iszero(x - x)
      @test iszero(L())
      @test zero(x) == zero(L)
      @test x + zero(L) == x
      @test_throws ArgumentError L(b[2])
      @test_throws ArgumentError L(elem_type(C)[])
      @test_throws ArgumentError L([C(1), C(2)])
      @test_throws ArgumentError K(1//2)*x
      @test_throws ArgumentError x*K(1//2)

      LL = Hecke.lattice(A, C, [2*b[1]])
      xx = LL(a)
      @test L == LL
      @test x != xx
      @test_throws ArgumentError x + xx
      @test_throws ArgumentError x - xx
      @test LL(x) == xx
      @test x in LL
      @test_throws ArgumentError L(Hecke.elem_in_module(xx))

      Z = Hecke.zero_lattice(A, C)
      z = Z(elem_type(C)[])
      @test iszero(z)
      @test coordinates(Z()) == elem_type(C)[]
      @test Hecke.elem_in_algebra(z) == zero(A)
      @test z + z == z
      @test 2*z == z
      @test_throws ArgumentError Z(b[1])
    end
  end

  @testset "Copying and ambient parents" begin
    A = matrix_algebra(QQ, 2)
    b = basis(A)
    L = Hecke.lattice(A, ZZ, [QQ(1//2)*b[1], 3*b[2]])
    v = ZZRingElem[2, -1]
    x = L(v)
    a = b[1] - 3*b[2]
    v[1] = ZZ(99)
    @test Hecke.elem_in_algebra(x) == a

    aa = deepcopy(a)
    xx = L(aa)
    coefficients(aa; copy = false)[1] = QQ(99)
    @test Hecke.elem_in_algebra(xx) == a
    @test Hecke.elem_in_algebra(x) === Hecke.elem_in_algebra(x)
    acopy = deepcopy(Hecke.elem_in_algebra(x))
    coefficients(acopy; copy = false)[1] = QQ(99)
    @test Hecke.elem_in_algebra(x) == a

    c = coordinates(x)
    c[1] = ZZ(99)
    @test coordinates(x) == ZZRingElem[2, -1]
    ac = Hecke.ambient_coordinates(x)
    ac[1] = QQ(99)
    @test Hecke.elem_in_algebra(x) == a
    y = copy(x)
    m = Hecke.elem_in_module(y)
    coordinates(m; copy = false)[1] = ZZ(99)
    @test coordinates(y) == ZZRingElem[99, -1]
    @test coordinates(x) == ZZRingElem[2, -1]

    for f in (copy, deepcopy)
      y = f(x)
      @test y == x
      @test parent(y) === L
      @test Hecke.elem_in_module(y) !== Hecke.elem_in_module(x)
      @test Hecke.elem_in_algebra(y) == a
      @test Hecke.elem_in_algebra(y) !== Hecke.elem_in_algebra(x)
      coordinates(y; copy = false)[1] = ZZ(99)
      @test coordinates(x) == ZZRingElem[2, -1]
    end
    @test coordinates(x; copy = false) === coordinates(x; copy = false)
    @test Hecke.elem_in_module(x) === Hecke.elem_in_module(x)

    m = Hecke._element_from_coordinates(Hecke.underlying_module(L), ZZRingElem[2, -1])
    aa = copy(a)
    z = @inferred Hecke.AssociativeAlgebraLatticeElem(L, m, aa)
    @test Hecke.elem_in_module(z) == m
    @test Hecke.elem_in_algebra(z) == aa
    @test coordinates(z) == coordinates(x)
    y = L(m)
    coordinates(m; copy = false)[1] = ZZ(99)
    @test coordinates(y) == ZZRingElem[2, -1]
    @test !isempty(sprint(show, y))

    A2 = matrix_algebra(QQ, 2)
    @test_throws ArgumentError L(basis(A2)[1])
    @test_throws ArgumentError Hecke.AssociativeAlgebraLatticeElem(L, m, one(A2))
    L2 = Hecke.lattice(A, ZZ, basis(A))
    @test_throws ArgumentError Hecke.AssociativeAlgebraLatticeElem(L2, m, aa)
    lazy = L(a; check = false)
    @test coordinates(lazy) == coordinates(x)
    @test_throws ArgumentError L(QQ(1//4)*b[1])
  end

  @testset "Copying stored ambient elements" begin
    A = group_algebra(QQ, small_group(2, 1))
    b = basis(A)
    L = Hecke.lattice(A, ZZ, b)
    for warm in (false, true), f in (copy, deepcopy)
      x = L(ZZRingElem[2, -1])
      warm && Hecke.elem_in_algebra(x)
      y = f(x)
      a = @inferred Hecke.elem_in_algebra(y)
      @test a == 2*b[1] - b[2]
      @test (@inferred Hecke.elem_in_algebra(y)) === a
      @test Hecke.elem_in_algebra(x) !== a
      coefficients(a; copy = false)[1] = QQ(99)
      @test coefficients(Hecke.elem_in_algebra(y))[1] == 99
      @test Hecke.elem_in_algebra(x) == 2*b[1] - b[2]
    end
    x = L(ZZRingElem[2, -1])
    a = Hecke.elem_in_algebra(x)
    coefficients(a; copy = false)[1] = QQ(99)
    y = deepcopy(x)
    @test Hecke.elem_in_algebra(y) == a
    @test Hecke.elem_in_algebra(y) !== a
    repeated = deepcopy([x, x])
    @test repeated[1] === repeated[2]
    @test repeated[1] !== x
    @test Hecke.elem_in_algebra(repeated[1]) !== a
  end

  @testset "Dedekind coordinates and nonprincipal ideals" begin
    K, a = quadratic_field(-5)
    O = maximal_order(K)
    J = ideal(O, 2, O(1 + a))
    @test !is_principal(J)
    I = fractional_ideal(O, J, 2)
    II = fractional_ideal(O, J)
    A = matrix_algebra(K, 2)
    b = basis(A)
    B = Hecke.coordinates(A, b[1:2])
    L = Hecke.lattice(A, O, pseudo_matrix(O, B, [I, II]); is_basis_matrix = true)
    c = elem_type(K)[(1 + a)//2, K(2)]
    e = c[1]*b[1] + c[2]*b[2]
    x = @inferred L(e)
    y = @inferred L(c)

    @test typeof(x) === elem_type(L) === elem_type(typeof(L))
    @test parent(x) === L
    @test coordinates(x) == c
    @test x == y
    @test @inferred(Hecke.elem_in_algebra(y)) == e
    @test L(Hecke.elem_in_module(y)) == x
    @test hash(x) == hash(y)
    @test x in L
    @test coordinates(x + y) == 2*c
    @test Hecke.elem_in_algebra(x + y) == 2*e
    @test iszero(x - y)
    @test Hecke.elem_in_algebra(-x) == -e
    @test Hecke.elem_in_algebra(O(1 + a)*x) == (1 + a)*e
    @test 2*x == O(2)*x == x*ZZ(2)
    @test_throws ArgumentError K(2)*x
    @test_throws ArgumentError L(elem_type(K)[K(1//2), K(0)])
    @test_throws ArgumentError L(elem_type(K)[K(0), K(1)])
    @test_throws ArgumentError L(b[3])
    @test coordinates(L(e; check = false)) == c

    LL = Hecke.lattice(A, O, identity_matrix(K, dim(A)))
    @test_throws ArgumentError LL(x)
    u = LL(one(A))
    @test Hecke.elem_in_algebra(u) == one(A)
    @test LL(coordinates(u)) == u
    LN = Hecke.lattice(A, O, pseudo_matrix(O, B, [I, II]))
    xn = LN(e)
    @test Hecke.elem_in_algebra(xn) == e
    @test LN(coordinates(xn)) == xn
    z = L()
    @test iszero(z)
    @test coordinates(z) == elem_type(K)[K(0), K(0)]
    @test Hecke.elem_in_algebra(z) == zero(A)

    Z = Hecke.zero_lattice(A, O)
    @test iszero(Z(elem_type(K)[]))
    @test Hecke.elem_in_algebra(Z(elem_type(K)[])) == zero(A)
    @test coordinates(Z()) == elem_type(K)[]
    @test_throws ArgumentError Z(b[1])
  end
end
