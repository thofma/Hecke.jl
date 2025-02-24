@testset "Spaces" begin
  k = QQ

  q = quadratic_space(QQ, QQ[1 1; 1 1;])
  @test 0 in diagonal(q)
  w = matrix(k, 2, 2, [1, 2, 3, 4])
  @test inner_product(q, w, w) == w * QQ[1 1; 1 1] * transpose(w)

  q = quadratic_space(k, 2)
  @test sprint(show, q) isa String
  @test sprint(show, Hecke.isometry_class(q)) isa String
  @test sprint(show, Hecke.isometry_class(q, 2)) isa String
  @test is_definite(q)
  v = matrix(k,1,2,[2,1])
  @test inner_product(q,v,v) == matrix(k,1,1,[5])
  @test Hecke._inner_product(lattice(q),v,v) == matrix(k,1,1,[5])
  w = matrix(k, 2, 2, [1, 2, 3, 4])
  @test inner_product(q, w, w) == w * transpose(w)

  q = quadratic_space(QQ, 2)
  v = QQ[1 1; 1 1]
  w = QQ[1 1;]
  p = @inferred inner_product(q, v, w)
  @test p == v * gram_matrix(q) * transpose(w)
  for T in [Int, BigInt, ZZRingElem, Rational{BigInt}, Rational{Int}]
    @test inner_product(q, [1, 1], [1, 2]) == 3
  end

  Qx, x = polynomial_ring(QQ, "x")
  K1, a1 = number_field(x^2 - 2, "a1")
  K2, a2 = number_field(x^3 - 2, "a2")

  K1t, t = polynomial_ring(K1, "t")
  L, b = number_field(t^2 + a1)

  for K in [k, K1, K2, L]
    V = @inferred quadratic_space(K, 2)
    @test_throws ArgumentError quadratic_space(K, -1)

    V = @inferred quadratic_space(K, identity_matrix(ZZ, 2))
    @test V == V
    @test V === V
    W = quadratic_space(K, identity_matrix(ZZ, 2))
    @test V === W
    W = quadratic_space(K, identity_matrix(ZZ, 2), cached = false)
    @test V != W

    @test (@inferred gram_matrix(V)) == identity_matrix(K, 2)
    @test (@inferred dim(V)) == 2
    @test (@inferred rank(V)) == 2
    @test @inferred is_regular(V)
    @test (@inferred involution(V)) === identity

    V = @inferred quadratic_space(K, zero_matrix(K, 2, 2))
    @test (@inferred gram_matrix(V)) == zero_matrix(K, 2, 2)
    @test (@inferred gram_matrix(V)) isa dense_matrix_type(K)
    @test (@inferred dim(V)) == 2
    @test (@inferred rank(V)) == 0
    @test @inferred is_quadratic(V)
    @test @inferred !is_hermitian(V)
    @test (@inferred fixed_field(V)) === K

    @test_throws ArgumentError quadratic_space(K, zero_matrix(K, 1, 2))

    M = identity_matrix(K, 2)
    M[1, 2] = 2
    M[2, 1] = 1
    @test_throws ArgumentError quadratic_space(K, M)

    # Determinant & discrimimant

    V = quadratic_space(K, 2)
    @test (@inferred discriminant(V)) == -1
    @test (@inferred det(V)) == 1

    V = quadratic_space(K, 4)
    @test (@inferred discriminant(V)) == 1
    @test (@inferred det(V)) == 1

    M = identity_matrix(K, 2)
    M[1, 2] = 2
    M[2, 1] = 2
    V = quadratic_space(K, M)
    @test (@inferred discriminant(V)) == 3
    @test (@inferred det(V)) == -3

    # Gram matrix

    M = identity_matrix(K, 2)
    M[1, 2] = 2
    M[2, 1] = 2
    V = @inferred quadratic_space(K, M)
    N = zero_matrix(K, 4, 2)
    @test (@inferred gram_matrix(V, N)) == zero_matrix(K, 4, 4)

    N = identity_matrix(QQ, 2)
    @test (@inferred gram_matrix(V, N)) == M

    N = zero_matrix(K, 4, 4)
    @test_throws ArgumentError gram_matrix(V, N)

    v = [[1, 0], [0, 1]]
    @test (@inferred gram_matrix(V, v) == M)

    v = [[1, 0, 0], [0, 1]]
    @test_throws ErrorException gram_matrix(V, v)

    B = @inferred orthogonal_basis(V)
    @test is_diagonal(gram_matrix(V, B))

    V1 = quadratic_space(K, zero_matrix(K,2,2))
    V2, _, _ = biproduct(V, V1)
    B2 = @inferred orthogonal_basis(V2)
    @test is_diagonal(gram_matrix(V2, B2))


    D = @inferred diagonal(V)
    @test length(D) == 2
    @test issetequal(D, map(K, [1, -3]))

    M = rand(matrix_space(K, 4, 4), -10:10)
    M = M + transpose(M)
    while iszero(det(M))
      M = rand(matrix_space(K, 4, 4), -10:10)
      M = M + transpose(M)
    end

    V = quadratic_space(K, M)

    F, S = @inferred Hecke._gram_schmidt(M, identity)
    @test gram_matrix(V, S) == F

    M[1, 1] = 0
    M[1, 2] = 0
    M[1, 3] = 0
    M[1, 4] = 0
    M[2, 1] = 0
    M[3, 1] = 0
    M[4, 1] = 0

    V = quadratic_space(K, M)

    @test_throws ErrorException Hecke._gram_schmidt(M, identity)
    F, S = @inferred Hecke._gram_schmidt(M, identity, false)
    @test gram_matrix(V, S) == F
  end

  fl, T =  Hecke.is_isometric_with_isometry(quadratic_space(QQ, matrix(QQ, 2, 2, [4, 0, 0, 1])),
                                            quadratic_space(QQ, matrix(QQ, 2, 2, [1, 0, 0, 1])))
  @test fl

  Qx, x = polynomial_ring(QQ, "x", cached = false)
  f = x - 1;
  K, a = number_field(f)
  D = matrix(K, 2, 2, [1, 0, 0, 3]);
  V = quadratic_space(K, D)
  fl, T = Hecke.is_isometric_with_isometry(V, V)
  @test fl

  F,a = number_field(x^2 - 2, :a)
  tt = [#[-4, 13, -5, 16],
        #[-4, 19, 5, -24],
        [1, -1, 0, 1],
      #[3, 8, -2, -5],
      #[-3, -13, 4, 17],
      #[7, 19, -3, -8],
      #[3, -17, -1, 6],
      #[11, -9, 5, -4],
      #[-5, 7, -3, 4],
      #[10, 27, -3, -8]
      ]
  dd = [#[7//5*a - 5//8, -2//9],
      #[-a + 8//3, 4//5*a - 4//3],
      #[2*a - 9//4, 10//9*a - 3],
      [-a - 1, -9*7*a - 4*49],
      #[-9//2, 1//2*a - 5//4],
      #[a - 1//3, 1//2*a - 7//4],
      #[-3//7*a - 5//6, 9//2*a + 5//9],
      #[-1//2*a + 3//4, 1//10*a - 10//9],
      #[2//3*a + 1//5, 3//10*a + 1//4],
      #[3//5*a + 7//9, -1//2*a + 1//9],
      #[-1//3, a - 10//7],
      #[6//5, -9//2*a - 7//3],
      #[5//3*a - 1, -5//7*a + 1//9],
      #[4//5*a + 1, -10//9*a + 7//5],
      #[2//5*a - 6//5, -3//4*a - 5],
      #[-2*a + 2, -1//8*a + 4//7],
      #[a - 1//8, 2*a - 10//7],
      #[5//4, 9*a + 1],
      #[-5//7*a - 1//3, -3//5*a + 4//7],
      #[-5//3*a + 1//2, -1//9*a - 8//9]
     ]
  tt = [matrix(F, 2, 2, [F(s) for s in t]) for t in tt]
  dd = [diagonal_matrix([F(s) for s in d]) for d in dd]

  for i in 1:1
    t = rand(tt)
    d = rand(dd)
    q1 = quadratic_space(F, d)
    q2 = quadratic_space(F, t*d*transpose(t))
    fl, T = Hecke.is_isometric_with_isometry(q1, q2)
    @test fl
    @test d == T*gram_matrix(q2)*transpose(T)

    # the above calls _isisometric_with_isometry_rank_2 on small input
    # test _isisometric_with_isometry with small input here
    fl, T = Hecke._isisometric_with_isometry(gram_matrix(q1), gram_matrix(q2))
    @test fl
    @test d == T*gram_matrix(q2)*transpose(T)
  end

  @testset "quadratic spaces from invariants" begin
    q = Hecke._quadratic_form_with_invariants(8,QQ(1),[ZZ(2),ZZ(3)],0)
    q = quadratic_space(QQ, q)
    @test hasse_invariant(q, 2) == -1
    @test hasse_invariant(q, ideal(ZZ,3)) == -1
    @test hasse_invariant(q, ZZ(3)) == -1
    # small ranks should be covered by the tests of GenusRep
    K, a = rationals_as_number_field()
    OK = maximal_order(K)
    rk = 8
    det = K(1)
    pinf = infinite_places(K)[1]
    for finite in [[ideal(OK, 2),ideal(OK,5)],[ideal(OK, 3),ideal(OK,7)]]
      for neg in [Dict(pinf=>0),Dict(pinf=>4),Dict(pinf=>8)]
        q = Hecke._quadratic_form_with_invariants(rk, det, finite, neg)
        rkq, ker, detq, finiteq, negq = Hecke._quadratic_form_invariants(q)
        @test rkq == rk
        @test ker == 0
        @test is_square(detq*det)[1]
        @test all(finiteq[p] == -1 for p in finite)
        @test Dict(negq) == neg
      end
    end

    R,x = polynomial_ring(QQ,:x)
    F, a = number_field(x^2 - 3)
    OF = maximal_order(F)
    inf1, inf2 = infinite_places(F)
    p2 = prime_ideals_over(OF, 2)[1]
    p3 = prime_ideals_over(OF, 3)[1]
    p5 = prime_ideals_over(OF, 5)[1]
    p13a, p13b = prime_ideals_over(OF, 13)

    d = [F(t) for t in [-3//4*a, -2*a - 5//4, -3//10*a + 1//5, -4//3*a - 2//9, -5//7*a - 3//4]]
    q = quadratic_space(F, diagonal_matrix(d))
    s = Hecke.isometry_class(q)
    @test s == Hecke.isometry_class(representative(s))
    rk = 5
    det = F(30)
    neg =
    for (finite,neg) in [([p2,p13a],(0,0)),([p2,p3,p13a],(2,0)), ([p3,p13b],(4,4))]
      neg = Dict(inf1=>neg[1],inf2=>neg[2])
      q = Hecke._quadratic_form_with_invariants(rk, det, finite, neg)
      rkq, ker, detq, finiteq, negq = Hecke._quadratic_form_invariants(q)
      @test rkq == rk
      @test ker == 0
      @test is_square(detq*det)[1]
      @test all(finiteq[p] == -1 for p in finite)
      @test Dict(negq) == neg
    end

    rk = 3
    det = F(-30)
    Hecke._quadratic_form_with_invariants(1, det, [], Dict(inf1=>1,inf2=>1))
    for (finite,neg) in [([p2,p13a,p5],(1,3)),([p3,p13a],(1,1)), ([p3,p13b],(3,3))]
      neg = Dict(inf1=>neg[1],inf2=>neg[2])
      q = Hecke._quadratic_form_with_invariants(rk, det, finite, neg)
      rkq, ker, detq, finiteq, negq = Hecke._quadratic_form_invariants(q)
      @test rkq == rk
      @test ker == 0
      @test is_square(detq*det)[1]
      @test all(finiteq[p] == -1 for p in finite)
      @test Dict(negq) == neg
    end

    _Q, = Hecke.rationals_as_number_field()
    K, = quadratic_field(3)
    u = QQ(1)
    v = QQ(2)
    for _A in -3:3
      for _B in -3:3
        for KK in [QQ, _Q, K]
          (iszero(_A) || iszero(_B)) && continue
          A = KK(_A)
          B = KK(_B)
          a = A * u^2 + B * v^2
          fl, _u, _v = Hecke._solve_conic_affine(A, B, a)
          @test fl
          @test a == A * _u^2 + B * _v^2
          A = KK(1//_A)
          B = KK(1//_B)
          a = A * u^2 + B * v^2
          fl, _u, _v = Hecke._solve_conic_affine(A, B, a)
          @test fl
          @test a == A * _u^2 + B * _v^2
        end
      end
    end
  end

  @testset begin "finding isotropic vectors"
    d  = QQFieldElem[25//21, -1, 37//26, 31//45, -24//25, -9//25]
    q = quadratic_space(QQ, diagonal_matrix(d))
    b, v = Hecke.is_isotropic_with_vector(q)
    @test b
    @test inner_product(q, v, v)==0

    # a degenerate example
    d1  = QQFieldElem[25//21, -1, 37//26, 31//45,0, -24//25, -9//25]
    q1 = quadratic_space(QQ, diagonal_matrix(d1))
    b1, v1 = Hecke.is_isotropic_with_vector(q1)
    @test b1
    @test any(i!=0 for i in v1)
    @test inner_product(q1, v1, v1)==0

    q = quadratic_space(QQ,matrix(QQ, 16, 16 ,[-2, -1, -1, -1, -1, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -2, -1, -1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -2, 0, -1, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -2, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 0, -2, -1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, -2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, -1, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, 1, 1, 1, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, -1, -1, -1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 2, 0, 1, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 2, 0, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 1, 1, 2, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 1, 1, 1, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1, -1, 0, -1, -1, 2]))
    ok, v = is_isotropic_with_vector(q)
    @test ok
    @test iszero(inner_product(q, v,v))

  #  too long even for a long test
  #   if long_test
  #     K,b = cyclotomic_field(16)
  #     F, _a = number_field(minpoly(b+b^-1))
  #     d = [36//25*_a - 35//29, -7//2*_a + 26//3, -28//15*_a - 33//28, -12//37*_a + 12, 7//32*_a + 11//3]
  #     q = diagonal_matrix(d)
  #     Hecke._isisotropic_with_vector(q)
  #  end
  end

  @testset "isometry classes of spaces" begin
    # isometry classes over the rationals
    q = quadratic_space(QQ,QQ[-1 0; 0 1])
    qq = quadratic_space(QQ,QQ[-1 0; 0 3])
    q_deg = quadratic_space(QQ,QQ[-1 0 0; 0 3 0; 0 0 0])
    g = Hecke.isometry_class(q)
    gg = Hecke.isometry_class(qq)
    gg_deg = Hecke.isometry_class(q_deg)
    ggg = Hecke.isometry_class(direct_product(q,qq)[1])
    @test g + gg == ggg
    @test g + gg - g == gg
    @test g + g + gg - g == gg+ g
    @test is_locally_represented_by(q, qq, 2) == represents(local_symbol(g,2), local_symbol(gg,2))
    @test !is_locally_represented_by(direct_sum(q,q)[1],q, 2)
    @test represents(gg, -1)
    @test represents(gg, 3)
    @test represents(gg, 2)
    @test represents(gg, -6)
    @test represents(gg_deg, 3)
    @test represents(gg_deg, 2)
    @test Hecke.is_isometric_with_isometry(q, representative(g))[1]
    g2 = Hecke.isometry_class(q,2)
    for p in [2,3,5,7,11]
      @test Hecke.isometry_class(q, p) == local_symbol(g, p)
    end
    @test g2 == local_symbol(g, 2)
    @test Hecke.signature_tuple(q) == Hecke.signature_tuple(g)
    @test hasse_invariant(q,2) == hasse_invariant(g2)
    @test dim(q) == dim(g)
    @test is_square(det(q)*det(g))
    @test witt_invariant(q, 2) == witt_invariant(g2)
    q0 = quadratic_space(QQ,matrix(QQ,0,0,QQFieldElem[]))
    g0 = Hecke.isometry_class(q0)
    g0p = Hecke.isometry_class(q0, 2)
    @test g == g+g0
    @test Hecke.represents(g, g0)
    @test Hecke.isometry_class(representative(gg + gg + g)) == gg + gg + g
    @test Hecke.isometry_class(representative(g+g+gg+gg)) == g + g + gg+gg
    gdegenerte = Hecke.isometry_class(quadratic_space(QQ,zero_matrix(QQ,2,2)))
    h = direct_sum(g,gdegenerte)
    @test is_isotropic(h)
    @test is_isotropic(local_symbol(h,2))
    @test is_isotropic(local_symbol(h,3))

    # isometry classes over number fields
    R, x = polynomial_ring(QQ, "x")
    F, a = number_field(x^2 -3)
    infF, infF2 = infinite_places(F)
    q = quadratic_space(F, F[1 0; 0 a])
    @test Hecke.is_isotropic(q, infF)
    qq = quadratic_space(F, F[-49 0; 0 a])
    h = quadratic_space(F, F[0 1; 1 a])
    @test Hecke.is_isotropic(qq, infF2)
    @test Hecke._isisotropic_with_vector(gram_matrix(h))[1]
    @test !Hecke._isisotropic_with_vector(gram_matrix(q))[1]
    hh,_,_ = biproduct(qq,quadratic_space(F,-gram_matrix(qq)))
    i = Hecke._maximal_isotropic_subspace(gram_matrix(hh))
    @test nrows(i)==dim(qq)
    @test i*gram_matrix(hh)*transpose(i) == 0

    g = Hecke.isometry_class(q)
    gg = Hecke.isometry_class(qq)
    @test represents(g, a)
    @test represents(g, 1+a)
    @test represents(gg, -49)
    @test represents(gg, a-49)
    @test represents(gg+g, g)
    @test represents(gg+g, gg)
    p = prime_ideals_over(maximal_order(F),2)[1]
    gp = Hecke.isometry_class(q, p)
    @test g + gg + g - g  == g + gg
    @test Hecke.signature_tuples(q) == Hecke.signature_tuples(g)
    @test Hecke.signature_tuple(q, infF) == Hecke.signature_tuple(g, infF)
    @test hasse_invariant(q,p) == hasse_invariant(gp)
    @test dim(q) == dim(g)
    @test is_square(det(q)*det(g))[1]
    r = quadratic_space(g)
    @test Hecke.is_isometric_with_isometry(q, r)[1]
    @test is_isometric(q,r, p)
    @test is_isometric(q,r, infF)
    @test is_isometric(q,r)
    L = integer_lattice(gram=ZZ[1 1; 1 2])
    g = genus(L)
    c1 = Hecke.isometry_class(ambient_space(L))
    c2 = Hecke.rational_isometry_class(g)
    @test c1 == c2

    # More complicated isisotropic_with_vector
    F = QQ[2 0 0 0 0 0; 0 1 0 0 0 0; 0 0 70//9 0 0 0; 0 0 0 -311//105 64//21 -286//105; 0 0 0 64//21 -67//21 65//21; 0 0 0 -286//105 65//21 -446//105]
    q = quadratic_space(QQ, F)
    fl, v = Hecke.is_isotropic_with_vector(q)
    @test fl
    vm = matrix(QQ, 1, 6, v)
    @test iszero(vm * F * transpose(vm))

    q = quadratic_space(QQ,diagonal_matrix(QQFieldElem[1,2,3]))
    @inferred Hecke.isometry_class(q)
    @test represents(q, 0)
    @test !is_isotropic(q)
    @inferred is_isotropic_with_vector(q)
    @test !is_isotropic_with_vector(q)[1]
    q = quadratic_space(QQ,diagonal_matrix(QQFieldElem[-8,2,3]))
    @test represents(q, 0)
    @test is_isotropic(q)
    q = quadratic_space(QQ,diagonal_matrix(QQFieldElem[-1,2,3]))
    @test represents(q, 0)
    @test !is_isotropic(q)

    for i in 1:100
      for r in 1:4
        I = [i for i in -20:20 if i!=0]
        q = quadratic_space(QQ,diagonal_matrix(QQFieldElem.(rand(I,r))))
        G = gram_matrix(q)
        q1 = quadratic_space(QQ, G[1:r-1,1:r-1])
        @test represents(q, q1)
        q2 = quadratic_space(QQ, G[1:r-2,1:r-2])
        @test represents(q, q2)
        for d in diagonal(gram_matrix(q))
          @test represents(q, d)
        end
      end
    end
  end

  @testset "orthogonal proj" begin
    L = root_lattice(:E, 8)
    f = matrix(QQ, 8, 8, [ 1  0  0  0  0  0  0  0;
                           0  1  0  0  0  0  0  0;
                           1  2  4  4  3  2  1  2;
                          -2 -4 -6 -5 -4 -3 -2 -3;
                           2  4  6  4  3  2  1  3;
                          -1 -2 -3 -2 -1  0  0 -2;
                           0  0  0  0  0 -1  0  0;
                          -1 -2 -3 -3 -2 -1  0 -1])
    M = invariant_lattice(L, f)
    pr = @inferred orthogonal_projection(ambient_space(L), basis_matrix(M))
    @test pr.matrix^2 == pr.matrix # in fact, it is a projection
    @test rank(pr.matrix) == 4 # M has rank 4 so pr should project onto a 4 dimensional subspace
                               # of the ambient
    @test rank(pr(M)) == 0     # orthogonal projection along M => M should be sent to the zero vector
    N = orthogonal_submodule(L, M)
    @test rank(pr(N)) == 4     # the image of N should be of full rank under the projection
    @test basis_matrix(N)*pr.matrix == basis_matrix(N) # N is contained in the complement in
                                                       # in the ambient, so its basis is fixed
                                                       # by projection

    B = Hecke.kernel(pr.matrix, side = :left)
    @test nrows(B) == 4
    Msup = lattice(ambient_space(L), B)
    @test is_sublattice(Msup, M) # A priori the kernel is bigger since M is integral
    @test !is_integral(Msup)
    @test intersect(L, Msup) == M # in our case M is primitive integral in L, it is a kernel
    @test iszero(inner_product(ambient_space(L), basis_matrix(Msup), basis_matrix(N)))
    @test rank(intersect(Msup, N)) == 0 # in fact this is the intersection of M and N
                                        # which are orthogonal by def. of N

    B2 = hnf(pr.matrix)[1:rank(pr.matrix), :] # basis matrix for the complement of M in the ambient
    Nsup = lattice(ambient_space(L), B2)
    @test is_sublattice(Nsup, N)
    @test iszero(inner_product(ambient_space(L), B, B2))
  end
end

@testset "direct sums" begin
  K, _ = cyclotomic_field(27, cached=false)
  V = quadratic_space(K, 4)
  S, inj, proj = @inferred biproduct(V, rescale(V, -1//5))
  @test dim(S) == 8
  for i in 1:2, j in 1:2
    f = compose(inj[i], proj[j])
    m = f.matrix
    @test i != j ? iszero(m) : isone(m)
  end
  S, inj, proj = @inferred biproduct(V, V, V)
end

@testset "fix is_isotropic" begin
  # Example Chapter 4, 1. (i) from Cassels
  V = quadratic_space(QQ, diagonal_matrix(QQ, [5,-1,-3]))
  # So by Cassels, Lemma 2.5, V is isotropic at all primes except 3 and 5
  @test hilbert_symbol(QQ(-1), QQ(-15), ZZ(3)) != hasse_invariant(V, 3)
  # What was previously implemented was then wrong because of the following
  # inequality
  @test hilbert_symbol(QQ(-1), QQ(-1), ZZ(3)) != hilbert_symbol(QQ(-1), QQ(-15), ZZ(3))
  @test !is_isotropic(V, 3)
  @test hilbert_symbol(QQ(-1), QQ(-15), ZZ(5)) != hasse_invariant(V, 5)
  @test !is_isotropic(V, 5)
  @test_throws ArgumentError is_isotropic(V, 4)
end

@testset "diagonal with transform" begin
  K, a = cyclotomic_field(8)
  V = quadratic_space(K, K[a 3 a; 3 3 3; a 3 a])
  diag, U = @inferred diagonal_with_transform(V)
  @test diagonal(U*gram_matrix(V)*transpose(U)) == diag
end

# hashing of global isometry classes
let
  q = quadratic_space(QQ, QQ[-1 0; 0 1])
  qq = quadratic_space(QQ, QQ[-1 0; 0 1])
  @test hash(Hecke.isometry_class(q)) == hash(Hecke.isometry_class(qq))
end

# hashing of local isometry classes
let
  R, x = polynomial_ring(QQ, "x")
  F, a = number_field(x^2 -3)
  infF, infF2 = infinite_places(F)
  q = quadratic_space(F, F[1 0; 0 a])
  p, = prime_ideals_over(maximal_order(base_ring(q)), 3)
  cls1 = Hecke.isometry_class(q, p)
  @test cls1 == Hecke.isometry_class(q, p)
  @test cls1 !== Hecke.isometry_class(q, p)
  @test hash(cls1) == hash(Hecke.isometry_class(q, p))
end
 
