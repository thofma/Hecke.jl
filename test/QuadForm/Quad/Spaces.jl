@testset "Spaces" begin
  k = FlintQQ

  Qx, x = PolynomialRing(FlintQQ, "x")
  K1, a1 = NumberField(x^2 - 2, "a1")
  K2, a2 = NumberField(x^3 - 2, "a2")

  K1t, t = PolynomialRing(K1, "t")
  F = GF(3)

  Hecke.change_base_ring(::FlintRationalField, ::Hecke.gfp_mat) = error("asd")
  @test_throws ErrorException quadratic_space(FlintQQ, F[1 2; 2 1])

  Hecke.change_base_ring(::FlintRationalField, x::Hecke.gfp_mat) = x
  @test_throws ErrorException quadratic_space(FlintQQ, F[1 2; 2 1])

  L, b = NumberField(t^2 + a1)

  for K in [k, K1, K2, L]
    V = @inferred quadratic_space(K, 2)
    @test_throws ArgumentError quadratic_space(K, -1)

    V = @inferred quadratic_space(K, identity_matrix(FlintZZ, 2))
    @test (@inferred gram_matrix(V)) == identity_matrix(K, 2)
    @test (@inferred dim(V)) == 2
    @test (@inferred rank(V)) == 2
    @test @inferred isregular(V)
    @test (@inferred involution(V)) === identity

    V = @inferred quadratic_space(K, zero_matrix(K, 2, 2))
    @test (@inferred gram_matrix(V)) == zero_matrix(K, 2, 2)
    @test (@inferred gram_matrix(V)) isa dense_matrix_type(K)
    @test (@inferred dim(V)) == 2
    @test (@inferred rank(V)) == 0
    @test @inferred isquadratic(V)
    @test @inferred !ishermitian(V)
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
    @test isdiagonal(gram_matrix(V, B))

    D = @inferred diagonal(V)
    @test length(D) == 2
    @test issetequal(D, map(K, [1, -3]))

    M = rand(MatrixSpace(K, 4, 4), -10:10)
    M = M + transpose(M)
    while iszero(det(M))
      M = rand(MatrixSpace(K, 4, 4), -10:10)
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

  fl, T =  Hecke.isisometric_with_isometry(quadratic_space(QQ, matrix(QQ, 2, 2, [4, 0, 0, 1])),
                                            quadratic_space(QQ, matrix(QQ, 2, 2, [1, 0, 0, 1])))
  @test fl

  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  f = x - 1;
  K, a = number_field(f)
  D = matrix(K, 2, 2, [1, 0, 0, 3]);
  V = quadratic_space(K, D)
  fl, T = Hecke.isisometric_with_isometry(V, V)
  @test fl
end

@testset "isometry classes of spaces" begin
  # isometry classes over the rationals
  q = quadratic_space(QQ,QQ[-1 0; 0 1])
  qq = quadratic_space(QQ,QQ[-1 0; 0 3])
  q_deg = quadratic_space(QQ,QQ[-1 0 0; 0 3 0; 0 0 0])
  g = Hecke.isometry_class(q)
  gg = Hecke.isometry_class(qq)
  gg_deg = Hecke.isometry_class(q_deg)
  ggg = Hecke.isometry_class(orthogonal_sum(q,qq)[1])
  @test g + gg == ggg
  @test g + gg - g == gg
  @test g + g + gg - g == gg+ g
  @test gg_deg + g - gg_deg == g
  @test represents(gg,-1)
  @test represents(gg,-3)
  @test represents(gg_deg, -3)
  @test Hecke.isisometric_with_isometry(q, representative(g))[1]
  g2 = Hecke.isometry_class(q,2)
  for p in [2,3,5,7,11]
    @test Hecke.isometry_class(q, p) == local_symbol(g, p)
  end
  @test g2 == local_symbol(g, 2)
  @test Hecke.signature_tuple(q) == Hecke.signature_tuple(g)
  @test hasse_invariant(q,2) == hasse_invariant(g2)
  @test dim(q) == dim(g)
  @test issquare(det(q)*det(g))
  @test witt_invariant(q, 2) == witt_invariant(g2)
  q0 = quadratic_space(QQ,matrix(QQ,0,0,fmpq[]))
  g0 = Hecke.isometry_class(q0)
  g0p = Hecke.isometry_class(q0, 2)
  @test g == g+g0
  @test Hecke.represents(g, g0)
  @test Hecke.isometry_class(representative(gg + gg + g)) == gg + gg + g
  @test Hecke.isometry_class(representative(g+g+gg+gg)) == g + g + gg+gg

  # isometry classes over number fields
  R, x = PolynomialRing(QQ, "x")
  F, a = number_field(x^2 -3)
  infF = infinite_place(F,1)
  infF2 = infinite_place(F,2)
  q = quadratic_space(F, F[1 0; 0 a])
  @test Hecke.isisotropic(q, infF)
  qq = quadratic_space(F, F[-49 0; 0 a])
  h = quadratic_space(F, F[0 1; 1 a])
  @test Hecke.isisotropic(qq, infF2)
  @test Hecke._isisotropic_with_vector(gram_matrix(h))[1]
  @test !Hecke._isisotropic_with_vector(gram_matrix(q))[1]
  hh,_,_ = orthogonal_sum(qq,quadratic_space(F,-gram_matrix(qq)))
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
  @test issquare(det(q)*det(g))[1]
  r = quadratic_space(g)
  @test Hecke.isisometric_with_isometry(q, r)[1]
  @test isisometric(q,r, p)
  @test isisometric(q,r, infF)
  @test isisometric(q,r)
  L = Zlattice(gram=ZZ[1 1; 1 2])
  g = genus(L)
  c1 = Hecke.isometry_class(ambient_space(L))
  c2 = Hecke.rational_isometry_class(g)
  @test c1 == c2
end
