@testset "Eisenstein reduction" begin
  # Gram matrix [a t s; t b r; s r c] of Dickson's form (13),
  # a*x^2 + b*y^2 + c*z^2 + 2*r*y*z + 2*s*x*z + 2*t*x*y
  dickson_gram(a, b, c, r, s, t) = matrix(ZZ, 3, 3, [a, t, s, t, b, r, s, r, c])

  # Sylvester's criterion
  is_pd(G) = G[1, 1] > 0 && G[1, 1] * G[2, 2] - G[1, 2]^2 > 0 && det(G) > 0

  # One form per condition of Dickson's Theorem 103 that violates that
  # condition and no other, paired, where the condition applies on a
  # boundary, with a form on the same boundary that satisfies it
  violating = [
    "(16), a <= b <= c" => dickson_gram(5, 4, 6, 1, 1, 1),
    "r, s, t of one sign" => dickson_gram(4, 5, 6, 1, -1, 1),
    "(17), |2t| <= a" => dickson_gram(4, 5, 6, 1, 1, 3),
    "(17), |2s| <= a" => dickson_gram(4, 5, 6, 1, 3, 1),
    "(17), |2r| <= b" => dickson_gram(4, 5, 6, 3, 1, 1),
    "(18)" => dickson_gram(10, 11, 12, -5, -4, -4),
    "(25), s <= 2r if a = 2t" => dickson_gram(8, 9, 10, 1, 3, 4),
    "(25), t <= 2r if a = 2s" => dickson_gram(8, 9, 10, 1, 4, 3),
    "(25), t <= 2s if b = 2r" => dickson_gram(8, 10, 11, 5, 1, 3),
    "(26), s = 0 if a = -2t" => dickson_gram(8, 9, 10, -1, -1, -4),
    "(26), t = 0 if a = -2s" => dickson_gram(8, 9, 10, -1, -4, -1),
    "(26), t = 0 if b = -2r" => dickson_gram(8, 10, 11, -5, -1, -1),
    "(26_4)" => dickson_gram(8, 10, 11, -4, -2, -3),
    "(41), |r| <= |s| if a = b" => dickson_gram(8, 8, 10, 2, 1, 1),
    "(41), |s| <= |t| if b = c" => dickson_gram(8, 10, 10, 1, 2, 1),
  ]
  satisfying = [
    "no boundary" => dickson_gram(4, 5, 6, 1, 1, 1),
    "(25), a = 2t" => dickson_gram(8, 9, 10, 2, 3, 4),
    "(25), a = 2s" => dickson_gram(8, 9, 10, 2, 4, 3),
    "(25), b = 2r" => dickson_gram(8, 10, 11, 5, 2, 3),
    "(26), a = -2t" => dickson_gram(8, 9, 10, -1, 0, -4),
    "(26), a = -2s" => dickson_gram(8, 9, 10, -1, -4, 0),
    "(26), b = -2r" => dickson_gram(8, 10, 11, -5, -1, 0),
    "(26_4)" => dickson_gram(8, 10, 11, -3, -3, -3),
    "(41), a = b" => dickson_gram(8, 8, 10, 1, 1, 1),
    "(41), b = c" => dickson_gram(8, 10, 10, 1, 1, 1),
    "identity" => dickson_gram(1, 1, 1, 0, 0, 0),
    "a = b = c = 2r = 2s = 2t" => dickson_gram(2, 2, 2, 1, 1, 1),
    "a = b = c, (18) an equality" => dickson_gram(3, 3, 3, -1, -1, -1),
  ]

  # changes of basis in GL_3(Z), rows the new basis vectors
  unimodular = [
    ZZ[1 1 0; 0 1 1; 0 0 1],
    ZZ[2 1 0; 1 1 0; 0 0 1],
    ZZ[1 0 0; 3 1 0; -2 5 1],
    ZZ[0 1 0; 0 0 1; 1 0 0] * ZZ[1 2 3; 0 1 4; 0 0 1],
    ZZ[-1 0 0; 0 1 0; 0 0 1] * ZZ[1 -1 0; 1 0 -1; 4 -3 -2],
    ZZ[1 1 1; 1 2 2; 1 2 3] * ZZ[1 0 0; -7 1 0; 5 -6 1],
    ZZ[0 0 1; 1 0 0; 0 1 0] * ZZ[5 3 0; 3 2 0; 1 1 1],
  ]
  @test all(U -> abs(det(U)) == 1, unimodular)

  @testset "is_eisenstein_reduced" begin
    @test all(is_pd(G) for (_, G) in vcat(violating, satisfying))
    # each form fails exactly the condition it was built to fail, so a
    # predicate that drops or misreads one condition fails one of these
    for (name, G) in violating
      @test !is_eisenstein_reduced(G)
    end
    # a predicate that reads a condition on a boundary too strictly rejects
    # one of these
    for (name, G) in satisfying
      @test is_eisenstein_reduced(G)
    end
  end

  @testset "argument checks" begin
    malformed = [
      ZZ[1 0; 0 1],
      ZZ[1 0 0 0; 0 1 0 0; 0 0 1 0; 0 0 0 1],
      ZZ[2 1 0; 0 2 0; 0 0 2],
      ZZ[1 0 0; 0 -1 0; 0 0 1],
      ZZ[1 0 0; 0 1 0; 0 0 0],
      ZZ[1 2 0; 2 1 0; 0 0 1],
      zero_matrix(ZZ, 3, 3),
    ]
    for G in malformed, f in (is_eisenstein_reduced, eisenstein_reduction,
                              eisenstein_reduction_with_transform)
      @test_throws ArgumentError f(G)
    end
    # without the checks, a form that is not positive definite still raises
    # rather than looping or returning: indefinite with a negative diagonal
    # entry, indefinite with a positive diagonal, semidefinite, and an
    # indefinite form with entries beyond 2^63
    V = ZZ[1 0 0; 2^40 1 0; ZZ(3)^30 ZZ(5)^20 1]
    not_definite = [
      ZZ[1 0 0; 0 1 0; 0 0 -1],
      ZZ[1 2 0; 2 1 0; 0 0 1],
      ZZ[1 1 0; 1 1 0; 0 0 1],
      V * ZZ[3 0 0; 0 -5 0; 0 0 7] * transpose(V),
    ]
    @test !any(is_pd, not_definite)
    for G in not_definite, f in (eisenstein_reduction,
                                 eisenstein_reduction_with_transform)
      @test_throws ArgumentError f(G; check = false)
    end
  end

  @testset "reduction" begin
    # the bases include a form on each boundary of (25), (26) and (41), and
    # one violating each, so the reduction meets every boundary case
    bases = [G for (_, G) in vcat(violating, satisfying)]
    corpus = [(G, U * G * transpose(U)) for G in bases for U in unimodular]
    @test all(is_pd(H) for (_, H) in corpus)
    @test !any(is_eisenstein_reduced(H) for (_, H) in corpus)

    for G in bases
      R = eisenstein_reduction(G)
      @test is_eisenstein_reduced(R)
      @test eisenstein_reduction(R) == R
      # Theorem 104: every form equivalent to G reduces to the same matrix
      @test all(eisenstein_reduction(H) == R for (B, H) in corpus if B === G)
    end

    for (_, H) in corpus
      R, U = eisenstein_reduction_with_transform(H)
      @test abs(det(U)) == 1
      @test U * H * transpose(U) == R
      @test R == eisenstein_reduction(H)
    end

    # any integer matrix type, not only ZZMatrix
    generic(H) = Hecke.AbstractAlgebra.Generic.MatSpaceElem{ZZRingElem}(
                   ZZ, Matrix(H))
    @test all(eisenstein_reduction(generic(H)) == eisenstein_reduction(H)
              for (_, H) in corpus)
  end

  @testset "large entries" begin
    # entries of about 2^80, 2^140 and 2^400, each equivalent to a small form
    # by construction, so each must reduce to that form's reduction
    G = dickson_gram(8, 10, 11, -4, -2, -3)
    R = eisenstein_reduction(G)
    for e in (40, 70, 200)
      V = ZZ[1 0 0; ZZ(2)^e + 1 1 0; -ZZ(3)^div(e, 2) ZZ(5)^div(e, 3) 1]
      H = V * G * transpose(V)
      @test maximum(abs, Matrix(H)) > ZZ(2)^(2 * e - 2)
      @test eisenstein_reduction(H) == R
      R_H, U = eisenstein_reduction_with_transform(H)
      @test U * H * transpose(U) == R_H
    end
    # the conditions of Theorem 103 are homogeneous, so scaling commutes with
    # reduction; at 2^100 the scaled forms are far beyond machine words
    k = ZZ(2)^100
    for (_, G) in satisfying
      @test eisenstein_reduction(k * G) == k * eisenstein_reduction(G)
    end
    # entries that fit in 64 bits whose sums do not
    m = ZZ(2)^62
    W = m * ZZ[1 1 1; 1 1 1; 1 1 1] + dickson_gram(3, 4, 5, 1, 1, 1)
    @test all(x -> abs(x) < ZZ(2)^63, Matrix(W))
    R = eisenstein_reduction(W)
    @test is_eisenstein_reduced(R)
    @test det(R) == det(W)
    U = unimodular[1]
    @test eisenstein_reduction(U * W * transpose(U)) == R

    # the machine integers the reduction runs on raise on overflow instead of
    # wrapping, which is what makes the fallback to wider arithmetic sound
    W = Hecke._TernaryWord{Int64}
    @test_throws OverflowError W(typemax(Int64)) + W(1)
    @test_throws OverflowError W(typemin(Int64)) - W(1)
    @test_throws OverflowError W(2^32) * W(2^31)
    @test_throws OverflowError -W(typemin(Int64))
    @test_throws OverflowError abs(W(typemin(Int64)))
    @test (W(2^31) * W(2^31)).v == 2^62
  end

  @testset "lattices" begin
    G = ZZ[23 34 68; 34 68 102; 68 102 204]
    R = eisenstein_reduction(G)
    L = integer_lattice(; gram = G)
    M = eisenstein_reduction(L)
    @test ambient_space(M) === ambient_space(L)
    @test M == L
    @test gram_matrix(M) == R
    @test is_eisenstein_reduced(M)
    @test !is_eisenstein_reduced(L)
    @test gram_matrix(eisenstein_reduction(L; same_ambient = false)) == R

    # a lattice with a rational Gram matrix, and one in a larger space
    L = integer_lattice(; gram = QQ(1, 6) * G)
    @test gram_matrix(eisenstein_reduction(L)) == QQ(1, 6) * R
    L = lattice(quadratic_space(QQ, 4), QQ[1 1 0 0; 0 1 1 0; 1 0 3 1])
    M = eisenstein_reduction(L)
    @test M == L
    @test is_eisenstein_reduced(M)

    @test_throws ArgumentError eisenstein_reduction(root_lattice(:A, 2))
    L = integer_lattice(; gram = ZZ[1 0 0; 0 1 0; 0 0 -1])
    @test_throws ArgumentError eisenstein_reduction(L)
    @test_throws ArgumentError is_eisenstein_reduced(root_lattice(:A, 4))
  end

  @testset "against isometry testing" begin
    # Theorem 104 checked against Hecke's own isometry test: in every genus
    # of positive definite ternary lattices of determinant at most 30, the
    # representatives, pairwise not isometric, have distinct reductions, and
    # a change of basis does not change the reduction
    for d in 1:30, g in integer_genera((3, 0), d)
      reps = representatives(g)
      R = [gram_matrix(eisenstein_reduction(L)) for L in reps]
      @test allunique(R)
      for (L, RL) in zip(reps, R), U in unimodular[1:3]
        B = U * basis_matrix(L)
        LU = lattice(ambient_space(L), B; isbasis = true)
        @test gram_matrix(eisenstein_reduction(LU)) == RL
      end
    end
    # and on pairs of forms of one determinant, equal reductions exactly when
    # is_isometric says so
    forms = [dickson_gram(a, b, c, r, s, t)
             for a in 1:3 for b in a:4 for c in b:5
             for r in -1:1 for s in -1:1 for t in -1:1]
    lattices = [integer_lattice(; gram = G) for G in forms if is_pd(G)]
    for D in unique(det.(gram_matrix.(lattices)))
      Ls = filter(L -> det(gram_matrix(L)) == D, lattices)
      length(Ls) > 6 && (Ls = Ls[1:6])
      for i in eachindex(Ls), j in i+1:lastindex(Ls)
        L, M = Ls[i], Ls[j]
        @test (gram_matrix(eisenstein_reduction(L)) ==
               gram_matrix(eisenstein_reduction(M))) == is_isometric(L, M)
      end
    end
  end
end
