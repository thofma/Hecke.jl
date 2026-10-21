@testset "Gross lattices" begin
  # The quaternion algebra ramified exactly at p and infinity, as (-p, -q)
  # with q = 3 mod 8 and (p/q) = -1 (Ibukiyama, Nagoya Math. J. 88, Lemma 1.1)
  Bp = [2 => 3, 3 => 19, 5 => 3, 7 => 11, 13 => 11, 97 => 19]
  # the coordinates of elements on 1, i, j, ij, as rows
  coords(xs) = matrix(QQ, [coefficients(x)[k] for x in xs, k in 1:4])

  for (p, q) in Bp
    A = quaternion_algebra(QQ, -p, -q)
    O = maximal_order(A)
    L = gross_lattice(O)
    B = gross_lattice_basis(O)
    @test rank(L) == 3 && length(B) == 3
    @test basis_matrix(L) == coords(B)
    # the pairing trd(x conj(y))/2, with the reduced norm on the diagonal
    G = gross_gram_matrix(B)
    @test gram_matrix(L) == G
    @test all(G[i, j] == trred(B[i] * conjugate(B[j]))//2
              for i in 1:3, j in 1:3)
    @test is_positive_definite(L)
    # Chevyrev-Galbraith, Lemma 2 of arXiv:1301.6875v4
    @test det(L) == 4 * p^2
    # the definition: trace zero, in Z + 2O, and all of it, as the Gross
    # lattice is the image of O under x -> 2x - trd(x)
    for x in B
      @test iszero(trred(x))
      @test any(n -> QQ(1, 2) * (x - n) in O, 0:1)
    end
    images = [2 * elem_in_algebra(y) - trred(elem_in_algebra(y))
              for y in basis(O)]
    @test L == lattice(ambient_space(L), coords(images); isbasis = false)
  end

  # Goren-Love, Thm. 1.4: maximal orders of B_p are isomorphic if and only if
  # their Gross lattices are isometric; Hecke's _is_isomorphic compares the
  # rank 4 lattices of the orders instead (Kirschmer). The maximal orders are
  # the left orders of the right ideals of norm 2 and 3 of a maximal order,
  # fixed so that they are the same on every run: Ibukiyama's
  # Z + Z(1 + j)/2 + Z i(1 + j)/2 + Z (6 + i)j/19, as 6^2 = -97 mod 19
  # (Nagoya Math. J. 88, Lemma 1.2).
  A = quaternion_algebra(QQ, -97, -19)
  e, i, j, k = basis(A)
  O = order(A, [e, QQ(1, 2) * (e + j), QQ(1, 2) * (i + k),
                QQ(1, 19) * (6 * j + k)]; isbasis = true)
  @test is_maximal(O)
  Os = [O; [left_order(I) for l in (2, 3)
            for I in Hecke.maximal_integral_ideals(O, l; side = :right)]]
  Ls = gross_lattice.(Os)
  @test all(det(L) == 4 * 97^2 for L in Ls)
  iso = [Hecke._is_isomorphic(R, S) for R in Os, S in Os]
  @test [is_isometric(L, M) for L in Ls, M in Ls] == iso
  # 8 orders in 4 isomorphism classes
  @test length(unique(findfirst(iso[r, :]) for r in 1:8)) == 4

  # orders that are not maximal: an Eichler order of level 2 and Z + 3M. The
  # determinant is 4 d(O)^2, d(O) the reduced discriminant: for a maximal order
  # this is Chevyrev-Galbraith, Lemma 2, which they derive from Kohel's thesis,
  # Corollary 71, stated there for any order.
  for (p, q) in [(3, 19), (97, 19)]
    A = quaternion_algebra(QQ, -p, -q)
    M = maximal_order(A)
    I = first(Hecke.maximal_integral_ideals(M, 2; side = :right))
    E = order(A, vcat([one(A)], basis(I)))
    Z3M = order(A, vcat([one(A)], [3 * elem_in_algebra(x) for x in basis(M)]))
    for O in (E, Z3M)
      L = gross_lattice(O)
      B = gross_lattice_basis(O)
      @test rank(L) == 3 && is_positive_definite(L)
      @test gram_matrix(L) == gross_gram_matrix(B)
      @test det(L) == 4 * Hecke._reduced_disc(O)^2
      for x in B
        @test iszero(trred(x))
        @test any(n -> QQ(1, 2) * (x - n) in O, 0:1)
      end
      images = [2 * elem_in_algebra(y) - trred(elem_in_algebra(y))
                for y in basis(O)]
      @test L == lattice(ambient_space(L), coords(images); isbasis = false)
    end
  end

  # the Gross lattice is defined for orders of B_p only: not for M_2(QQ), nor
  # for (-3, -10), definite but ramified at 2, 3 and 5
  for (a, b) in [(1, 1), (-3, -10)]
    A = quaternion_algebra(QQ, a, b)
    M = maximal_order(A)
    @test_throws ArgumentError gross_lattice(M)
    @test_throws ArgumentError gross_lattice_basis(M)
    @test_throws ArgumentError gross_gram_matrix(basis(A)[2:4])
  end

  B = gross_lattice_basis(maximal_order(quaternion_algebra(QQ, -1, -3)))
  @test_throws ArgumentError gross_gram_matrix(B[1:2])
  @test_throws ArgumentError gross_gram_matrix(QQ(1, 3) .* B)
end
