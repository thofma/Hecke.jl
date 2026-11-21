@testset "Reduced characteristic vectors" begin
  # for lattices whose shortest vectors are roots, the reduced characteristic
  # vectors are computed from the minuscule vectors of the root sublattice;
  # this has to agree with the generic computation from all characteristic
  # vectors
  function generic_reduction(L)
    cv = Hecke._characteristic_vectors(L)
    cv = unique!(append!(cv, ZZMatrix[-v for v in cv]))
    return Set(vec(v) for v in Hecke._reduce_characteristic_vectors(cv, L))
  end

  n = 12
  M = zero_matrix(QQ, n+1, n)
  for i in 1:n-1
    M[i, i] = 1
    M[i, i+1] = -1
  end
  M[n, n-1] = 1
  M[n, n] = 1
  for j in 1:n
    M[n+1, j] = 1//2
  end
  # the unimodular lattice D_12^+, whose root sublattice D_12 has index 2
  Dplus = lattice(quadratic_space(QQ, identity_matrix(QQ, n)), M; is_basis=false)
  G = matrix(QQ, 4, 4, [2,0,0,0, 0,3,1,1, 0,1,3,-1, 0,1,-1,5])
  Ls = ZZLat[root_lattice(:A, 5), root_lattice(:D, 6), root_lattice(:E, 7),
             Dplus, integer_lattice(gram = G)]
  append!(Ls, root_lattices(6))
  for L in Ls
    @test Set(vec(v) for v in Hecke._reduced_characteristic_vectors_without_1(L)) == generic_reduction(L)
  end

  # the cache of minuscule tables is keyed on the ADE type of a component: its
  # fundamental roots come out in the standard numbering, so that its Cartan
  # matrix is the one of `root_lattice(t, k)`
  for L in Ls
    gram = Hecke._integral_split_gram(L)[1]
    types, components = Hecke._root_lattice_recognition_fundamental(L)
    for ((t, k), c) in zip(types, components)
      @test c*gram*transpose(c) == change_base_ring(ZZ, gram_matrix(root_lattice(t, k)))
    end
  end

  # lattices whose shortest vectors are not roots, and lattices with vectors of
  # norm one, which are split off first
  for L in [integer_lattice(gram = matrix(QQ, 2, 2, [4,1,1,4])), integer_lattice(gram = identity_matrix(QQ, 4)),
            direct_sum(integer_lattice(gram = identity_matrix(QQ, 1)), root_lattice(:D, 6))[1],
            direct_sum(integer_lattice(gram = identity_matrix(QQ, 2)), integer_lattice(gram = matrix(QQ, 2, 2, [4,1,1,4])))[1]]
    @test length(Hecke._reduced_characteristic_vectors(L)) == length(generic_reduction(L)) # the sets are only equal up to the action of the Weyl group.
  end

  # the hardcoded minuscule tables agree with what the Cartan matrix says: `d`
  # is its determinant and `adj` is `d` times its inverse. And the minuscule
  # vector of a class really solves the closest vector problem it stands for:
  # its norm is the distance of the class to the root lattice
  for (t, k) in vcat([(:A, k) for k in 1:12], [(:D, k) for k in 4:12], [(:E, k) for k in 6:8])
    R = root_lattice(t, k)
    cartan = gram_matrix(R)
    tab = Hecke._minuscule_table(t, k)
    @test tab.d == det(cartan)
    @test tab.adj == Int[Int(ZZ(x)) for x in tab.d*inv(cartan)]
    @test length(tab.data) == tab.d
    for (w, nrm) in values(tab.data)
      # `w` are weight coordinates, so the vector is `w*cartan^-1` in the
      # coordinates of `R`
      v = (matrix(QQ, 1, k, w)*inv(cartan))[1, :]
      @test Hecke._closest_vectors(R, v)[1] == nrm
    end
  end

  # the reduced characteristic vector set does not depend on the chosen basis
  U = matrix(QQ, 4, 4, [0,1,1,0, 0,0,0,-1, 0,0,-1,1, 1,-1,-1,1])
  norms(L) = sort!([(matrix(ZZ, v)*Hecke._integral_split_gram(L)[1]*transpose(matrix(ZZ, v)))[1, 1]
                    for v in Hecke._reduced_characteristic_vectors(L)])
  @test norms(integer_lattice(gram = G)) == norms(integer_lattice(gram = U*G*transpose(U)))

  # why lll is needed:
  L = integer_lattice(gram=QQ[-2 0 0 0 0 0 0 0 0 1 1 1 1 -1 0 0; 0 -2 1 -1 1 0 0 0 0 1 1 1 1 -1 1 0; 0 1 -2 1 -1 0 0 0 0 0 -1 0 -1 1 -1 0; 0 -1 1 -2 1 0 0 0 0 0 0 1 0 0 0 0; 0 1 -1 1 -2 0 0 0 0 0 -1 -1 0 1 -1 0; 0 0 0 0 0 -2 0 0 0 1 0 0 0 0 -1 -1; 0 0 0 0 0 0 -2 1 1 -1 -1 1 1 -1 1 0; 0 0 0 0 0 0 1 -2 -1 0 0 -1 -1 0 -1 0; 0 0 0 0 0 0 1 -1 -2 1 0 -1 -1 0 -1 0; 1 1 0 0 0 1 -1 0 1 -4 -2 0 -1 0 1 1; 1 1 -1 0 -1 0 -1 0 0 -2 -4 0 -1 1 -1 0; 1 1 0 1 -1 0 1 -1 -1 0 0 -4 -1 1 -1 0; 1 1 -1 0 0 0 1 -1 -1 -1 -1 -1 -4 2 -2 0; -1 -1 1 0 1 0 -1 0 0 0 1 1 2 -4 2 0; 0 1 -1 0 -1 -1 1 -1 -1 1 -1 -1 -2 2 -4 -1; 0 0 0 0 0 -1 0 0 0 1 0 0 0 0 -1 -2]);
  @test length(Hecke._reduced_characteristic_vectors(lll(L))) == 22


end

@testset "Canonical Gram matrix" begin
  # the canonical Gram matrix does not depend on the basis, it is compatible
  # with rescaling, and it separates the isometry classes of a genus
  E8 = root_lattice(:E, 8)
  D4 = root_lattice(:D, 4)
  G = QQ[3 1 1 0 0; 1 3 0 0 0; 1 0 3 0 0; 0 0 0 3 0; 0 0 0 0 3]
  Ls = ZZLat[integer_lattice(; gram = zero_matrix(QQ, 0, 0)),
             integer_lattice(; gram = QQ[-3//2;]),          # rank one
             integer_lattice(; gram = identity_matrix(QQ, 3)),
             integer_lattice(; gram = diagonal_matrix(QQ[1 0; 0 1], gram_matrix(D4))),
             integer_lattice(; gram = QQ[1 0 0; 0 7 3; 0 3 9]),
             integer_lattice(; gram = QQ[2 0; 0 6]),        # roots of norm 2 and 6
             integer_lattice(; gram = QQ[3 1; 1 5]),        # no roots
             integer_lattice(; gram = G),
             E8, rescale(root_lattice(:E, 7), -1//3), rescale(D4, 2),
             root_lattice(:A, 6), direct_sum(E8, rescale(D4, 3))[1]]
  for L in Ls
    n = rank(L)
    C, T = Hecke._canonical_gram_matrix(L)
    @test T * gram_matrix(L) * transpose(T) == C
    @test is_unit(det(T))
    for _ in 1:3
      U = identity_matrix(ZZ, n)
      for _ in 1:(3 * n)
        i, j = rand(1:n), rand(1:n)
        i != j && add_row!(U, rand(-2:2), i, j)
      end
      M = integer_lattice(; gram = U * gram_matrix(L) * transpose(U))
      @test Hecke._canonical_gram_matrix(M)[1] == C
    end
    @test Hecke._canonical_gram_matrix(rescale(L, -5//7))[1] == -5//7 * C
  end
  @test_throws ArgumentError Hecke._canonical_gram_matrix(hyperbolic_plane_lattice())

  # the two even unimodular lattices of rank 16 have the same theta series
  n = 16
  M = zero_matrix(QQ, n + 1, n)
  for i in 1:(n - 1)
    M[i, i] = 1
    M[i, i + 1] = -1
  end
  M[n, n - 1] = M[n, n] = 1
  M[n + 1, :] = fill(QQ(1, 2), n)
  Dplus = lattice(quadratic_space(QQ, identity_matrix(QQ, n)), M; is_basis = false)
  C = Hecke._canonical_gram_matrix(direct_sum(E8, E8)[1])[1]
  @test genus(Dplus) == genus(direct_sum(E8, E8)[1])
  @test Hecke._canonical_gram_matrix(Dplus)[1] != C
  @test Hecke._canonical_gram_matrix(integer_lattice(; gram = QQ[1 0; 0 6]))[1] !=
        Hecke._canonical_gram_matrix(integer_lattice(; gram = QQ[2 0; 0 3]))[1]
end
