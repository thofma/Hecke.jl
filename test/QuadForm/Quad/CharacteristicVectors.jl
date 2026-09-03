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
  Dplus = lattice(quadratic_space(QQ, identity_matrix(QQ, n)), M; isbasis=false)
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
    @test Set(vec(v) for v in Hecke._reduced_characteristic_vectors(L)) == generic_reduction(L)
  end

  # the minuscule vectors of an irreducible root lattice of type ADE represent
  # the non-trivial classes of its discriminant group and have known norms
  for (t, k, nrm) in [(:A, 5, 3//2), (:A, 11, 3//1), (:D, 8, 2//1), (:D, 17, 17//4),
                      (:E, 6, 4//3), (:E, 7, 3//2), (:E, 8, 0//1)]
    cartan = Int[Int(ZZ(x)) for x in gram_matrix(root_lattice(t, k))]
    tab = Hecke._minuscule_table(cartan)
    @test length(tab.data) == tab.d
    @test maximum(x[2] for x in values(tab.data)) == nrm
  end

  # the reduced characteristic vector set does not depend on the chosen basis
  U = matrix(QQ, 4, 4, [0,1,1,0, 0,0,0,-1, 0,0,-1,1, 1,-1,-1,1])
  norms(L) = sort!([(matrix(ZZ, v)*Hecke._integral_split_gram(L)[1]*transpose(matrix(ZZ, v)))[1, 1]
                    for v in Hecke._reduced_characteristic_vectors(L)])
  @test norms(integer_lattice(gram = G)) == norms(integer_lattice(gram = U*G*transpose(U)))
end
