function _random_invertible_matrix(n, B)
  A = identity_matrix(FlintZZ, n)
  if n == 1
    return A
  end
  for k in 1:10
    i = rand(1:(n - 1))
    j = rand((i + 1):n)
    A[i, j] += rand(B)
  end
  @assert det(A) == 1
  C = identity_matrix(FlintZZ, n)
  for k in 1:10
    i = rand(1:(n - 1))
    j = rand((i + 1):n)
    C[i, j] += rand(B)
  end
  @assert det(C) == 1
  return transpose(C) * A
end

const lattices_and_aut_order = [
(([[2]]), 2), 
# 2
(([[1, 0], [0, 2]]), 4),
(([[2, -1], [-1, 2]]), 12),
# 3
(([[2, 1, 0],
   [1, 2, 0],
   [0, 0, 26]]), 24),
# 4
(([[1, 0, 0, 0],
   [0, 2, -1, 1],
   [0, -1, 3, -1],
   [0, 1, -1, 3]]), 16),
# 5
(([[2, 1, 1, 1, -1],
   [1, 2, 1, 1, 0],
   [1, 1, 2, 1, -1],
   [1, 1, 1, 2, -1],
   [-1, 0, -1, -1, 2]]), 3840),
(([[1, 0, 0, 0, 0],
   [0, 1, 0, 0, 0],
   [0, 0, 1, 0, 0],
   [0, 0, 0, 2, 1],
   [0, 0, 0, 1, 3]]), 192),
# 6
(([[2, -1, 0, 0, 0, 0],
   [-1, 2, -1, 0, 0, 0],
   [0, -1, 2, -1, 0, -1],
   [0, 0, -1, 2, -1, 0],
   [0, 0, 0, -1, 2, 0],
   [0, 0, -1, 0, 0, 2]]), 103680),
# 6
(([[1, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 0, 0],
   [0, 0, 2, 1, 0, 1],
   [0, 0, 1, 3, 1, 1],
   [0, 0, 0, 1, 2, 1],
   [0, 0, 1, 1, 1, 3]]), 512),
#(([[8, 4, 4, 4, 4, 4, 4, 2, 4, 4, 4, 2, 4, 2, 2, 2, 4, 2, 2, 2, 0, 0, 0, -3],
#   [4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 2, 1, 1, 2, 1, 0, 0, -1],
#   [4, 2, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 1, 1, 1, 0, 0, -1],
#   [4, 2, 2, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 0, 0, -1],
#   [4, 2, 2, 2, 4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, -1],
#   [4, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2, 1, 2, 2, 1, 1, 2, 1, 2, 1, 0, 0, 0, -1],
#   [4, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2, 1, 2, 1, 2, 1, 2, 1, 1, 2, 0, 0, 0, -1],
#   [2, 2, 2, 2, 2, 2, 2, 4, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 0, 0, 1],
#   [4, 2, 2, 2, 2, 2, 2, 1, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, -1],
#   [4, 2, 2, 2, 2, 2, 2, 1, 2, 4, 2, 2, 2, 2, 1, 1, 2, 2, 1, 1, 0, 1, 0, -1],
#   [4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 4, 2, 2, 1, 2, 1, 2, 1, 2, 1, 0, 0, 1, -1],
#   [2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 1, 1],
#   [4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 4, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, -1],
#   [2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 4, 2, 2, 1, 2, 2, 2, 2, 2, 1, 1],
#   [2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 4, 2, 1, 2, 2, 2, 2, 1, 2, 1],
#   [2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 2, 2, 1, 1, 1],
#   [4, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, -1],
#   [2, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 4, 2, 2, 2, 2, 1, 1],
#   [2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 4, 2, 2, 1, 2, 1],
#   [2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 4, 2, 1, 1, 1],
#   [0, 1, 1, 1, 1, 0, 0, 2, 1, 0, 0, 2, 1, 2, 2, 2, 1, 2, 2, 2, 4, 2, 2, 2],
#   [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2],
#   [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2],
#   [-3, -1, -1, -1, -1, -1, -1, 1, -1, -1, -1, 1, -1, 1, 1, 1, -1, 1, 1, 1, 2,
#    2, 2, 4]]), 8315553613086720000)]
(([[2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [-1, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, -1, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, -1, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, -1, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, -1, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, -1, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, -1, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, -1, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, -1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2]]), 711374856192000)]

function test_automorphisms(L, G, ambient_representation)
  if ambient_representation
    @test all(g * gram_matrix(ambient_space(L)) * transpose(g)  == gram_matrix(ambient_space(L)) for g in G)
  else
    @test all(g * gram_matrix(L) * transpose(g) == gram_matrix(L) for g in G)
  end
end

@testset "Z-lattice automorphisms" begin
  for (m, o) in lattices_and_aut_order
    n = length(m[1])
    G = matrix(FlintZZ, n, n, reduce(vcat, m))
    L = Zlattice(gram = G)
    Ge = automorphism_group_generators(L, ambient_representation = true)
    test_automorphisms(L, Ge, true)
    Ge = automorphism_group_generators(L, ambient_representation = false)
    test_automorphisms(L, Ge, false)
    @test automorphism_group_order(L) == o
  end

  D = lattice_database()
  l = number_of_lattices(D)
  for i in 1:min(l, 200)
    L = lattice(D, i)
    L = Zlattice(gram = gram_matrix(L)) # to avoid caching
    @test automorphism_group_order(L) == lattice_automorphism_group_order(D, i)
  end
end

@testset "Z-lattice isomorphisms" begin
  for (m, o) in lattices_and_aut_order 
    n = length(m[1])
    G = matrix(FlintZZ, n, n, reduce(vcat, m))
    L = Zlattice(gram = G)
    X = _random_invertible_matrix(n, -3:3)
    @assert abs(det(X)) == 1
    L2 = Zlattice(gram = X * G * X')
    b, T = isisometric(L, L2, ambient_representation = false)
    @test b
    @test T * gram_matrix(L2) * T' == gram_matrix(L)
    L2 = Zlattice(X, gram = G)
    b, T = isisometric(L, L2, ambient_representation = false)
    @test b
    @test T * gram_matrix(L2) * T' == gram_matrix(L)
    b, T = isisometric(L, L2, ambient_representation = true)
    @test b
    @test T * gram_matrix(ambient_space(L2)) * T' ==
            gram_matrix(ambient_space(L))
  end

  D = lattice_database()
  l = number_of_lattices(D)
  for i in 1:min(l, 200)
    L = lattice(D, i)
    L = Zlattice(gram = gram_matrix(L)) # to avoid caching
    n = rank(L)
    X = change_base_ring(FlintQQ, _random_invertible_matrix(n, -3:3))
    @assert abs(det(X)) == 1
    L2 = Zlattice(gram = X * gram_matrix(L) * X')
    b, T = isisometric(L, L2, ambient_representation = false)
    @test b
    @test T * gram_matrix(L2) * T' == gram_matrix(L)
  end
end
