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
#    2, 2, 4]]), 8315553613086720000),
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

@testset "Zlattices" begin

  # Creation

  G = matrix(QQ, 2, 2, [2, 1, 1, 2])
  B = matrix(ZZ, 1, 2, [1, 0])
  @test (@inferred Zlattice(B ;gram = G)) isa ZLat
  @test (@inferred Zlattice(B)) isa ZLat
  B = matrix(QQ, 1, 2, [1, 0])
  @test (@inferred Zlattice(B ;gram = G)) isa ZLat
  @test (@inferred Zlattice(B)) isa ZLat
  @test (@inferred Zlattice(B; gram = G, check=false)) isa ZLat
  @test (@inferred Zlattice(gram = G, check=false)) isa ZLat
  @test_throws ArgumentError Zlattice(gram = B)

  V = quadratic_space(FlintQQ, G)
  B = matrix(ZZ, 1, 2, [1, 0])
  @test (@inferred lattice(V, B)) isa ZLat
  Lr1 = lattice(V, B)
  B = matrix(QQ, 1, 2, [1, 0])
  @test (@inferred lattice(V, B)) isa ZLat

  B = matrix(GF(2), 1, 2, [1, 0])
  @test_throws MethodError lattice(V, B)

  B = matrix(QQ, 1, 2, [1, 0])
  Lr1 = lattice(V, B)
  B = matrix(ZZ, 2, 2, [2, 0, 0, 2])
  Lr2 = lattice(V, B)
  B = matrix(ZZ, 0, 2, [])
  Lr0 = lattice(V, B)

  @test (@inferred base_ring(Lr0)) isa ZZRing

  @test !(@inferred is_sublattice(Lr2, Lr1))
  M = Zlattice(;gram = FlintQQ[2 2; 2 2])
  @test !(@inferred is_sublattice(Lr0, M))
  @test is_sublattice(Lr2, Lr0)
  @test is_sublattice(Lr1, lattice(V, QQ[2 0;]))

  fl, rels = @inferred is_sublattice_with_relations(Lr1, lattice(V, QQ[2 0;]))
  @test fl
  @test rels == QQ[2;]

  # lattices of rank 0

  B = matrix(QQ, 0, 2, [])
  @test (@inferred lattice(V, B)) isa ZLat

  # Gram matrix

  @test zero_matrix(QQ, 0, 0) == @inferred gram_matrix(Lr0)
  @test zero_matrix(QQ, 0, 0) == @inferred gram_matrix_of_rational_span(Lr0)

  @test matrix(QQ, 1, 1, [2]) == @inferred gram_matrix(Lr1)
  @test matrix(QQ, 1, 1, [2]) == @inferred gram_matrix_of_rational_span(Lr1)

  B = matrix(ZZ, 2, 2, [2, 0, 0, 2])
  L = lattice(V, B)
  @test matrix(QQ, 2, 2, [8, 4, 4, 8]) == @inferred gram_matrix(Lr2)
  @test matrix(QQ, 2, 2, [8, 4, 4, 8]) == @inferred gram_matrix(Lr2)

  # rational span

  for L in [Lr0, Lr1, Lr2]
    V = @inferred rational_span(L)
    @test gram_matrix(V) == gram_matrix(L)
  end

  # orthogonal sum

  for L in [Lr0, Lr1, Lr2]
    for LL in [Lr0, Lr1, Lr2]
      LLL, = @inferred orthogonal_sum(L, LL)
      @test gram_matrix(LLL) == diagonal_matrix(gram_matrix(L), gram_matrix(LL))
    end
  end

  # printing

  s = sprint(show, "text/plain", Lr0)
  @test occursin("lattice", s)

  # root lattice recognition

  L = Zlattice(gram=ZZ[4;])
  LL,i,j = orthogonal_sum(L,L)
  @test LL == i(L)+j(L)
  @test L == preimage(i, LL)
  R = @inferred root_sublattice(L)
  @test 0 == rank(R)
  L = root_lattice(:A,2)
  R = lattice(ambient_space(L),basis_matrix(L)[1,:])
  @test rank(root_sublattice(R))==1

  L = orthogonal_sum(root_lattice(:A,2),root_lattice(:D,4))[1]
  R = root_lattice_recognition(L)
  @test length(R[1]) == 2
  @test (:D,4) in R[1] && (:A,2) in R[1]
  R = root_lattice_recognition_fundamental(L)
  @test gram_matrix(R[3][1])==gram_matrix(root_lattice(R[2][1]...))


  B = matrix(FlintQQ, 6, 6 ,[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]);
  G = matrix(FlintQQ, 6, 6 ,[3, 1, -1, 1, 0, 0, 1, 3, 1, 1, 1, 1, -1, 1, 3, 0, 0, 1, 1, 1, 0, 4, 2, 2, 0, 1, 0, 2, 4, 2, 0, 1, 1, 2, 2, 4]);
  L = Zlattice(B, gram = G);
  R = root_lattice_recognition(L)
  @test (isempty(R[1]) && isempty(R[2]))

  B = matrix(FlintQQ, 19, 20 ,[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]);
  G = matrix(FlintQQ, 20, 20 ,[-2, 0, 1, -1, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -4, 0, 0, 0, -1, -1, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, -2, 1, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, -2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, -2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -2, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -2, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -1, -1, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 1, 1, 0, -1, -1, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -1, 1, -1, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -2, 1, -1, 0, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -2, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -2, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, -2, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, -1, 0, -1, -2, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, -1, 0, -1, -1, -2, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2]);
  rsL = Zlattice(B, gram = G);
  @test length(root_lattice_recognition(rsL)[1]) == 4
  rsLp = rescale(rsL,-1)
  @test length(Hecke._irreducible_components_short_vectors(rsLp, 2))==4
  @test length(Hecke._irreducible_components_short_vectors(rsLp, 4))==4

  # isometry testing
  C1 = root_lattice(:A, 2)
  C1m = rescale(C1,-1)
  @test is_isometric(C1m, C1m)
  # automorphisms
  C2 = (1//3)*C1

  for (m, o) in lattices_and_aut_order
    n = length(m[1])
    G = matrix(FlintZZ, n, n, reduce(vcat, m))
    L = Zlattice(gram = G)
    Ge = automorphism_group_generators(L, ambient_representation = true)
    test_automorphisms(L, Ge, true)
    Ge = automorphism_group_generators(L, ambient_representation = false)
    test_automorphisms(L, Ge, false)
    @test automorphism_group_order(L) == o

    # L as a non-full lattice
    for C in [C1,C2]
      if rank(L) > 4 # small examples suffice
        continue
      end
      C1L, _, f = orthogonal_sum(C1, L)
      V = ambient_space(C1L)
      imL = lattice(V, f.matrix)
      Ge = automorphism_group_generators(imL, ambient_representation = true)
      test_automorphisms(imL, Ge, true)
      Ge = automorphism_group_generators(imL, ambient_representation = false)
      test_automorphisms(imL, Ge, false)
      @test automorphism_group_order(L) == o
      @test is_isometric_with_isometry(imL, imL)[1]
    end
  end

  D = lattice_database()
  l = number_of_lattices(D)
  for i in 1:min(l, 200)
    L = lattice(D, i)
    L = Zlattice(gram = gram_matrix(L)) # to avoid caching
    Ge = automorphism_group_generators(L, ambient_representation = true)
    test_automorphisms(L, Ge, true)
    Ge = automorphism_group_generators(L, ambient_representation = false)
    test_automorphisms(L, Ge, false)
    @test automorphism_group_order(L) == lattice_automorphism_group_order(D, i)
  end

  # automorphisms for indefinite of rank 2
  U = hyperbolic_plane_lattice()
  G = @inferred automorphism_group_generators(U)
  @test length(G) == 2
  @test all(m -> multiplicative_order(m) == 2, G)
  @test_throws ArgumentError automorphism_group_order(U)

  g = Zgenera((1,1), 12)
  Lg = representative.(g)
  for L in Lg
    V = ambient_space(L)
    G = @inferred automorphism_group_generators(L, ambient_representation = false)
    @test all(m -> m*gram_matrix(L)*transpose(m) == gram_matrix(L), G)
    G = @inferred automorphism_group_generators(L)
    @test all(m -> m*gram_matrix(V)*transpose(m) == gram_matrix(V), G)
  end
  # isometry

  for (m, o) in lattices_and_aut_order
    n = length(m[1])
    G = matrix(FlintZZ, n, n, reduce(vcat, m))
    L = Zlattice(gram = G)
    X = _random_invertible_matrix(n, -3:3)
    @assert abs(det(X)) == 1
    L2 = Zlattice(gram = X * G * transpose(X))
    b, T = is_isometric_with_isometry(L, L2, ambient_representation = false)
    @test b
    @test T * gram_matrix(L2) * transpose(T) == gram_matrix(L)
    L2 = Zlattice(X, gram = G)
    b, T = is_isometric_with_isometry(L, L2, ambient_representation = false)
    @test b
    @test T * gram_matrix(L2) * transpose(T) == gram_matrix(L)
    b, T = is_isometric_with_isometry(L, L2, ambient_representation = true)
    @test b
    @test T * gram_matrix(ambient_space(L2)) * transpose(T) ==
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
    L2 = Zlattice(gram = X * gram_matrix(L) * transpose(X))
    b, T = is_isometric_with_isometry(L, L2, ambient_representation = false)
    @test b
    @test T * gram_matrix(L2) * transpose(T) == gram_matrix(L)
  end

  #discriminant of a lattice
  L = Zlattice(ZZ[1 0; 0 1], gram = matrix(QQ, 2,2, [2, 1, 1, 2]))
  @test discriminant(L) == -3

  G = matrix(ZZ, 2, 2, [2, 1, 1, 2])
  L = Zlattice(gram=G)
  @test norm(L)==2
  G = (1//4)*matrix(QQ, 2, 2, [2, 1, 1, 2])
  L = Zlattice(gram=G)
  @test norm(L)==1//2
  G = matrix(ZZ, 0, 0, [])
  L = Zlattice(gram=G)
  @test norm(L) == 0
  @test scale(L) == 0


  #orthogonal submodule of a lattice
  V = quadratic_space(QQ, QQ[1 0 0; 0 1 0; 0 0 1])
  L = lattice(V, ZZ[1 -1 0; 0 1 -1])
  S = lattice(V, ZZ[1 -1 0;])
  submod = Hecke.orthogonal_submodule(L, S)
  @test  basis_matrix(submod) == matrix(QQ, 1, 3, [1 1 -2])

  @test is_definite(L)
  @test is_positive_definite(L)
  @test !is_negative_definite(L)
  @test L+L == L
  @test intersect(L,L) == L
  @test 2*L == L*2
  @test 0*L == L*0
  @test (1//2)L*2 == L
  @test !(L == 2*L)

  gram = QQ[-2 1 0 0 0 0 0 0 0 0; 1 -2 1 1 0 0 0 0 0 0; 0 1 -2 1 0 0 0 0 0 0; 0 1 1 -2 0 0 0 0 0 0; 0 0 0 0 -2 1 0 0 0 0; 0 0 0 0 1 -2 1 0 0 0; 0 0 0 0 0 1 -2 1 0 1; 0 0 0 0 0 0 1 -2 1 0; 0 0 0 0 0 0 0 1 -2 0; 0 0 0 0 0 0 1 0 0 -2]
  BS = QQ[1 0 0 0 0 0 0 0 0 0; 0 1 0 0 0 0 0 0 0 0; 0 0 1 0 0 0 0 0 0 0; 0 0 0 1 0 0 0 0 0 0]
  BH = QQ[3 12 11 11 0 0 0 0 0 0]
  V = quadratic_space(QQ,gram)
  L = lattice(V, BS)
  H = lattice(V, BH)
  R = Hecke.orthogonal_submodule(L,H)
  @test is_sublattice(L,R)

  # local modification
  L = rescale(Hecke.root_lattice(:A,3),15)
  M = Hecke.maximal_integral_lattice(L)
  M1 = Hecke._maximal_integral_lattice(L) # legacy
  @test genus(M) == genus(M1)
  for p in prime_divisors(ZZ(discriminant(L)))
    M = Hecke.local_modification(M, L, p)
  end
  @test genus(M) == genus(L)

  # maximal integral lattice
  G = ZZ[3 0 0 0 0 0 0 0 0 0 0 0;
         0 18 0 0 0 0 0 0 0 0 0 0;
         0 0 9 0 0 0 0 0 0 0 0 0;
         0 0 0 9 0 0 0 0 0 0 0 0;
         0 0 0 0 9 0 0 0 0 0 0 0;
         0 0 0 0 0 9 0 0 0 0 0 0;
         0 0 0 0 0 0 9 0 0 0 0 0;
         0 0 0 0 0 0 0 9 0 0 0 0;
         0 0 0 0 0 0 0 0 9 0 0 0;
         0 0 0 0 0 0 0 0 0 9 0 0;
         0 0 0 0 0 0 0 0 0 0 9 0;
         0 0 0 0 0 0 0 0 0 0 0 54]
  L = Zlattice(gram = G)
  LL = @inferred Hecke.maximal_integral_lattice(L)
  @test isone(norm(LL))

  G = QQ[1 0 0 0; 0 2 0 0; 0 0 17 0; 0 0 0 6]
  V = quadratic_space(QQ, G)
  B = QQ[2 0 0 0; 1 1 0 0; 1 0 1 0; 1//2 1//4 1//2 1//4]
  L = lattice(V, B)
  Ld = dual(L)
  @test is_sublattice(Ld,L)
  discriminant_group(L)

  # Kernel lattice
  L = root_lattice(:A, 2)
  f = matrix(ZZ, 2, 2, [0, 1, 1, 0])
  L1 = lattice(ambient_space(L), ZZ[1 1])
  L2 = lattice(ambient_space(L), ZZ[1 -1])
  L3 = lattice(ambient_space(L), ZZ[1 0])
  M = kernel_lattice(L, f - 1)
  @test basis_matrix(M) == QQ[1 1;]
  M = kernel_lattice(L, f - 1, ambient_representation = false)
  @test basis_matrix(M) == QQ[1 1;]
  M1 = kernel_lattice(L1, f - 1)
  M2 = kernel_lattice(L2, f - 1)
  @test_throws ArgumentError M3 = kernel_lattice(L3, f - 1)
  @test rank(M1) == 1
  @test rank(M2) == 0
  g = matrix(ZZ,1,1,[1])
  M0 = kernel_lattice(L1,g, ambient_representation =false)
  @test rank(M0) == 0

  f = matrix(QQ, 2, 2, [0, 1, 1, 0])
  M = kernel_lattice(L, f - 1)
  @test basis_matrix(M) == QQ[1 1;]
  M = kernel_lattice(L, f - 1, ambient_representation = false)
  @test basis_matrix(M) == QQ[1 1;]

  L = Zlattice(QQ[1 0; 0 2])
  f = matrix(QQ, 2, 2, [0, 1, 0, 0])
  @test_throws ErrorException kernel_lattice(L, f)
  M = kernel_lattice(L, f, ambient_representation = false)
  @test basis_matrix(M) == QQ[0 2;]

  @test_throws ErrorException root_lattice(:F,3)
  @test_throws ErrorException root_lattice(:D,1)


  L = root_lattice(:A, 2)
  @test signature_tuple(L) == (2,0,0)
  @test local_basis_matrix(L, 2) == 1
  @test local_basis_matrix(L, ideal(ZZ,2)) == 1
  @test det(L) == 3
  G = automorphism_group_generators(L)
  N = invariant_lattice(L, G)
  @test ambient_space(N) === ambient_space(L)
  @test rank(N) == 0
  @test basis_matrix(invariant_lattice(L, identity_matrix(QQ, 2))) == basis_matrix(L)

  L = [root_lattice(:D,i) for i in 2:10]
  @test all(l -> det(l) == 4, L)
  @test all(iseven, L)
  @test all(l -> norm(l) == 2, L)


  @test root_lattice(:D, 3) != root_lattice(:A, 2)
  # relies on caching
  @test root_lattice(:D, 3) == root_lattice(:A, 3)

  L = root_lattice(:D,4)
  @test norm(L) == 2
  @test automorphism_group_order(L) == 1152

  L = root_lattice(:E,6)
  @test discriminant(L) == -3
  @test iseven(L)
  @test norm(L) == 2
  @test Hecke.kissing_number(L) == 72

  L = root_lattice(:E,7)
  @test discriminant(L) == -2
  @test iseven(L)
  @test norm(L) == 2
  @test Hecke.kissing_number(L) == 126

  L = root_lattice(:E, 8)
  @test discriminant(L) == 1
  @test iseven(L)
  @test norm(L) == 2
  @test norm(L) == 2 # tests caching

  for n in 1:10
    L = hyperbolic_plane_lattice(n)
    @test iseven(L)
    @test det(L) == -n^2
    @test scale(L) == abs(n)
  end

  q = quadratic_space(QQ, QQ[2 1; 1 2])
  L = lattice(q, QQ[0 0; 0 0], isbasis = false)
  g = automorphism_group_generators(L)
  @test rank(L) == 0
  @test g == [identity_matrix(QQ, 2)]

  # membership check
  G = QQ[1 0 0 0; 0 2 0 0; 0 0 17 0; 0 0 0 6]
  V = quadratic_space(QQ, G)
  B = QQ[2 0 0 0; 1 1 0 0; 1 0 1 0; 1//2 1//4 1//2 1//4]
  L = lattice(V, B)
  x1 = [27//11, 1, 1//7, 2]
  x2 = [2//1, 14//2, 5//1, 9//3]
  x4 = [2, 1, 0, 1, 2]
  v = [1//2]
  l = Zlattice(matrix(QQ,1,1,[1//2;]))
  @test !(x1 in L)
  @test_throws ArgumentError is_primitive(L, v)
  @test divisibility(L, x1) == 1//154
  @test !(x2 in L)
  @test divisibility(L, x2) == 1//2
  @test B[1,:] in L
  @test is_primitive(L, B[1,:])
  @test !is_primitive(L, 2*B[1,:])
  @test divisibility(L, B[1,:]) == 1
  @test_throws ArgumentError divisibility(L, B[1,2:end])
  @test [B[4,i] for i in 1:ncols(B)] in L
  @test divisibility(L, [B[4,i] for i in 1:ncols(B)]) == 1
  @test_throws ArgumentError divisibility(L, B[1:2, :])
  @test_throws ArgumentError x4 in L
  @test_throws ArgumentError divisibility(L, x4)
  @test v in l
  @test is_primitive(l, v)
  @test divisibility(l, v) == 1//4

  U2 = hyperbolic_plane_lattice(2)
  B = basis_matrix(U2)
  v = B[1,:]+B[2,:]
  @test is_primitive(U2, v)
  @test divisibility(U2, v) == 2

  # Mass of lattices
  E8 = root_lattice(:E, 8)
  @test mass(E8) == 1//automorphism_group_order(E8)

  F23a = Zlattice(gram = matrix(ZZ,2,2,[2 1; 1 12]))
  F23b = Zlattice(gram = matrix(ZZ,2,2,[4 1; 1 6]))

  @test mass(F23a) == mass(F23b) == 3//4

  # LLL-reduction

  L = representative(Zgenera((0,16), 768, max_scale = 6, even=true)[2])
  LL = lll(L) # L and LL are equal since they are in the same space
  @test L == LL

  LL = lll(L, same_ambient = false) # L and LL are not equal, but isometric
  @test_broken false && is_isometric_with_isometry(L, LL)[1] # tests takes too long

  L = representative(Zgenera((2,1), -1)[1])
  LL = lll(L)
  @test L == LL
  @test rescale(L, -1) == lll(rescale(L, -1))

  L = representative(Zgenera((3,11), 1)[2])
  LL = lll(L)
  @test L == LL

  L = representative(Zgenera((3,12), 3)[1])
  LL = lll(L)
  @test L == LL

  L = Zlattice(gram=QQ[1//2;])
  @inferred lll(L)

  # Primitive extensions

  M = root_lattice(:E, 6)
  N = root_lattice(:E, 7)
  @test_throws ArgumentError primitive_closure(M, N) # Not in the same ambient space

  bM = basis_matrix(M)
  N1 = lattice_in_same_ambient_space(M, 2*bM[1:3,:])
  N2 = lattice_in_same_ambient_space(M, bM[4:6,:])
  N3 = @inferred primitive_closure(M, N1)

  @test_throws ArgumentError primitive_closure(N1, N2) # N2 not contained in \QQ N2
  @test_throws ArgumentError is_primitive(M, dual(M))  # M does not contain its dual
  @test !is_primitive(M, N1)  # Can't be primitive since its basis vector is not
  @test is_primitive(M, N2)
  @test is_primitive(M, N3)   # Primitive closure has to be primitive

  zM = lattice_in_same_ambient_space(M, bM[2:1,:]) # test for the zero lattice, always primitive
                                                   # since M is torsion-free
  @test is_primitive(M, zM)

  L = root_lattice(:E, 7)
  f = matrix(QQ, 7, 7, [1 2 3 2 1 1 1; -1 -2 -3 -3 -2 -1 -1; -1 -1 -1 0 0 0 -1; 1 0 0 0 0 0 0; 0 1 1 1 0 0 1; 0 0 0 0 1 1 0; 1 2 2 1 1 0 1])      # minpoly(f) = (x+1)*(x^6-x^5+x^4-x^3+x^2-x+1)
  g = matrix(QQ, 7, 7, [1 0 0 0 0 0 0; 0 1 0 0 0 0 0; 0 0 1 1 1 1 0; -1 -2 -3 -3 -2 -1 -1; 1 2 3 3 2 1 2; -1 -2 -3 -2 -1 -1 -2; 0 0 0 0 -1 -1 0]) # (x^2+x+1) divides minpoly(g)
  S = kernel_lattice(L, f+1)
  R = kernel_lattice(L, f^6-f^5+f^4-f^3+f^2-f+1)
  M = kernel_lattice(L, f)
  N = kernel_lattice(L, g^2 + g + 1)

  for lat in [S, R, M, N]
    @test is_primitive(L, lat)  # Kernel lattices are primitive
  end

  @test_throws ArgumentError glue_map(1//2*L, S, R) # 1//2*L is not all integral
  @test_throws ArgumentError glue_map(L, 2*S, R)    # 2*S is not primitive in L
  @test_throws ArgumentError glue_map(L, S, M)      # Sum of the ranks do not match
  @test_throws ArgumentError glue_map(L, R, N)      # R and N are not orthognal

  glue, iS, iR = @inferred glue_map(L, S, R)
  @test is_bijective(glue)          # It is an anti-isometry so it has to be bijective
  HS = domain(glue)

  for a in collect(HS)
    @test a*a == -glue(a)*glue(a)   # Checking that it is indeed an anti-isometry
  end

  L2 = @inferred overlattice(glue)
  @test L2 == L  # We found back our initial overlattice

  # primary and elementary lattices

  L = Zlattice(gram=matrix(ZZ, [[2, -1, 0, 0, 0, 0],[-1, 2, -1, -1, 0, 0],[0, -1, 2, 0, 0, 0],[0, -1, 0, 2, 0, 0],[0, 0, 0, 0, 6, 3],[0, 0, 0, 0, 3, 6]]))
  @test_throws ArgumentError is_primary_with_prime(dual(L))
  bool, p = @inferred is_primary_with_prime(L)
  @test !bool && p == -1

  for i in [6,7,8]
    L = root_lattice(:E, i)
    @test is_elementary(L, 9-i)
    @test i != 8 || is_unimodular(L)
  end

  for i in [1,2,4,6,10,12,16,18]
    A = root_lattice(:A, i)
    bool, p = @inferred is_elementary_with_prime(A)
    @test bool
    @test p == i+1
  end
  L = direct_sum(hyperbolic_plane_lattice(), root_lattice(:D, 7))[1]
  @test is_primary(L, 2) && !is_elementary(L, 2)
  @test is_unimodular(hyperbolic_plane_lattice())
end

@testset "isometry testing" begin
  u = ZZ[-69 -46 -58 17; -81 -54 -68 20; -54 -36 -45 13; -241 -161 -203 60]
  @test abs(det(u))==1
  L = Zlattice(gram=ZZ[0 2 0 0; 2 0 0 0; 0 0 2 1; 0 0 1 2])
  M = Zlattice(gram=u*gram_matrix(L)*transpose(u))
  @test Hecke.is_isometric(L, M)
  f, r = Hecke._is_isometric_indef_approx(L, M);
  G = genus(L)
  @test all(valuation(r,p)==0 for p in bad_primes(G))
  @test is_automorphous(G, r)

  # some trivia for code coverage
  L1 = hyperbolic_plane_lattice()
  L2 = hyperbolic_plane_lattice(2)
  @test !is_isometric(L1, L2)

  L1 = root_lattice(:A, 4)
  L2 = root_lattice(:D, 4)
  @test !is_isometric_with_isometry(L1, L2)[1]

  # Example from Conway Sloane Chapter 15 p.393
  L1 = Zlattice(gram=ZZ[2 1 0; 1 2 0; 0 0 18])
  L2 = Zlattice(gram=ZZ[6 3 0; 3 6 0; 0 0 2])
  @test genus(L1)==genus(L2)
  @test !Hecke.is_isometric(L1, L2)
end

@testset "orthogonal sums" begin
  L1 = root_lattice(:A, 6)
  L2 = root_lattice(:E, 7)
  L, inj, proj = @inferred direct_sum([L1, L2])
  @test genus(L) == orthogonal_sum(genus(L1), genus(L2))
  for i in 1:2, j in 1:2
    f = compose(inj[i], proj[j])
    m = f.matrix
    @test i != j ? iszero(m) : isone(m)
  end
end

