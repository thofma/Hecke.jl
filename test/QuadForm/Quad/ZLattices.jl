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

  V = quadratic_space(FlintQQ, G)
  B = matrix(ZZ, 1, 2, [1, 0])
  @test (@inferred lattice(V, B)) isa ZLat
  Lr1 = lattice(V, B)
  B = matrix(QQ, 1, 2, [1, 0])
  @test (@inferred lattice(V, B)) isa ZLat

  B = matrix(GF(2), 1, 2, [1, 0])
  @test_throws ErrorException lattice(V, B)

  B = matrix(QQ, 1, 2, [1, 0])
  Lr1 = lattice(V, B)
  B = matrix(ZZ, 2, 2, [2, 0, 0, 2])
  Lr2 = lattice(V, B)
  B = matrix(ZZ, 0, 2, [])
  Lr0 = lattice(V, B)

  @test (@inferred base_ring(Lr0)) isa FlintIntegerRing

  @test !(@inferred issublattice(Lr2, Lr1))
  M = Zlattice(;gram = FlintQQ[2 2; 2 2])
  @test !(@inferred issublattice(Lr0, M))
  @test issublattice(Lr2, Lr0)
  @test issublattice(Lr1, lattice(V, QQ[2 0;]))

  fl, rels = @inferred issublattice_with_relations(Lr1, lattice(V, QQ[2 0;]))
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

  # automorphisms

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
    Ge = automorphism_group_generators(L, ambient_representation = true)
    test_automorphisms(L, Ge, true)
    Ge = automorphism_group_generators(L, ambient_representation = false)
    test_automorphisms(L, Ge, false)
    @test automorphism_group_order(L) == lattice_automorphism_group_order(D, i)
  end

  # isometry

  for (m, o) in lattices_and_aut_order
    n = length(m[1])
    G = matrix(FlintZZ, n, n, reduce(vcat, m))
    L = Zlattice(gram = G)
    X = _random_invertible_matrix(n, -3:3)
    @assert abs(det(X)) == 1
    L2 = Zlattice(gram = X * G * transpose(X))
    b, T = isisometric(L, L2, ambient_representation = false)
    @test b
    @test T * gram_matrix(L2) * transpose(T) == gram_matrix(L)
    L2 = Zlattice(X, gram = G)
    b, T = isisometric(L, L2, ambient_representation = false)
    @test b
    @test T * gram_matrix(L2) * transpose(T) == gram_matrix(L)
    b, T = isisometric(L, L2, ambient_representation = true)
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
    b, T = isisometric(L, L2, ambient_representation = false)
    @test b
    @test T * gram_matrix(L2) * transpose(T) == gram_matrix(L)
  end

  #discriminant of a lattice
  L = Zlattice(ZZ[1 0; 0 1], gram = matrix(QQ, 2,2, [2, 1, 1, 2]))
  @test discriminant(L) == 3

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
  @test  basis_matrix(submod) == matrix(QQ, 1, 3, [1//2 1//2 -1])

  @test isdefinite(L)
  @test ispositive_definite(L)
  @test !isnegative_definite(L)
  @test L+L == L
  @test intersect(L,L) == L
  @test 2*L == L*2
  @test 0*L == L*0
  @test (1//2)L*2 == L
  @test !(L == 2*L)

  # local modification
  L = rescale(Hecke.root_lattice(:A,3),15)
  M = Hecke.maximal_integral_lattice(L)
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
  @test issublattice(Ld,L)
  discriminant_group(L)

  # Kernel lattice
  L = root_lattice(:A, 2)
  f = matrix(ZZ, 2, 2, [0, 1, 1, 0])
  M = kernel_lattice(L, f - 1)
  @test basis_matrix(M) == QQ[1 1;]
  M = kernel_lattice(L, f - 1, ambient_representation = false)
  @test basis_matrix(M) == QQ[1 1;]

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

  L = root_lattice(:A, 2)
  G = automorphism_group_generators(L)
  N = invariant_lattice(L, G)
  @test ambient_space(N) === ambient_space(L)
  @test rank(N) == 0
  @test basis_matrix(invariant_lattice(L, identity_matrix(QQ, 2))) == basis_matrix(L)
  
  randlist = rand(2:20,10)
  L = [root_lattice(:D,i) for i in randlist]
  @test any(l -> discriminant(l) == 4, L)
  @test any(iseven, L)
  @test any(l -> norm(l) == 2, L)

  L = root_lattice(:D,3)
  #Problem here: equality of lattices depends on 'strict' equality of their ambient
  #space, as julia object!
  @test gram_matrix(L) == gram_matrix(root_lattice(:A,3)) 
  
  L = root_lattice(:D,4)
  @test norm(L) == 2
  @test automorphism_group_order(L) == 1152

  L = root_lattice(:E,6)
  @test discriminant(L) == 3
  @test iseven(L)
  @test norm(L) == 2
  @test Hecke.kissing_number(L) == 72

  L = root_lattice(:E,7)
  @test discriminant(L) == 2
  @test iseven(L)
  @test norm(L) == 2
  @test Hecke.kissing_number(L) == 126

  L = root_lattice(:E, 8)
  @test discriminant(L) == 1
  @test iseven(L)
  @test norm(L) == 2
  @test norm(L) == 2 # tests caching

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
  x3 = [4, 5, 11, 9]
  x4 = [2, 1, 0, 1, 2]
  @test !(x1 in L)
  @test x2 in L
  @test x3 in L
  @test_throws AssertionError x4 in L
end
