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

@testset "Lattices" begin
  # Smoke test for genus symbol
  Qx, x = PolynomialRing(FlintQQ, "x")
  K, a = NumberField(x^2 - 2, "a")
  L = quadratic_lattice(K, identity_matrix(K, 10), gram_ambient_space = 35*identity_matrix(K, 10))
  P = prime_decomposition(maximal_order(K), 5)[1][1]
  @test Hecke._genus_symbol_kirschmer(L, P).data == [(10, 1, 1)]

  P = prime_decomposition(maximal_order(K), 2)[1][1]
  GS = Hecke._genus_symbol_kirschmer(L, P)
  @test GS.data[1] == [10]
  @test GS.data[2] == [0]
  @test GS.data[3] == [2]
  @test GS.data[4] == [35]
  @test GS.data[5] == []

  Qx, x = FlintQQ["x"];
  K, a = number_field(x^2 - 2, cached = true);
  Kt, t = K["t"];
  L, b= number_field(t^2 + 11, "b", check = true)
  p = prime_decomposition(maximal_order(K), 2)[1][1]
  P = prime_decomposition(maximal_order(L), p)[1][1]
  H = Hecke.lattice(hermitian_space(K, 2 * identity_matrix(K, 3)), pseudo_matrix(identity_matrix(K, 3), [p, p, p]))
  @test Hecke._genus_symbol_kirschmer(H, fmpz(2)) == Any[(3, 4, true, 4, -64)]
  @test islocally_isometric(H, H, fmpz(2))

  H = Hecke.lattice(hermitian_space(L, L(elem_in_nf(uniformizer(p))) * identity_matrix(L, 3)), pseudo_matrix(identity_matrix(L, 3), [P, P, P]))
  @test Hecke._genus_symbol_kirschmer(H, p) == Any[(3, 3, false)]
  @test islocally_isometric(H, H, p)
  @test Hecke.genus(H, p) == genus(HermLat, L, p, [(3, 3, -1)])

  V = hermitian_space(L, L(a) * identity_matrix(L, 3))
  M = Hecke.maximal_integral_lattice(V)
  @test Hecke.genus(M, p) == genus(HermLat, L, p, [(0, 2, 1), (1, 1, -1)])
  q = prime_decomposition(maximal_order(K), 11)[1][1]
  @test Hecke.genus(M, q) == genus(HermLat, L, q, [(-1, 2, 1), (0, 1, 1)])

  L, _ = number_field(t^2 - gen(K) * t + 1)
  V = hermitian_space(L, L(a) * identity_matrix(L, 3))
  M = Hecke.maximal_integral_lattice(V)
  @test Hecke.genus(M, p) == genus(HermLat, L, p, [(-2, 2, 1, 0), (0, 1, -1, 0)])
  
  V = hermitian_space(L, L(10) * identity_matrix(L, 3))
  M = Hecke.maximal_integral_lattice(V)
  @test Hecke.genus(M, p) == genus(HermLat, L, p, [(-2, 2, 1, 0), (0, 1, 1, 0)])


   Qx, x = QQ["x"]
   f = x^3-39*x-65
   K, a = MaximalRealSubfield(8, "a")
   Kt, t = K["t"]
   E, b = number_field(t^2 - a * t + 1, "b")
   p = prime_decomposition(maximal_order(K), 2)[1][1]
   P = prime_decomposition(maximal_order(E), p)[1][1]
   pm = pseudo_matrix(matrix(E, 3, 3, [1, 0, 0, b, 1, 0, 0, 0, 1]), [P^0, inv(P)^2, P^0])
   V = hermitian_space(E, identity_matrix(E, 3))
   L = lattice(V, pm)
   o = Hecke.automorphism_group_order(L)
   @test o == 1536
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
end
