@testset "ModAlgAss" begin
  K1, a = cyclotomic_field(7, "a") # C6
  Qx, x = QQ["x"]
  K2, = number_field(x^8 + 12*x^6 + 36*x^4 + 36*x^2 + 9, "a") # Q8
  for K in [K1, K2]
    G, mG = automorphism_group(K)
    V, f = galois_module(K, mG)
    QG = algebra(V)
    for i in 1:10
      b = rand(K, -1:1)
      c = rand(K, -1:1)
      o = rand(QQ, -10:10)
      @test f(o * b + c) == o * f(b) + f(c)
      @test preimage(f, f(b)) == b
      g = G[rand(1:order(G))]
      @test f(mG(g)(b)) == f(b) * QG(g)
    end
  end

  # hashing
  let
    K, a = cyclotomic_field(7, "a")
    G, mG = automorphism_group(K)
    V, f = galois_module(K, mG)
    x = V([1, 2, 3, 4, 5, 6])
    y = V([1, 2, 3, 4, 5, 6])
    z = V([1, 2, 3, 4, 5, 7])
    @test x == y
    @test x != z
    @test hash(x) == hash(y)
  end

  # module over an algebra given only by the action of generators
  let
    QG = group_algebra(QQ, abelian_group([2]))
    ms = [matrix(QQ, [0 1; 1 0])]
    V = Hecke.ModAlgAss{QQMatrix, typeof(QG)}(QG; action_of_gens = ms)
    @test dim(V) == 2
    @test Hecke.action_of_gens(V) == ms
  end

  # modules without nonzero homomorphisms are not isomorphic
  let
    V = Amodule([matrix(QQ, 1, 1, [1])])
    W = Amodule([matrix(QQ, 1, 1, [-1])])
    fl, h = is_isomorphic_with_isomorphism(V, W)
    @test !fl
    @test domain(h) === V && codomain(h) === W
    @test matrix(h) == zero_matrix(QQ, 1, 1)
  end

  # isomorphism test for modules with nonzero homomorphisms
  let
    V = Amodule([diagonal_matrix(QQ, [1, 1])])
    W = Amodule([diagonal_matrix(QQ, [1, -1])])
    U = Amodule([diagonal_matrix(QQ, [1, 1, -1])])
    @test !is_isomorphic_with_isomorphism(V, W)[1]
    @test !is_isomorphic_with_isomorphism(W, V)[1]
    fl, h = is_isomorphic_with_isomorphism(V, U)
    @test !fl
    @test matrix(h) == zero_matrix(QQ, 2, 3)
    @test !is_isomorphic_with_isomorphism(U, V)[1]

    T = matrix(QQ, [1 2; 1 3])
    for (K, m) in [(QQ, [0 1; 0 0]), (QQ, [1 0; 0 -1]), (GF(2), [1 1; 0 1])]
      M = matrix(K, m)
      V = Amodule([M])
      W = Amodule([change_base_ring(K, T) * M * inv(change_base_ring(K, T))])
      fl, h = is_isomorphic_with_isomorphism(V, W)
      @test fl
      @test is_invertible(matrix(h))
      @test M * matrix(h) == matrix(h) * Hecke.action_of_gens(W)[1]
      @test !is_isomorphic_with_isomorphism(V, Amodule([one(M)]))[1]
    end
  end
end

