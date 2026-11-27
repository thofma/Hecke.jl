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

  # zero maps preserve endpoints and dimensions, and require compatible modules
  let
    for K in (QQ, GF(3)), (m, n) in ((0, 0), (0, 2), (2, 0), (2, 3))
      V = Amodule([zero_matrix(K, m, m)])
      W = Amodule([identity_matrix(K, n)])
      h = zero_map(V, W)
      @test domain(h) === V && codomain(h) === W
      @test matrix(h) == zero_matrix(K, m, n)
      if m != n
        fl, h = is_isomorphic_with_isomorphism(V, W)
        @test !fl
        @test domain(h) === V && codomain(h) === W
        @test matrix(h) == zero_matrix(K, m, n)
      end
    end

    for n in (0, 1)
      V = Amodule([zero_matrix(GF(3), n, n)])
      W = Amodule([zero_matrix(GF(5), n, n)])
      U = Amodule([zero_matrix(GF(3), n, n) for _ in 1:2])
      @test_throws ArgumentError zero_map(V, W)
      @test_throws AssertionError zero_map(V, U)
    end
  end

  # separately constructed zero-dimensional modules have a unique isomorphism
  let
    for K in (QQ, GF(3))
      A = group_algebra(K, abelian_group([2]))
      for (V, W) in ((Amodule([zero_matrix(K, 0, 0)]),
                     Amodule([zero_matrix(K, 0, 0)])),
                    (Amodule(A, [zero_matrix(K, 0, 0) for _ in 1:dim(A)]),
                     Amodule(A, [zero_matrix(K, 0, 0) for _ in 1:dim(A)])))
        fl, h = is_isomorphic_with_isomorphism(V, W)
        @test fl
        @test domain(h) === V && codomain(h) === W
        @test matrix(h) == zero_matrix(K, 0, 0)
        @test is_invertible(matrix(h))
      end
    end

    V = Amodule([zero_matrix(GF(3), 0, 0)])
    W = Amodule([zero_matrix(GF(5), 0, 0)])
    U = Amodule([zero_matrix(GF(3), 0, 0) for _ in 1:2])
    @test_throws ArgumentError is_isomorphic_with_isomorphism(V, W)
    @test_throws AssertionError is_isomorphic_with_isomorphism(V, U)
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

  # isomorphism test over GF(2) where dim Hom(V, W) = dim End(V)
  let
    F = GF(2)
    V = Amodule([matrix(F, [0 0; 0 1]), matrix(F, [1 0; 0 1])])
    W = Amodule([matrix(F, [0 0; 0 0]), matrix(F, [1 0; 0 1])])
    @test !is_isomorphic_with_isomorphism(V, W)[1]
    V = Amodule([matrix(F, [1 1; 0 0]), matrix(F, [1 1; 0 1])])
    W = Amodule([matrix(F, [1 1; 0 0]), matrix(F, [1 0; 0 1])])
    @test !is_isomorphic_with_isomorphism(V, W)[1]

    # V is the sum of k pairwise non-isomorphic simple modules, so a random
    # element of Hom(V, W) is invertible with probability 2^-k.
    k = 16
    gens = [diagonal_matrix(F, [F((i >> j) & 1) for i in 0:(k - 1)])
            for j in 0:3]
    T = matrix(F, k, k, [i <= j ? 1 : 0 for i in 1:k for j in 1:k])
    V = Amodule(gens)
    W = Amodule([T * m * inv(T) for m in gens])
    fl, h = is_isomorphic_with_isomorphism(V, W)
    @test fl
    @test is_invertible(matrix(h))
    @test all(m * matrix(h) == matrix(h) * T * m * inv(T) for m in gens)
  end
end

