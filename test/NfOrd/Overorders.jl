@testset "Overorders" begin
  Qx,  x = QQ["x"]

  f = x^2 + 100x + 100

  A = StructureConstantAlgebra(f * (f - 1))
  O = order(A, basis(A))

  orders = @inferred poverorders(O, 2)
  @test length(orders) == 6

  orders = @inferred poverorders(O, ZZRingElem(5))
  @test length(orders) == 2

  orders = @inferred poverorders(O, ZZRingElem(7))
  @test length(orders) == 3

  orders = @inferred overorders(O)
  @test length(orders) == 36

  @test count(is_gorenstein, orders) == 36
  @test count(is_bass, orders) == 36
  @test count(is_maximal, orders) == 1

  orders = @inferred overorders(O, type = :bass)
  @test length(orders) == 36

  orders = @inferred overorders(O, type = :gorenstein)
  @test length(orders) == 36

  G = small_group(6, 1)
  A = StructureConstantAlgebra(group_algebra(QQ, G))[1]
  O = order(A, basis(A))
  orders = @inferred overorders(O)
  @test length(orders) == 12

  orders = @inferred overorders(O, type = :all)
  @test length(orders) == 12

  @test count(is_maximal, orders) == 2

  @test_throws ErrorException overorders(O, type =  :gorenstein)
  @test_throws ErrorException overorders(O, type =  :bass)
  @test_throws ErrorException overorders(O, type =  :blub)

  f = x^4-1680*x^3-25920*x^2-1175040*x+25214976
  O = equation_order(f)
  orders = @inferred overorders(O)
  @test length(orders) == 2535
  @test count(is_maximal, orders) == 1
  @test count(is_gorenstein, orders) == 657
  @test count(is_bass, orders) == 5

  @test length(overorders(O, type = :gorenstein)) == 657
  @test length(overorders(O, type = :bass)) == 5

  f = x^4-1680*x^3-25920*x^2-1175040*x+25214976
  A = StructureConstantAlgebra(f)
  O = order(A, basis(A))
  @test length(overorders(O)) == 2535

  let # issue reported by M. Kirschmer
    P, x = polynomial_ring(QQ)
    K, a  = number_field(x^6 - x^5 - x^4 + 2*x^3 - x + 1)
    R = ring_of_integers(K)
    P = prime_ideals_over(R, 5)
    OO = order(K, basis(P[1]*P[2]^2))
    X = overorders(OO);
    S = Set([ basis_matrix(x) for x in X ]);
    @test length(S) == length(X) == 29
  end

  @testset "intersect" begin
    # x and y of full rank: covol(x cap y) covol(x + y) = covol(x) covol(y),
    # x + y from a Hermite form, independently of intersect
    function covolume(M::QQMatrix)
      N, g = integral_split(M, ZZ)
      H = hnf(N)
      return abs(det(H[1:ncols(M), :])) // g^ncols(M)
    end
    function test_intersect(x, y, elem)
      z = @inferred intersect(x, y)
      X = basis_matrix(x)
      Y = basis_matrix(y)
      @test covolume(basis_matrix(z)) * covolume(vcat(X, Y)) ==
            covolume(X) * covolume(Y)
      @test all(b -> elem(b) in x && elem(b) in y, basis(z))
      @test intersect(y, x) == z
    end

    K, a = quadratic_field(-3)
    O2 = order(K, [one(K), 2a])
    O3 = order(K, [one(K), 3a])
    @test intersect(O2, O3) == order(K, [one(K), 6a])
    @test intersect(O2, maximal_order(K)) == O2
    test_intersect(O2, O3, elem_in_nf)

    Qx, x = QQ["x"]
    K, a = number_field(x^3 - 2)
    O = maximal_order(K)
    for (u, v) in [(2a, 3a^2), (a + 1, 5a), (7a, a^2 + a)]
      test_intersect(order(K, [one(K), u, u^2]), order(K, [one(K), v, v^2]),
                     elem_in_nf)
    end

    A = quaternion_algebra(QQ, -1, -1)
    i, j, k = basis(A)[2:4]
    M = maximal_order(A)
    L = order(A, basis(A))
    @test intersect(L, M) == L
    test_intersect(L, M, elem_in_algebra)
    u = 1 + 2i
    N = order(A, [u * elem_in_algebra(b) * inv(u) for b in basis(M)])
    test_intersect(M, N, elem_in_algebra)
  end
end
