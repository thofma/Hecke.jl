function _test_morphism(f)
  R = domain(f)
  @test is_one(f(one(R)))
  @test is_zero(f(zero(R)))
  for i in 1:10
    x = rand(R)
    y = rand(R)
    @test f(x + y) == f(x) + f(y)
    @test f(x * y) == f(x) * f(y)
  end
  if f isa Hecke.FiniteRings.FiniteRingHom
    if isdefined(f, :g)
      S = codomain(f)
      for i in 1:10
        x = rand(S)
        y = rand(S)
        @test f\(x + y) == (f\x) + (f\y)
        @test f\(x * y) == (f\x) * (f\y)
      end
    end
  end
end

@testset "Rings" begin
  R = finite_ring([1], [zero_matrix(ZZ, 1, 1)])

  @test number_of_additive_generators(R) == 1
  @test length(additive_generators(R)) == number_of_additive_generators(R)
  @test Hecke.is_known(is_finite, R)
  @test elementary_divisors(R) == []
  @test order(R) == 1
  @test characteristic(R) == 1
  @test is_finite(R) == 1
  @test is_zero(R)
  @test is_commutative(R)
  @test sprint(show, R) isa String
  @test sprint(show, "text/plain", R) isa String

  S, = finite_ring(matrix_algebra(GF(3), 2))
  @test elementary_divisors(S) == [3, 3, 3, 3]
  @test order(S) == 3^4
  @test characteristic(S) == 3
  @test is_finite(S)
  @test !is_zero(S)
  @test !is_commutative(S)
  @test sprint(show, S) isa String
  @test sprint(show, "text/plain", S) isa String

  let
    mats = [[1 0 0 0; 0 0 0 0; 0 0 1 0; 0 0 0 0], [0 1 0 0; 0 0 0 0; 0 0 0 1; 0 0 0 0], [0 0 0 0; 1 0 0 0; 0 0 0 0; 0 0 1 0], [0 0 0 0; 0 1 0 0; 0 0 0 0; 0 0 0 1]]
    mult = Array{Int}(undef, 4, 4, 4)
    for i in 1:4
      mult[i, :, :] = mats[i]
    end
    R = finite_ring([2, 2, 2, 2], mult)
    b = additive_generators(R)
    for i in 1:4, j in 1:4, k in 1:4
      @test b[i] * b[j] == sum(mult[i, j, k] * b[k] for k in 1:4)
    end
  end

  # a non-ring
  @test_throws ArgumentError finite_ring([2, 2], [zero_matrix(ZZ, 1, 1)])
  @test_throws ArgumentError finite_ring([2, 2], [zero_matrix(ZZ, 2, 2)])
  @test_throws ArgumentError finite_ring([2, 2], [zero_matrix(ZZ, 1, 1), identity_matrix(ZZ, 2)])

  # more constructions
  Q = quaternion_algebra(GF(3), -1, -1)
  R, = finite_ring(Q)
  @test elementary_divisors(R) == [3, 3, 3, 3]

  Q = group_algebra(GF(2), abelian_group([2, 2]))
  R, = finite_ring(Q)
  Hecke.FiniteRings._rgens(R)
  Hecke.FiniteRings._rgens(R)
  @test order(R) == 2^4
  R, = finite_ring(matrix_ring(R, 2))
  @test order(R) == 2^16

  R, = finite_ring(matrix_algebra(GF(3), 2))
  S, = finite_ring(matrix_ring(R, 1))

  ZG = integral_group_ring(QQ[abelian_group([2, 2])])
  Q, = quo(ZG, 2 * ZG)
  R, = finite_ring(Q)
  @test order(R) == 2^4
  # todo: proper test for ring generators
  Hecke.FiniteRings._rgens(R)
  Hecke.FiniteRings._rgens(R)

  let
    # maximal_p_quotient_ring
    ZG = integral_group_ring(QQ[abelian_group([2, 2])])
    Q, = quo(ZG, 12 * ZG)
    R, = finite_ring(Q)
    S, StoR = maximal_p_quotient_ring(R, 2)
    @test order(S) == 4^4
    _test_morphism(StoR)

    # decomposition
    Rs, ps = decompose_into_p_rings(R)
    for p in ps
      _test_morphism(p)
    end
    @test prod(order.(Rs)) == order(R)
    @test all(Hecke.is_prime_power, order.(Rs))
  end

  let
    # decomposition of semisimple p rings
    ZG = integral_group_ring(QQ[abelian_group([2, 2])])
    Q, = quo(ZG, 3 * ZG)
    R, = finite_ring(Q)

    Rs, ps = decompose_into_p_rings(R)
    for p in ps
      _test_morphism(p)
    end
    @test prod(order.(Rs)) == order(R)
    @test all(Hecke.is_prime_power, order.(Rs))

    Rs, ps = Hecke.FiniteRings.decompose_semisimple_p_ring(R)
    for p in ps
      _test_morphism(p)
    end
    @test prod(order.(Rs)) == order(R)
    @test all(==(3), order.(Rs))

    Z, ZtoR = center(R)
    _test_morphism(ZtoR)
    @test order(Z) == order(R)
  end

  let
    # decomposition of semisimple p rings
    ZG = integral_group_ring(QQ[small_group(8, 3)])
    Q, = quo(ZG, 9 * 25 * ZG)
    R, = finite_ring(Q)
    @test !is_commutative(R)

    Z, ZtoR = center(R)
    _test_morphism(ZtoR)
    @test order(Z) == ZZ(9*25)^5
    @test is_commutative(Z)

    Rs, ps = decompose_into_indecomposable_rings(R)
    @test !is_indecomposable(R)
  end

  let
    R = GF(7)[small_group(8, 3)]
    Rs, ps = decompose_into_indecomposable_rings(R)
  end

  let
    R, _ = finite_ring(matrix_algebra(GF(2), 2));
    @test is_indecomposable(R)
    @test length(central_primitive_idempotents(R)) == 1
  end
end
