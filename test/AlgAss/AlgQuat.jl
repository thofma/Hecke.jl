@testset "Quaternion algebras" begin

  let
    Q = quaternion_algebra(QQ, -1, -1)
    @test Q isa Hecke.QuaternionAlgebra
    Q = quaternion_algebra(QQ, QQ(-1), -1)
    @test Q isa Hecke.QuaternionAlgebra
  end

  M = Array{QQFieldElem,3}(undef, 4, 4, 4)
  M[:, :, 1] = [-2 4 -2 0; 0 0 -1 -3; 1 1 0 3; -3 3 -3 0]
  M[:, :, 2] = [-4 0 -1 -3; 2 0 2 0; -3 2 -5//2 -3//2; -3 0 -3//2 -9//2]
  M[:, :, 3] = [-4 0 -2 -6; 4 -4 5 3; -4 4 -7//2 -9//2; 0 0 -3//2 -9//2]
  M[:, :, 4] = [4//3 -8//3 8//3 0; 4//3 4//3 -1//3 3; -4//3 -4//3 5//6 -3//2; 0 0 3//2 -3//2]
  A = StructureConstantAlgebra(QQ, M)
  fl, f = Hecke._is_quaternion_algebra(A)
  @assert fl
  B = domain(f)
  for b in basis(B)
    for bb in basis(B)
      @test f(b) * f(bb) == f(b * bb)
    end
  end

  let
    K, a = quadratic_field(5)
    A = Hecke.quaternion_algebra2(K, K(-1), K(-1))
    O = maximal_order(A)
    I = basis(A)[2] * O
    fl, b = Hecke._is_principal_with_data_definite_quaternion(I, O, :right)
    @assert fl
    @test b * O == I

    K, a = quadratic_field(5)
    A = Hecke.quaternion_algebra(K, -1, -1)
    O = maximal_order(A)
    I = basis(A)[2] * O
    fl, b = Hecke._is_principal_with_data_definite_quaternion(I, O, :right)
    @assert fl
    @test b * O == I
  end

  let
    # from Swan '62
    Qx, x = QQ["x"]
    K, tau = number_field(x^4 - 4 * x^2 + 2)
    M = Array{elem_type(K),3}(undef, 4, 4, 4)
    M[:, :, 1] = K.([1 0 0 0; 0 -1 0 0; 0 0 -1 -tau; 0 0 0 -1])
    M[:, :, 2] = K.([0 1 0 0; 1 tau 0 0; 0 0 0 1; 0 0 -1 0])
    M[:, :, 3] = K.([0 0 1 0; 0 0 0 -1; 1 tau 0 0; 0 1 0 0])
    M[:, :, 4] = K.([0 0 0 1; 0 0 1 tau; 0 -1 0 0; 1 0 0 0])
    sqrt2 = sqrt(K(2))
    B = associative_algebra(K, M)
    zeta = basis(B)[2]
    j = basis(B)[3]
    i = tau^2 - 1 + (-tau^3 + 2 * tau) * zeta
    alpha = inv(sqrt2 * tau) * (sqrt2 + 1 + i)
    beta = tau / sqrt2 * (1 + j)
    gamma = alpha * beta
    Gamma = Hecke._get_order_from_gens(B, [one(B), alpha, beta, alpha * beta])
    @test is_maximal(Gamma)
    P = Gamma * B(tau) + Gamma * beta
    @test left_order(P) == Gamma
    @test Gamma * P == P
    @test P * Gamma != P
    # P is a left ideal of Gamma that is not principal, tested directly and
    # through its image, a right ideal, in the opposite algebra
    fl, _ = Hecke._is_principal_with_data_definite_quaternion(P, Gamma, :left)
    @test !fl
    BOp, BtoBOp = opposite_algebra(B)
    GammaOp = Hecke._get_order_from_gens(BOp, [BtoBOp(elem_in_algebra(x)) for x in absolute_basis(Gamma)])
    POp = +([BtoBOp(x) * GammaOp for x in absolute_basis(P)]...)
    fl, _ = Hecke._is_principal_with_data_definite_quaternion(POp, GammaOp,
                                                              :right)
    @test !fl
  end

  # finding zero-divisors
  let
    Q = Hecke.QuaternionAlgebra(QQ, QQ(3), QQ(2))
    fl, _ = Hecke.is_split_with_zero_divisor(Q)
    @test !fl
    for (a, b) in [(1, 1), (2, 1), (1, 2), (-2, 2), (-4, 4)]
      Q = Hecke.QuaternionAlgebra(QQ, QQ(a), QQ(b))
      fl, alpha = Hecke.is_split_with_zero_divisor(Q)
      @test fl
      @test !is_zero(alpha)
      @test norm(alpha) == 0
    end
  end

  let
    K, = rationals_as_number_field()
    Q = Hecke.QuaternionAlgebra(K, K(3), K(2))
    fl, _ = Hecke.is_split_with_zero_divisor(Q)
    @test !fl
    for (a, b) in [(1, 1), (2, 1), (1, 2), (-2, 2), (-4, 4)]
      Q = Hecke.QuaternionAlgebra(K, K(a), K(b))
      fl, alpha = Hecke.is_split_with_zero_divisor(Q)
      @test fl
      @test !is_zero(alpha)
      @test norm(alpha) == 0
    end
  end

  let
    K, ii = quadratic_field(-1)
    Q = Hecke.QuaternionAlgebra(K, K(-1), K(-1))
    for (a, b) in [(-1, -1), (2, 1), (1, 2), (2 * ii, ii)]
      Q = Hecke.QuaternionAlgebra(K, K(a), K(b))
      fl, alpha = Hecke.is_split_with_zero_divisor(Q)
      @test fl
      @test !is_zero(alpha)
      @test norm(alpha) == 0
    end
  end

  let
    K, x, (a, b) = rational_function_field(QQ, :x => 1:4, [:a, :b])
    A = quaternion_algebra(K, a, b)
    z = A(x)
    _, i, j, k = basis(A)
    @test normred(z) == x[1]^2 - x[2]^2 * a - x[3]^2 * b + x[4]^2 * a * b
    @test trred(z) == 2 * x[1]
    @test conjugate(z) == x[1] - x[2] * i - x[3] * j - x[4] * k
    m = reduced_charpoly(z)
    @test m(z) == 0 && degree(m) == 2
  end

  let
    R, t = polynomial_ring(GF(2), "t")
    K = fraction_field(R)
    tt = K(t)
    A = quaternion_algebra(K, tt, tt + 1)
    z = A([1, tt, tt^2 + 1, tt^3 + tt + 1])
    @test normred(z) == coefficients(z * conjugate(z), copy = false)[1]
    @test trred(z) == coefficients(z + conjugate(z), copy = false)[1]
  end

  let
    # opposite algebra
    for K in [QQ, quadratic_field(2)[1], GF(3), rational_function_field(GF(3), :x)[1]]
      A = quaternion_algebra(K, K(-1), K(-2))
      B, BtoA = opposite_algebra(A)
      B, BtoA = opposite_algebra(A) # twice to check caching does not fail
      for b in basis(B)
        for bb in basis(B)
          @test BtoA(b + bb) == BtoA(b) + BtoA(bb)
          @test BtoA(b * bb) == BtoA(bb) * BtoA(b)
        end
        @test b == preimage(BtoA, BtoA(b))
      end
    end
  end

  let
    # center
    for K in [QQ, quadratic_field(2)[1], GF(3), rational_function_field(GF(3), :x)[1]]
      A = quaternion_algebra(K, K(-1), K(-2))
      C, CtoA = center(A)
      C, CtoA = center(A) # twice to check that caching does not fail
      @test dim(C) == 1 && domain(CtoA) === C && codomain(CtoA) === A
    end
  end

  let
    # decomposition
    for K in [QQ, quadratic_field(2)[1], GF(3), rational_function_field(GF(3), :x)[1]]
      A = quaternion_algebra(K, K(-1), K(-2))
      dec = decompose(A)
      dec = decompose(A)
      @test length(dec) == 1 && dim(dec[1][1]) == 4
    end
  end

  let # StructureConstantAlgebra conversion
    for K in [QQ, quadratic_field(2)[1], GF(3), rational_function_field(GF(3), :x)[1]]
      A = quaternion_algebra(K, K(-1), K(-2))
      B, BtoA = StructureConstantAlgebra(A)
      @test B isa StructureConstantAlgebra && domain(BtoA) === B && codomain(BtoA) === A
    end
  end

  let # unit group
    data = ([-6, 0, 1], [-1, 0], [-1, 0], Vector{Vector{Rational{Int64}}}[[[1, 0], [0, 0], [0, 0], [0, 0]], [[0, 1], [0, 0], [0, 0], [0, 0]], [[0, 0], [1, 0], [0, 0], [0, 0]], [[0, 0], [0, 1], [0, 0], [0, 0]], [[0, 1//2], [1//2, 0], [1//2, 0], [0, 0]], [[3, 0], [0, 1//2], [0, 1//2], [0, 0]], [[1//2, 0], [0, 1//2], [0, 0], [1//2, 0]], [[0, 1//2], [3, 0], [0, 0], [0, 1//2]]])
    Qx, x = QQ[:x]
    K, = number_field(Qx(data[1]))
    aa = K(data[2]); bb = K(data[3]); B = [([K(x) for x in y]) for y in data[4]]; A = quaternion_algebra(K, aa, bb)
    O = order(A, sub(pseudo_hnf(pseudo_matrix(matrix(B)), :lowerleft), length(data[4])-3:length(data[4]), 1:4));
    ugens = Hecke.unit_group_modulo_scalars(O)
    @test length(ugens) == 8 && allunique(ugens) && all(is_unit, ugens)
  end

  let # quaternion_algebra_ramified_at
    # Ibukiyama's conditions on q, Nagoya Math. J. 88 (1982), p. 181
    admissible(p, q) =
      is_prime(q) && mod(q, 8) == 3 && kronecker_symbol(ZZ(p), ZZ(q)) == -1
    # 2, 3 and every class modulo 8
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 73, 89, 97, 241,
              257, 647, 1811]
      A = quaternion_algebra_ramified_at(QQ, p)
      a, b = Hecke.standard_form(A)
      q = -ZZ(b)
      @test a == -p
      @test admissible(p, q) && !any(s -> admissible(p, s), 2:(q - 1))
      # the ramification, of the same (a, b) built by quaternion_algebra,
      # which carries no maximal order
      B = quaternion_algebra(QQ, a, b)
      @test Hecke.local_schur_indices(B) == [ZZ(0) => 2, ZZ(p) => 2]
      # the order carried is maximal: rebuilt with the closure check, its
      # discriminant is p^2 (Voight, Quaternion algebras, Thm. 15.5.5)
      O = maximal_order(A)
      @test O === maximal_order(A)
      bO = [elem_in_algebra(x) for x in basis(O)]
      @test abs(discriminant(order(A, bO; isbasis = true, check = true))) ==
            ZZ(p)^2
      # and it is Ibukiyama's O(q, r), p. 182
      e, i, j, _ = basis(A)
      r = only(filter(r -> mod(r^2 + p, q) == 0, 1:div(q, 2)))
      @test bO == [e, QQ(1, 2) * (e + j), QQ(1, 2) * (i * (e + j)),
                   QQ(1, q) * ((r * e + i) * j)]
    end
    @test Hecke.standard_form(quaternion_algebra_ramified_at(QQ, 97)) ==
          (-97, -19)
    @test Hecke.standard_form(quaternion_algebra_ramified_at(QQ, ZZ(647))) ==
          (-647, -3)
    @test_throws ArgumentError quaternion_algebra_ramified_at(QQ, 91)
    @test_throws ArgumentError quaternion_algebra_ramified_at(QQ, 1)
    @test_throws ArgumentError quaternion_algebra_ramified_at(QQ, -5)
    A = quaternion_algebra_ramified_at(QQ, 97; check = false)
    @test Hecke.standard_form(A) == (-97, -19)
  end
end
