@testset "Quaternion algebras" begin

  let
    Q = quaternion_algebra(QQ, -1, -1)
    @test Q isa Hecke.QuaternionAlgebra
    Q = quaternion_algebra(QQ, QQ(-1), -1)
    @test Q isa Hecke.QuaternionAlgebra
  end

  M = Array{QQFieldElem, 3}(undef, 4, 4, 4)
  M[:, :, 1] = [-2 4 -2 0; 0 0 -1 -3; 1 1 0 3; -3 3 -3 0]
  M[:, :, 2] = [ -4 0 -1 -3; 2 0 2 0; -3 2 -5//2 -3//2; -3 0 -3//2 -9//2]
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
    fl, b = Hecke._is_principal_maximal_quaternion_generic_proper(I, O)
    @assert fl
    @test b * O == I

    K, a = quadratic_field(5)
    A = Hecke.quaternion_algebra(K, -1, -1)
    O = maximal_order(A)
    I = basis(A)[2] * O
    fl, b = Hecke._is_principal_maximal_quaternion_generic_proper(I, O)
    @assert fl
    @test b * O == I
  end

  let
    # from Swan '62
    Qx, x = QQ["x"]
    K, tau = number_field(x^4 - 4*x^2 + 2)
    M = Array{elem_type(K), 3}(undef, 4, 4, 4)
    M[:, :, 1] = K.([1 0 0 0; 0 -1 0 0; 0 0 -1 -tau; 0 0 0 -1])
    M[:, :, 2] = K.([0 1 0 0; 1 tau 0 0; 0 0 0 1; 0 0 -1 0])
    M[:, :, 3] = K.([0 0 1 0; 0 0 0 -1; 1 tau 0 0; 0 1 0 0])
    M[:, :, 4] = K.([0 0 0 1; 0 0 1 tau; 0 -1 0 0; 1 0 0 0])
    sqrt2 = sqrt(K(2))
    B = associative_algebra(K, M)
    zeta = basis(B)[2]
    j = basis(B)[3]
    i = tau^2 - 1 + (-tau^3 + 2*tau)*zeta
    alpha = inv(sqrt2 * tau) * (sqrt2 + 1 + i)
    beta = tau/sqrt2 * (1 + j)
    gamma = alpha * beta
    Gamma = Hecke._get_order_from_gens(B, [one(B), alpha, beta, alpha*beta])
    @test is_maximal(Gamma)
    P = Gamma * B(tau) + Gamma * beta
    @test left_order(P) == Gamma
    @test Gamma * P == P
    @test P * Gamma != P
    # we can only test right ideals so far ...
    BOp, BtoBOp = opposite_algebra(B)
    GammaOp = Hecke._get_order_from_gens(BOp, [BtoBOp(elem_in_algebra(x)) for x in absolute_basis(Gamma)])
    POp = +([BtoBOp(x) * GammaOp for x in absolute_basis(P)]...)
    fl, _ = Hecke._is_principal_maximal_quaternion_generic_proper(POp, GammaOp)
    @test !fl
  end

  # make sure to forbid characteristic 2
  let
    K = GF(2)
    @test_throws ArgumentError Hecke.QuaternionAlgebra(K, K(1), K(1))
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
    for (a, b) in [(-1, -1), (2, 1), (1, 2), (2*ii, ii)]
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
    @test normred(z) == x[1]^2 - x[2]^2*a - x[3]^2*b + x[4]^2*a*b
    @test trred(z) == 2*x[1]
    @test conjugate(z) == x[1] - x[2]*i - x[3]*j - x[4]*k
    m = reduced_charpoly(z)
    @test m(z) == 0 && degree(m) == 2
  end
end
