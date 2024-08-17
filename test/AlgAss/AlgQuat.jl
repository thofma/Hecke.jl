@testset "Quaternion algebras" begin
  M = Array{QQFieldElem, 3}(undef, 4, 4, 4)
  M[:, :, 1] = [-2 4 -2 0; 0 0 -1 -3; 1 1 0 3; -3 3 -3 0]
  M[:, :, 2] = [ -4 0 -1 -3; 2 0 2 0; -3 2 -5//2 -3//2; -3 0 -3//2 -9//2]
  M[:, :, 3] = [-4 0 -2 -6; 4 -4 5 3; -4 4 -7//2 -9//2; 0 0 -3//2 -9//2]
  M[:, :, 4] = [4//3 -8//3 8//3 0; 4//3 4//3 -1//3 3; -4//3 -4//3 5//6 -3//2; 0 0 3//2 -3//2]
  A = StructureConstantAlgebra(QQ, M)
  B, f = Hecke.is_quaternion_algebra(A)
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
end
