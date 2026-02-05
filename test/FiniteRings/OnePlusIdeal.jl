@testset "FiniteRings/OnePlusIdeal" begin
  ZG = integral_group_ring(QQ[small_group(1, 1)])
  R, = finite_ring(quo(ZG, 9 * ZG)[1])
  _I = ideal(R, [R(3)]; side = :twosided)

  A = group_algebra(GF(2), small_group(2, 1))
  _J = radical(A)

  for I in (_I, _J)
    OpI = Hecke.FiniteRings.OnePlusIdeal(I)
    @test ideal(OpI) === I
    @test base_ring(OpI) === base_ring(I)
    @test sprint(show, OpI) isa String

    x = one(OpI)
    @test sprint(show, x) isa String
    @test parent(x) === OpI
    @test is_one(x)
    @test x == one(x)
    z = rand(OpI)
    @test z == x * z == z * x
    zz = inv(z)
    @test zz * z == zz * z == x
    @test z^2 == z * z
    @test z^1 == z
    @test z^0 == x

    II = I*I
    OpII = Hecke.FiniteRings.OnePlusIdeal(II)
    Q, RtoQ = quo(OpI, OpII)
    u, v = rand(OpI), rand(OpI)
    @test RtoQ(u * v) == RtoQ(u) * RtoQ(v)
    uu = RtoQ(u)
    @test sprint(show, uu) isa String
    @test sprint(show, Q) isa String
    @test preimage(RtoQ, RtoQ(u)) == u

    u = rand(Q)
    @test RtoQ(preimage(RtoQ, u)) == u
  end
end

