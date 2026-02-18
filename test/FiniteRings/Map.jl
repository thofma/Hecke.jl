@testset "FiniteRings/Map" begin
  let
    mats = [[1 0 0 0; 0 0 0 0; 0 0 1 0; 0 0 0 0], [0 1 0 0; 0 0 0 0; 0 0 0 1; 0 0 0 0], [0 0 0 0; 1 0 0 0; 0 0 0 0; 0 0 1 0], [0 0 0 0; 0 1 0 0; 0 0 0 0; 0 0 0 1]]
    R = finite_ring([2, 2, 2, 2], matrix.(Ref(ZZ), mats)) # M_2(F_2)
    e11, e21, e12, e22 = Hecke.FiniteRings._zgens(R)
    h = hom(R, R, [R([1, 0, 1, 0]), R([1, 1, 1, 1]), R([0, 0, 1, 0]), R([0, 0, 1, 1])])
    # conjugation with [1 1; 0 1]
    for i in 1:10
      x, y = rand(R), rand(R)
      @test h(x * y) == h(x) * h(y)
      @test preimage(h, h(x)) == x
      @test h\(h(x)) == x
    end
    @test_throws ArgumentError hom(R, R, [R([0, 0, 1, 0]), R([1, 1, 1, 1]), R([0, 0, 1, 0]), R([0, 0, 1, 1])])
    @test_throws ArgumentError hom(R, R, [R([1, 1, 1, 1]), R([0, 0, 1, 0]), R([0, 0, 1, 1])])
  end

  let
    mats = [[1 0 0 0; 0 0 0 0; 0 0 1 0; 0 0 0 0], [0 1 0 0; 0 0 0 0; 0 0 0 1; 0 0 0 0], [0 0 0 0; 1 0 0 0; 0 0 0 0; 0 0 1 0], [0 0 0 0; 0 1 0 0; 0 0 0 0; 0 0 0 1]]
    R = finite_ring([2, 2, 2, 2], matrix.(Ref(ZZ), mats)) # M_2(F_2)
    f = id_hom(R)
    for _ in 1:10
      x = rand(R)
      @test f(x) == x
      @test preimage(f, x) == x
    end
  end

  let
    mats = [[1 0 0 0; 0 0 0 0; 0 0 1 0; 0 0 0 0], [0 1 0 0; 0 0 0 0; 0 0 0 1; 0 0 0 0], [0 0 0 0; 1 0 0 0; 0 0 0 0; 0 0 1 0], [0 0 0 0; 0 1 0 0; 0 0 0 0; 0 0 0 1]]
    R = finite_ring([2, 2, 2, 2], matrix.(Ref(ZZ), mats)) # M_2(F_2)
    S = matrix_ring(GF(2), 2)
    f = hom(R, S, [S([1 0; 0 0]), S([0 0; 1 0]), S([0 1; 0 0]), S([0 0; 0 1])])
    @test domain(f) === R
    @test codomain(f) === S
    @test is_one(f(one(R)))
    for _ in 1:10
      x = rand(R)
      y = rand(R)
      @test f(x * y) == f(x) * f(y)
    end
    @test_throws Hecke.AbstractAlgebra.NotImplementedError preimage(f, one(S))
    @test_throws ArgumentError hom(R, S, [S([1 1; 0 0]), S([0 0; 1 0]), S([0 1; 0 0]), S([0 0; 0 1])])

    g = hom(R, S, [S([1 0; 0 0]), S([0 0; 1 0]), S([0 1; 0 0]), S([0 0; 0 1])]; inverse = x -> R(lift.(Ref(ZZ), [matrix(x)...])))
    for _ in 1:10
      x = rand(R)
      @test preimage(g, g(x)) == x
    end
  end
end
