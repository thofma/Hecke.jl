@testset "AlgAssRelOrd" begin
  Qx, x = FlintQQ["x"]
  f = x^2 - 5x - 1
  K, a = number_field(f, "a")

  @testset "Any order" begin
    Ky, y = K["y"]
    A = StructureConstantAlgebra(y^2 - QQFieldElem(1, 5))

    O = any_order(A)

    # Test whether O is indeed an order
    @test one(A) in O

    gens_O = Vector{elem_type(A)}()
    for (e, a) in pseudo_basis(O, copy = false)
      for b in basis(a)
        push!(gens_O, e*b)
      end
    end

    for x in gens_O
      @test is_integral(x)
      for y in gens_O
        @test x*y in O
      end
    end

    # Some more miscellaneous tests
    x = rand(O, 10)
    @test elem_in_algebra(x) in O

    x = A([ K(1), K(QQFieldElem(1, 3)) ])
    @test denominator(x, O)*x in O
  end

  @testset "Maximal Orders" begin
    G = small_group(8, 4)
    KG = group_algebra(K, G)

    O1 = Hecke.maximal_order_via_absolute(KG)
    O2 = Hecke.maximal_order_via_relative(KG)
    @test discriminant(O1) == discriminant(O2)

    KG = StructureConstantAlgebra(KG)[1]

    O1 = Hecke.maximal_order_via_absolute(KG)
    O2 = Hecke.maximal_order_via_relative(KG)
    @test discriminant(O1) == discriminant(O2)

    Qx, x = FlintQQ["x"]
    K, a = number_field(x^4 - 4 * x^2 + 2)
    A = Hecke.quaternion_algebra2(K, -1, -1)
    M = maximal_order(A)
    @test norm(discriminant(M)) == 1
  end

  @testset "Misc" begin
    k, = Hecke.rationals_as_number_field()
    A = Hecke.quaternion_algebra2(k, -1, -1)
    @test !Hecke.is_maximal_order_known(A)
    maximal_order(A)
    @test Hecke.is_maximal_order_known(A)
  end
end
