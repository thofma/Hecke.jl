@testset "RelNonSimpleNumField" begin
  Qx, x = QQ["x"]
  K, _ = number_field(x^2 - 2)
  Ky, y = K["y"]
  L, (a, b) = @inferred number_field([y^2 - 3, y^3 - 5])

  @testset "Basics" begin
    @test K == @inferred base_field(L)
    @test 6 == @inferred degree(L)
    @test [2, 3] == @inferred degrees(L)
    @test 2 == @inferred ngens(L)
    @test [a, b] == @inferred gens(L)
    @test [Symbol(a), Symbol(b)] == @inferred vars(L)
    @test [one(L), a, b, a * b, b^2, a * b^2] == @inferred basis(L)
    @test string(L) isa String
    @test string(a) isa String
  end

  @testset "coercion" begin
    @test QQ(2*a^0) == 2*one(QQ)
    @test_throws ArgumentError QQ(a)
    @test_throws ErrorException QQ(gen(K) * a^0)
    @test is_rational(2*a^0)
    @test !is_rational(gen(K) * a^0)
  end

  @testset "consistency check" begin
    # Q(sqrt(3)) lies inside Q(sqrt[4](3))
    @test_throws ErrorException number_field([y^2 - 3, y^4 - 3]; cached = false)
    # first polynomial is reducible (since sqrt(2) is in the base field)
    @test_throws ErrorException number_field([y^4 - 10*y^2 + 1, y^3+2]; cached = false)
    # intersect at sqrt(3): roots are +- sqrt(3) +- sqrt(5) and +- sqrt(3) +- sqrt(7)
    @test_throws ErrorException number_field([y^4 - 16*y^2 + 4, y^4 - 20*y^2 + 16]; cached = false)
    # should hit early-out on pairwise coprime degrees (so this should be super fast)
    L = number_field([y^11 + 2, y^4 + 3, y^7 + 4]; cached = false, check = false)[1]
    @test Hecke._check_consistency(L)
  end

  @testset "primitive element" begin
    # these fields intersect at sqrt(3)
    # the roots are a = \pm \sqrt{3} \pm \sqrt{5} and b = \pm \sqrt{3} \pm \sqrt{7}
    # this test case was specifically constructed to trigger "non-trivial" primitive element
    #   when using resultant algorithm: c = 1 gives non-squarefree resultant
    L, (a, b) = number_field([y^4 - 16*y^2 + 4, y^4 - 20*y^2 + 16]; check = false, cached = false)
    pe = @inferred Hecke.primitive_element(L)
    @test pe != a+b
    @test degree(minpoly(pe)) == degree(L)

    # for small-degree linearly disjoint fields, c = 1 always works
    # we still want to do some simple tests
    for f in [y^2 - 7, y^3 - 4, y^4 - 5], g in [y^2 + 1, y^3 + 3, y^4 + 3]
      L, (a, b) = number_field([f, g]; check = false, cached = false)
      @test degree(minpoly(Hecke.primitive_element(L))) == degree(L)
    end
  end
end
