@testset "Overorders" begin
  Qx,  x = FlintQQ["x"]

  f = x^2 + 100x + 100

  A = AlgAss(f * (f - 1))
  O = Order(A, basis(A))

  orders = @inferred poverorders(O, 2)
  @test length(orders) == 6

  orders = @inferred poverorders(O, fmpz(5))
  @test length(orders) == 2

  orders = @inferred poverorders(O, fmpz(7))
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
  A = AlgAss(group_algebra(FlintQQ, G))[1]
  O = Order(A, basis(A))
  orders = @inferred overorders(O)
  @test length(orders) == 12

  orders = @inferred overorders(O, type = :all)
  @test length(orders) == 12

  @test count(is_maximal, orders) == 2

  @test_throws ErrorException overorders(O, type =  :gorenstein)
  @test_throws ErrorException overorders(O, type =  :bass)
  @test_throws ErrorException overorders(O, type =  :blub)

  f = x^4-1680*x^3-25920*x^2-1175040*x+25214976
  O = EquationOrder(f)
  orders = @inferred overorders(O)
  @test length(orders) == 2535
  @test count(is_maximal, orders) == 1
  @test count(is_gorenstein, orders) == 657
  @test count(is_bass, orders) == 5

  @test length(overorders(O, type = :gorenstein)) == 657
  @test length(overorders(O, type = :bass)) == 5

  f = x^4-1680*x^3-25920*x^2-1175040*x+25214976
  A = AlgAss(f)
  O = Order(A, basis(A))
  @test length(overorders(O)) == 2535
end
