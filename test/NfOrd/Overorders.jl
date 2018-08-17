@testset "Overorders" begin
  global Qx,  x = FlintQQ["x"]

  f = x^3 - 1000*x^2 + 1000*x - 1000

  global K,  a = NumberField(f, "a");

  E = EquationOrder(K)

  #@test length(overorders(E)) == 16

  f = x^3 + 31 * x^2 + 43* x + 77

  global K,  a = NumberField(f, "a");

  E = EquationOrder(K)


  #@test length(overorders(E)) == 15
  #@test length(Hecke.overorders_naive(E)) == 15
end
