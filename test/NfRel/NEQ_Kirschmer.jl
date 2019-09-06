@testset "NEQ Kirschmer" begin
  R,x = FlintZZ["x"]
  K,a = number_field(x^2+3x+1,"a")
  kt,t = K["t"]
  E, b = number_field( t^2 + (a+5)* (-2*a+2) )
  @test Hecke.isnorm( E, -a*(-2*a+2) )[1]

  K, a = NumberField(x^2 - 2, "a")
  Kt, t = K["t"]
  L, b = number_field(t^2 - 7)
  @test isnorm(L, K(324))[1]
end
