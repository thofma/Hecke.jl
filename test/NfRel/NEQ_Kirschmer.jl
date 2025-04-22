@testset "NEQ Kirschmer" begin
  R,x = ZZ["x"]
  K,a = number_field(x^2+3x+1,"a")
  kt,t = K["t"]
  E, b = number_field( t^2 + (a+5)* (-2*a+2) )
  @test Hecke.is_norm( E, -a*(-2*a+2) )[1]

  K, a = number_field(x^2 - 2, "a")
  Kt, t = K["t"]
  L, b = number_field(t^2 - 7)
  @test is_norm(L, K(324))[1]

  K,a = number_field(x^2+3*x+1)
  kt,t=K["t"]
  E,b=number_field(t^2-(a-1),"b")
  @test is_norm(E, a+3)[1]

  K, a = quadratic_field(-5)
  kt,t=K["t"]
  theta = 11*(4*a-22)
  E,b=number_field(t^2+theta,"b")

  @test is_norm(E, K(-11))[1]
end
