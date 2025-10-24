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

  # #2050
  let
    QQx, x = QQ[:x]
    f = x^2 - 1//2
    k, _ = number_field(f)
    fl, el = is_norm(k, 2)
    @test norm(el) == 2
  end

  # #2051
  let
    k, _a = Hecke.number_field(x^3 + 11*x^2 + 8*x - 1)
    ky, y = k[:y]
    l, _b = Hecke.number_field(y^3 + (3*_a - 2)*y^2 + (3*_a^2 - 4*_a - 8)*y - 13*_a^2 - 16*_a + 9)
    _, n1 = Hecke.is_norm(l, k(-2))
    @test norm(n1) == k(-2)
  end
end
