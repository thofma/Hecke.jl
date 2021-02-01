@testset "Simplify" begin
  Qx, x = QQ["x"]
  K, a = number_field(x^2 - x + 1289)
  Kt, t = K["t"]
  L, = number_field(t^2 - 5, cached = false)
  k, = @inferred Hecke.simplified_absolute_field(L, cached = false)
  @test isisomorphic(k, number_field(x^4 + 513*x^2 + 67081)[1])[1]

  K, a = number_field(x^3 + 42*x - 192, "a", cached = false);
  Kt, t = K["t"]
  L, = number_field(t^2 + 3, cached = false)
  k, = @inferred  Hecke.simplified_absolute_field(L)
end
