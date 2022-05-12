@testset "Is integral" begin
  Qx, x = FlintQQ["x"]
  f = x^2 + 1
  K, a = number_field(f, "a")
  Ky, y = K["y"]

  g = y^3 + 3
  L, b = number_field(g, "b")

  @test Hecke.is_integral(b) == true
  @test Hecke.is_integral(fmpq(1, 2)*b) == false

  h = y^4 + 3
  M, c = number_field([g, h], "c")

  @test Hecke.is_integral(c[1]) == true
  @test Hecke.is_integral(fmpq(1, 2)*c[1]) == false
end
