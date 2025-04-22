@testset "Simplify" begin
  Qx, x = QQ["x"]
  K, a = number_field(x^2 - x + 1289)
  Kt, t = K["t"]
  L, = number_field(t^2 - 5, cached = false)
  k, = @inferred Hecke.simplified_absolute_field(L, cached = false)
  @test is_isomorphic(k, number_field(x^4 + 513*x^2 + 67081)[1])

  K, a = number_field(x^3 + 42*x - 192, "a", cached = false);
  Kt, t = K["t"]
  L, = number_field(t^2 + 3, cached = false)
  k, = @inferred  Hecke.simplified_absolute_field(L)

  K, a = number_field(x^6 - 2*x^5 + x^4 - 398*x^3 - 15961*x^2 + 41496*x + 829621)
  Kx, x = K["x"]
  g = x^2 + 715563140//10487238697*a^5 - 6095690353//10487238697*a^4 +
  48931518460//10487238697*a^3 - 538842733308//10487238697*a^2 -
  6596745411420//10487238697*a + 4782497108432//806710669
  L, b = number_field(g, "b");
  k, = @inferred Hecke.simplified_absolute_field(L)

  Qx, x = QQ["x"]
  K, a = number_field(x^3 + 42*x - 192, "a")
  Kt, t = K["t"]
  L, = number_field([t^2 + 3], cached = false);
  k, = @inferred absolute_simple_field(L, cached = false, simplify = true)

  Qx, x = QQ["x"]
  f = x^2 - x + 743
  K, a = number_field(f, "a")
  Kt, t = K["t"]
  L, = number_field([t^2 - a + 27])
  k, = @inferred absolute_simple_field(L, cached = false, simplify = true)

  # #1257
  R, x = polynomial_ring(QQ)
  Q, = number_field(x)
  S, y = polynomial_ring(Q)
  K, = number_field([y])
  b = absolute_primitive_element(K)
  @test parent(b) === K # b could be anything in K
end
