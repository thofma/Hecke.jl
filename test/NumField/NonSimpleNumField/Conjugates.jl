@testset begin
  Qx, x = QQ["x"]
  K, a = NumberField(x^3 + 2, "a")
  Kt, t = K["t"]
  L, b = number_field([t^2 - 3, t^2 - t - 50], "b")

  r, s = @inferred signature(L)
  @test (r, s) == (4, 4)

  m = rand(L, -1:1)

  Labs, LabstoL = absolute_field(L)

  c = conjugates(m, 64)
  cc = conjugates(LabstoL\m, 64)

  for _c in c
    @test count(_cc -> overlaps(_cc, _c), cc) == 1
  end
  for _cc in cc
    @test count(_c -> overlaps(_cc, _c), c) == 1
  end
end
