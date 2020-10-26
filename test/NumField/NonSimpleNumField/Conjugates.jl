@testset begin
  Qx, x = QQ["x"]
  K, a = NumberField(x^3 + 2, "a")
  Kt, t = K["t"]
  L, b = number_field([t^2 - 3, t^2 - t - 50], "b")

  r, s = @inferred signature(L)
  @test (r, s) == (4, 4)

  m = rand(L, -1:1)

  Labs, LabstoL = absolute_field(L)
  Hecke._compute_preimage(LabstoL)

  c = conjugates(m, 64)
  cc = conjugates(LabstoL\m, 64)

  for _c in c
    @test count(_cc -> overlaps(_cc, _c), cc) == count(_cc -> overlaps(_cc, _c), c)
  end
end
