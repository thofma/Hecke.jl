@testset begin
  Qx, x = QQ["x"]
  K, a = NumberField(x^3 + 2, "a")
  Kt, t = K["t"]
  L, b = number_field([t^2 - 3, t^2 - t - 50], "b")

  r, s = @inferred signature(L)
  @test (r, s) == (4, 4)

  m = rand(L, -1:1)

  Labs, LabstoL = absolute_simple_field(L)

  c = conjugates(m, 64)
  cc = conjugates(LabstoL\m, 64)

  for _c in c
    @test count(_cc -> overlaps(_cc, _c), cc) == count(_cc -> overlaps(_cc, _c), c)
  end

  f = x^2+1
  K, a = number_field(f, cached = false, check = false);
  Kt, t = K["t"]
  f1 = t^3 + 249*t - 830
  f2 = t^7 - 1162*a*t^5 + (-29050*a + 29050)*t^4 - 542073*t^3 + (-14412286*a - 14412286)*t^2 - 80411562*a*t + 3869576532*a - 3869576532
  L, gL = number_field([f1, f2], cached = false)
  s, t = gL
  el = (1//978369084*a + 5//978369084)*t^6 + (-4//7411887*a + 89//978369084)*t^5 + (3181//489184542*a - 2753//489184542)*t^4 + (128197//978369084*a + 52165//81530757)*t^3 + (-6920957//489184542*a + 273422//22235661)*t^2 + (1243580//9058973*a - 2545783//18117946)*t + 67078685//27176919*a + 133062707//27176919
  c = t2(el)
  Labs, mLabs = absolute_simple_field(L)
  cc = t2(mLabs\el)
  @test overlaps(c, cc)
end
