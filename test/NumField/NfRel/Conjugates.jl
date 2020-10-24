@testset "NumField/NfRel/Conjugates.jl" begin
  Qx, x = QQ["x"]
  K, a = NumberField(x^2 - 2, "a")
  Kt, t = K["t"]
  g = t^3 + a*t + 5
  L, b = NumberField(g, "b")
  r, s = @inferred signature(L)
  @test (r, s) == (2, 2)
  plc = @inferred infinite_places(L)
  @test count(isreal, plc) == 2
  @test count(!isreal, plc) == 2

  Labs, LabstoL, = absolute_field(L)
  c = conjugates(b, 64)
  cc = conjugates(LabstoL\b, 64)

  for _c in c
    @test count(_cc -> overlaps(_cc, _c), cc) == count(_cc -> overlaps(_cc, _c), c)
  end

  Ly, y = L["y"]
  M, m = number_field(y^2 + y + b - 5, "c")
  r, s = @inferred signature(M)
  @test (r, s) == (4, 4)

  plc = @inferred infinite_places(M)
  @test count(isreal, plc) == 4
  @test count(!isreal, plc) == 4

  Mabs, MabstoM, = absolute_field(M)
  Mabsabs, MabsabstoMabs = absolute_field(Mabs)

  o = rand(M, -1:1)

  c = conjugates(o, 64)
  cc = conjugates(MabsabstoMabs\(MabstoM\o), 64)

  for _c in c
    @test count(_cc -> overlaps(_cc, _c), cc) == count(_cc -> overlaps(_cc, _c), c)
  end
end
