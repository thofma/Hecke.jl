@testset "NumField/AbsNonSimpleNumField/ConjugatesNS.jl" begin
  Qx, x = QQ["x"]
  K, a = number_field([x^2 - 2, x^2 - 3, x^2 - 5], "a")
  r, s = @inferred signature(K)
  @test (r, s) == (8, 0)
  Kabs, KabstoK = simple_extension(K)
  b = rand(K, -1:1)

  c = conjugates(b, 64)
  cc = conjugates(KabstoK\b, 64)

  for _c in c
    @test count(_cc -> overlaps(_cc, _c), cc) == count(_cc -> overlaps(_cc, _c), c)
  end

  Kt, t = K["t"]
  L, b = number_field(t^2 - a[1] * a[2])
  @test signature(L) == (8, 4)
end

@testset "NumField/AbsNonSimpleNumField/Conjugates.jl" begin
  Qx, x = QQ["x"]
  K, a = wildanger_field(3, 13)
  r, s = @inferred signature(K)
  @test (r, s) == (1, 1)
  b = rand(K, -1:1)

  c = conjugates(b, AcbField(64))
  cc = conjugates(b, 64)

  for _c in c
    @test count(_cc -> overlaps(_cc, _c), cc) == count(_cc -> overlaps(_cc, _c), c)
  end
end
