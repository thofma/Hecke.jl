@testset "Map" begin
  begin
    G = small_group(2, 1)
    QG = QQ[G]
    ZG = Hecke.new_order(QG, ZZ, basis(QG))
    f = hom(ZG, ZZ, [one(ZZ), one(ZZ)])
    @test domain(f) === ZG
    @test codomain(f) === ZZ
    @test is_one(f(one(ZG)))
  end

  G = small_group(2, 1)
  k, t = rational_function_field(GF(3), :t)
  kt = parent(numerator(t))
  QG = k[G]
  ktG = Hecke.new_order(QG, kt, basis(QG))
  F, kttoF = residue_field(kt, gen(kt)^2 + 1)
  f = hom(ktG, F, kttoF, [one(F), one(F)])
  @test domain(f) === ktG
  @test codomain(f) === F
  @test is_one(f(one(ktG)))
end
