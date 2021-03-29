@testset "Misc/MPolyAbsFact" begin

  f = Hecke.MPolyFact.example(wildanger_field(3, 13)[1], 3, 5)
  @test length(factor_absolute(f)) >= 2

  f = Hecke.MPolyFact.example(cyclotomic_field(4)[1], 3, 5) 
  @test length(factor_absolute(f)) >= 2
end
