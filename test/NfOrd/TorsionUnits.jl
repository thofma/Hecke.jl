@testset "Torsion Units" begin
  l = Hecke.primes_up_to(20)
  for i = 2:length(l)
    p = l[i]
    K, a = cyclotomic_field(p)
    OK = maximal_order(K)
    @test is_torsion_unit(OK(a))
    @test Hecke.torsion_unit_order(OK(a), p) == p
    TU = Hecke.torsion_units(K)
    @test length(TU) == 2*p
    ST = Set([x.elem_in_nf for x in Hecke.torsion_units(OK)])
    STK = Set(TU)
    @assert ST == STK
    gen = Hecke.torsion_units_generator(OK)
    @test !isone(gen^p)
    @test !isone(gen^2)
  end
end