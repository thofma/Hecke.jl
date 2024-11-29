@testset "Conjugates" begin
   k, a = wildanger_field(3, 13)

   @testset "Regulator" begin
     C_29 = Hecke.qAdicConj(k, 29)
     C_31 = Hecke.qAdicConj(k, 31)

     @test valuation(regulator(k, C_29)) == 2
     @test valuation(regulator(k, C_31)) == 2

     #@test valuation(regulator(k, C_29, flat = true)) == 3
     @test valuation(regulator(k, C_31, flat = true)) == 2

     @test valuation(regulator(k, C_29, flat = false)) == 2
     @test valuation(regulator(k, C_31, flat = false)) == 2
   end

   @testset "Completion" begin
     L1, mL1 = completion(k, 37, 2)
     L2, mL2 = completion(k, 37, 3)

     @test degree(parent(mL1(a))) == 2
     @test degree(parent(mL2(a))) == 1

     lp = prime_decomposition(maximal_order(k), 37)

     @test valuation(a - preimage(mL1, mL1(a)), lp[2][1]) >= 10
     @test valuation(a - preimage(mL2, mL2(a)), lp[1][1]) >= 10

     @test degree(codomain(completion(k, 37, 2; cached = false)[2])) == 2
   end
end


