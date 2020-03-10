@testset "FieldFactory" begin
  printstyled(" Quadratic Fields\n", color = :red)
  @time begin
    lq = fields(2, 1, fmpz(10)^4)
    @test length(lq) == 6086
  
    lqreal = fields(2, 1, fmpz(10)^4, only_real = true)
    @test length(lqreal) == 3043

    lq2 = [x for x in lq if istotally_real(x.field)]
    @test length(lq2) == 3043
  end

  printstyled("\n Biquadratic Fields\n", color = :red)
  @time begin
    l = fields(4, 2, fmpz(10)^6)
    @test length(l) ==  1014
  
    l1 = fields(4, 2, fmpz(10)^6, only_real = true)
    @test length(l1) == 196
  
    l2 = [x for x in l if istotally_real(x.field)]
    @test length(l2) == 196
  end

  printstyled("\n Direct product decomposition\n", color = :red)
  @time begin
    l_direct_product = fields(12, 4, fmpz(10)^13)
    @test length(l_direct_product) == 25
  
    l_without = fields(12, 4, fmpz(10)^13, using_direct_product = false)
    @test length(l_without) == 25

    d1 = length(fields(24, 13, fmpz(10)^24, simplify = false)) 
    d2 = length(fields(24, 13, fmpz(10)^24, using_direct_product = false, simplify = false))
    @test d1 == d2
  end


  printstyled("\n Obstructions: degree 2\n", color = :red)
  @time begin
    G = GAP.Globals.SmallGroup(8, 4)
    L = GAP.Globals.DerivedSeries(G)
    forQ8_old = Hecke.check_obstruction(l, L, 2, [2])
    @test length(forQ8_old) == 53
    forQ8 = [Hecke.FieldsTower(x.field, x.generators_of_automorphisms, x.subfields) for x in forQ8_old]
  
    lQ8 = fields(8, 4, fmpz(10)^12)
    @test length(lQ8) == 2
  
    lQ8_2 = fields(8, 4, forQ8, fmpz(10)^12)
    @test length(lQ8_2) == 2
  
    lQ8real = fields(8, 4, fmpz(10)^12, only_real = true)
    @test length(lQ8real) == 1
  end
  
  printstyled("\n Obstructions: prime degree\n", color = :red)
  @time begin
    l = fields(6, 2, fmpz(10)^8)
    G = GAP.Globals.SmallGroup(54, 5)
    L = GAP.Globals.DerivedSeries(G)
    lsieved = Hecke.check_obstruction(l, L, 2, [3, 3])
    @test length(lsieved) == length(l)
    l = fields(9, 2, fmpz(10)^20)
    G = GAP.Globals.SmallGroup(27, 3)
    L = GAP.Globals.DerivedSeries(G)
    lsieved = Hecke.check_obstruction(l, L, 2, [3])
    @test length(lsieved) == 24
  end
  
  printstyled("\n Obstructions: prime_power_case\n", color = :red)
  @time begin
    l = fields(4, 2, fmpz(10)^5);
    G = GAP.Globals.SmallGroup(16, 9)
    L = GAP.Globals.DerivedSeries(G)
    lsieved = Hecke.check_obstruction(l, L, 2, [4])
    @test length(lsieved) == 78
    l = fields(4, 2, fmpz(10)^6);
    G = GAP.Globals.SmallGroup(32, 20)
    L = GAP.Globals.DerivedSeries(G)
    lsieved = Hecke.check_obstruction(l, L, 2, [8])
    @test length(lsieved) == 232
  end
  
  printstyled("\n Obstructions: reduction to cyclic case\n", color = :red)
  @time begin
    l = fields(8, 2, fmpz(10)^10)
    G = GAP.Globals.SmallGroup(96, 13)
    L = GAP.Globals.DerivedSeries(G)
    lsieved = Hecke.check_obstruction(l, L, 2, [2, 6])
    @test length(l) == length(lsieved)
    @test length(fields(32, 30, fmpz(10)^39, simplify = false)) == 2
  end
  

  printstyled("\n Some examples\n", color = :red)
  @time begin
    @test length(fields(6, 1, fmpz(10)^8, simplify = false)) == 107
    @test length(fields(24, 8, fmpz(10)^30, simplify = false)) == 15
  end

  printstyled("\n Tests were successful\n", color = :red)
end
