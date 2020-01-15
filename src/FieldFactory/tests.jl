function FFtests()
  printstyled(" Quadratic Fields\n", color = :red)
  @time begin
    lq = fields(2, 1, fmpz(10)^4)
    @assert length(lq) == 6086
  
    lqreal = fields(2, 1, fmpz(10)^4, only_real = true)
    @assert length(lqreal) == 3043

    lq2 = [x for x in lq if istotally_real(x.field)]
    @assert length(lq2) == 3043
  end

  printstyled("\n Biquadratic Fields\n", color = :red)
  @time begin
    l = fields(4, 2, fmpz(10)^6)
    @assert length(l) ==  1014
  
    l1 = fields(4, 2, fmpz(10)^6, only_real = true)
    @assert length(l1) == 196
  
    l2 = [x for x in l if istotally_real(x.field)]
    @assert length(l2) == 196
  end

  printstyled("\n Direct product decomposition\n", color = :red)
  @time begin
    l_direct_product = fields(12, 4, fmpz(10)^13)
    @assert length(l_direct_product) == 25
  
    l_without = fields(12, 4, fmpz(10)^13, using_direct_product = false)
    @assert length(l_without) == 25

    d1 = length(fields(24, 13, fmpz(10)^24, simplify = false)) 
    d2 = length(fields(24, 13, fmpz(10)^24, using_direct_product = false, simplify = false))
    @assert d1 == d2
  end


  printstyled("\n Obstructions: degree 2\n", color = :red)
  @time begin
    G = GAP.Globals.SmallGroup(8, 4)
    L = GAP.Globals.DerivedSeries(G)
    forQ8_old = Hecke.check_obstruction(l, L, 2, [2])
    @assert length(forQ8_old) == 53
    forQ8 = [FieldsTower(x.field, x.generators_of_automorphisms, x.subfields) for x in forQ8_old]
  
    lQ8 = fields(8, 4, fmpz(10)^12)
    @assert length(lQ8) == 2
  
    lQ8_2 = fields(8, 4, forQ8, fmpz(10)^12)
    @assert length(lQ8_2) == 2
  
    lQ8real = fields(8, 4, fmpz(10)^12, only_real = true)
    @assert length(lQ8real) == 1
  end
  
  printstyled("\n Obstructions: prime degree\n", color = :red)
  @time begin
    @assert length(fields(54, 5, fmpz(10)^70, simplify = false)) == 3
    @assert length(fields(27, 3, fmpz(10)^60, simplify = false)) == 10
  end
  
  printstyled("\n Obstructions: prime_power_case\n", color = :red)
  @time begin
    l = fields(4, 2, fmpz(10)^5);
    G = GAP.Globals.SmallGroup(16, 9)
    L = GAP.Globals.DerivedSeries(G)
    lsieved = check_obstruction(l, L, 2, [4])
    @assert length(lsieved) == 78
    l = fields(4, 2, fmpz(10)^6);
    G = GAP.Globals.SmallGroup(32, 20)
    L = GAP.Globals.DerivedSeries(G)
    lsieved = check_obstruction(l, L, 2, [8])
    @assert length(lsieved) == 232
  end
  
  printstyled("\n Obstructions: reduction to cyclic case\n", color = :red)
  @time begin
    @assert length(fields(32, 30, fmpz(10)^39, simplify = false)) == 2
  end
  

  printstyled("\n Some examples\n", color = :red)
  @time begin
    @assert length(fields(6, 1, fmpz(10)^8, simplify = false)) == 107
  end

  printstyled("\n Tests were successful", color = :red)
end
