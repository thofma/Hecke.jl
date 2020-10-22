@testset "FieldFactory" begin

  println("Quadratic Fields")
  @time begin
    @testset "Quadratic Fields" begin
      lq = fields(2, 1, fmpz(10)^4)
      @test length(lq) == 6086
  
      lqreal = fields(2, 1, fmpz(10)^4, only_real = true)
      @test length(lqreal) == 3043

      ind = 0
      for x in lq
        if istotally_real(x.field)
          ind += 1
        end
      end
      @test ind == 3043
    end
  end 

  println("Biquadratic Fields")
  @time begin
    @testset "Biquadratic Fields" begin
      l = fields(4, 2, fmpz(10)^6)
      @test length(l) ==  1014
  
      l1 = fields(4, 2, fmpz(10)^6, only_real = true)
      @test length(l1) == 196
  
      ind = 0
      for x in l
        if istotally_real(x.field)
          ind += 1
        end
      end
      @test ind == 196
    end
  end

  println("Abelian Fields")
  @time begin
    @testset "Abelian fields" begin
      l = fields(6, 2, fmpz(10)^6)
      @test length(l) ==  10
  
      l1 = fields(9, 2, fmpz(10)^13)
      @test length(l1) == 4
    end
  end


  println("Direct product decomposition")
  @time begin
    @testset "Direct product decomposition" begin
      l_direct_product = fields(12, 4, fmpz(10)^13)
      @test length(l_direct_product) == 25
  
      l_without = fields(12, 4, fmpz(10)^13, using_direct_product = false)
      @test length(l_without) == 25

      d1 = length(fields(24, 13, fmpz(10)^24)) 
      d2 = length(fields(24, 13, fmpz(10)^24, using_direct_product = false))
      @test d1 == d2

      l_direct_product = fields(18, 3, fmpz(10)^18)
      l_without = fields(18, 3, fmpz(10)^18, using_direct_product = false)
      @test length(l_direct_product) == length(l_without)
      for x in l_direct_product
        @test GAP.gap_to_julia(Vector{Int}, Hecke.IdGroup(closure(x.generators_of_automorphisms))) == [18, 3]
      end
      for x in l_without
        @test GAP.gap_to_julia(Vector{Int}, Hecke.IdGroup(closure(x.generators_of_automorphisms))) == [18, 3]
      end
    end
  end

  println("Split extension")
  @time begin
    @testset "Split extension" begin
      x = PolynomialRing(FlintZZ, "x", cached = false)[2]
      K =  number_field(x^2+1)[1]
      l = Hecke.FieldsTower[Hecke.field_context(K)]
      l1 = fields(42, 5, l, fmpz(10)^90)
      @test length(l1) == 1
      @test GAP.gap_to_julia(Vector{Int}, Hecke.IdGroup(closure(l1[1].generators_of_automorphisms))) == [42, 5]
    end
  end


  println("Obstructions: degree 2")
  @time begin
    @testset "Obstructions: degree 2" begin
      G = GAP.Globals.SmallGroup(8, 4)
      L = GAP.Globals.DerivedSeries(G)
      l = fields(4, 2, fmpz(10)^6)
      forQ8 = Hecke.check_obstruction(l, L, 2, [2])
      @test length(forQ8) == 53
      
  
      lQ8 = fields(8, 4, fmpz(10)^12)
      @test length(lQ8) == 2
  
      lQ8_2 = fields(8, 4, forQ8, fmpz(10)^12)
      @test length(lQ8_2) == 2
  
      lQ8real = fields(8, 4, forQ8, fmpz(10)^12, only_real = true)
      @test length(lQ8real) == 1
    end
  end

  println("Obstructions: prime degree")
  @time begin
    @testset "Obstructions: prime degree" begin
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
  end
  
  println("Obstructions: prime power case")
  @time begin
    @testset "Obstructions: prime_power_case" begin
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
  end

  println("Obstructions: reduction to cyclic case")
  @time begin
    @testset "Obstructions: reduction to cyclic case" begin
      l = fields(8, 2, fmpz(10)^10)
      G = GAP.Globals.SmallGroup(96, 13)
      L = GAP.Globals.DerivedSeries(G)
      lsieved = Hecke.check_obstruction(l, L, 2, [2, 6])
      @test length(l) == length(lsieved)
      @test length(fields(32, 30, fmpz(10)^39)) == 2
    end
  end

  
  println("Some examples")
  @time begin
    @testset "Some examples" begin
      l1 = fields(6, 1, fmpz(10)^8)
      @test length(l1) == 107
      for x in l1
        @test GAP.gap_to_julia(Vector{Int}, Hecke.IdGroup(closure(x.generators_of_automorphisms))) == [6, 1]
      end
      l2 = fields(24, 8, fmpz(10)^30)
      @test length(l2) == 15
      for x in l2
        @test GAP.gap_to_julia(Vector{Int}, Hecke.IdGroup(closure(x.generators_of_automorphisms))) == [24, 8]
      end
      l3 = fields(30, 3, fmpz(10)^40)
      @test length(l3) == 5
      for x in l3
        @test GAP.gap_to_julia(Vector{Int}, Hecke.IdGroup(closure(x.generators_of_automorphisms))) == [30, 3]
      end
    end
  end

end
