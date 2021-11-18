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
      @time l_direct_product = fields(12, 4, fmpz(10)^13)
      @test length(l_direct_product) == 25

      @time l_without = fields(12, 4, fmpz(10)^13, using_direct_product = false)
      @test length(l_without) == 25

      d1 = length(fields(24, 13, fmpz(10)^24))
      d2 = length(fields(24, 13, fmpz(10)^24, using_direct_product = false))
      @test d1 == d2

      @time l_direct_product = fields(18, 3, fmpz(10)^18)
      @time l_without = fields(18, 3, fmpz(10)^18, using_direct_product = false)
      @test length(l_direct_product) == length(l_without)
      for x in l_direct_product
        @test GAP.gap_to_julia(Vector{Int}, Hecke.IdGroup(closure(x.generators_of_automorphisms))) == [19, 3]
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
      @time lQ = fields(1, 1, fmpz(1))
      @test length(lQ) == 1
      @test degree(number_field(lQ[1])) == 1
      @time l1 = fields(6, 1, fmpz(10)^8)
      @test length(l1) == 107
      for x in l1
        @test GAP.gap_to_julia(Vector{Int}, Hecke.IdGroup(closure(x.generators_of_automorphisms))) == [6, 1]
      end
      @time l2 = fields(24, 8, fmpz(10)^30)
      @test length(l2) == 15
      for x in l2
        @test GAP.gap_to_julia(Vector{Int}, Hecke.IdGroup(closure(x.generators_of_automorphisms))) == [24, 8]
      end
      @time l3 = fields(30, 3, fmpz(10)^40)
      @test length(l3) == 5
      for x in l3
        @test GAP.gap_to_julia(Vector{Int}, Hecke.IdGroup(closure(x.generators_of_automorphisms))) == [30, 3]
      end
      Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
      f = x^36 - x^33 + x^27 - x^24 + x^18 - x^12 + x^9 - x^3 + 1
      K, a = number_field(f, cached = false, check = false)
      d = fmpz(1252291517600545939502745293690906945712691746311040212121628914687318440182651069503694911322360563684969)
      flds = [Hecke.field_context(K)]
      @time @test isone(length(fields(72, 37, flds, d)))

      f = x^24 + 12*x^23 + 12*x^22 - 372*x^21 - 1224*x^20 + 4192*x^19 + 22370*x^18 - 17518*x^17 - 198383*x^16 - 30608*x^15 + 1017900*x^14 + 582696*x^13 - 3257224*x^12 - 2385744*x^11 + 6751956*x^10 + 4794056*x^9 - 9162405*x^8 - 4964804*x^7 + 7887120*x^6 + 2258008*x^5 - 3853388*x^4 - 85944*x^3 + 797010*x^2 - 160358*x + 1483
      K, a = number_field(f, check = false, cached = false)
      c = Hecke.field_context(K)
      @test length(c.subfields) == 3
      @test degree(domain(c.subfields[1])) == 1
      @test degree(domain(c.subfields[2])) == 2
      @test degree(domain(c.subfields[3])) == 6
      @test domain(c.subfields[2]) == codomain(c.subfields[1])
      @test domain(c.subfields[3]) == codomain(c.subfields[2])

      f = x^16 + 2*x^15 - 9*x^14 + 157*x^12 + 56*x^11 + 505*x^10 - 2324*x^9 + 1608*x^8 - 4252*x^7 + 19587*x^6 - 26800*x^5 - 52305*x^4 - 97006*x^3 + 164822*x^2 + 444940*x + 245969
      K, a = number_field(f, check = false, cached = false)
      l = [Hecke.field_context(K)];
      # This is too expensive with assertions
      Hecke.assertions(false)
      @time @test length(fields(64, 6, l, fmpz(80)^64)) == 1
      Hecke.assertions(true)
    end
  end

  # Fix for #452

  Qx, x = QQ["x"]
  k, _ = number_field(x^4-11*x^2+9)
  L = abelian_extensions(k, [3], fmpz(10)^16)
  @test length(L) == 2
end
