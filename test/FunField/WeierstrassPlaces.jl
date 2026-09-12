@testset "Gap numbers and Weierstrass places" begin
  kx, x = rational_function_field(GF(49), :x)
  kxy, y = kx[:y]
  F, a = function_field(y^7 + y - x^4)
  Ofin = finite_maximal_order(F)
  p1, _ = first(factor(ideal(Ofin, x-1)))
  D = divisor(p1)

  @test gap_numbers(F) == [1, 2, 3, 4, 5, 8, 9, 10, 15]
  @test degree(ramification_divisor(F)) == 912

  gaps, R = @inferred Hecke._gaps_and_ramification_divisor(D, false)
  @test gaps == [1, 2, 3, 4, 5, 8, 9, 10]
  @test degree(R) == 664

  kx, x = rational_function_field(QQ, :x)
  kxy, y = kx[:y]
  F, a = function_field(y^2 - x^7 - 1)
  Ofin = finite_maximal_order(F)
  Oinf = infinite_maximal_order(F)


  @test gap_numbers(F) == [1, 2, 3]
  Ps = weierstrass_places(F)
  test_Ps = [ideal(Ofin, x+1, Ofin(a)),
    ideal(Ofin, x^6 - x^5 + x^4 - x^3 + x^2 - x + 1, Ofin(a)), 
    ideal(Oinf, (1//x), Oinf(1//x^4*a))]
  for P in Ps
    @test P in test_Ps
  end

  P = test_Ps[1]
  @test gap_numbers(divisor(P)) == [1,2]
  P = test_Ps[2]
  @test gap_numbers(divisor(P)) == []
  weierstrass_places(divisor(P)) == []
end
