@testset "Classical" begin
  Zxy, (x, y) = ZZ["x", "y"]
  p = @inferred classical_modular_polynomial(1)
  @test base_ring(p) == ZZ
  @test p(x, y) == x + y
  # test caching
  p = @inferred classical_modular_polynomial(1)
  @test base_ring(p) == ZZ
  @test p(x, y) == x + y

  p = @inferred classical_modular_polynomial(2)
  @test base_ring(p) == ZZ
  @test p(x, y) == x^3 - x^2*y^2 + 1488*x^2*y - 162000*x^2 + 1488*x*y^2 + 40773375*x*y + 8748000000*x + y^3 - 162000*y^2 + 8748000000*y - 157464000000000

  p = @inferred classical_modular_polynomial(25)
  @test constant_coefficient(p) == 14386245985272883324015703111660587192675726207106874718351335853206325654615424338254825121125498589319271599569067149492491688571248840175657900729489337202694836796781744548654922311933270371526939116126423746856625240926636499707485146768291922848003590590567564246007279019912714416725791203246166108581436154959822182988259800760898050588672000
  @test total_degree.(classical_modular_polynomial.(1:12)) == [1, 4, 6, 9, 10, 18, 14, 20, 20, 30, 22, 38]

  p = @inferred classical_modular_polynomial(Zxy, 1)
  @test parent(p) === Zxy

  Fxy, (x, y) = GF(2)["x", "y"]
  p = @inferred classical_modular_polynomial(Fxy, 1)
  @test parent(p) === Fxy

  F = GF(13)
  E = elliptic_curve_from_j_invariant(F(1))
  E = elliptic_curve(F, [1, 0, 0, 8, 6])
  Fx, x = F["x"]
  g = x^18 + 11*x^16 + 7*x^15 + 6*x^13 + x^12 + 9*x^11 + 12*x^10 + 8*x^9 + 3*x^8 + 4*x^7 + 4*x^6 + 5*x^5 + 7*x^4 + 3*x^3 + 8*x^2 + 6*x + 5
  i = isogeny_from_kernel(E, g)
  EE = codomain(i)
  @test degree(i) == 37
  classical_modular_polynomial(37)(j_invariant(E), j_invariant(EE))

  @test_throws ArgumentError classical_modular_polynomial(-1)
  @test_throws ArgumentError classical_modular_polynomial(0)
  @test_throws ArgumentError classical_modular_polynomial(60)
end

@testset "Atkin" begin
  Zxy, (x, y) = ZZ["x", "y"]
  p = @inferred atkin_modular_polynomial(2)
  @test base_ring(p) == ZZ
  @test p(x, y) == x^3 - x^2*y + 744*x^2 - x*y + 184512*x + y^2 + 7256*y + 15252992
  # test caching
  p = @inferred atkin_modular_polynomial(2)
  @test base_ring(p) == ZZ
  @test p(x, y) == x^3 - x^2*y + 744*x^2 - x*y + 184512*x + y^2 + 7256*y + 15252992

  p = @inferred atkin_modular_polynomial(23)
  @test constant_coefficient(p) == 1073741824
  p = @inferred atkin_modular_polynomial(223)
  @test constant_coefficient(p) == 15152690493256589832960153283553072259220674788850853681254083433291324627559120896000000000000

  @test total_degree.(atkin_modular_polynomial.([2, 3, 5, 7, 11, 13])) == [3, 4, 6, 8, 12, 14]

  p = @inferred atkin_modular_polynomial(Zxy, 2)
  @test parent(p) === Zxy

  Fxy, (x, y) = GF(2)["x", "y"]
  p = @inferred atkin_modular_polynomial(Fxy, 2)
  @test parent(p) === Fxy

  @test_throws ArgumentError atkin_modular_polynomial(-1)
  @test_throws ArgumentError atkin_modular_polynomial(0)
  @test_throws ArgumentError atkin_modular_polynomial(60)
  @test_throws ArgumentError atkin_modular_polynomial(1)
  @test_throws ArgumentError atkin_modular_polynomial(401)
end
