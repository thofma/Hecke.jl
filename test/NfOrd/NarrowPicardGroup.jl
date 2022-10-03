@testset "Narrow Picard group of non-maximal orders" begin
  D = [-97, -95, -94, -93, -91, -89, -87, -86, -85, -83, -82, -79, -78, -77, -74, -73, -71, -70, -69, -67, -66, -65, -62, -61, -59, -58, -57, -55, -53, -51, -47, -46, -43, -42, -41, -39, -38, -37, -35, -34, -33, -31, -30, -29, -26, -23, -22, -21, -19, -17, -15, -14, -13, -11, -10, -7, -6, -5, -3, -2, 1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, 17, 19, 21, 22, 23, 26, 29, 30, 31, 33, 34, 35, 37, 38, 39, 41, 42, 43, 46, 47, 51, 53, 55, 57, 58, 59, 61, 62, 65, 66, 67, 69, 70, 71, 73, 74, 77, 78, 79, 82, 83, 85, 86, 87, 89, 91, 93, 94, 95, 97]
  Qx, x = QQ["x"]
  for d in D
    OK = maximal_order(number_field(x^2 + d)[1])
    C = narrow_class_group(OK)[1]
    CC = Hecke.narrow_picard_group(OK)[1]
    @test is_isomorphic(C, CC)
  end

  K = number_field(x^4 + 2*x^3 - 35*x^2 - 36*x + 5, "a", cached = false)[1]
  E = equation_order(K)
  @test order(picard_group(E)[1]) == 1
  C, _dlog, _exp = Hecke.narrow_picard_group(E)
  for i in 1:10
    c = rand(C)
    @test _dlog(_exp(c)) == c
  end

  Qx, x = QQ["x"]
  K = number_field(x^2 - 4 * 9 * 13, "a", cached = false)[1]
  E = equation_order(K)
  C, _dlog, _exp = Hecke.narrow_picard_group(E)
  for i in 1:10
    c = rand(C)
    @test _dlog(_exp(c)) == c
  end

  f = x^2 - 136*x + 4590
  E = equation_order(f, cached = false)
  C, _dlog, _exp = Hecke.narrow_picard_group(E)
  @test length(unique(_exp.(C))) == 4
end
