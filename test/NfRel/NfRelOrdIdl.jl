@testset "Relative ideals" begin
  Qx, x = FlintQQ["x"]
  f = x^2 + 12*x - 92
  K, a = NumberField(f, "a")
  OK = MaximalOrder(K)
  Ky, y = K["y"]
  g = y^2 - 54*y - 73
  L, b = number_field(g, "b")
  OL = MaximalOrder(L)

  coeff_ideals = [ deepcopy(Hecke.pseudo_basis(OL, Val{false})[i][2]) for i = 1:2 ]
  PM = Hecke.PseudoMatrix(matrix(K, [1 0; 0 1]), coeff_ideals)
  PM1 = pseudo_hnf(Hecke.PseudoMatrix(matrix(K, [3 0; 0 3]), coeff_ideals), :lowerleft, true)
  PM2 = pseudo_hnf(Hecke.PseudoMatrix(matrix(K, [6 0; 0 6]), coeff_ideals), :lowerleft, true)
  PM3 = pseudo_hnf(Hecke.PseudoMatrix(matrix(K, [9 0; 0 9]), coeff_ideals), :lowerleft, true)
  I = ideal(OL, PM)
  I1 = frac_ideal(OL, PM)
  A = ideal(OL, PM1)
  A1 = frac_ideal(OL, PM1)
  B = ideal(OL, PM2)
  C = ideal(OL, PM3)
  C1 = frac_ideal(OL, PM3)

  @test A == B + C
  @test B == intersection(A, B)
  @test K(2)*C == A*B
  @test inv(C)*C1 == I1
  @test norm(A) == OK(9)*OK
  @test norm(I) == OK(1)*OK
  D = divexact(C, B)
  D = fmpz(2)*D
  @test D == A1

  p = prime_decomposition(OK, 11)[1][1]
  (p1, e1), (p2, e2) = prime_decomposition(OL, p)
  @test e1 == 1 && e2 == 1
  @test p1*p2 == p*OL

  Q, q = number_field(x, "q")
  Z = maximal_order(Q)
  Qy, y = Q["y"]
  g =  y^3 + 34*y^2 + 45*y + 98
  p = prime_decomposition(Z, 11)[1][1]
  L, b = number_field(g, "b")
  OL = maximal_order(L)
  (p1, e1), (p2, e2) = prime_decomposition(OL, p)
  @test e1 == 1 && e2 == 1
  @test p1*p2 == p*OL
  @test p1.splitting_type[2] == 2 || p2.splitting_type[2] == 2

  g = y^4 + 56*y^3 + 27*y^2 + -10*y + 56
  p = prime_decomposition(Z, 2)[1][1]
  L, b = number_field(g, "b")
  OL = maximal_order(L)
  (p1, e1), (p2, e2), (p3, e3) = prime_decomposition(OL, p)
  @test p1^e1*p2^e2*p3^e3 == p*OL
  @test p1.splitting_type[2] == 1 && p2.splitting_type[2] == 1 && p3.splitting_type[2] == 1
end
