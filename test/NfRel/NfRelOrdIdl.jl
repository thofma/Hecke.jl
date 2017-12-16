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
  I1 = frac_ideal(OL, I, OK(1))
  A = ideal(OL, PM1)
  A1 = frac_ideal(OL, A, OK(1))
  B = ideal(OL, PM2)
  C = ideal(OL, PM3)
  C1 = frac_ideal(OL, C, OK(1))

  @test A == B + C
  @test B == intersection(A, B)
  @test K(2)*C == A*B
  @test inv(C)*C1 == I1
  @test norm(A) == OK(9)*OK
  @test norm(I) == OK(1)*OK
  D = divexact(C, B)
  D.num = K(2)*numerator(D)
  @test D == A1

  p = prime_decomposition(OK, fmpz(11))[1][1]
  (p1, e1), (p2, e2) = prime_decomposition(OL, p)
  @test e1 == 1 && e2 == 1
  @test p1*p2 == ideal(OL, L(1), L(1), frac_ideal(OK, p, 1), frac_ideal(OK, p, 1))
end

