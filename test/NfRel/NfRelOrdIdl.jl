@testset "Relative ideals" begin
  Qx, x = FlintQQ["x"]
  f = x^2 + 12*x - 92
  K, a = NumberField(f, "a")
  OK = MaximalOrder(K)
  Ky, y = K["y"]
  g = y^2 - 54*y - 73
  L, b = NumberField(g, "b")
  OL = MaximalOrder(L)

  coeff_ideals = [ deepcopy(Hecke.pseudo_basis(OL, Val{false})[i][2]) for i = 1:2 ]
  PM = Hecke.PseudoMatrix(matrix(K, [1 0; 0 1]), coeff_ideals)
  PM1 = pseudo_hnf(Hecke.PseudoMatrix(matrix(K, [3 0; 0 3]), coeff_ideals), :lowerleft, true)
  PM2 = pseudo_hnf(Hecke.PseudoMatrix(matrix(K, [6 0; 0 6]), coeff_ideals), :lowerleft, true)
  PM3 = pseudo_hnf(Hecke.PseudoMatrix(matrix(K, [9 0; 0 9]), coeff_ideals), :lowerleft, true)
  A = ideal(OL, PM1)
  B = ideal(OL, PM2)
  C = ideal(OL, PM3)

  @test A == B + C
  @test B == intersection(A, B)
  @test K(2)*C == A*B
  @test inv(C)*C == ideal(OL, PM)
  @test norm(A) == OK(9)*OK
end

