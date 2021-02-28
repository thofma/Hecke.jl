@testset "Relative fractional ideals" begin
  Qx, x = FlintQQ["x"]
  f = x^2 + 12*x - 92
  K, a = number_field(f, "a")
  OK = maximal_order(K)
  Ky, y = K["y"]
  g = y^2 - 54*y - 73
  L, b = number_field(g, "b")
  OL = maximal_order(L)

  I = L(fmpq(1, 2))*OL
  @test denominator(I) == fmpz(2)
  @test Hecke.isintegral(I.den*I)

  PM = basis_pmatrix(OL)
  PM.matrix[1, 1] = K(fmpq(1, 2))
  PM.matrix[2, 1] = K()
  PM.matrix[2, 2] = K(fmpq(1, 3))
  PM = pseudo_hnf(PM, :lowerleft)
  J = fractional_ideal(OL, PM)
  @test denominator(J) == fmpz(6)
  @test Hecke.isintegral(J.den*J)

  @testset "Weird modulus" begin
    K, a = Hecke.rationals_as_number_field()
    Kt, t = K["t"]
    E, z = NumberField(t^2 + 1, "z")
    OE = Order(E, pseudo_matrix(matrix(K, 2, 2, [1, 0, 0, 1]), [1 * maximal_order(K), 2 * maximal_order(K)]))
    I = E(1) * OE
    @test I * I == I
    @test I + I == I
    @test isone(I//I)
  end
end
