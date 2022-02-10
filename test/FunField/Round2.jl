@testset "Round2" begin
  @testset "Qt" begin
    qt, t = RationalFunctionField(QQ, "t")
    qtx, x = PolynomialRing(qt, "x")
    f = x^4 + t*x^3 - 6*x^2 - t*x + 1
    F, a = FunctionField(f, "a")
    O = integral_closure(Hecke.Localization(qt, degree), F)
    b = basis(O, F)
    mp = map(minpoly, b)
    @test all(i->iszero(mp[i](b[i])), 1:length(b))

    integral_closure(parent(numerator(t)), F)
    integral_closure(Hecke.Globals.Zx, F)
    factor(F.pol, F)
  end

  @testset "FldNum" begin
    R = Hecke.Localization(ZZ, 13)
    K, _ = wildanger_field(3, 9*13^2)
    O = integral_closure(R, K)
    b = basis(O, K)
    mp = map(minpoly, b)
    @test all(i->iszero(mp[i](b[i])), 1:length(b))
  end

  @testset "FldFin" begin
    for q = [GF(17), GF(next_prime(fmpz(10)^30)), FiniteField(5, 2)[1], FiniteField(next_prime(fmpz(10)^25), 2, "a", cached = false)[1]]
      qt, t = RationalFunctionField(q, "t", cached = false)
      qtx, x = PolynomialRing(qt, cached = false)
      f = x^3+(t+1)^5*(x+1)+(t^2+t+1)^7
      F, a = FunctionField(f, "a", cached = false)
      integral_closure(parent(numerator(t)), F)
      integral_closure(Localization(qt, degree), F)
    end
  end
end
