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
    #= crashes julia in 1.6
    integral_closure(Hecke.Globals.Zx, F)
    factor(F.pol, F)
    =#
  end

  @testset "FldNum" begin
    R = Hecke.Localization(ZZ, 13)
    K, _ = wildanger_field(3, 9*13^2)
    O = integral_closure(R, K)
    b = basis(O, K)
    mp = map(minpoly, b)
    @test all(i->iszero(mp[i](b[i])), 1:length(b))
  end
end
