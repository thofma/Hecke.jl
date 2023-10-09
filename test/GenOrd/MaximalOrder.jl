@testset "Qt" begin
  qt, t = rational_function_field(QQ, "t")
  qtx, x = polynomial_ring(qt, "x")
  f = x^4 + t*x^3 - 6*x^2 - t*x + 1
  F, a = function_field(f, "a")
  O = integral_closure(Hecke.localization(qt, degree), F)
  b = basis(O, F)
  mp = map(minpoly, b)
  @test all(i->iszero(mp[i](b[i])), 1:length(b))

  integral_closure(parent(numerator(t)), F)
  integral_closure(Hecke.Globals.Zx, F)
  factor(F, F.pol)
end

@testset "FldNum" begin
  R = Hecke.localization(ZZ, 13)
  K, _ = wildanger_field(3, 9*13^2)
  O = integral_closure(R, K)
  b = basis(O, K)
  mp = map(minpoly, b)
  @test all(i->iszero(mp[i](b[i])), 1:length(b))
end

@testset "FldFin" begin
  for q = [GF(17), GF(next_prime(ZZRingElem(10)^30)), finite_field(5, 2)[1], finite_field(next_prime(ZZRingElem(10)^25), 2, "a", cached = false)[1]]
    qt, t = rational_function_field(q, "t", cached = false)
    qtx, x = polynomial_ring(qt, cached = false)
    f = x^3+(t+1)^5*(x+1)+(t^2+t+1)^7
    F, a = function_field(f, "a", cached = false)
    integral_closure(parent(numerator(t)), F)
    integral_closure(localization(qt, degree), F)
  end

  k = GF(5)
  kx, x = rational_function_field(k, "x")
  kt = parent(numerator(x))
  ky, y = polynomial_ring(kx, "y")
  F, a = function_field(y^3+(4*x^3 + 4*x^2 + 2*x +2)*y^2 + (3*x+3)*y +2)
  Ofin = integral_closure(kt, F)
  R = localization(base_ring(F),degree)
  Oinfi = integral_closure(R,F)
end
