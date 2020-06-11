@testset "Mass of hermitian lattices" begin
  Qx, x = PolynomialRing(FlintQQ, "x")
  f = x-1
  K, a = NumberField(f, "a", cached = false)
  Kt, t = PolynomialRing(K, "t")
  g = t^2+(2)
  E, b = NumberField(g, "b", cached = false)
  D = matrix(E, 3, 3, [(1), 0, 0, 0, (1), 0, 0, 0, (1)])
  gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [(-2)*b+(-2), b+(6), 0]), map(E, [0, (1), (1)]), map(E, [b+(-6), (-6)*b+(6), 0])]
  L = hermitian_lattice(E, generators = gens, gram_ambient_space = D)
  m = @inferred mass(L)
  @test m == 1//32

  Qx, x = PolynomialRing(FlintQQ, "x")
  f = x^2-3
  K, a = NumberField(f, "a", cached = false)
  Kt, t = PolynomialRing(K, "t")
  g = t^2+(1)
  E, b = NumberField(g, "b", cached = false)
  D = matrix(E, 3, 3, [(1), 0, 0, 0, (1), 0, 0, 0, (1)])
  gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [(-1//2*a-1//2)*b+(1//2*a+5//2), (-1), 0]), map(E, [(a-9)*b+(15*a+3), 0, (-a)*b+(8*a+13)]), map(E, [(-1610*a+2990)*b+(2070*a-2990), 0, (-68*a+393)*b+(19*a+462)])]
  L = hermitian_lattice(E, generators = gens, gram_ambient_space = D)
  m = @inferred mass(L)
  @test m == 1//108

  Qx, x = PolynomialRing(FlintQQ, "x")
  f = x^4-x^3-4*x^2+4*x+1
  K, a = NumberField(f, "a", cached = false)
  Kt, t = PolynomialRing(K, "t")
  g = t^2+(a^3 - 1*a^2 - 4*a + 5)
  E, b = NumberField(g, "b", cached = false)
  D = matrix(E, 3, 3, [(1), 0, 0, 0, (1), 0, 0, 0, (1)])
  gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [(1), 0, 0]), map(E, [0, (1), 0]), map(E, [0, 0, (1)])]
  L = hermitian_lattice(E, generators = gens, gram_ambient_space = D)
  m = @inferred mass(L)
  @test m == 1//10125
end
