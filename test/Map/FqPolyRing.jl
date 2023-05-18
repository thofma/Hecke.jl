function randpoly(R::Union{ fqPolyRepPolyRing, FqPolyRepPolyRing }, dmax::Int)
  r = R()
  F = base_ring(R)
  d = rand(0:dmax)
  for i = 0:d
    setcoeff!(r, i, rand(F))
  end
  return r
end

@testset "Extensions of finite fields" begin
  Fp = Native.GF(2)
  Fpx, x = Fp["x"]
  f = x^3 + x + 1
  Fq = fqPolyRepField(f, :$)
  a = gen(Fq)
  Fqy, y = Fq["y"]
  g = y^3 + a*y + a^2
  G, FqytoG = Hecke.field_extension(g)
  @test characteristic(G) == 2
  @test degree(G) == 9
  GtoFqy = pseudo_inv(FqytoG)

  # Check if FqytoG does something reasonable with constant polynomials
  @test iszero(FqytoG(Fqy(1))^8 - FqytoG(Fqy(1)))
  @test iszero(FqytoG(Fqy(a))^8 - FqytoG(Fqy(a)))
  @test iszero(FqytoG(Fqy(a^2))^8 - FqytoG(Fqy(a^2)))

  # Check if FqytoG is linear
  for i = 1:5
    h1 = randpoly(Fqy, 5)
    h2 = randpoly(Fqy, 5)
    @test mod(h1, g) == GtoFqy(FqytoG(h1))
    @test mod(h2, g) == GtoFqy(FqytoG(h2))
    @test FqytoG(h1 + h2) == FqytoG(h1) + FqytoG(h2)
    @test FqytoG(h1*h2) == FqytoG(h1)*FqytoG(h2)
  end
  @test iszero(FqytoG(Fqy()))

  # Now everything with FqFiniteFields
  Fp = Native.GF(ZZRingElem(2))
  Fpx, x = Fp["x"]
  f = x^3 + x + 1
  Fq = FqPolyRepField(f, :$)
  a = gen(Fq)
  Fqy, y = Fq["y"]
  g = y^3 + a*y + a^2
  G, FqytoG = Hecke.field_extension(g)
  @test characteristic(G) == 2
  @test degree(G) == 9
  GtoFqy = pseudo_inv(FqytoG)

  # Check if FqytoG does something reasonable with constant polynomials
  @test iszero(FqytoG(Fqy(1))^8 - FqytoG(Fqy(1)))
  @test iszero(FqytoG(Fqy(a))^8 - FqytoG(Fqy(a)))
  @test iszero(FqytoG(Fqy(a^2))^8 - FqytoG(Fqy(a^2)))

  # Check if FqytoG is linear
  for i = 1:5
    h1 = randpoly(Fqy, 5)
    h2 = randpoly(Fqy, 5)
    @test mod(h1, g) == GtoFqy(FqytoG(h1))
    @test mod(h2, g) == GtoFqy(FqytoG(h2))
    @test FqytoG(h1 + h2) == FqytoG(h1) + FqytoG(h2)
    @test FqytoG(h1*h2) == FqytoG(h1)*FqytoG(h2)
    @test iszero(FqytoG(Fqy()))
  end
end
