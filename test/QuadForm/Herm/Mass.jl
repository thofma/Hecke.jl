@testset "Mass" begin

  #
  # Examples from arguments checks: indefinite and rank 0 cases
  #

  Qx, x = polynomial_ring(FlintQQ, "x")
  f = x^2 - 2
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2 - a*t + 1
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 3, 3, [-1, 0, 0, 0, 1, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [2, 0, 0]), map(E, [a, 0, 0]), map(E, [b + 1, 0, 0]), map(E, [a*b + a, 0, 0]), map(E, [0, 10, 0]), map(E, [0, 10*a, 0]), map(E, [0, 2*b + 6*a + 10, 0]), map(E, [0, a*b + 5*a + 6, 0]), map(E, [0, 5, 5]), map(E, [0, 5*a, 5*a]), map(E, [0, b + 3*a, b + 3*a]), map(E, [0, a*b + 6, a*b + 6])]
  L = hermitian_lattice(E, gens, gram = D)
  @test !is_definite(L)
  @test_throws ArgumentError mass(L)

  D = matrix(E, 0, 0, [])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[]
  L = hermitian_lattice(E, gens, gram = D)
  @test is_definite(L)
  @test rank(L) == 0
  @test @inferred mass(L) == 1

  #
  # Bunch of examples
  #

  K, a = rationals_as_number_field()
  Kt, t = polynomial_ring(K, "t")
  g = t^2 + 5
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 2])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [b + 8, b + 9, 0]), map(E, [-25*b + 66, -51//2*b + 171//2, -5//2*b + 1]), map(E, [104*b + 150, 132*b + 145, 5//2*b + 35//2]), map(E, [529*b - 47, 1243//2*b - 437//2, 28*b + 95//2])]
  L = hermitian_lattice(E, gens, gram = D)
  @test is_definite(L)
  m = @inferred mass(L)
  @test m == sum([inv(QQFieldElem(automorphism_group_order(LL))) for LL in genus_representatives(L)])


  K, a = rationals_as_number_field()
  Kt, t = polynomial_ring(K, "t")
  g = t^2 + 2
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [-11*b - 18, 5*b - 8, 0, 0]), map(E, [-763//4*b - 373, 471//4*b - 279//2, -3//2*b + 5, 0]), map(E, [-205589//4*b - 45927, 54261//4*b - 71509//2, -13*b + 1018, -1//2*b + 2]), map(E, [-267023*b + 283211, -206429//2*b - 168273, 14671//4*b + 2083, 25//4*b + 15//2])]
  L = hermitian_lattice(E, gens, gram = D)
  m = @inferred mass(L)
  @test m == 1//512

  D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [14*b - 18, 8*b - 10, 0, 0]), map(E, [85//2*b - 493//2, 25*b - 277//2, 1, 0]), map(E, [-399//4*b - 2843//2, -205//4*b - 803, 11//4*b + 8, -1//4*b + 3//2]), map(E, [13929//2*b - 6826, 3955*b - 3803, -121//4*b + 61, -35//4*b + 7//2])]
  L = hermitian_lattice(E, gens, gram = D)
  m = @inferred mass(L)
  @test m == 1//512

  D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [-9*b - 38, 3*b + 8, 0, 0]), map(E, [-1//2*b - 5//2, -1//2, 1, 0]), map(E, [-716*b - 173, 329//2*b, -1//4*b + 1//2, -1//4*b]), map(E, [59*b - 84, -11*b + 22, 0, 0])]
  L = hermitian_lattice(E, gens, gram = D)
  m = @inferred mass(L)
  @test m == sum([inv(QQFieldElem(automorphism_group_order(LL))) for LL in genus_representatives(L)])

  D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [-6*b - 38, 4*b + 10, 0, 0]), map(E, [1321//4*b - 2323//2, -91//4*b + 369, -1//2*b, 0]), map(E, [-2089//2*b + 5256, -23*b - 1610, 5//4*b - 5//2, 5//4*b]), map(E, [6376*b + 13976, -2645*b - 3174, -3//2*b - 9, 5//2*b - 4])]
  L = hermitian_lattice(E, gens, gram = D)
  m = @inferred mass(L)
  @test m == sum([inv(QQFieldElem(automorphism_group_order(LL))) for LL in genus_representatives(L)])

  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [-2*b-2, b+6, 0]), map(E, [0, 1, 1]), map(E, [b-6, -6*b+6, 0])]
  L = hermitian_lattice(E, gens, gram = D)
  m = @inferred mass(L)
  @test m == 1//32

  g = t^2 + 1
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [8*b + 14, 4*b + 10, 0, 0]), map(E, [57*b + 443//2, 17*b + 303//2, -3//2*b + 3//2, 0]), map(E, [5//2*b - 7//2, b - 2, -3//2*b + 1, 3//2*b]), map(E, [1//2*b - 3, -3//2, -1//2*b + 1, b - 1//2])]
  L = hermitian_lattice(E, gens, gram = D)
  m = @inferred mass(L)
  @test m == sum([inv(QQFieldElem(automorphism_group_order(LL))) for LL in genus_representatives(L)])

  D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [1, 1, 0, 0]), map(E, [-3*b + 5, 0, 8, 0]), map(E, [-40*b - 24, 0, -129//2*b + 2, -3//2*b + 1]), map(E, [-312*b - 208, 0, -1037//2*b - 17//2, -25//2*b + 15//2])]
  L = hermitian_lattice(E, gens, gram = D)
  m = @inferred mass(L)
  @test m == sum([inv(QQFieldElem(automorphism_group_order(LL))) for LL in genus_representatives(L)])

  D = matrix(E, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [-b - 2, 1, 0, 0]), map(E, [-9*b - 9, 0, -8, 0]), map(E, [-30*b - 24, 0, -9//2*b - 31//2, -1//2*b - 3//2]), map(E, [-48*b - 96, 0, 13//2*b - 89//2, 1//2*b - 9//2])]
  L = hermitian_lattice(E, gens, gram = D)
  @test is_definite(L)
  m = @inferred mass(L)
  @test m == sum([inv(QQFieldElem(automorphism_group_order(LL))) for LL in genus_representatives(L)])

  D = matrix(E, 6, 6, [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [-11*b + 1, -3*b + 1, 0, 0, 0, 0]), map(E, [-42*b + 27//2, -4*b + 17//2, 3//2*b + 13//2, 0, 0, 0]), map(E, [-2074*b + 4314, 370*b + 952, 624*b + 368, 7*b - 1, 0, 0]), map(E, [-1//2, -1//2, 0, 1//2*b - 1//2, 1, 0]), map(E, [-64401//2*b - 379225, -127585//2*b - 50257, -57600*b, -440*b + 352, -1//2*b - 1, -1//2*b - 1]), map(E, [178435*b + 414553, 90613*b + 32617, 64800*b - 21600, 363*b - 561, b + 1, b + 1])]
  L = hermitian_lattice(E, gens, gram = D)
  m = @inferred mass(L)
  @test m == 1//147456


  Qx, x = polynomial_ring(FlintQQ, "x")
  f = x^2-3
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2+1
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [(-1//2*a-1//2)*b+(1//2*a+5//2), -1, 0]), map(E, [(a-9)*b+ 15*a+3, 0, -a*b+ 8*a+13]), map(E, [(-1610*a+2990)*b + 2070*a-2990, 0, (-68*a+393)*b + 19*a+462])]
  L = hermitian_lattice(E, gens, gram = D)
  m = @inferred mass(L)
  @test m == 1//108


  Qx, x = polynomial_ring(FlintQQ, "x")
  f = x^4-x^3-4*x^2+4*x+1
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2+(a^3 - 1*a^2 - 4*a + 5)
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [1, 0, 0]), map(E, [0, 1, 0]), map(E, [0, 0, 1])]
  L = hermitian_lattice(E, gens, gram = D)
  m = @inferred mass(L)
  @test m == 1//10125

end

