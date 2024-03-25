test_elem(E::Hecke.EmbeddedNumField) = E(rand(number_field(E), -10:10))

@testset "Embedded number field" begin
  Qx, x = QQ["x"]
  K, _a = number_field(x^2 - 2, "a")
  i = Hecke.real_embedding(K, 1.41)
  E, a = Hecke.embedded_field(K, i)
  @test is_positive(a)
  @test !is_negative(a)
  @test sign(a) == one(E)
  @test sign(-a) == -one(E)
  @test sign(zero(E)) == zero(E)
  @test abs(a) == a
  @test abs(-a) == a
  @test abs(zero(E)) == zero(E)
  @test a > 0
  @test a >= 0
  @test !(a > a)
  @test !(a < 0)
  @test !(a <= 0)
  @test sprint(show, E) isa String
  @test sprint(show, "text/plain", E) isa String
  @test sprint(show, a) isa String
  @test sprint(show, "text/plain", a) isa String
  @test E([1, 2]) == 1 + 2*a
  test_Ring_interface(E)
  # trigger expressify
  Et, t = E["t"]
  @test sprint(show, a * t) isa String
  @test sprint(show, "text/plain", a * t) isa String

  # other constructor
  E, a = Hecke.embedded_number_field(x^2 - 2, 1.41)
  E, a = Hecke.embedded_number_field(x^2 - 2, big"1.41")
  E, a = Hecke.embedded_number_field(x^2 - 2, (0, 3))
  E, a = Hecke.embedded_number_field(x^2 - 2, (1, 3.0))
  E, a = Hecke.embedded_number_field(x^2 - 2, (1, Inf))
  @test_throws ErrorException Hecke.embedded_number_field(x^2 - 2, (2, 3))
  @test_throws ErrorException Hecke.embedded_number_field(x^2 - 2, (-3, 3))
  @test_throws ErrorException Hecke.embedded_number_field(x^2 - 2, 0.0)

  K, a = number_field([x^2 - 2, x^2 - 3], "a")
  i = Hecke.real_embedding(K, [1.41, -2.0])
  E, a = Hecke.embedded_field(K, i)
  @test a[1] > 0 && a[2] < 0
  @test sprint(show, E) isa String
  @test sprint(show, "text/plain", E) isa String
  @test sprint(show, a[1]) isa String
  @test sprint(show, "text/plain", a[1]) isa String
  test_Ring_interface(E)

  # other constructors
  E, a = Hecke.embedded_number_field([x^2 - 2, x^2 - 3], [1.41, 1.6])
  E, a = Hecke.embedded_number_field([x^2 - 2, x^2 - 3], [(-Inf, 0), (0, Inf)])
  @test_throws ErrorException Hecke.embedded_number_field([x^2 - 2, x^2 - 3], [(0, 1), (0, Inf)])
  @test_throws ErrorException Hecke.embedded_number_field([x^2 - 2, x^2 - 3], [(0, Inf), (0, 1)])
  @test_throws ErrorException Hecke.embedded_number_field([x^2 - 2, x^2 - 3], [(-3, 3), (-3, 3)])

  E, a = Hecke.embedded_number_field(x^100 - 2, (0, Inf))
  # To trigger the sharpening in the precision
  @test 1 + inv(a)^10000 > 1 + inv(a)^10001

  # Inexact comparisons
  @test 1 + inv(a)^10000 > 1 + 0.99^10001
  @test 1 + 0.99^10001 < 1 + inv(a)^10000
  @test !(2*a^0 < 2.0)
  @test !(1//2*a^0 < 0.5)
  @test !(2*a^0 > 2.0)
  @test !(1//2*a^0 > 0.5)
  @test a > 0.0
  @test !(a > 2.0)
  @test a < 2.0
  @test !(a < 0.0)

  E, a = Hecke.embedded_number_field([x^100 - 2, x^3 - 2], [(0, Inf), (0, Inf)])
  @test 1 + inv(a[1])^10000 > 1 + inv(a[1])^10001

  # Something more complicated
  k, = Hecke.rationals_as_number_field()
  kt, t = k["t"]
  K, _a = number_field(t^2 - 2)
  E, a = Hecke.embedded_field(K, real_embeddings(K)[1])
  @test a^2 > 0
  # promotion
  @test E(1) + k(1) == E(2)
  @test_throws ErrorException E(1) + one(GF(2))
  @test_throws ErrorException E(1) + K(1)
  ET, T = E["T"]
  @test parent(a * T^2 + a) === ET
  @test sprint(show, a * T^2) isa String
  @test sprint(show, "text/plain", a * T^2) isa String

  # coercion
  k, = Hecke.rationals_as_number_field()
  kt, t = k["t"]
  K, _a = number_field(t^2 - 2)
  E, a = Hecke.embedded_field(K, real_embeddings(K)[1])
  @test @inferred is_rational(a^0)
  @test !is_rational(a)
  @test (@inferred QQ(2*a^0)) == 2 * one(QQ)

  # roots and factor
  let
    Qx, x = QQ["x"]
    K, _a = number_field(x^2 - 2, "a")
    i = Hecke.real_embedding(K, 1.41)
    E, a = Hecke.embedded_field(K, i)
    Et, t = E["t"]
    @test issetequal(roots(t^2 - 2), [a, -a])
    fa = factor(t^2 - 2)
    @test unit(fa) * prod(g^e for (g, e) in fa) == t^2 - 2
    fa = factor(t^2 - a)
    @test unit(fa) * prod(g^e for (g, e) in fa) == t^2 - a
  end

  # floor, ceil, round
  let
    Qx, x = QQ["x"]
    K, a = embedded_number_field(x^2 - 2, 1.4)
    # element, floor, ceiling, round, rounddown, roundup, roundnear
    test_data = [(a, 1, 2, 1, 1, 2, 1), (K(1), 1, 1, 1, 1, 1, 1), (K(0), 0, 0, 0, 0, 0, 0), (K(1//2), 0, 1, 1, 0, 1, 0), (K(3//2), 1, 2, 2, 1, 2, 2), (K(-1//2), -1, 0, -1, -1, 0, 0)]
    for (e, f, c, r, rd, ru, rn) in test_data
      @test floor(e) == f && parent(floor(e)) === K
      @test floor(ZZRingElem, e) == f && floor(ZZRingElem, e) isa ZZRingElem
      @test ceil(e) == K(c) && parent(ceil(e)) === K
      @test ceil(ZZRingElem, e) == c && ceil(ZZRingElem, e) isa ZZRingElem
      @test round(e) == r && parent(round(e)) === K
      @test round(ZZRingElem, e) == r && round(ZZRingElem, e) isa ZZRingElem
      @test round(e, RoundDown) == rd && parent(round(e, RoundDown)) === K
      @test round(ZZRingElem, e, RoundDown) == rd && round(ZZRingElem, e, RoundDown) isa ZZRingElem
      @test round(e, RoundUp) == ru && parent(round(e, RoundUp)) === K
      @test round(ZZRingElem, e, RoundUp) == ru && round(ZZRingElem, e, RoundUp) isa ZZRingElem
      @test round(e, RoundNearest) == rn && parent(round(e, RoundNearest)) === K
      @test round(ZZRingElem, e, RoundNearest) == rn && round(ZZRingElem, e, RoundNearest) isa ZZRingElem
    end
  end
end
