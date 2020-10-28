@testset "Map/NumField.jl" begin
  # AnticNumberField -> AnticNumberField
  Qx, x = FlintQQ["x"]
  K, a = NumberField(x^2 - 2, "a")

  f = @inferred hom(K, K, -a)
  @test f(a) == -a

  @test_throws ErrorException hom(K, K, a + 1)

  f = @inferred hom(K, K, -a, inverse = (-a))
  @test f(a) == -a
  @test f\a == -a
  @test_throws ErrorException hom(K, K, a, inverse = a + 1)
  @test_throws ErrorException hom(K, K, a + 1, inverse = a)

  K, a = NumberField(x^4 - x^2 + 1, "a")
  k, b = NumberField(x^2 + 1, "b")
  f = @inferred hom(k, K, a^3)
  @test_throws ErrorException hom(k, K, a)
  @test f(b) == a^3

  # AnticNumberField -> NfRel{nf_elem}
  
  QQQ, q = NumberField(x - 1, "q")
  QQQt, t = QQQ["t"]
  K, a = NumberField(x^2 - 2, "a")
  L, b = NumberField(t^2 - 2, "b")
  h = hom(QQQ, K, one(K))

  f = @inferred hom(K, L, -b)
  @test f(a) == -b
  @test_throws ErrorException hom(K, L, b + 1)

  f = @inferred hom(K, L, -b, inverse = (one(K), -a))
  @test f(a) == -b
  @test f\b == -a

  f = @inferred hom(K, L, -b, inverse = (h, -a))
  @test f(a) == -b
  @test f\b == -a
  @test_throws ErrorException hom(K, L, -b, inverse = (one(K), a + 1))

  # NfRel{nf_elem} -> AnticNumberField

  K, a = NumberField(x^2 - 2, "a")
  Kt, t = K["t"]
  L, b = NumberField(t^2 - 3, "b")
  M, z = NumberField(x^4 - 10*x^2 + 1, "z")

  f = @inferred hom(L, M, 1//2*z^3 - 9//2*z, -1//2*z^3 + 11//2*z, inverse = b + L(a))
  @test f(L(a)) == 1//2*z^3 - 9//2*z
  @test f\(z) == b + L(a)
  @test f\(z^2) == (b + L(a))^2
  @test_throws ErrorException hom(L, M, one(M), one(M))
  @test_throws ErrorException hom(L, M, 1//2*z^3 - 9//2*z, -1//2*z^3 + 11//2*z, inverse = L(a))
  @test_throws ErrorException hom(L, M, one(M), -1//2*z^3 + 11//2*z, inverse = b + L(a))

  h = hom(K, M, 1//2*z^3 - 9//2*z)
  f = @inferred hom(L, M, h, -1//2*z^3 + 11//2*z, inverse = b + L(a))
  @test f(L(a)) == 1//2*z^3 - 9//2*z
  @test f\(z) == b + L(a)
  @test f\(z^3) == (b + L(a))^3
  @test_throws ErrorException hom(L, M, h, one(M))
  @test_throws ErrorException hom(L, M, h, -1//2*z^3 + 11//2*z, inverse = b)
  @test_throws ErrorException hom(L, M, one(M), -1//2*z^3 + 11//2*z, inverse = b + L(a))

  f = x^8 - 40*x^6 + 352*x^4 - 960*x^2 + 576
  M, z = NumberField(f, "z") # x^2 -2, x^2 - 3, x^2 - 5
  f = @inferred hom(L, M, 1//576*z^7 - 7//144*z^5 - 7//72*z^3 + 5//3*z, -1//96*z^7 + 37//96*z^5 - 61//24*z^3 + 15//4*z)
  @test_throws ErrorException hom(L, M, one(M), one(M))
  @test f(L(a)) == 1//576*z^7 - 7//144*z^5 - 7//72*z^3 + 5//3*z
  h = hom(K, M, 1//576*z^7 - 7//144*z^5 - 7//72*z^3 + 5//3*z)
  f = @inferred hom(L, M, h, -1//96*z^7 + 37//96*z^5 - 61//24*z^3 + 15//4*z)
  @test_throws ErrorException hom(L, M, h, one(M))
  @test f(L(a)) == 1//576*z^7 - 7//144*z^5 - 7//72*z^3 + 5//3*z

  # NfRel{nf_elem} -> NfRel{nf_elem}

  K, a = NumberField(x^2 - 2, "a")
  Kt, t = K["t"]
  L, b = NumberField(t^2 - 3, "b")

  f = @inferred hom(L, L, -b)
  @test f(b) == -b
  @test f(L(a)) == a
  f = @inferred hom(L, L, -b, inverse = -b)
  @test f(b) == -b
  @test f\b == -b
  @test_throws ErrorException hom(L, L, zero(L))
  @test_throws ErrorException hom(L, L, zero(L), inverse = b)
  @test_throws ErrorException hom(L, L, b, inverse = zero(L))

  f = @inferred hom(L, L, -a, -b, inverse = (-a, -b))
  @test_throws ErrorException hom(L, L, a + 1, -b, inverse = (-a, -b))
  @test_throws ErrorException hom(L, L, -a, b + 1, inverse = (-a, -b))
  @test_throws ErrorException hom(L, L, -a, -b, inverse = (a + 1, -b))
  @test f(L(a)) == L(-a)
  @test f(L(b)) == L(-b)
  @test f\(L(a)) == L(-a)
  @test f\(L(b)) == L(-b)

  f = @inferred hom(L, L, -b, inverse = (-b))
  @test f(L(a)) == L(a)
  @test f(L(b)) == L(-b)
  @test f\(L(a)) == L(a)
  @test f\(L(b)) == L(-b)

  LL, bb = NumberField(t^4 - 16*t^2 + 4, "b")
  f = @inferred hom(L, LL, 1//4*bb^3 - 7//2*bb)
  @test_throws ErrorException hom(L, LL, zero(LL))
  @test f(b) == 1//4*bb^3 - 7//2*bb
  @test f(L(a)) == LL(a)
  f = @inferred hom(L, LL, -a, 1//4*bb^3 - 7//2*bb)
  @test_throws ErrorException hom(L, LL, zero(K), 1//4*bb^3 - 7//2*bb)
  @test f(b) == 1//4*bb^3 - 7//2*bb
  @test f(L(a)) == LL(-a)

  # NfRel to NfRelNfRel
  
  Qx, x = QQ["x"]
  _K, a = NumberField(x^2 - 2, "a")
  _Ky, y = _K["y"]
  Ka, _b = NumberField(y^6 + 3*y^5 - 12*y^4 - 29*y^3 + (a + 60)*y^2 + (a + 75)*y - 5*a - 130, "_b")
  L, b = NumberField(y^3 + a * y + 5)
  Ly, y = L["y"]
  K, c = NumberField(y^2 + y + b - 5, "c")
  f = hom(Ka, K, c, inverse = (-_b^2 - _b + 5, _b))



end
