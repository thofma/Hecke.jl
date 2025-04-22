@testset "Complex embeddings (generic)" begin
  K1, a1 = QQ, one(QQ)
  OK1 = ZZ
  K2, a2 = rationals_as_number_field()
  OK2 = maximal_order(K2)
  Qx, x = QQ["x"]
  K3, (a3, ) = number_field([x - 1])
  OK3 = maximal_order(K3)
  Kt, t = K2["t"]
  K4, (a4, ) = number_field([t - 1])
  OK4 = maximal_order(K4)

  fields = ((K1, a1, OK1), (K2, a2, OK2), (K3, a3, OK3), (K4, a4, OK4))

  @testset for (K, a, OK) in fields
    embs = @inferred complex_embeddings(K)
    @test length(embs) == 1
    embs = @inferred real_embeddings(K)
    @test length(embs) == 1
    e = embs[1]
    @test @inferred is_real(e)
    @test !(@inferred is_imaginary(e))
    @test (@inferred number_field(e)) === K
    @test sprint(show, "text/plain", e) isa String
    @test count(isequal('\n'), sprint(show, e)) == 0

    @test restrict(e, QQ) == complex_embeddings(QQ)[1]

    if K !== QQ
      eQQ = hom(QQ, K)
      id = hom(K, K)
      ee = complex_embeddings(QQ)[1]
      @test compose(eQQ, e) == ee
      @test compose(id, e) == e
    end

    for b in (a, FacElem(a), OK(a))
      @test contains(e(a), 1)
      @test @inferred is_positive(b, e)
      @test @inferred !is_negative(b, e)
      @test @inferred is_totally_positive(b)
      @test (@inferred signs(b)) == Dict(e => 1)
      @test (@inferred signs(b, real_embeddings(K))) == Dict(e => 1)
      @test (@inferred sign(b, e) == 1)
      @test contains(e(b), 1)
      if !(b isa FacElem)
        @test (@inferred sign(zero(parent(b)), e) == 0)
      end
      @test contains(log(abs(e))(b), 0)
    end

    for b in (-a, FacElem(-a), OK(-a))
      @test @inferred !is_positive(b, e)
      @test @inferred is_negative(b, e)
      @test @inferred !is_totally_positive(b)
      @test (@inferred signs(b)) == Dict(e => -1)
      @test (@inferred signs(b, real_embeddings(K))) == Dict(e => -1)
      @test (@inferred sign(b, e) == -1)
      @test contains(e(b), -1)
    end

    c = FacElem(K(2))^1000 * FacElem(K(3))^-1000 * FacElem(K(5))^1000
    @test (@inferred e(c)) isa AcbFieldElem

    c = complex_conjugation(K)
    if !(K isa QQField)
      @test c == id_hom(K)
    end
  end

  K, a = quadratic_field(-1)
  e = complex_embeddings(K)[1]
  @test overlaps(log(abs(e))(FacElem(K(2))^1000000), 1000000 * log(abs(e(K(2)))))

  K, a = cyclotomic_field(5)
  k, ktoK = Hecke.subfield(K, [a + inv(a)])
  b = gen(k)
  e = complex_embeddings(k)[1]
  eext = extend(e, ktoK)
  @test all(overlaps(c(ktoK(b)), e(b)) for c in eext)

  Qx, x = QQ["x"]
  K, _ = rationals_as_number_field()
  Kt, t = K["t"]
  K1, = number_field(t^2 - 2)
  K2, = number_field([t^2 - 2, t^2 - 3])
  K3, = number_field([x^2 - 2, x^2 - 3])
  for K in Any[K1, K2, K3]
    c = complex_conjugation(K)
    @test c == id_hom(K)
  end

  K1, = number_field(t^2 + 2)
  K2, = number_field([t^2 + 2])
  K3, = number_field([x^2 + 2])
  for K in Any[K1, K2, K3]
    c = complex_conjugation(K)
    @test c != id_hom(K)
  end
end
