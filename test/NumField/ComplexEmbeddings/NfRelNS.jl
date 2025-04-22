@testset "Embeddings" begin
  Qx, x = QQ["x"]
  K, a = number_field(x^3 + 2, "a")
  K2, (a2, ) = number_field([x^3 + 2], "a")
  QQx, x = Hecke.rationals_as_number_field()[1]["x"]
  K3, a3 = number_field(x^3 + 2, "a")
  K4, (a4, ) = number_field([x^3 + 2], "a")
  # Let's go a bit crazy with the type of the base field
  for (K, a) in [(K, a), (K2, a2), (K3, a3), (K4, a4)]
    Kt, t = K["t"]
    L, b = number_field([t^2 - 3, t^2 - t - 50], "b")

    r, s = @inferred signature(L)
    @test (r, s) == (4, 4)

    emb = @inferred complex_embeddings(L)
    @test emb === complex_embeddings(L)
    @test (@inferred number_field(emb[1])) === L

    # isreal
    @test length(real_embeddings(L)) == 4
    @test @inferred isreal(emb[1])
    @test count(isreal, emb) == 4
    @test count(!isreal, emb) == 8
    @test count(is_imaginary, emb) == 8

    for e in emb
      if isreal(e)
        @test (@inferred conj(e)) == e
      else
        @test conj(e) in emb && conj(e) != e
      end
    end

    # print
    sprint(show, emb[1])
    sprint(show, MIME"text/plain"(), emb[1])

    # restrict
    @test number_field(@inferred restrict(emb[1], K)) === K
    Set([restrict(e, K) for e in emb]) == Set(complex_embeddings(K))
    Set([restrict(e, L) for e in emb]) == Set(emb)
    @test_throws ArgumentError restrict(emb[1], number_field(x^2 - 3, "a", cached = false)[1])

    embK = complex_embeddings(K)
    h = hom(K, L)
    for e in embK
      eext = @inferred extend(e, h)
      @test length(eext) == 4
      @test all(f -> h * f == e, eext)
    end

    # compare with complex_embeddings of absolute field
    Labs, LabstoL = @inferred absolute_simple_field(L)
    embabs = complex_embeddings(Labs)
    ainLabs = LabstoL\(L(a))
    binLabs = [ LabstoL\bb for bb in b]
    @inferred emb[1](b[1])

    for e in emb
      imageofb = e.(b)
      @test all(overlaps.(conj(e).(b), conj.(e.(b))))
      imageofa = e(L(a))
      @test count(ee -> all(overlaps.(ee.(binLabs), imageofb)) && overlaps(ee(ainLabs), imageofa), embabs) == 1
      @test all(Hecke.radiuslttwopower.(e.(b, 128), -128))
    end

    # restrict along a morphism
    LtoLabs = inv(LabstoL)
    for e in embabs
      ee = @inferred restrict(e, LtoLabs)
      @test overlaps(ee(LabstoL(gen(Labs))), e(gen(Labs)))
      @test ee == LtoLabs * e
      @test_throws ArgumentError restrict(e, LabstoL)
    end

    for e in embabs
      ee = @inferred extend(e, LabstoL)
      @test length(ee) == 1
      @test LabstoL * ee[1] == e
    end

    for e in emb
      ee = @inferred extend(e, LtoLabs)
      @test length(ee) == 1
      @test LtoLabs * ee[1] == e
    end

    z = (a + b[1] + b[2])^100
    for p in [32, 128, 256, 1024]
      for e in emb
        fn = evaluation_function(e, p)
        @test Hecke.radiuslttwopower(fn(z), -p)
        c = e(z, p)
        @test Hecke.radiuslttwopower(c, -p)
      end
    end
  end

  # Some non-trivial example
  Qx, x = QQ["x"]
  f = x^2+1
  K, a = number_field(f, cached = false, check = false);
  Kt, t = K["t"]
  f1 = t^3 + 249*t - 830
  f2 = t^7 - 1162*a*t^5 + (-29050*a + 29050)*t^4 - 542073*t^3 + (-14412286*a - 14412286)*t^2 - 80411562*a*t + 3869576532*a - 3869576532
  L, gL = number_field([f1, f2], cached = false)
  s, t = gL
  el = (1//978369084*a + 5//978369084)*t^6 + (-4//7411887*a + 89//978369084)*t^5 + (3181//489184542*a - 2753//489184542)*t^4 + (128197//978369084*a + 52165//81530757)*t^3 + (-6920957//489184542*a + 273422//22235661)*t^2 + (1243580//9058973*a - 2545783//18117946)*t + 67078685//27176919*a + 133062707//27176919
  Labs, LabstoL = @inferred absolute_simple_field(L)
  embabs = complex_embeddings(Labs)
  emb = complex_embeddings(L)
  elinLabs = LabstoL\el

  for e in emb
    @test count(ee -> overlaps(ee(elinLabs), e(el)), embabs) == count(ee -> overlaps(ee(el), e(el)), emb)
  end

  Qx, x = QQ["x"]
  K, a = number_field(x^2 - 2, "a")
  L, b = number_field(polynomial(K, [-3, 0, 0, 1], cached = false))
  M, c = number_field([polynomial(L, [-5, 0, 1], cached = false)])
  emb = complex_embeddings(M)
  @test Set([restrict(e, L) for e in emb]) == Set(complex_embeddings(L))
  @test Set([restrict(e, K) for e in emb]) == Set(complex_embeddings(K))

  # Creation

  Qx, x = QQ["x"]
  K, a = number_field(x^2 - 2, "a")
  L, b = number_field([polynomial(K, [-3, 0, 1], cached = false)])
  for e in complex_embeddings(L)
    @test complex_embedding(L, restrict(e, K), e.(b)) == e
  end
end
