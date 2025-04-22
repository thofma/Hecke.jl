@testset "Embeddings" begin
  Qx, x = QQ["x"]
  K, a = number_field(x^3 - 2, "a")
  K2, (a2, ) = number_field([x^3 - 2], "a")
  QQx, x = Hecke.rationals_as_number_field()[1]["x"]
  K3, a3 = number_field(x^3 - 2, "a")
  K4, (a4, ) = number_field([x^3 - 2], "a")
  # Let's go a bit crazy with the type of the base field
  for (K, a) in [(K, a), (K2, a2), (K3, a3), (K4, a4)]
    Kt, t = K["t"]
    g = t^3 + a*t + 5
    L, b = number_field(g, "b")
    r, s = @inferred signature(L)
    @test (r, s) == (1, 4)

    emb = @inferred complex_embeddings(L)
    @test emb === complex_embeddings(L)
    @test (@inferred number_field(emb[1])) === L

    # isreal
    @test length(real_embeddings(L)) == 1
    @test @inferred isreal(emb[1])
    @test count(isreal, emb) == 1
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
    @test_throws ArgumentError restrict(emb[1], number_field(x^2 - 2, "a", cached = false)[1])

    # compare with complex_embeddings of absolute field
    Labs, LabstoL = @inferred absolute_simple_field(L)
    embabs = complex_embeddings(Labs)
    ainLabs = LabstoL\(L(a))
    binLabs = LabstoL\b

    for e in emb
      imageofb = @inferred e(b)
      @test overlaps(conj(e)(b), conj(e(b)))
      imageofa = e(L(a))
      @test count(ee -> overlaps(ee(binLabs), imageofb) && overlaps(ee(ainLabs), imageofa), embabs) == 1
      @test Hecke.radiuslttwopower(e(b, 128), -128)
    end

    # restrict along morphism
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

    z = (a + b)^100
    for p in [32, 128, 256, 1024]
      for e in emb
        fn = evaluation_function(e, p)
        @test Hecke.radiuslttwopower(fn(z), -p)
        c = e(z, p)
        @test Hecke.radiuslttwopower(c, -p)
      end
    end
  end

  # More complicated restriction

  Qx, x = QQ["x"]
  K, a = number_field(x^2 - 2, "a")
  L, b = number_field(polynomial(K, [-3, 0, 0, 1], cached = false))
  M, c = number_field(polynomial(L, [-5, 0, 1], cached = false))
  emb = complex_embeddings(M)
  @test Set([restrict(e, L) for e in emb]) == Set(complex_embeddings(L))
  @test Set([restrict(e, K) for e in emb]) == Set(complex_embeddings(K))

  # Creation

  Qx, x = QQ["x"]
  K, a = number_field(x^2 - 2, "a")
  L, b = number_field(polynomial(K, [-3, 0, 1], cached = false))
  for e in complex_embeddings(L)
    @test complex_embedding(L, restrict(e, K), e(b)) == e
  end
end
