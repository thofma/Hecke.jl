@testset "Embeddings" begin
  Qx, x = QQ["x"]
  L, b = number_field([x^2 - 2, x^2 - 3, x^3 + 2], "a")
  r, s = @inferred signature(L)
  @test (r, s) == (4, 4)
  @test complex_embeddings(L) === complex_embeddings(L)

  emb = @inferred complex_embeddings(L)
  @test (@inferred number_field(emb[1])) === L
  @test emb[1] == emb[1]
  @test emb[1] != emb[2]

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

  # compare with absolute simple field
  Labs, LabstoL = @inferred absolute_simple_field(L)
  embabs = complex_embeddings(Labs)
  binLabs = [ LabstoL\bb for bb in b]
  @inferred emb[1](b[1])

  for e in emb
    imageofb = e.(b)
    @test all(overlaps.(conj(e).(b), conj.(e.(b))))
    @test count(ee -> all(overlaps.(ee.(binLabs), imageofb)), embabs) == 1
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

  z = rand(L, -10:10)^100
  for p in [32, 128, 256, 1024]
    for e in emb
      fn = evaluation_function(e, p)
      @test Hecke.radiuslttwopower(fn(z), -p)
      c = e(z, p)
      @test Hecke.radiuslttwopower(c, -p)
    end
  end

  K, (a, b) = number_field([x^2 + 5, x^2 + 7])
  CC = AcbField(64)
  r1 = Hecke.complex_embedding(K, [CC(0, 2.24), CC(0, 2.65)])
  r2 = Hecke.complex_embedding(K, [CC(0, -2.24), CC(0, 2.65)])
  r3 = Hecke.complex_embedding(K, [CC(0, 2.24), CC(0, -2.65)])
  r4  = Hecke.complex_embedding(K, [CC(0, -2.24), CC(0, -2.65)])

  @test Set(complex_embeddings(K)) == Set([r1, r2, r3, r4])
  @test_throws ErrorException Hecke.complex_embedding(K, [0.0, 0.0])

  # Some issue

  Qx, x = QQ["x"]
  K, (a,) = number_field([x^4 - 8])
  e = complex_embedding(K, [1.68])
  @test number_field(e) === K
  @test is_real(e(a)) && real(e(a)) > 0
end
