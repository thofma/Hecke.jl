@testset "Embeddings" begin
  Qx, x = QQ["x"]
  K, a = number_field(x^3 - 2, "a")
  @test (1, 1) == @inferred signature(K)
  emb = @inferred complex_embeddings(K)
  @test (@inferred number_field(emb[1])) === K
  @test length(emb) == 3
  @test length(real_embeddings(K)) == 1
  @test real_embeddings(K) == real_embeddings(K)
  @test complex_embeddings(K) === complex_embeddings(K) # caching

  @test @inferred isreal(emb[1])
  @test @inferred !isreal(emb[2])
  @test @inferred is_imaginary(emb[2])
  @test conj(emb[1]) === emb[1]
  @test conj(emb[2]) === emb[3]
  @test conj(emb[3]) === emb[2]

  for e in emb
    @test sprint(show, MIME"text/plain"(), e) isa String
    @test sprint(show, e) isa String
  end

  for e in emb
    for p in [32, 64, 128, 256]
      @test Hecke.radiuslttwopower(e(a, p), -p)
      @test Hecke.radiuslttwopower(evaluate(a, e, p), -p)
    end
  end

  @test overlaps(conj(emb[2](a)), (conj(emb[2]))(a))

  k, b = number_field(x - 1)
  f = hom(k, K, one(K))
  for e in emb
    length(unique([restrict(e, f) for e in emb])) == 1
  end

  ee = complex_embeddings(k)[1]
  @test length(@inferred extend(ee, f)) == 3

  ee = restrict(emb[1], f)
  c = ee(b)
  @test overlaps(c, one(parent(c)))

  z = rand(K, -10:10)^100
  for p in [32, 128, 256, 1024]
    for e in emb
      fn = evaluation_function(e, p)
      @test Hecke.radiuslttwopower(fn(z), -p)
      c = e(z, p)
      @test Hecke.radiuslttwopower(c, -p)
    end
  end

  # Creating embeddings from roots
  
  K, a = quadratic_field(2)
  r = Hecke.real_embedding(K, 1.41)
  s = Hecke.real_embedding(K, -1.41)
  @test Set(real_embeddings(K)) == Set([r, s])
  @test_throws ErrorException Hecke.real_embedding(K, 0.0)
  r = Hecke.real_embedding(K, (0,2))
  s = Hecke.real_embedding(K, (-2, 0))
  @test Set(real_embeddings(K)) == Set([r, s])
  @test_throws ErrorException Hecke.real_embedding(K, (-2,2))

  K, a = quadratic_field(-2)
  CC = AcbField(64)
  r = Hecke.complex_embedding(K, CC(0, 0.1))
  s = Hecke.complex_embedding(K, CC(0, -0.1))
  @test Set(complex_embeddings(K)) == Set([r, s])
  @test_throws ErrorException Hecke.complex_embedding(K, 0.0)

  K, a = quadratic_field(-2)
  @test Hecke.infinite_uniformizers(K) == Dict{Hecke.embedding_type(K), AbsSimpleNumFieldElem}()
  K, a = quadratic_field(2)
  em = complex_embeddings(K)
  for (e, elt) in Hecke.infinite_uniformizers(K)
    @test is_negative(elt, e)
    @test all(is_positive(elt, ee) for ee in em if ee != e)
  end

  # This should be fast
  K, a = cyclotomic_field(19^3, cached = false)
  @test length(@inferred complex_embeddings(K)) == degree(K)

  # Some issue
  Qx, x = QQ["x"]
  K, a = number_field(x^4 - 8)
  e = complex_embedding(K, 1.68)
  @test number_field(e) === K
  @test is_real(e(a)) && real(e(a)) > 0
end
