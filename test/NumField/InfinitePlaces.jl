@testset "InfinitePlaces" begin
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
    embs = @inferred infinite_places(K)
    @test length(embs) == 1
    embs = @inferred real_places(K)
    @test length(embs) == 1
    e = embs[1]
    @test (@inferred number_field(e)) === K
    @test sprint(show, "text/plain", e) isa String
    @test count(isequal('\n'), sprint(show, e)) == 0

    @test restrict(e, QQ) == infinite_places(QQ)[1]

    @test embedding(e) == complex_embeddings(K)[1]
    @test embeddings(e) == complex_embeddings(K)

    @test @inferred (is_real(e))
    @test !(@inferred is_complex(e))

    for b in (a, FacElem(a), OK(a))
      @test @inferred is_positive(b, e)
      @test @inferred is_positive(b, [e])
      @test @inferred !is_negative(b, e)
      @test @inferred !is_negative(b, [e])
      @test @inferred is_totally_positive(b)
      @test (@inferred signs(b, real_places(K))) == Dict(e => 1)
      @test (@inferred sign(b, e) == 1)
      if !(b isa FacElem)
        @test (@inferred sign(zero(parent(b)), e) == 0)
      end
    end

    for b in (-a, FacElem(-a), OK(-a))
      @test @inferred !is_positive(b, e)
      @test @inferred !is_positive(b, [e])
      @test @inferred is_negative(b, e)
      @test @inferred is_negative(b, [e])
      @test @inferred !is_totally_positive(b)
      @test (@inferred signs(b, real_places(K))) == Dict(e => -1)
      @test (@inferred sign(b, e) == -1)
    end
  end

  K, a = quadratic_field(-1)
  c = complex_places(K)
  @test_throws ArgumentError embedding(c[1])
  @test embeddings(c[1]) == complex_embeddings(K)
  @test @inferred is_complex(c[1])
  @test !(@inferred is_real(c[1]))
end

