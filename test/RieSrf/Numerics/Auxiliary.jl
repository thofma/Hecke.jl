@testset "Auxiliary" begin
  # Embedding number field elements from many threads at many precisions at
  # once. Hecke caches the roots of the defining polynomial per precision in
  # a Dict on the field, which is not thread safe; unguarded this corrupted
  # the Dict (UndefRefError in rehash!) in the period computation.
  # _embed_coefficient serializes the evaluations. (Only meaningful with
  # several threads.)
  Qt, t = polynomial_ring(QQ, :t)
  K, a = number_field(t^5 - 3*t + 1, :a)       # a fresh field: empty cache
  emb = complex_embeddings(K)[1]
  c = 3*a^4 - a + QQ(1, 10^20)
  results = Vector{AcbFieldElem}(undef, 400)
  Threads.@threads for i in 1:400
    results[i] = RSM._embed_coefficient(c, emb, 64 + 7*i)
  end
  @test all(i -> overlaps(results[i], results[1]), 2:400)
  @test precision(parent(results[400])) == 64 + 7*400

  # embedding polynomials: same terms, coefficients embedded by the place
  v = infinite_places(K)[1]
  R, (X, Y) = polynomial_ring(K, [:x, :y])
  f = a*X^2*Y + 3*Y^3 - X + 1
  F = RSM._embed_mpoly(f, v, 128)
  @test precision(base_ring(F)) == 128 && length(F) == length(f)
  @test all(collect(exponent_vectors(F)) .== collect(exponent_vectors(f)))
  @test all(overlaps(c, RSM._embed_coefficient(d, v.embedding, 128))
            for (c, d) in zip(coefficients(F), coefficients(f)))
  Kt, T = polynomial_ring(K, :T)
  p = a*T^3 - 2*T + a^2
  P = RSM._embed_poly(p, v, 128)
  @test degree(P) == 3 && overlaps(coeff(P, 1), base_ring(P)(-2)) && iszero(coeff(P, 2))

  # interior points of Newton polygons (Baker's basis)
  Qxy, (X, Y) = polynomial_ring(QQ, [:x, :y])
  @test sort(RSM._newton_polygon_interior_points(Y^2 - X^5 - 1)) == [[1, 1], [2, 1]]
  @test sort(RSM._newton_polygon_interior_points(X^4 + Y^4 + 1)) == [[1, 1], [1, 2], [2, 1]]

  # the order of the sheets
  CC = AcbField(64)
  @test RSM.sheet_ordering(CC(1), CC(2)) && !RSM.sheet_ordering(CC(2), CC(1))
  @test RSM.sheet_ordering(CC(1, 0), CC(1, 1))
  @test_throws ErrorException RSM.sheet_ordering(CC(1), CC(1))
end
