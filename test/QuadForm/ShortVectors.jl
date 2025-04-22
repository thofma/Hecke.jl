@testset "Short[test] vectors" begin
  D = lattice_database()
  _minima = QQFieldElem[minimum(lattice(D, i)) for i in 1:300]
  @test _minima == QQFieldElem[2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 2, 3, 1, 2, 2, 3,
                        6, 1, 2, 1, 2, 3, 4, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2,
                        2, 1, 2, 3, 4, 2, 2, 4, 2, 4, 2, 2, 2, 4, 4, 2, 2, 4,
                        2, 3, 2, 4, 4, 6, 2, 2, 3, 1, 2, 5, 3, 4, 2, 4, 2, 2,
                        4, 4, 4, 7, 4, 2, 6, 4, 4, 4, 2, 4, 2, 4, 2, 3, 3, 2,
                        7, 2, 4, 2, 3, 2, 2, 4, 12, 2, 4, 6, 6, 8, 6, 8, 6, 6,
                        8, 6, 3, 6, 6, 4, 6, 6, 6, 4, 4, 4, 4, 4, 4, 4, 4, 2,
                        2, 4, 6, 4, 4, 10, 6, 4, 6, 4, 8, 2, 8, 2, 4, 2, 2, 2,
                        2, 4, 8, 4, 8, 3, 3, 4, 6, 6, 2, 9, 2, 4, 4, 16, 4, 4,
                        4, 3, 3, 2, 2, 10, 4, 6, 3, 2, 4, 4, 16, 4, 3, 4, 2,
                        11, 60, 2, 4, 4, 12, 4, 4, 4, 8, 4, 4, 8, 4, 2, 12, 2,
                        8, 2, 4, 6, 2, 2, 4, 2, 4, 2, 2, 2, 2, 2, 2, 15, 12, 4,
                        4, 4, 4, 4, 3, 4, 2, 13, 3, 5, 2, 4, 4, 9, 4, 4, 4, 3,
                        2, 14, 4, 4, 4, 4, 2, 4, 2, 4, 4, 4, 4, 4, 4, 7, 6, 6,
                        2, 15, 2, 3, 2, 4, 4, 4, 4, 4, 4, 4, 3, 3, 8, 6, 8, 12,
                        12, 8, 10, 6, 10, 4, 2, 16, 6, 8, 4, 4, 4, 4, 8, 6, 8,
                        4, 6, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 2 ]

  _kissing = Int[kissing_number(lattice(D, i)) for i in 1:300]
  @test _kissing == [2, 2, 2, 2, 6, 6, 2, 4, 4, 4, 12, 8, 12, 8, 6, 4, 12, 8,
                     8, 6, 6, 2, 4, 4, 6, 2, 2, 2, 2, 2, 8, 2, 2, 2, 2, 4, 4,
                     4, 4, 4, 4, 6, 6, 10, 20, 10, 24, 24, 24, 8, 6, 2, 2, 4,
                     24, 4, 6, 12, 4, 12, 6, 4, 8, 8, 30, 12, 20, 30, 40, 10,
                     12, 40, 12, 6, 30, 24, 6, 42, 14, 42, 44, 42, 60, 12, 72,
                     54, 72, 20, 8, 56, 16, 84, 14, 126, 56, 126, 126, 92, 2,
                     126, 64, 60, 56, 56, 58, 56, 60, 56, 56, 56, 56, 56, 56,
                     60, 56, 56, 56, 60, 60, 60, 58, 72, 56, 56, 56, 56, 84,
                     72, 64, 68, 64, 56, 120, 16, 48, 72, 30, 72, 18, 112, 16,
                     240, 240, 240, 240, 132, 12, 150, 42, 16, 16, 120, 48,
                     48, 90, 20, 144, 18, 180, 6, 198, 272, 270, 20, 20, 30,
                     110, 22, 220, 110, 40, 180, 20, 276, 54, 336, 80, 260,
                     132, 24, 24, 220, 22, 432, 82, 438, 432, 216, 270, 420,
                     336, 336, 360, 156, 26, 12, 126, 18, 126, 60, 24, 42,
                     756, 264, 24, 264, 60, 72, 36, 36, 36, 12, 2, 756, 756,
                     648, 632, 624, 64, 84, 182, 28, 52, 52, 312, 26, 918, 2,
                     906, 890, 888, 112, 210, 30, 378, 756, 210, 1260, 364,
                     28, 252, 1242, 1248, 1422, 1228, 1212, 1210, 156, 182,
                     546, 240, 32, 240, 240, 420, 30, 1746, 1644, 2340, 1872,
                     1630, 1596, 70, 240, 600, 960, 180, 1680, 480, 1200,
                     1440, 336, 336, 720, 272, 34, 1088, 360, 240, 4320, 4320,
                     440, 420, 2400, 360, 480, 360, 480, 32, 720, 2772, 2436,
                     2448, 4320, 2982, 2402, 2364, 512, 256, 306 ]

  # Floating point bounds
  L = integer_lattice(gram = QQ[1//2 0; 0 1//3])
  v = short_vectors(L, 0.1, 0.6)
  @test length(v) == 2
  L = integer_lattice(gram = QQ[-1//2 0; 0 -1//3])
  v = short_vectors(L, 0.1, 0.6)
  @test length(v) == 2
  v = short_vectors(L, 0.4, 0.6)
  @test length(v) == 1
  @test v[1][1] == [1, 0]
  @test v[1][2] == 1//2

  L = integer_lattice(gram = QQ[1//2 0; 0 1//3])
  v = collect(short_vectors_iterator(L, 0.1, 0.6))
  @test length(v) == 2
  v = collect(short_vectors_iterator(L, 0.4, 0.6))
  @test length(v) == 1
  @test v[1][1] == [1, 0]
  @test v[1][2] == 1//2

  G = QQ[37284162112275300417246466355574714960 -13475345948269524138620045643237003610;
         -13475345948269524138620045643237003610 4870297148658720162079534168117444310]
  L = integer_lattice(;gram = G)
  @test minimum(L) == 35600528619523312710

  gram = QQ[1 0 0 1; 0 1 0 0; 0 0 1 0; 1 0 0 13//10]
  delta = 9//10
  L = integer_lattice(;gram = gram)
  sv = @inferred short_vectors_iterator(L, delta, Int)
  @test collect(sv) == Tuple{Vector{Int64}, QQFieldElem}[([1, 0, 0, -1], 3//10)]
  sv = @inferred short_vectors_iterator(L, delta, ZZRingElem)
  @test collect(sv) == Tuple{Vector{ZZRingElem}, QQFieldElem}[([1, 0, 0, -1], 3//10)]

  L = integer_lattice(;gram = -gram)
  sv = @inferred short_vectors_iterator(L, delta, Int)
  @test collect(sv) == Tuple{Vector{Int64}, QQFieldElem}[([1, 0, 0, -1], 3//10)]
  sv = @inferred short_vectors_iterator(L, delta, ZZRingElem)
  @test collect(sv) == Tuple{Vector{ZZRingElem}, QQFieldElem}[([1, 0, 0, -1], 3//10)]

  L = integer_lattice(;gram = identity_matrix(ZZ, 0))
  sv = @inferred short_vectors(L, 1)
  @test collect(sv) == Tuple{Vector{ZZRingElem}, QQFieldElem}[]
  sv = @inferred short_vectors_iterator(L, 1)
  @test collect(sv) == Tuple{Vector{ZZRingElem}, QQFieldElem}[]

  L = integer_lattice(;gram = identity_matrix(ZZ, 0))
  sv = @inferred short_vectors(L, 0, 1)
  @test collect(sv) == Tuple{Vector{ZZRingElem}, QQFieldElem}[]
  sv = @inferred short_vectors_iterator(L, 0, 1)
  @test collect(sv) == Tuple{Vector{ZZRingElem}, QQFieldElem}[]

  L = integer_lattice(;gram = identity_matrix(ZZ, 2))
  sv = @inferred shortest_vectors(L)
  @test length(sv) == 2

  L = rescale(root_lattice(:A, 4), -1)
  @test minimum(L) == 2
  sv = short_vectors_iterator(L, 2, 3)
  for (_v, n) in sv
    v = matrix(QQ, 1, 4, _v)
    @test (v*gram_matrix(L)*transpose(v))[1] == -n
  end
end

@testset "Short vectors affine" begin
  B = matrix(QQ, 13, 13 ,[2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3//2, 1//2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1//2, 3//2, 3//2, 1//2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3//2, 0, 1, 1//2, 1//2, 1//2, 0, 0, 0, 0, 0, 0, 0, 1, 1//2, 0, 1//2, 1//2, 0, 1//2, 0, 0, 0, 0, 0, 0, 1//2, 1//2, 1, 0, 1//2, 0, 0, 1//2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3//2, 1//2, 1//2]);
  G = matrix(QQ, 13, 13 ,[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3]);
  L = integer_lattice(B, gram = G);
  v = B[1:1, :]
  vT = transpose(v)

  sva = short_vectors_affine(L, v, QQ(-2), QQ(-2))
  @test length(sva) == 492
  @test all(w -> w*G*transpose(w) == -2, sva)
  @test all(w -> w*G*vT == -2, sva)
end
