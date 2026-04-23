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

@testset "Short vectors affine iterator" begin
  B = matrix(QQ, 13, 13 ,[2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3//2, 1//2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1//2, 3//2, 3//2, 1//2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3//2, 0, 1, 1//2, 1//2, 1//2, 0, 0, 0, 0, 0, 0, 0, 1, 1//2, 0, 1//2, 1//2, 0, 1//2, 0, 0, 0, 0, 0, 0, 1//2, 1//2, 1, 0, 1//2, 0, 0, 1//2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3//2, 1//2, 1//2]);
  G = matrix(QQ, 13, 13 ,[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3]);
  L = integer_lattice(B, gram = G);
  v = B[1:1, :]
  vT = transpose(v)
  sva = []
  for v in short_vectors_affine_iterator(L, v, QQ(-2), QQ(-2))
    push!(sva, v)
  end
  @test length(sva) == 492
  @test all(w -> w*G*transpose(w) == -2, sva)
  @test all(w -> w*G*vT == -2, sva)
end

@testset "Center density" begin
  L = root_lattice(:E, 6)
  r = center_density(L)
  @test contains(parent(r)("[0.0721687836487032205 +/- 9.72e-10]"), r)

  L = root_lattice(:E, 8)
  r = density(L)
  @test contains(parent(r)("[0.253669507901048014 +/- 6.66e-10]"), r)

  L = root_lattice(:E, 7)
  r =  hermite_number(L)
  @test contains(parent(r)("[1.811447328527813353 +/- 5.13e-10]"), r)
end

@testset "Successive minima" begin
  L = integer_lattice(gram = ZZ[1 0 0; 0 2 0; 0 0 3]);
  @test successive_minima(L) == [1, 2, 3]
  s, v = successive_minima_with_vectors(L)
  @test s == [1, 2, 3]
  @test allunique(v)
  @test all(inner_product(L, v[i], v[i]) == s[i] for i in 1:length(s))

  L = integer_lattice(; gram = matrix(ZZ, [[1,0,0,0,0,0,0], [0,3,0,0,-1,-1,1], [0,0,3,1,0,1,-1], [0,0,1,3,0,1,1], [0,-1,0,0,3,1,1], [0,-1,1,1,1,3,0], [0,1,-1,1,1,0,6]]))
  s, v = successive_minima_with_vectors(L)
  @test s == [1, 3, 3, 3, 3, 3, 6]
  @test allunique(v)
  @test all(inner_product(L, v[i], v[i]) == s[i] for i in 1:length(s))

  L = integer_lattice(gram = QQ[1//2 0 0; 0 2//3 0; 0 0 3//4]);
  s, v = successive_minima_with_vectors(L)
  @test s == [1//2, 2//3, 3//4]
  @test allunique(v)
  @test all(inner_product(L, v[i], v[i]) == s[i] for i in 1:length(s))

  # Fix old wrong code
  L = integer_lattice(gram=ZZ[3 1 -1 1 1 0 -1 -1 0 -1 1 0 -1 1 0 0 -1 1 1 -1 0 0 0 0 0 0; 1 3 1 1 0 1 0 0 -1 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1; -1 1 3 -1 0 0 0 1 -1 0 1 0 0 0 0 0 0 -1 -1 1 0 0 1 -1 1 1; 1 1 -1 3 1 1 -1 0 0 1 0 1 0 0 1 0 0 0 1 -1 0 1 0 1 0 0; 1 0 0 1 3 1 -1 1 1 0 0 0 -1 1 0 0 -1 1 1 -1 0 0 1 0 1 0; 0 1 0 1 1 3 1 0 1 0 0 1 0 1 0 0 0 0 0 0 1 0 0 0 0 1; -1 0 0 -1 -1 1 3 -1 1 0 -1 0 1 0 0 0 0 0 0 1 0 0 -1 0 -1 0; -1 0 1 0 1 0 -1 3 0 0 0 0 0 0 0 0 1 0 0 0 0 0 1 0 1 0; 0 -1 -1 0 1 1 1 0 3 -1 -1 1 -1 1 0 -1 0 1 1 0 0 1 0 1 0 0; -1 0 0 1 0 0 0 0 -1 3 0 0 1 -1 0 0 0 0 0 0 0 0 0 0 0 0; 1 1 1 0 0 0 -1 0 -1 0 3 0 0 1 0 0 0 0 0 0 0 0 1 0 1 1; 0 0 0 1 0 1 0 0 1 0 0 3 -1 0 0 -1 0 0 0 0 0 1 0 0 0 1; -1 0 0 0 -1 0 1 0 -1 1 0 -1 3 -1 0 0 0 -1 0 0 0 0 0 0 -1 -1; 1 0 0 0 1 1 0 0 1 -1 1 0 -1 3 0 0 0 0 1 0 1 0 0 0 1 0; 0 0 0 1 0 0 0 0 0 0 0 0 0 0 3 1 1 0 0 0 -1 1 0 1 0 0; 0 0 0 0 0 0 0 0 -1 0 0 -1 0 0 1 3 0 0 0 0 0 -1 0 0 1 0; -1 0 0 0 -1 0 0 1 0 0 0 0 0 0 1 0 3 0 -1 1 0 0 0 1 0 0; 1 0 -1 0 1 0 0 0 1 0 0 0 -1 0 0 0 0 3 1 0 -1 0 0 1 0 0; 1 0 -1 1 1 0 0 0 1 0 0 0 0 1 0 0 -1 1 3 -1 0 1 0 1 0 -1; -1 0 1 -1 -1 0 1 0 0 0 0 0 0 0 0 0 1 0 -1 3 0 0 -1 0 0 1; 0 0 0 0 0 1 0 0 0 0 0 0 0 1 -1 0 0 -1 0 0 3 0 0 -1 0 0; 0 0 0 1 0 0 0 0 1 0 0 1 0 0 1 -1 0 0 1 0 0 3 0 1 0 0; 0 0 1 0 1 0 -1 1 0 0 1 0 0 0 0 0 0 0 0 -1 0 0 3 0 1 0; 0 0 -1 1 0 0 0 0 1 0 0 0 0 0 1 0 1 1 1 0 -1 1 0 3 0 0; 0 0 1 0 1 0 -1 1 0 0 1 0 -1 1 0 1 0 0 0 0 0 0 1 0 3 1; 0 1 1 0 0 1 0 0 0 0 1 1 -1 0 0 0 0 0 -1 1 0 0 0 0 1 3])
  s, v = successive_minima_with_vectors(L)
  @test length(s) == 26
  @test all(isequal(3), s)
  @test allunique(v)
  @test all(inner_product(L, v[i], v[i]) == s[i] for i in 1:length(s))
end

@testset "short vector with condition" begin
  L = [ZZ[-2 0 0 0 0 0 0 0 0 -1 0 0 0 0 0 0 1; 0 -2 -1 1 -1 1 -1 -1 1 1 0 0 0 0 0 0 -1; 0 -1 -2 1 -1 1 -1 -1 1 0 0 0 0 0 0 0 0; 0 1 1 -2 0 0 0 0 0 0 0 0 0 0 0 0 0; 0 -1 -1 0 -2 1 -1 -1 1 1 0 0 0 0 0 0 -1; 0 1 1 0 1 -2 1 1 -1 0 0 0 0 0 0 0 0; 0 -1 -1 0 -1 1 -2 -1 1 1 0 0 0 0 0 0 -1; 0 -1 -1 0 -1 1 -1 -2 1 1 0 0 0 0 0 0 -1; 0 1 1 0 1 -1 1 1 -2 0 0 0 0 0 0 0 0; -1 1 0 0 1 0 1 1 0 -4 0 0 0 0 0 0 3; 0 0 0 0 0 0 0 0 0 0 -2 -1 -1 -1 1 1 0; 0 0 0 0 0 0 0 0 0 0 -1 -2 -1 0 1 1 0; 0 0 0 0 0 0 0 0 0 0 -1 -1 -2 -1 1 1 0; 0 0 0 0 0 0 0 0 0 0 -1 0 -1 -2 1 0 0; 0 0 0 0 0 0 0 0 0 0 1 1 1 1 -2 -1 0; 0 0 0 0 0 0 0 0 0 0 1 1 1 0 -1 -2 0; 1 -1 0 0 -1 0 -1 -1 0 3 0 0 0 0 0 0 -6],
  ZZ[-2 1 -1 1 -1 1 0 0 0 1 -1 -1 -1 1 -1 1 1; 1 -2 1 -1 1 -1 0 0 0 0 0 0 1 0 0 0 0; -1 1 -2 1 -1 1 0 0 0 1 -1 -1 0 1 -1 1 1; 1 -1 1 -2 1 -1 0 0 0 -1 0 1 1 -1 1 0 -1; -1 1 -1 1 -2 1 0 0 0 1 -1 0 0 0 0 1 0; 1 -1 1 -1 1 -2 0 0 0 -1 1 0 1 0 0 -1 -1; 0 0 0 0 0 0 -2 0 0 -1 0 1 -1 -1 1 0 0; 0 0 0 0 0 0 0 -2 -1 -1 -1 0 0 0 0 -1 1; 0 0 0 0 0 0 0 -1 -2 -1 -1 0 0 0 0 -1 1; 1 0 1 -1 1 -1 -1 -1 -1 -4 0 2 -1 -2 2 -2 -1; -1 0 -1 0 -1 1 0 -1 -1 0 -4 0 0 0 0 1 1; -1 0 -1 1 0 0 1 0 0 2 0 -4 0 3 -3 1 2; -1 1 0 1 0 1 -1 0 0 -1 0 0 -4 -1 1 0 0; 1 0 1 -1 0 0 -1 0 0 -2 0 3 -1 -4 3 -1 -2; -1 0 -1 1 0 0 1 0 0 2 0 -3 1 3 -4 1 2; 1 0 1 0 1 -1 0 -1 -1 -2 1 1 0 -1 1 -4 0; 1 0 1 -1 0 -1 0 1 1 -1 1 2 0 -2 2 0 -4],
  ZZ[-2 1 0 0 0 0 0 0 0 -1 0 0 0 1 -1 1 0; 1 -2 0 0 0 0 0 0 0 1 0 0 0 0 0 -1 0; 0 0 -2 0 0 0 0 -1 1 -1 1 1 1 -1 -1 0 -1; 0 0 0 -2 -1 -1 -1 0 0 -1 0 0 0 1 -1 -1 -1; 0 0 0 -1 -2 -1 -1 0 0 0 0 0 0 1 0 -1 0; 0 0 0 -1 -1 -2 -1 0 0 -1 0 0 0 1 -1 0 -1; 0 0 0 -1 -1 -1 -2 0 0 -1 0 0 0 1 -1 -1 0; 0 0 -1 0 0 0 0 -2 1 0 1 0 1 -1 -1 0 -1; 0 0 1 0 0 0 0 1 -2 1 -1 0 -1 0 1 0 1; -1 1 -1 -1 0 -1 -1 0 1 -4 1 1 0 1 -2 0 -1; 0 0 1 0 0 0 0 1 -1 1 -2 0 -1 0 1 0 1; 0 0 1 0 0 0 0 0 0 1 0 -2 0 1 0 0 0; 0 0 1 0 0 0 0 1 -1 0 -1 0 -2 0 1 0 1; 1 0 -1 1 1 1 1 -1 0 1 0 1 0 -4 1 0 0; -1 0 -1 -1 0 -1 -1 -1 1 -2 1 0 1 1 -4 0 -2; 1 -1 0 -1 -1 0 -1 0 0 0 0 0 0 0 0 -4 0; 0 0 -1 -1 0 -1 0 -1 1 -1 1 0 1 0 -2 0 -4],
  ZZ[-2 -1 1 1 0 0 0 1 -1 1 1 1 1 1 1 1 -1; -1 -2 1 1 0 0 0 1 -1 0 0 1 0 1 1 1 0; 1 1 -2 -1 0 0 0 0 0 -1 -1 0 -1 0 0 0 1; 1 1 -1 -2 0 0 0 -1 1 0 -1 0 -1 0 0 0 1; 0 0 0 0 -2 1 1 1 -1 1 -1 -1 -1 -1 -1 -1 -1; 0 0 0 0 1 -2 -1 -1 1 -1 1 1 1 1 1 1 1; 0 0 0 0 1 -1 -2 0 0 0 1 1 1 1 1 1 1; 1 1 0 -1 1 -1 0 -4 3 0 1 -1 1 -1 -1 -1 0; -1 -1 0 1 -1 1 0 3 -4 1 -1 1 -1 0 1 1 -1; 1 0 -1 0 1 -1 0 0 1 -4 -1 0 -1 1 0 0 2; 1 0 -1 -1 -1 1 1 1 -1 -1 -4 -1 -3 -1 -1 -1 1; 1 1 0 0 -1 1 1 -1 1 0 -1 -4 -1 -2 -3 -3 -1; 1 0 -1 -1 -1 1 1 1 -1 -1 -3 -1 -4 -1 -1 -1 1; 1 1 0 0 -1 1 1 -1 0 1 -1 -2 -1 -4 -2 -2 -1; 1 1 0 0 -1 1 1 -1 1 0 -1 -3 -1 -2 -4 -3 -1; 1 1 0 0 -1 1 1 -1 1 0 -1 -3 -1 -2 -3 -4 -1; -1 0 1 1 -1 1 1 0 -1 2 1 -1 1 -1 -1 -1 -4]]
  LL = [integer_lattice(gram=-g) for g in L]
  @test length.(first.(Hecke.short_vectors_with_condition.(LL; search_fixed_vectors = false))) == [25, 42, 31, 53]
  @test length.(first.(Hecke.short_vectors_with_condition_direct.(Int, LL))) == [25, 42, 31, 53]


  function test_short_vectors_with_condition(L::ZZLat; search_fixed_vectors=false)
    n = rank(L)
    _V1, _grams,_T,_ = Hecke.short_vectors_with_condition(Int, L; search_fixed_vectors)
    V1 = [(QQ.(i[1]), QQ.(i[2])) for i in _V1]
    _V2, grams, T, proj_root_inv = Hecke.short_vectors_with_condition(ZZRingElem, L;
                                                                      search_fixed_vectors)
    V2 = [(QQ.(i[1]), QQ.(i[2])) for i in _V2]

    @assert grams == _grams # check consistency between methods
    @assert T==_T
    # confirm consistency of the output
    for V in [V1,V2]
      for (v, n) in V1
        @assert all(dot(v * grams[i], v) == n[i] for i in 1:length(grams))
      end
    end
    # compute the same set by filtering
    # invariants of the standard basis vectors
    target = Set((ZZRingElem[grams[i][j,j] for i in 1:length(grams)], Hecke._canonicalize!(deepcopy(T[j,:])), Hecke._canonicalize!(deepcopy(proj_root_inv[j,:]))) for j in 1:n)
    target12 = Set(i[1:2] for i in target)
    target_norms = Set(i[1] for i in target)
    target_T = Set(i[2] for i in target)
    target_proj = Set(i[3] for i in target)
    V3 = Tuple{Vector{QQFieldElem},Vector{QQFieldElem}}[]
    for (v, _) in short_vectors(L, maximum(abs.(diagonal(gram_matrix(L)))))
      v_proj = Hecke._canonicalize!(v*proj_root_inv)
      v_proj in target_proj || continue
      v_T = Hecke._canonicalize!(v*T)
      v_T in target_T || continue
      v_norms = [dot(v, g*v) for g in grams]
      v_norms in target_norms || continue
      # now the 3 invariants match individually
      # check if they match in combination.
      v_invariants = (v_norms, v_T)
      v_invariants in target12 || continue
      #v_invariants = (v_norms, v_T, v_proj)
      #v_invariants in target || continue  # this test fails because we do not filter like this ....
      push!(V3, (Hecke._canonicalize!(v), v_norms))
    end
    S1 = Set(V1)
    S2 = Set(V2)
    S3 = Set(V3)
    @test length(S1) == length(S3)
    @test S1 == S2
    @test S1 == S3
    return nothing
  end

  for l in LL[2:4] #takes a bit long for LL[1] we test it separately
    test_short_vectors_with_condition(l; search_fixed_vectors = false)
  end

  for l in LL[2:4]
    test_short_vectors_with_condition(l; search_fixed_vectors = true)
  end

  @test 25 == length(Hecke.short_vectors_with_condition(Int, LL[1]; search_fixed_vectors=false)[1])
  @test 25 == length(Hecke.short_vectors_with_condition(ZZRingElem, LL[1]; search_fixed_vectors=false)[1])

  Lbad = integer_lattice(;gram = matrix(ZZ, 17, 17, [-2 1 0 0 -1 -1 0 -1 -1 -1 -1 -1 1 0 1 0 -1; 1 -2 0 0 0 0 0 1 1 1 1 0 -1 0 -1 0 0; 0 0 -2 -1 -1 1 1 0 0 0 0 -1 1 -1 1 0 -1; 0 0 -1 -2 -1 0 1 0 0 0 0 -1 0 -1 0 0 0; -1 0 -1 -1 -4 1 0 -1 -1 -1 -1 -2 0 0 0 0 0; -1 0 1 0 1 -4 1 1 1 1 -1 -1 -1 -1 -1 1 -1; 0 0 1 1 0 1 -4 -2 -2 -2 -1 1 0 0 0 0 2; -1 1 0 0 -1 1 -2 -4 -3 -3 0 1 0 1 0 -1 0; -1 1 0 0 -1 1 -2 -3 -4 -3 -1 1 0 0 1 -1 0; -1 1 0 0 -1 1 -2 -3 -3 -4 0 1 0 1 0 -1 0; -1 1 0 0 -1 -1 -1 0 -1 0 -4 -2 0 -2 1 1 1; -1 0 -1 -1 -2 -1 1 1 1 1 -2 -4 0 -1 0 1 0; 1 -1 1 0 0 -1 0 0 0 0 0 0 -4 1 -3 0 1; 0 0 -1 -1 0 -1 0 1 0 1 -2 -1 1 -4 1 1 0; 1 -1 1 0 0 -1 0 0 1 0 1 0 -3 1 -4 0 1; 0 0 0 0 0 1 0 -1 -1 -1 1 1 0 1 0 -2 0; -1 0 -1 0 0 -1 2 0 0 0 1 0 1 0 1 0 -4]))
  @test 110 == length(Hecke.short_vectors_with_condition(ZZRingElem, rescale(Lbad, -1); search_fixed_vectors=false)[1])
  @test 110 == length(Hecke.short_vectors_with_condition(Int, rescale(Lbad, -1); search_fixed_vectors=false)[1])
  test_short_vectors_with_condition(rescale(Lbad,-1); search_fixed_vectors=true)

  # A lattice without roots.
  L = integer_lattice(;gram = matrix(ZZ, 3, 3, [3, -1, -1, -1, 3, -1, -1, -1, 3]));
  @test length(Hecke.short_vectors_with_condition(ZZRingElem, L)[1])==4
  @test length(Hecke.short_vectors_with_condition(Int, L)[1])==4

  # Some lattices for cheaper testing
  A = [[2 -1 0 0 0 0; -1 2 -1 0 0 0; 0 -1 2 -1 0 0; 0 0 -1 2 -1 0; 0 0 0 -1 2 0; 0 0 0 0 0 20], [2 0 0 0 -1 -1; 0 2 0 -1 0 -1; 0 0 2 -1 1 0; 0 -1 -1 4 1 2; -1 0 1 1 4 1; -1 -1 0 2 1 4], [2 -1 1 0 0 0; -1 2 -1 0 0 0; 1 -1 2 0 0 0; 0 0 0 2 0 0; 0 0 0 0 2 1; 0 0 0 0 1 8], [2 1 -1 -1 0 0; 1 2 -1 -1 0 0; -1 -1 2 1 0 0; -1 -1 1 2 0 0; 0 0 0 0 2 0; 0 0 0 0 0 12], [2 -1 0 0 0 -1; -1 2 0 0 0 0; 0 0 2 0 1 0; 0 0 0 2 1 0; 0 0 1 1 4 0; -1 0 0 0 0 4], [2 -1 1 0 -1 -1; -1 2 -1 0 1 1; 1 -1 2 0 0 0; 0 0 0 2 0 0; -1 1 0 0 4 1; -1 1 0 0 1 6], [2 -1 1 1 -1 0; -1 2 -1 -1 0 0; 1 -1 2 0 0 0; 1 -1 0 2 -1 0; -1 0 0 -1 2 0; 0 0 0 0 0 30]]
  # Genus representatives of some genus
  L = [integer_lattice(gram=matrix(QQ,6,6,i),cached=false) for i in A]
  for l in L
    test_short_vectors_with_condition(l; search_fixed_vectors = false)
    test_short_vectors_with_condition(l; search_fixed_vectors = true)
  end

  let # some random failure with large entries
    B = matrix(QQ, 6, 6 ,[1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1])
    G = matrix(QQ, 6, 6 ,[876708188094148315826780735392810, 798141405233250328867679564294410, -352823337641433300965521329447720, 326768950610851461363580717982402, -690595881941554449465975342845028, 433433545243019702766746394677218, 798141405233250328867679564294410, 867615301468758683549323652197099, -301315621373858240463110267500961, 316796431934778296047626373086339, -725765288914917260527454069649226, 505082964151083450666500945258490, -352823337641433300965521329447720, -301315621373858240463110267500961, 809946152369211852531731702980788, -343784636213856787915462553587466, 84764902049682607076640678540130, -613908853150167850995565570653796, 326768950610851461363580717982402, 316796431934778296047626373086339, -343784636213856787915462553587466, 219957919673551825679009958633894, -226934633316066727073394927118195, 298257387132139131540277459301842, -690595881941554449465975342845028, -725765288914917260527454069649226, 84764902049682607076640678540130, -226934633316066727073394927118195, 671443408734467545153681225010914, -277626128761200144008657217470664, 433433545243019702766746394677218, 505082964151083450666500945258490, -613908853150167850995565570653796, 298257387132139131540277459301842, -277626128761200144008657217470664, 640432299215298238271419741190578])
    L = integer_lattice(B, gram = G)
    @test (@inferred is_empty(short_vectors(L, 0, 1)))
  end
end
