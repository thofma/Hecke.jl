@testset "Genus representatives" begin
  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  f = x-1;
  K, a = number_field(f)
  D = matrix(K, 3, 3, [-717210130, 0, 0, 0, -55, 0, 0, 0, -1173298395869600]);
  gens = [[1, 0, 0], [1, 0, 0], [4//5, 2//5, 0], [4//5, 2//5, 0], [1493459//5517001, 0, 1//15778622860], [1493459//5517001, 0, 1//15778622860]]
  L = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L)) == 6

  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  f = x-1;
  K, a = number_field(f)
  D = matrix(K, 3, 3, [-34, 0, 0, 0, -17, 0, 0, 0, -17192032]);
  gens = [[26, 0, 0], [234, 0, 0], [177//17, 2//17, 0], [177//17, 2//17, 0], [27//2, 0, 1//1768], [27//2, 0, 1//1768]]
  L = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L)) == 93

  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  f = x-1;
  K, a = number_field(f)
  D = matrix(K, 3, 3, [-98, 0, 0, 0, -2, 0, 0, 0, -5829824]);
  gens = [[8//7, 0, 0], [8//7, 0, 0], [5//14, 13//2, 0], [45//14, 117//2, 0], [29//28, 3//4, 1//1456], [29//28, 3//4, 1//1456]]
  L = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L)) == 114

  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  f = x^2-2;
  K, a = number_field(f)
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -7436]);
  gens = [[13, 0, 0], [156*a+143, 0, 0], [3//2*a+5, 1, 0], [3//2*a+5, 1, 0], [21//2*a, 0, 1//26], [21//2*a, 0, 1//26]]
  L = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L)) == 1

  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  f = x - 1
  K, a = number_field(f)
  M = matrix(QQ, 2, 2, [47, 80, 80, 560])
  w = Int[]
  for i in 1:10
    M[2, 2] = 560 + i
    V = quadratic_space(K, M)
    L = lattice(V, identity_matrix(K, 2))
    g = length(Hecke._genus_representatives_binary_quadratic_definite(L))
    push!(w, g)
  end
  @test w == Int[37, 16, 19, 11, 6, 3, 52, 7, 13, 21]

  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  f = x^2 - 2;
  K, a = number_field(f)
  D = matrix(K, 2, 2, [15, 2, 2, 32]);
  gens = [[1, 0], [1, 0], [0, 1], [0, 1]]
  L = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L)) == 6

  # Local isometry test

  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  f = x - 1;
  K, a = number_field(f)
  D = matrix(K, 7, 7, [8, -4, 3, 4, 0, 1, 1, -4, 8, 1, 0, 4, 1, 1, 3, 1, 8, 4, 0, 1, 1, 4, 0, 4, 8, 3, 0, 4, 0, 4, 0, 3, 8, 4, 0, 1, 1, 1, 0, 4, 8, -4, 1, 1, 1, 4, 0, -4, 8]);
  gens = [[1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1]]
  L = quadratic_lattice(K, gens, gram = D)

  D = matrix(K, 7, 7, [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 56]);
  gens = [[1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1]]
  LL = quadratic_lattice(K, gens, gram = D)

  p = prime_decomposition(maximal_order(K), 2)[1][1]
  @test is_locally_isometric(L, LL, p)

  # Rank 2 case
  # This is the Zlattice with basis [1 2; 3 4]

  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  f = x - 1;
  K, a = number_field(f)
  D = matrix(K, 2, 2, [1, 0, 0, 1]);
  gens = [[1, 2], [1, 2], [3, 4], [3, 4]]
  L = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L)) == 1

  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  f = x - 1
  K, a = number_field(f)
  D = matrix(K, 3, 3, [-18, -6, -9, -6, -3, -3, -9, -3, -6])
  gens = [[1, 0, 0], [1, 0, 0], [0, 1, 0], [0, 1, 0], [0, 0, 1], [0, 0, 1]]
  L = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L)) == 1

  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  f = x - 1;
  K, a = number_field(f)
  D = matrix(K, 2, 2, [2, 0, 0, 3]);
  gens = [[1, 0], [1, 0], [0, 1], [0, 1]]
  L = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L)) == 1

  B = QQ[2 0; 3//2 1//2]
  G = QQ[1 0; 0 23]
  V = quadratic_space(QQ, G)
  L = lattice(V, B)
  @test length(genus_representatives(L)) == 2
  @test length(genus_representatives(Zlattice(gram = gram_matrix(L)))) == 2

  L = Zlattice(ZZ[4 3; 3 8])
  @test length(genus_representatives(L)) == 4

  B = matrix(FlintQQ, 5, 5 ,[1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]);
  G = matrix(FlintQQ, 5, 5 ,[-2, 0, 0, 0, 0, 0, -4, -2, 2, 2, 0, -2, -4, 0, 0, 0, 2, 0, -4, 0, 0, 2, 0, 0, -4]);
  L = Zlattice(B, gram = G);
  @test length(genus_representatives(L))==1

end

@testset "Genus Representatives Number Field" begin
  R, x = polynomial_ring(QQ,:x)
  F, a = number_field(x^2-2,:a)
  OF = maximal_order(F)
  pl = real_places(F)
  f = x^2 - 2;
  K, a = number_field(f, "a")

  # The following is unrolled
  # sig = Dict([(pl[1],0),(pl[2],0)])
  # for d in 1:12
  #   for g in Hecke.quadratic_genera(F,rank=3,det=d*OF,signatures=sig)
  #     representatives(g)

  res = [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1,
          1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 3, 3, 2, 2, 3, 2, 1,
          1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1,
          1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 6, 4, 4, 1, 2, 2, 4, 3, 3, 5, 3,
          3, 3, 3, 6, 8, 6, 2, 1, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 2, 2, 2, 3, 2, 2, 2, 3,
          3, 4, 4, 2, 6, 2, 2, 3, 2, 3, 3 ]

  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 16]);
  gens = [[2, 0, 0], [a + 2, 0, 0], [a, 4, 0], [1, 2*a, 0], [1//2*a + 1//2, 1//2, 1//8], [1//2*a + 1//2, 1//2, 1//8]]
  L78 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L78)) == res[78]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 16]);
  gens = [[1, 0, 0], [3//2*a + 1, 0, 0], [0, 4, 0], [0, 8*a + 4, 0], [0, 2*a + 5, 1//4], [0, 15//2*a + 6, 3//8*a]]
  L79 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L79)) == res[79]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 16]);
  gens = [[2, 0, 0], [2, 0, 0], [0, 2, 0], [0, 2, 0], [a + 3//2, a + 3//2, 1//8], [a + 3//2, a + 3//2, 1//8]]
  L80 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L80)) == res[80]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 16]);
  gens = [[2, 0, 0], [2*a + 2, 0, 0], [3//2*a, 1, 0], [3//2*a, 1, 0], [1//2*a, 0, 1//4], [1//2*a, 0, 1//4]]
  L81 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L81)) == res[81]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 16]);
  gens = [[2, 0, 0], [2, 0, 0], [0, 2, 0], [0, a, 0], [a + 2, 1, 1//4], [3*a + 3, 3//2*a, 3//8*a]]
  L82 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L82)) == res[82]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 16]);
  gens = [[2, 0, 0], [a + 2, 0, 0], [a, 4, 0], [1, 2*a, 0], [1//2*a + 1//2, 3//2, 1//8], [1//2*a + 1//2, 3//2, 1//8]]
  L83 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L83)) == res[83]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 16]);
  gens = [[2, 0, 0], [2*a + 2, 0, 0], [a + 2, 2, 0], [a + 1, a, 0], [2, 1, 1//4], [3*a, 3//2*a, 3//8*a]]
  L84 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L84)) == res[84]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 16]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 4, 0], [0, 12*a + 12, 0], [1//2, a + 1//2, 1//8], [1//2, a + 1//2, 1//8]]
  L85 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L85)) == res[85]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 16]);
  gens = [[2, 0, 0], [2, 0, 0], [a + 2, 2, 0], [a + 1, a, 0], [2, a + 1, 1//4], [3*a, 3//2*a + 3, 3//8*a]]
  L86 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L86)) == res[86]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 16]);
  gens = [[2, 0, 0], [2, 0, 0], [a + 2, 2, 0], [a + 1, a, 0], [a + 1, 1, 1//4], [3//2*a + 3, 3//2*a, 3//8*a]]
  L87 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L87)) == res[87]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 16]);
  gens = [[4, 0, 0], [6*a + 4, 0, 0], [2*a + 1, 2, 0], [1//2*a + 2, a, 0], [3//2*a + 7//2, 1//2, 1//8], [3//2*a + 7//2, 1//2, 1//8]]
  L88 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L88)) == res[88]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 16]);
  gens = [[2, 0, 0], [2*a + 2, 0, 0], [a + 3, 2, 0], [3//2*a + 1, a, 0], [a, a + 1, 1//4], [3, 3//2*a + 3, 3//8*a]]
  L89 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L89)) == res[89]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 16]);
  gens = [[4, 0, 0], [2*a + 4, 0, 0], [1, 2, 0], [1//2*a, a, 0], [1//2*a + 5//2, 3//2, 1//8], [1//2*a + 5//2, 3//2, 1//8]]
  L90 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L90)) == res[90]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 16]);
  gens = [[4, 0, 0], [6*a, 0, 0], [2*a + 3, 2, 0], [3//2*a + 2, a, 0], [1//2*a + 7//2, 3//2, 1//8], [1//2*a + 7//2, 3//2, 1//8]]
  L91 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L91)) == res[91]
  D = matrix(K, 3, 3, [-414009*a + 607296, 0, 0, 0, -6*a + 57, 0, 0, 0, -245180601*a + 356255820]);
  gens = [[2, 0, 0], [a, 0, 0], [244, 1, 0], [6700972//353*a + 14607060//353, 27463//353*a + 59865//353, 0], [1//2*a + 3171925439//2, 0, 1//18], [3390527213343427310346891//4092151*a + 3486060813286836978037843//8184302, 0, 754655889070064585//26001527454*a + 387959770570427231//26001527454]]
  L92 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L92)) == res[92]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 18]);
  gens = [[3, 0, 0], [6*a + 6, 0, 0], [a + 3, 2, 0], [5//2*a + 4, a + 2, 0], [3//2*a + 1, 1//2*a, 1//6], [1//2*a + 3//2, 1//2, 1//12*a]]
  L93 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L93)) == res[93]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 18]);
  gens = [[3, 0, 0], [33//2*a + 6, 0, 0], [0, 2, 0], [0, 3*a + 2, 0], [a, 1//2*a, 1//6], [a, 1//2*a, 1//6]]
  L94 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L94)) == res[94]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 18]);
  gens = [[1, 0, 0], [1, 0, 0], [1, 6, 0], [9//2*a + 5, 27*a + 30, 0], [1//2*a, 1//2*a + 2, 1//6], [1//2, a + 1//2, 1//12*a]]
  L95 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L95)) == res[95]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 18]);
  gens = [[3, 0, 0], [3//2*a + 12, 0, 0], [a + 1, 2, 0], [1//2*a + 1, a, 0], [0, 1//2*a, 1//6], [0, 1//2*a, 1//6]]
  L96 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L96)) == res[96]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 18]);
  gens = [[3, 0, 0], [6*a + 3, 0, 0], [3, 2, 0], [9//2*a + 3, 3*a + 2, 0], [3//2*a + 5, 3//2*a, 1//6], [5//2*a + 3//2, 3//2, 1//12*a]]
  L97 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L97)) == res[97]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 18]);
  gens = [[3, 0, 0], [21//2*a + 3, 0, 0], [1, 1, 0], [1, 1, 0], [2, 0, 1//3], [a, 0, 1//6*a]]
  L98 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L98)) == res[98]
  D = matrix(K, 3, 3, [-205*a + 436, 0, 0, 0, 4*a + 7, 0, 0, 0, 3090*a + 14120]);
  gens = [[1, 0, 0], [1, 0, 0], [15, 1, 0], [2790//17*a + 3915//17, 186//17*a + 261//17, 0], [29070, 0, 1], [8462435788035//3119*a + 1812910241880//3119, 0, 9897585717//106046*a + 1060181428//53023]]
  L99 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L99)) == res[99]
  D = matrix(K, 3, 3, [-205*a + 436, 0, 0, 0, 4*a + 7, 0, 0, 0, 3090*a + 14120]);
  gens = [[2, 0, 0], [a, 0, 0], [32, 1, 0], [6016//17*a + 6336//17, 188//17*a + 198//17, 0], [1//2*a + 32898, 0, 1//2], [3361663056605//3119*a + 3486801763620//3119, 0, 868553880//53023*a + 900873805//53023]]
  L100 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L100)) == res[100]
  D = matrix(K, 3, 3, [-205*a + 436, 0, 0, 0, 4*a + 7, 0, 0, 0, 3090*a + 14120]);
  gens = [[2, 0, 0], [3*a + 2, 0, 0], [30, 2, 0], [13545//17*a + 2880//17, 903//17*a + 192//17, 0], [3//2*a + 25958, a + 5536, 1//2], [92798248069060//53023*a + 168073469590157//106046, 6345963398//17*a + 5747731305//17, 7149502471//212092*a + 1618499317//53023]]
  L101 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L101)) == res[101]
  D = matrix(K, 3, 3, [-205*a + 436, 0, 0, 0, 4*a + 7, 0, 0, 0, 3090*a + 14120]);
  gens = [[2, 0, 0], [a + 2, 0, 0], [30, 2, 0], [13905//17*a + 3270//17, 927//17*a + 218//17, 0], [1//2*a + 32898, 0, 1//2], [8909688593811//3119*a + 1240451654017//6238, 0, 9208130945//212092*a + 160180482//53023]]
  L102 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L102)) == res[102]
  D = matrix(K, 3, 3, [-205*a + 436, 0, 0, 0, 4*a + 7, 0, 0, 0, 3090*a + 14120]);
  gens = [[2, 0, 0], [2, 0, 0], [a + 4, 1, 0], [898//17*a + 834//17, 197//17*a + 110//17, 0], [3//2*a + 175670, 0, 1//2], [15848132682979//6238*a + 37422997176485//6238, 0, 1533630235//212092*a + 1810742731//106046]]
  L103 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L103)) == res[103]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 20]);
  gens = [[1, 0, 0], [3//2*a + 1, 0, 0], [0, 2, 0], [0, 2, 0], [0, a + 1, 1//2], [0, 3//2*a + 3, 3//4*a]]
  L104 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L104)) == res[104]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 20]);
  gens = [[1, 0, 0], [1, 0, 0], [1, 2, 0], [1//2*a, a, 0], [1, 1, 1//2], [3//2*a, 3//2*a, 3//4*a]]
  L105 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L105)) == res[105]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 20]);
  gens = [[1, 0, 0], [1//2*a, 0, 0], [0, 1, 0], [0, 1, 0], [0, 0, 1], [0, 0, 3//2*a]]
  L106 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L106)) == res[106]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 20]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 2, 0], [0, a, 0], [0, a + 1, 1//2], [0, 3//2*a + 3, 3//4*a]]
  L107 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L107)) == res[107]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 20]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 2, 0], [0, 2, 0], [1//2*a + 1//2, 3//2, 1//4], [1//2*a + 1//2, 3//2, 1//4]]
  L108 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L108)) == res[108]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 20]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 2, 0], [0, a, 0], [1, 1, 1//2], [3//2*a, 3//2*a, 3//4*a]]
  L109 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L109)) == res[109]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 20]);
  gens = [[2, 0, 0], [3*a, 0, 0], [a + 1, 2, 0], [1//2*a + 1, a, 0], [1//2*a + 3//2, 3//2, 1//4], [1//2*a + 3//2, 3//2, 1//4]]
  L110 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L110)) == res[110]
  D = matrix(K, 3, 3, [-1111*a + 2146, 0, 0, 0, -22*a + 77, 0, 0, 0, -1460349*a + 2355386]);
  gens = [[1, 0, 0], [1, 0, 0], [15, 1, 0], [21105//41*a + 22515//41, 1407//41*a + 1501//41, 0], [1931715, 0, 1//11], [39973961395832985//52114*a + 69816419510950935//26057, 0, 848433861739//23503414*a + 1481829980069//11751707]]
  L111 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L111)) == res[111]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 22]);
  gens = [[1, 0, 0], [3//2*a + 1, 0, 0], [0, 2, 0], [0, 2, 0], [0, 1//2*a + 2, 1//2], [0, 3*a + 3//2, 3//4*a]]
  L112 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L112)) == res[112]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 22]);
  gens = [[1, 0, 0], [3//2*a, 0, 0], [0, 2, 0], [0, a, 0], [0, 1//2*a, 1//2], [0, 1//2*a, 1//2]]
  L113 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L113)) == res[113]
  D = matrix(K, 3, 3, [-63*a + 154, 0, 0, 0, 10*a + 19, 0, 0, 0, 4116*a + 19992]);
  gens = [[1, 0, 0], [47//7*a + 34//7, 0, 0], [146, 2, 0], [3942657//161*a + 5238626//161, 54009//161*a + 71762//161, 0], [0, 0, 1//14], [0, 0, 1//322*a + 5//322]]
  L114 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L114)) == res[114]
  D = matrix(K, 3, 3, [-63*a + 154, 0, 0, 0, 10*a + 19, 0, 0, 0, 4116*a + 19992]);
  gens = [[2, 0, 0], [51//7*a + 162//7, 0, 0], [146, 2, 0], [4072743//161*a + 1604248//161, 55791//161*a + 21976//161, 0], [1//7*a + 179//7, 0, 1//14], [1259//14*a + 7509//7, 0, 151//644*a + 482//161]]
  L115 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L115)) == res[115]
  D = matrix(K, 3, 3, [-63*a + 154, 0, 0, 0, 10*a + 19, 0, 0, 0, 4116*a + 19992]);
  gens = [[2, 0, 0], [185//7*a + 124//7, 0, 0], [146, 2, 0], [2337095//161*a + 6025566//161, 32015//161*a + 82542//161, 0], [221//7, 1//7*a + 10//7, 1//14], [123539//322*a + 8177//23, 3054//161*a + 3149//161, 559//644*a + 37//46]]
  L116 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L116)) == res[116]
  D = matrix(K, 3, 3, [-63*a + 154, 0, 0, 0, 10*a + 19, 0, 0, 0, 4116*a + 19992]);
  gens = [[2, 0, 0], [109//7*a + 142//7, 0, 0], [146, 2, 0], [497349//161*a + 3341356//161, 6813//161*a + 45772//161, 0], [1//7*a + 239//7, 1//7*a + 10//7, 1//14], [88457//322*a + 203513//161, 2665//161*a + 8863//161, 363//644*a + 425//161]]
  L117 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L117)) == res[117]
  D = matrix(K, 3, 3, [-63*a + 154, 0, 0, 0, 10*a + 19, 0, 0, 0, 4116*a + 19992]);
  gens = [[2, 0, 0], [193//7*a + 58//7, 0, 0], [234, 1, 0], [1880892//161*a + 3064464//161, 8038//161*a + 13096//161, 0], [23, 0, 1//14], [101*a + 183, 0, 101//322*a + 183//322]]
  L118 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L118)) == res[118]
  D = matrix(K, 3, 3, [-63*a + 154, 0, 0, 0, 10*a + 19, 0, 0, 0, 4116*a + 19992]);
  gens = [[2, 0, 0], [8//7*a + 130//7, 0, 0], [234, 1, 0], [1771614//161*a + 5106816//161, 7571//161*a + 21824//161, 0], [69, 0, 1//14], [909//2*a + 858, 0, 303//644*a + 143//161]]
  L119 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L119)) == res[119]
  D = matrix(K, 3, 3, [-63*a + 154, 0, 0, 0, 10*a + 19, 0, 0, 0, 4116*a + 19992]);
  gens = [[4, 0, 0], [594//7*a + 444//7, 0, 0], [234, 1, 0], [4684212//161*a + 2070666//161, 20018//161*a + 8849//161, 0], [1//14*a + 823//14, 0, 1//28], [18//7*a + 179//14, 0, 1//644*a + 5//644]]
  L120 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L120)) == res[120]
  D = matrix(K, 3, 3, [-63*a + 154, 0, 0, 0, 10*a + 19, 0, 0, 0, 4116*a + 19992]);
  gens = [[1, 0, 0], [25//7*a + 30//7, 0, 0], [146, 2, 0], [1899460//161*a + 3865934//161, 26020//161*a + 52958//161, 0], [23, 0, 1//14], [723//2*a + 255, 0, 723//644*a + 255//322]]
  L121 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L121)) == res[121]
  D = matrix(K, 3, 3, [-63*a + 154, 0, 0, 0, 10*a + 19, 0, 0, 0, 4116*a + 19992]);
  gens = [[2, 0, 0], [16//7*a + 22//7, 0, 0], [1//7*a + 207//7, 1, 0], [620496//161*a + 36670//23, 20942//161*a + 8478//161, 0], [1//7*a + 179//7, 0, 1//14], [8325//14*a + 4708//7, 0, 1063//644*a + 599//322]]
  L122 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L122)) == res[122]
  D = matrix(K, 3, 3, [-63*a + 154, 0, 0, 0, 10*a + 19, 0, 0, 0, 4116*a + 19992]);
  gens = [[2, 0, 0], [17//7*a + 12//7, 0, 0], [1//7*a + 718//7, 2, 0], [2165122//161*a + 1768509//161, 42169//161*a + 34366//161, 0], [23, 0, 1//14], [375//2*a + 512, 0, 375//644*a + 256//161]]
  L123 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L123)) == res[123]
  D = matrix(K, 3, 3, [-63*a + 154, 0, 0, 0, 10*a + 19, 0, 0, 0, 4116*a + 19992]);
  gens = [[1, 0, 0], [38//7*a + 5//7, 0, 0], [146, 2, 0], [3705918//161*a + 6702714//161, 50766//161*a + 91818//161, 0], [31, 2, 1//14], [32333//46*a + 11315//23, 1043//23*a + 730//23, 149//92*a + 365//322]]
  L124 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L124)) == res[124]
  D = matrix(K, 3, 3, [-63*a + 154, 0, 0, 0, 10*a + 19, 0, 0, 0, 4116*a + 19992]);
  gens = [[4, 0, 0], [354//7*a + 352//7, 0, 0], [1//7*a + 3588//7, 1, 0], [5686306//161*a + 6780388//161, 11090//161*a + 13222//161, 0], [3//14*a + 1181//14, 0, 1//28], [13252//7*a + 23703//14, 0, 515//644*a + 459//644]]
  L125 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L125)) == res[125]
  D = matrix(K, 3, 3, [-63*a + 154, 0, 0, 0, 10*a + 19, 0, 0, 0, 4116*a + 19992]);
  gens = [[4, 0, 0], [510//7*a + 164//7, 0, 0], [1//7*a + 3588//7, 1, 0], [1046149//161*a + 12841008//161, 2034//161*a + 25051//161, 0], [1//14*a + 501//14, 0, 1//28], [8583//14*a + 5637//7, 0, 393//644*a + 129//161]]
  L126 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L126)) == res[126]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 24]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 4, 0], [0, 10*a + 8, 0], [1, 1//2*a, 1//4], [3//2*a, 3//2, 3//8*a]]
  L127 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L127)) == res[127]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 24]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 4, 0], [0, 2*a, 0], [1, 3//2*a + 2, 1//4], [3//2*a, 3*a + 9//2, 3//8*a]]
  L128 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L128)) == res[128]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 24]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 4, 0], [0, 2*a + 4, 0], [0, 1//2*a + 2, 1//4], [0, 3*a + 3//2, 3//8*a]]
  L129 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L129)) == res[129]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 24]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 2, 0], [0, 2, 0], [1//2*a, 3//2*a, 1//4], [1//2*a, 3//2*a, 1//4]]
  L130 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L130)) == res[130]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 24]);
  gens = [[2, 0, 0], [a + 2, 0, 0], [1//2*a + 1, 1, 0], [1//2*a + 1, 1, 0], [a, 0, 1//2], [3, 0, 3//4*a]]
  L131 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L131)) == res[131]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 24]);
  gens = [[1, 0, 0], [1, 0, 0], [1, 2, 0], [1//2*a, a, 0], [1, a, 1//2], [3//2*a, 3, 3//4*a]]
  L132 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L132)) == res[132]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 24]);
  gens = [[1, 0, 0], [1//2*a, 0, 0], [0, 2, 0], [0, 2*a + 2, 0], [0, a, 1//2], [0, 3, 3//4*a]]
  L133 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L133)) == res[133]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 24]);
  gens = [[2, 0, 0], [a + 2, 0, 0], [1//2*a, 2, 0], [1//2*a, 2, 0], [a + 1, 1//2*a + 2, 1//4], [3//2*a + 3, 3*a + 3//2, 3//8*a]]
  L134 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L134)) == res[134]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 24]);
  gens = [[2, 0, 0], [a, 0, 0], [1//2*a + 1, 2, 0], [1//2*a + 1, 2, 0], [a + 1, 1//2*a + 2, 1//4], [3//2*a + 3, 3*a + 3//2, 3//8*a]]
  L135 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L135)) == res[135]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 24]);
  gens = [[2, 0, 0], [a, 0, 0], [a + 1, 2, 0], [1//2*a + 1, a, 0], [1//2*a, 1//2*a, 1//4], [1//2*a, 1//2*a, 1//4]]
  L136 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L136)) == res[136]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 24]);
  gens = [[2, 0, 0], [3*a + 2, 0, 0], [0, 2, 0], [0, 2, 0], [0, 1//2*a + 2, 1//4], [0, 3*a + 3//2, 3//8*a]]
  L137 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L137)) == res[137]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 24]);
  gens = [[2, 0, 0], [3*a, 0, 0], [0, 2, 0], [0, a, 0], [0, 1//2*a, 1//4], [0, 1//2*a, 1//4]]
  L138 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L138)) == res[138]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 24]);
  gens = [[2, 0, 0], [a + 2, 0, 0], [1, 2, 0], [1//2*a, a, 0], [0, 1//2*a, 1//4], [0, 1//2*a, 1//4]]
  L139 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L139)) == res[139]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 24]);
  gens = [[2, 0, 0], [a, 0, 0], [1, 2, 0], [1, 2, 0], [1, 3//2*a + 2, 1//4], [3//2*a, 3*a + 9//2, 3//8*a]]
  L140 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L140)) == res[140]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 24]);
  gens = [[2, 0, 0], [a + 2, 0, 0], [0, 2, 0], [0, 2, 0], [1, 1//2*a + 2, 1//4], [3//2*a, 3*a + 3//2, 3//8*a]]
  L141 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L141)) == res[141]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 24]);
  gens = [[2, 0, 0], [3*a, 0, 0], [1//2*a, 1, 0], [1//2*a, 1, 0], [1, 0, 1//2], [3//2*a, 0, 3//4*a]]
  L142 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L142)) == res[142]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 24]);
  gens = [[2, 0, 0], [3*a, 0, 0], [1, 2, 0], [1, 2, 0], [a + 1, 3//2*a + 2, 1//4], [3//2*a + 3, 3*a + 9//2, 3//8*a]]
  L143 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L143)) == res[143]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 24]);
  gens = [[1, 0, 0], [3//2*a + 1, 0, 0], [0, 4, 0], [0, 4*a + 4, 0], [0, 1//2*a + 2, 1//4], [0, 3*a + 3//2, 3//8*a]]
  L144 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L144)) == res[144]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 24]);
  gens = [[1, 0, 0], [1//2*a, 0, 0], [0, 4, 0], [0, 6*a + 4, 0], [0, 1//2*a + 3, 1//4], [0, 1//2*a + 3, 1//4]]
  L145 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L145)) == res[145]

  # The next is the unrolled version of
  # sig = Dict([(pl[1],1),(pl[2],2)])
  # for d in 1:12
  #  for g in Hecke.quadratic_genera(F,rank=3,det=d*OF,signatures=sig)
  #    representatives(g)

  res = [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
         1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
         1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
         1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
         1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
         1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
         1, 1, 1, 1, 1, 1, 1 ]

  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -2*a - 2]);
  gens = [[2, 0, 0], [a, 0, 0], [1//4*a + 1, 1//2, 0], [1//4*a + 1, 1//2, 0], [0, 0, 1], [0, 0, 3//2*a]]
  L1 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L1)) == res[1]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -2*a - 2]);
  gens = [[1, 0, 0], [1, 0, 0], [1//2*a, 1, 0], [3//2, 3//2*a, 0], [0, 0, 1], [0, 0, 3//2*a]]
  L2 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L2)) == res[2]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -4*a - 4]);
  gens = [[2, 0, 0], [2*a + 2, 0, 0], [7//4*a + 1, 1//2, 0], [7//4*a + 1, 1//2, 0], [0, 0, 1//2], [0, 0, 1//2]]
  L3 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L3)) == res[3]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -4*a - 4]);
  gens = [[2, 0, 0], [a + 2, 0, 0], [1//2*a, 1, 0], [1//2*a + 1//2, 1//2*a + 1, 0], [0, 0, 1//2], [0, 0, 1//2]]
  L4 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L4)) == res[4]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -4*a - 4]);
  gens = [[1, 0, 0], [1//2*a, 0, 0], [0, 2, 0], [0, a, 0], [0, 0, 1//2], [0, 0, 1//2]]
  L5 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L5)) == res[5]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -4*a - 4]);
  gens = [[2, 0, 0], [3*a + 2, 0, 0], [1//2*a, 1, 0], [1//2*a + 1//2, 1//2*a + 1, 0], [1//4*a + 1, 1//2, 1//2], [1//4*a + 1, 1//2, 1//2]]
  L6 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L6)) == res[6]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -4*a - 4]);
  gens = [[1, 0, 0], [1, 0, 0], [1//2*a, 1, 0], [1//2*a, 1, 0], [1//2, 1//2*a, 1//2], [1//2, 1//2*a, 1//2]]
  L7 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L7)) == res[7]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -4*a - 4]);
  gens = [[1, 0, 0], [1, 0, 0], [1//2*a, 1, 0], [3//2, 3//2*a, 0], [0, 0, 1], [0, 0, 1//2*a + 1]]
  L8 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L8)) == res[8]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -4*a - 4]);
  gens = [[2, 0, 0], [a + 2, 0, 0], [3//4*a + 1, 1//2, 0], [3//4*a + 1, 1//2, 0], [0, 0, 1], [0, 0, 1//2*a]]
  L9 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L9)) == res[9]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -6*a - 6]);
  gens = [[2, 0, 0], [3*a + 2, 0, 0], [1//4*a + 1, 1//2, 0], [1//4*a + 1, 1//2, 0], [0, 0, 1], [0, 0, 3//2*a]]
  L10 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L10)) == res[10]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -6*a - 6]);
  gens = [[1, 0, 0], [1, 0, 0], [1//2*a, 1, 0], [3//2, 3//2*a, 0], [0, 0, 1], [0, 0, 3//2*a]]
  L11 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L11)) == res[11]
  D = matrix(K, 3, 3, [21*a - 14, 0, 0, 0, -2*a - 1, 0, 0, 0, -189*a - 168]);
  gens = [[2, 0, 0], [85//7*a + 80//7, 0, 0], [1, 1, 0], [1, 1, 0], [2//7*a + 9//14, 1//2*a + 5, 1//14], [3//14*a + 5//14, 13//14*a + 16//7, 1//98*a + 3//98]]
  L12 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L12)) == res[12]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -8*a - 8]);
  gens = [[2, 0, 0], [2, 0, 0], [3//4*a + 1, 1//2, 0], [3//4*a + 1, 1//2, 0], [0, 0, 1//2], [0, 0, 1//2]]
  L13 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L13)) == res[13]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -8*a - 8]);
  gens = [[2, 0, 0], [2*a + 2, 0, 0], [3//4*a, 1//2, 0], [3//4*a, 1//2, 0], [0, 0, 1//2], [0, 0, 1//2]]
  L14 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L14)) == res[14]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -8*a - 8]);
  gens = [[2, 0, 0], [2, 0, 0], [3//2*a + 2, 1, 0], [5//2*a + 7//2, 1//2*a + 1, 0], [a + 3//2, 1//2*a, 1//2], [9//4*a + 3, 3//2, 3//4*a]]
  L15 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L15)) == res[15]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -8*a - 8]);
  gens = [[2, 0, 0], [a + 2, 0, 0], [1//2*a + 1, 1, 0], [1//2*a + 1, 1, 0], [0, 0, 1//2], [0, 0, 3//4*a]]
  L16 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L16)) == res[16]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -8*a - 8]);
  gens = [[2, 0, 0], [2, 0, 0], [3//2*a + 2, 1, 0], [3*a + 9//2, 3//2*a, 0], [2, 0, 1//2], [3*a, 0, 3//4*a]]
  L17 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L17)) == res[17]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -8*a - 8]);
  gens = [[4, 0, 0], [2*a, 0, 0], [5//4*a, 1//2, 0], [5//4*a, 1//2, 0], [2*a, 0, 1//2], [6, 0, 3//4*a]]
  L18 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L18)) == res[18]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -8*a - 8]);
  gens = [[2, 0, 0], [2, 0, 0], [1//2*a, 1, 0], [3//2, 3//2*a, 0], [0, 0, 1//2], [0, 0, 3//4*a]]
  L19 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L19)) == res[19]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -8*a - 8]);
  gens = [[2, 0, 0], [a + 2, 0, 0], [0, 1, 0], [0, 1, 0], [a + 1, 0, 1//2], [3//2*a + 3, 0, 3//4*a]]
  L20 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L20)) == res[20]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -8*a - 8]);
  gens = [[1, 0, 0], [1//2*a + 1, 0, 0], [0, 2, 0], [0, 2*a + 2, 0], [0, a + 2, 1//2], [0, 3*a + 3, 3//4*a]]
  L21 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L21)) == res[21]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -8*a - 8]);
  gens = [[4, 0, 0], [2*a + 4, 0, 0], [5//4*a + 1, 1//2, 0], [5//4*a + 1, 1//2, 0], [2*a + 2, 0, 1//2], [3*a + 6, 0, 3//4*a]]
  L22 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L22)) == res[22]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -8*a - 8]);
  gens = [[2, 0, 0], [a, 0, 0], [1, 1, 0], [1, 1, 0], [a, 0, 1//2], [3, 0, 3//4*a]]
  L23 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L23)) == res[23]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -8*a - 8]);
  gens = [[2, 0, 0], [3*a + 2, 0, 0], [1//2*a, 1, 0], [1//2*a, 1, 0], [3//2*a + 1//2, 1//2*a + 1, 1//2], [3//4*a + 9//2, 3//2*a + 3//2, 3//4*a]]
  L24 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L24)) == res[24]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -8*a - 8]);
  gens = [[2, 0, 0], [2*a + 2, 0, 0], [1//2*a, 1, 0], [3//2, 3//2*a, 0], [a, 0, 1//2], [3, 0, 3//4*a]]
  L25 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L25)) == res[25]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -8*a - 8]);
  gens = [[2, 0, 0], [2, 0, 0], [3//4*a, 1//2, 0], [3//4*a, 1//2, 0], [a, 0, 1//2], [a, 0, 1//2]]
  L26 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L26)) == res[26]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -8*a - 8]);
  gens = [[4, 0, 0], [2*a + 4, 0, 0], [3//4*a + 2, 1//2, 0], [3//4*a + 2, 1//2, 0], [2*a + 2, 0, 1//2], [3*a + 6, 0, 3//4*a]]
  L27 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L27)) == res[27]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -8*a - 8]);
  gens = [[2, 0, 0], [3*a + 2, 0, 0], [1//2*a + 1, 1, 0], [1//2*a + 1, 1, 0], [1, 0, 1//2], [3//2*a, 0, 3//4*a]]
  L28 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L28)) == res[28]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -8*a - 8]);
  gens = [[2, 0, 0], [3*a + 2, 0, 0], [1//2*a, 1, 0], [1//2*a, 1, 0], [1, 0, 1//2], [3//2*a, 0, 3//4*a]]
  L29 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L29)) == res[29]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -8*a - 8]);
  gens = [[1, 0, 0], [1, 0, 0], [1//2*a, 1, 0], [3//2, 3//2*a, 0], [0, 0, 1], [0, 0, 3//2*a + 1]]
  L30 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L30)) == res[30]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -8*a - 8]);
  gens = [[2, 0, 0], [2, 0, 0], [1//4*a + 1, 1//2, 0], [1//4*a + 1, 1//2, 0], [a, 0, 1//2], [a, 0, 1//2]]
  L31 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L31)) == res[31]
  D = matrix(K, 3, 3, [55*a - 44, 0, 0, 0, -4*a - 3, 0, 0, 0, -1485*a - 1430]);
  gens = [[2, 0, 0], [3*a, 0, 0], [1, 1, 0], [1, 1, 0], [9//22*a + 12743//22, 1//2*a + 105, 1//22], [77444727//374*a + 40829486//187, 867040//23*a + 917331//23, 139677//8602*a + 73595//4301]]
  L32 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L32)) == res[32]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -10*a - 10]);
  gens = [[2, 0, 0], [3*a, 0, 0], [1//4*a + 1, 1//2, 0], [1//4*a + 1, 1//2, 0], [0, 0, 1], [0, 0, 3//2*a]]
  L33 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L33)) == res[33]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -10*a - 10]);
  gens = [[2, 0, 0], [3*a, 0, 0], [3//4*a, 1//2, 0], [3//4*a, 1//2, 0], [0, 0, 1], [0, 0, 3//2*a]]
  L34 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L34)) == res[34]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -12*a - 12]);
  gens = [[1, 0, 0], [1//2*a, 0, 0], [0, 2, 0], [0, a, 0], [0, 1, 1//2], [0, 1, 1//2]]
  L35 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L35)) == res[35]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -12*a - 12]);
  gens = [[1, 0, 0], [1, 0, 0], [1//2*a, 1, 0], [1//2*a, 1, 0], [0, 0, 1//2], [0, 0, 1//2]]
  L36 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L36)) == res[36]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -12*a - 12]);
  gens = [[2, 0, 0], [2, 0, 0], [5//4*a + 1, 1//2, 0], [5//4*a + 1, 1//2, 0], [a, 0, 1//2], [a, 0, 1//2]]
  L37 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L37)) == res[37]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -12*a - 12]);
  gens = [[1, 0, 0], [1, 0, 0], [1//2*a, 1, 0], [1//2*a, 1, 0], [1//2, 1//2*a, 1//2], [1//2, 1//2*a, 1//2]]
  L38 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L38)) == res[38]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -12*a - 12]);
  gens = [[2, 0, 0], [3*a + 2, 0, 0], [1//4*a + 1, 1//2, 0], [1//4*a + 1, 1//2, 0], [0, 0, 1], [0, 0, 3//2*a]]
  L39 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L39)) == res[39]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -12*a - 12]);
  gens = [[2, 0, 0], [3*a, 0, 0], [3//2*a, 1, 0], [3//2*a + 3//2, 1//2*a + 1, 0], [3//4*a + 1, 1//2, 1//2], [3//4*a + 1, 1//2, 1//2]]
  L40 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L40)) == res[40]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -12*a - 12]);
  gens = [[1, 0, 0], [1, 0, 0], [1//2*a, 1, 0], [1//2*a, 1, 0], [1//2*a + 1//2, 1//2*a, 1//2], [1//2*a + 1//2, 1//2*a, 1//2]]
  L41 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L41)) == res[41]
  D = matrix(K, 3, 3, [21*a - 14, 0, 0, 0, -2*a - 1, 0, 0, 0, -378*a - 336]);
  gens = [[2, 0, 0], [80//7*a + 58//7, 0, 0], [1//7*a + 3//7, 1, 0], [1//7*a + 3//7, 1, 0], [23//14*a + 18//7, 5, 1//14], [123//7*a + 337//14, 325//14*a + 120//7, 65//196*a + 12//49]]
  L42 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L42)) == res[42]
  D = matrix(K, 3, 3, [21*a - 14, 0, 0, 0, -2*a - 1, 0, 0, 0, -378*a - 336]);
  gens = [[2, 0, 0], [151//7*a + 166//7, 0, 0], [1, 1, 0], [1, 1, 0], [9//14*a + 4//7, 5, 1//14], [32//7*a + 58//7, 190//7*a + 80//7, 19//49*a + 8//49]]
  L43 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L43)) == res[43]
  D = matrix(K, 3, 3, [21*a - 14, 0, 0, 0, -2*a - 1, 0, 0, 0, -378*a - 336]);
  gens = [[2, 0, 0], [162//7*a + 66//7, 0, 0], [1, 1, 0], [1, 1, 0], [23//14*a + 4//7, 5, 1//14], [53//7*a + 11//2, 65//14*a + 150//7, 13//196*a + 15//49]]
  L44 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L44)) == res[44]
  D = matrix(K, 3, 3, [21*a - 14, 0, 0, 0, -2*a - 1, 0, 0, 0, -378*a - 336]);
  gens = [[2, 0, 0], [55//7*a + 130//7, 0, 0], [0, 1, 0], [0, 1, 0], [9//14*a + 4//7, 5, 1//14], [5//14*a + 3//7, 5//7*a + 15//7, 1//98*a + 3//98]]
  L45 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L45)) == res[45]
  D = matrix(K, 3, 3, [21*a - 14, 0, 0, 0, -2*a - 1, 0, 0, 0, -378*a - 336]);
  gens = [[2, 0, 0], [45//7*a + 128//7, 0, 0], [0, 2, 0], [0, 3*a, 0], [23//14*a + 4//7, 5, 1//14], [303//14*a + 695//14, 955//14*a + 295//7, 191//196*a + 59//98]]
  L46 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L46)) == res[46]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -14*a - 14]);
  gens = [[2, 0, 0], [3*a, 0, 0], [3//4*a + 1, 1//2, 0], [3//4*a + 1, 1//2, 0], [0, 0, 1], [0, 0, 3//2*a]]
  L47 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L47)) == res[47]
  D = matrix(K, 3, 3, [8, 0, 0, 0, -a - 2, 0, 0, 0, -168*a - 224]);
  gens = [[1, 0, 0], [3//2*a + 1, 0, 0], [1//4*a + 1//2, 1, 0], [1//4*a + 1//2, 1, 0], [1//8*a + 1//4, 1//4*a + 1//2, 1//8], [1//8*a + 1//4, 1//4*a + 1//2, 1//8]]
  L48 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L48)) == res[48]
  D = matrix(K, 3, 3, [735*a - 720, 0, 0, 0, -297*a + 138, 0, 0, 0, -1544760*a + 662130]);
  gens = [[2, 0, 0], [3*a + 2, 0, 0], [2//3*a + 6581//3, 1//3, 0], [7586941063//2498*a + 7337623298//3747, 3457889//7494*a + 1113920//3747, 0], [7//30*a + 174727//30, 7//6, 1//30], [25835117566//18735*a + 768641365057//37470, 2068805//7494*a + 10264509//2498, 413761//52458*a + 10264509//87430]]
  L49 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L49)) == res[49]
  D = matrix(K, 3, 3, [735*a - 720, 0, 0, 0, -15*a - 18, 0, 0, 0, -80640*a - 97650]);
  gens = [[2, 0, 0], [a, 0, 0], [a + 5//3, 1//3, 0], [5//2*a + 3, 1//2*a, 0], [4//5*a + 270037//30, 8743//6, 1//30], [149430044977//37470*a + 1983820290617//37470, 3869011//6*a + 51424643//6, 3869011//262290*a + 51424643//262290]]
  L50 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L50)) == res[50]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -14*a - 14]);
  gens = [[1, 0, 0], [1, 0, 0], [1//2*a, 1, 0], [1//2*a + 3//2, 3//2*a + 1, 0], [0, 0, 1], [0, 0, 3//2*a]]
  L51 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L51)) == res[51]
  D = matrix(K, 3, 3, [8, 0, 0, 0, -a - 2, 0, 0, 0, -168*a - 224]);
  gens = [[1, 0, 0], [3//2*a + 1, 0, 0], [1//4*a + 1//2, 1, 0], [1//4*a + 1//2, 1, 0], [3//8*a + 1//4, 1//4*a + 1//2, 1//8], [3//8*a + 1//4, 1//4*a + 1//2, 1//8]]
  L52 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L52)) == res[52]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[2, 0, 0], [2*a + 2, 0, 0], [3//2*a + 2, 1, 0], [3*a + 9//2, 3//2*a, 0], [0, 0, 1//2], [0, 0, 1//4*a + 1//2]]
  L53 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L53)) == res[53]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[2, 0, 0], [2*a + 2, 0, 0], [3//2*a, 1, 0], [9//2, 3//2*a, 0], [0, 0, 1//2], [0, 0, 3//4*a + 1//2]]
  L54 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L54)) == res[54]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[4, 0, 0], [6*a + 4, 0, 0], [7//4*a + 3, 1//2, 0], [7//4*a + 3, 1//2, 0], [0, 0, 1//2], [0, 0, 3//4*a]]
  L55 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L55)) == res[55]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[2, 0, 0], [a, 0, 0], [0, 2, 0], [0, a, 0], [0, 1, 1//4], [0, 1, 1//4]]
  L56 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L56)) == res[56]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[2, 0, 0], [3*a + 2, 0, 0], [1//2*a, 1, 0], [1//2*a, 1, 0], [1//2*a, 1, 1//2], [3//2, 3//2*a, 3//4*a]]
  L57 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L57)) == res[57]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[2, 0, 0], [3*a, 0, 0], [a, 2, 0], [1, a, 0], [1, 1, 1//4], [1, 1, 1//4]]
  L58 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L58)) == res[58]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[2, 0, 0], [3*a, 0, 0], [1//2*a + 1, 1, 0], [1//2*a + 1, 1, 0], [a, 0, 1//2], [3, 0, 3//4*a]]
  L59 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L59)) == res[59]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[2, 0, 0], [2, 0, 0], [3//2*a + 2, 1, 0], [9//2*a + 13//2, 3//2*a + 1, 0], [a + 3//2, 1//2*a, 1//2], [9//4*a + 3, 3//2, 3//4*a]]
  L60 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L60)) == res[60]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[2, 0, 0], [3*a + 2, 0, 0], [1//2*a, 1, 0], [3//2, 3//2*a, 0], [0, 0, 1//2], [0, 0, 1//2]]
  L61 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L61)) == res[61]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[4, 0, 0], [2*a + 4, 0, 0], [3//2*a + 2, 1, 0], [3*a + 9//2, 3//2*a, 0], [3//4*a + 3, 1//2, 1//4], [3//4*a + 3, 1//2, 1//4]]
  L62 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L62)) == res[62]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[4, 0, 0], [4*a + 4, 0, 0], [1//4*a + 2, 1//2, 0], [1//4*a + 2, 1//2, 0], [0, 0, 1//4], [0, 0, 1//4]]
  L63 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L63)) == res[63]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[4, 0, 0], [4*a + 4, 0, 0], [15//4*a + 2, 1//2, 0], [15//4*a + 2, 1//2, 0], [2*a, 0, 1//4], [2*a, 0, 1//4]]
  L64 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L64)) == res[64]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[2, 0, 0], [2*a + 2, 0, 0], [1//2*a, 1, 0], [1//2*a, 1, 0], [a + 1//2, 1//2*a, 1//4], [a + 1//2, 1//2*a, 1//4]]
  L65 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L65)) == res[65]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[2, 0, 0], [2*a + 2, 0, 0], [3//2*a, 1, 0], [3//2*a, 1, 0], [3//2, 1//2*a, 1//4], [3//2, 1//2*a, 1//4]]
  L66 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L66)) == res[66]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[4, 0, 0], [2*a, 0, 0], [5//2*a, 1, 0], [15//2, 3//2*a, 0], [2, 0, 1//4], [2, 0, 1//4]]
  L67 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L67)) == res[67]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[2, 0, 0], [a + 2, 0, 0], [0, 2, 0], [0, a, 0], [0, 0, 1//4], [0, 0, 1//4]]
  L68 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L68)) == res[68]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[4, 0, 0], [2*a + 4, 0, 0], [3//2*a + 2, 1, 0], [3*a + 9//2, 3//2*a, 0], [7//4*a + 1, 1//2, 1//4], [7//4*a + 1, 1//2, 1//4]]
  L69 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L69)) == res[69]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[4, 0, 0], [2*a + 4, 0, 0], [7//2*a + 2, 1, 0], [3*a + 21//2, 3//2*a, 0], [3//4*a + 1, 1//2, 1//4], [3//4*a + 1, 1//2, 1//4]]
  L70 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L70)) == res[70]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 1, 0], [0, 1, 0], [0, 0, 1//2], [0, 0, 1//2]]
  L71 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L71)) == res[71]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[2, 0, 0], [2, 0, 0], [3//2*a, 1, 0], [3//2*a, 1, 0], [1, 0, 1//4], [1, 0, 1//4]]
  L72 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L72)) == res[72]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[2, 0, 0], [2, 0, 0], [a, 1, 0], [a, 1, 0], [3//2*a + 1, 0, 1//4], [3//2*a + 1, 0, 1//4]]
  L73 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L73)) == res[73]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[4, 0, 0], [4, 0, 0], [3//4*a + 1, 1//2, 0], [3//4*a + 1, 1//2, 0], [0, 0, 1//4], [0, 0, 1//4]]
  L74 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L74)) == res[74]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[4, 0, 0], [4*a + 4, 0, 0], [15//4*a + 1, 1//2, 0], [15//4*a + 1, 1//2, 0], [0, 0, 1//4], [0, 0, 1//4]]
  L75 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L75)) == res[75]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[2, 0, 0], [2*a + 2, 0, 0], [0, 1, 0], [0, 1, 0], [3//2*a, 0, 1//4], [3//2*a, 0, 1//4]]
  L76 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L76)) == res[76]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, -16*a - 16]);
  gens = [[4, 0, 0], [4*a + 4, 0, 0], [7//4*a + 3, 1//2, 0], [7//4*a + 3, 1//2, 0], [a, 0, 1//4], [a, 0, 1//4]]
  L77 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L77)) == res[77]

  # The next is the unrolled version of
  # sig = Dict([(pl[1],1),(pl[2],1)])
  # for d in 1:12
  #  for g in Hecke.quadratic_genera(F,rank=3,det=d*OF,signatures=sig)
  #    representatives(g)

  res = [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
          1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
          1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
          1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
          1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
          1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
          1, 1, 1, 1, 1, 1, 1 ]

  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -2]);
  gens = [[1, 0, 0], [1//2*a + 1, 0, 0], [0, 2, 0], [0, 2, 0], [0, 1//2*a + 2, 1//2], [0, 3*a + 3//2, 3//4*a]]
  L1 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L1)) == res[1]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -2]);
  gens = [[1, 0, 0], [1//2*a, 0, 0], [0, 2, 0], [0, a, 0], [0, 1//2*a, 1//2], [0, 1//2*a, 1//2]]
  L2 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L2)) == res[2]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -4]);
  gens = [[1, 0, 0], [1, 0, 0], [1, 2, 0], [1//2*a, a, 0], [1, a + 1, 1//2], [3//2*a, 3//2*a + 3, 3//4*a]]
  L3 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L3)) == res[3]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -4]);
  gens = [[1, 0, 0], [3//2*a + 1, 0, 0], [0, 2, 0], [0, 2, 0], [0, 3, 1//2], [0, 9//2*a + 3, 3//4*a + 1//2]]
  L4 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L4)) == res[4]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -4]);
  gens = [[1, 0, 0], [1, 0, 0], [1//2*a, 2, 0], [1//2*a, 2, 0], [1//2*a, 3//2, 1//4], [1//2*a, 3//2, 1//4]]
  L5 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L5)) == res[5]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -4]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 2, 0], [0, 2, 0], [1//2*a, a + 3//2, 1//4], [1//2*a, a + 3//2, 1//4]]
  L6 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L6)) == res[6]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -4]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 2, 0], [0, 2, 0], [0, a + 3//2, 1//4], [0, a + 3//2, 1//4]]
  L7 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L7)) == res[7]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -4]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 2, 0], [0, a, 0], [0, 1, 1//2], [0, 3//2*a, 3//4*a]]
  L8 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L8)) == res[8]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -4]);
  gens = [[1, 0, 0], [1//2*a + 1, 0, 0], [0, 2, 0], [0, 2*a + 2, 0], [0, a + 3, 1//2], [0, 9//2*a + 3, 3//4*a]]
  L9 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L9)) == res[9]
  D = matrix(K, 3, 3, [21*a - 14, 0, 0, 0, -3*a + 3, 0, 0, 0, -315*a + 504]);
  gens = [[1, 0, 0], [17//7*a + 9//7, 0, 0], [0, 1, 0], [0, 1, 0], [5//7, 0, 1//21], [5//14*a, 0, 1//42*a]]
  L10 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L10)) == res[10]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -6]);
  gens = [[1, 0, 0], [1, 0, 0], [1, 2, 0], [1//2*a, a, 0], [1//2*a + 1, 1//2*a, 1//2], [3//2*a + 3//2, 3//2, 3//4*a]]
  L11 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L11)) == res[11]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -6]);
  gens = [[1, 0, 0], [3//2*a + 1, 0, 0], [0, 2, 0], [0, a, 0], [0, 1//2*a, 1//2], [0, 1//2*a, 1//2]]
  L12 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L12)) == res[12]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 4, 0], [0, 2*a, 0], [0, 1//2*a + 2, 1//4], [0, 3*a + 3//2, 3//8*a]]
  L13 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L13)) == res[13]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 2, 0], [0, 2, 0], [0, 1//2*a, 1//4], [0, 1//2*a, 1//4]]
  L14 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L14)) == res[14]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 4, 0], [0, 2*a, 0], [1, 3//2*a + 2, 1//4], [3//2*a, 3*a + 9//2, 3//8*a]]
  L15 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L15)) == res[15]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[1, 0, 0], [1, 0, 0], [1//2*a, 2, 0], [1//2*a, 2, 0], [0, 1//2*a, 1//4], [0, 1//2*a, 1//4]]
  L16 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L16)) == res[16]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[1, 0, 0], [1, 0, 0], [1//2*a, 2, 0], [1//2*a, 2, 0], [1//2*a, 1//2*a, 1//4], [1//2*a, 1//2*a, 1//4]]
  L17 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L17)) == res[17]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[1, 0, 0], [3//2*a + 1, 0, 0], [0, 4, 0], [0, 2*a + 4, 0], [0, 1//2*a + 2, 1//4], [0, 1//2*a + 2, 1//4]]
  L18 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L18)) == res[18]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 2, 0], [0, a, 0], [1, a, 1//2], [3//2*a, 3, 3//4*a]]
  L19 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L19)) == res[19]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[1, 0, 0], [1//2*a + 1, 0, 0], [0, 4, 0], [0, 12*a + 4, 0], [0, 3//2*a + 6, 1//4], [0, 9*a + 9//2, 3//8*a]]
  L20 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L20)) == res[20]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[1, 0, 0], [1, 0, 0], [1, 4, 0], [1//2*a, 2*a, 0], [0, 5//2*a + 2, 1//4], [0, 3*a + 15//2, 3//8*a]]
  L21 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L21)) == res[21]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[2, 0, 0], [a, 0, 0], [1, 1, 0], [1, 1, 0], [a, 0, 1//2], [3, 0, 3//4*a]]
  L22 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L22)) == res[22]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[2, 0, 0], [a, 0, 0], [1, 2, 0], [1, 2, 0], [1, 1//2*a + 2, 1//4], [3//2*a, 3*a + 3//2, 3//8*a]]
  L23 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L23)) == res[23]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[2, 0, 0], [3*a + 2, 0, 0], [a, 2, 0], [1, a, 0], [1//2*a + 1, 1//2*a + 1, 1//4], [1//2*a + 1, 1//2*a + 1, 1//4]]
  L24 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L24)) == res[24]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[2, 0, 0], [3*a + 2, 0, 0], [0, 2, 0], [0, 2, 0], [a, 3//2*a, 1//4], [3, 9//2, 3//8*a]]
  L25 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L25)) == res[25]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[2, 0, 0], [a + 2, 0, 0], [0, 2, 0], [0, a, 0], [1//2*a, 1//2*a, 1//4], [1//2*a, 1//2*a, 1//4]]
  L26 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L26)) == res[26]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[2, 0, 0], [3*a + 2, 0, 0], [1, 2, 0], [1, 2, 0], [0, 3//2*a + 2, 1//4], [0, 3*a + 9//2, 3//8*a]]
  L27 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L27)) == res[27]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[2, 0, 0], [a, 0, 0], [0, 2, 0], [0, a, 0], [1, 1//2*a, 1//4], [1, 1//2*a, 1//4]]
  L28 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L28)) == res[28]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[2, 0, 0], [3*a + 2, 0, 0], [1, 2, 0], [1, 2, 0], [a, 3//2*a + 2, 1//4], [3, 3*a + 9//2, 3//8*a]]
  L29 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L29)) == res[29]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[2, 0, 0], [a, 0, 0], [1//2*a, 2, 0], [1//2*a, 2, 0], [a + 1, 3//2*a + 2, 1//4], [3//2*a + 3, 3*a + 9//2, 3//8*a]]
  L30 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L30)) == res[30]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[1, 0, 0], [1//2*a + 1, 0, 0], [0, 4, 0], [0, 2*a, 0], [0, 1//2*a + 3, 1//4], [0, 1//2*a + 3, 1//4]]
  L31 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L31)) == res[31]
  D = matrix(K, 3, 3, [55*a - 44, 0, 0, 0, -15*a - 5, 0, 0, 0, -1925*a + 7150]);
  gens = [[2, 0, 0], [3*a + 2, 0, 0], [9, 1, 0], [522//17*a + 1152//17, 58//17*a + 128//17, 0], [4//11*a + 457//22, 1//2*a, 1//110], [2721//374*a + 129347//374, 283//34*a + 1//17, 1//1870*a + 283//1870]]
  L32 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L32)) == res[32]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -10]);
  gens = [[1, 0, 0], [1//2*a, 0, 0], [0, 2, 0], [0, a, 0], [0, 1//2*a + 1, 1//2], [0, 1//2*a + 1, 1//2]]
  L33 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L33)) == res[33]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -10]);
  gens = [[1, 0, 0], [3//2*a + 1, 0, 0], [0, 2, 0], [0, 2, 0], [0, 3//2*a, 1//2], [0, 9//2, 3//4*a]]
  L34 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L34)) == res[34]
  D = matrix(K, 3, 3, [21*a - 14, 0, 0, 0, -3*a + 3, 0, 0, 0, -630*a + 1008]);
  gens = [[2, 0, 0], [164//7*a + 114//7, 0, 0], [1, 1, 0], [1, 1, 0], [3//14*a + 18//7, 1, 1//42], [9//7*a + 3//14, 1//2*a, 1//84*a]]
  L35 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L35)) == res[35]
  D = matrix(K, 3, 3, [21*a - 14, 0, 0, 0, -3*a + 3, 0, 0, 0, -630*a + 1008]);
  gens = [[2, 0, 0], [65//7*a + 118//7, 0, 0], [1, 1, 0], [1, 1, 0], [1//14*a + 1//7, 0, 1//42], [1//14*a + 1//7, 0, 1//42]]
  L36 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L36)) == res[36]
  D = matrix(K, 3, 3, [21*a - 14, 0, 0, 0, -3*a + 3, 0, 0, 0, -630*a + 1008]);
  gens = [[2, 0, 0], [187//7*a + 148//7, 0, 0], [0, 1, 0], [0, 1, 0], [1//14*a + 8//7, 0, 1//42], [1//14*a + 8//7, 0, 1//42]]
  L37 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L37)) == res[37]
  D = matrix(K, 3, 3, [21*a - 14, 0, 0, 0, -3*a + 3, 0, 0, 0, -630*a + 1008]);
  gens = [[1, 0, 0], [30//7*a + 27//7, 0, 0], [0, 2, 0], [0, a + 2, 0], [1//14*a + 1//7, 1, 1//42], [1//14*a + 1//7, 1, 1//42]]
  L38 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L38)) == res[38]
  D = matrix(K, 3, 3, [21*a - 14, 0, 0, 0, -3*a + 3, 0, 0, 0, -630*a + 1008]);
  gens = [[2, 0, 0], [32//7*a + 82//7, 0, 0], [1//7*a + 3//7, 1, 0], [1//7*a + 3//7, 1, 0], [1//14*a + 8//7, 1, 1//42], [4//7*a + 1//14, 1//2*a, 1//84*a]]
  L39 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L39)) == res[39]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -12]);
  gens = [[2, 0, 0], [3*a, 0, 0], [1, 2, 0], [1//2*a, a, 0], [1//2*a + 3//2, 1//2, 1//4], [1//2*a + 3//2, 1//2, 1//4]]
  L40 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L40)) == res[40]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -12]);
  gens = [[1, 0, 0], [1//2*a + 1, 0, 0], [0, 2, 0], [0, a, 0], [0, 1, 1//2], [0, 1, 1//2]]
  L41 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L41)) == res[41]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -12]);
  gens = [[1, 0, 0], [3//2*a + 1, 0, 0], [0, 2, 0], [0, 2, 0], [0, 1, 1//2], [0, 3//2*a, 3//4*a]]
  L42 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L42)) == res[42]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -12]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 2, 0], [0, a, 0], [0, a + 1, 1//2], [0, 3//2*a + 3, 3//4*a]]
  L43 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L43)) == res[43]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -12]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 2, 0], [0, a, 0], [1, a + 1, 1//2], [3//2*a, 3//2*a + 3, 3//4*a]]
  L44 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L44)) == res[44]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -12]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 2, 0], [0, a, 0], [1, 1, 1//2], [3//2*a, 3//2*a, 3//4*a]]
  L45 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L45)) == res[45]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -12]);
  gens = [[2, 0, 0], [a, 0, 0], [a + 1, 2, 0], [1//2*a + 1, a, 0], [1//2*a + 1//2, 3//2, 1//4], [1//2*a + 1//2, 3//2, 1//4]]
  L46 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L46)) == res[46]
  D = matrix(K, 3, 3, [8, 0, 0, 0, 1, 0, 0, 0, -56]);
  gens = [[1//2, 0, 0], [1//4*a, 0, 0], [0, 2, 0], [0, a, 0], [0, 1//2*a + 1, 1//4], [0, 1//2*a + 1, 1//4]]
  L47 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L47)) == res[47]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, 14]);
  gens = [[1, 0, 0], [1, 0, 0], [1, 2, 0], [1//2*a, a, 0], [1//2*a + 1, 3//2*a, 1//2], [3//2*a + 3//2, 9//2, 3//4*a]]
  L48 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L48)) == res[48]
  D = matrix(K, 3, 3, [735*a - 720, 0, 0, 0, -99*a + 46, 0, 0, 0, -735630*a + 1250550]);
  gens = [[2, 0, 0], [a + 2, 0, 0], [1379, 1, 0], [7136660097//2498*a + 308769132//1249, 5175243//2498*a + 223908//1249, 0], [1//10*a + 479677//30, 7//2, 1//30], [105770908487//12490*a + 1842090012256//18735, 4630257//2498*a + 26881873//1249, 1543419//87430*a + 26881873//131145]]
  L49 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L49)) == res[49]
  D = matrix(K, 3, 3, [735*a - 720, 0, 0, 0, -24*a + 49, 0, 0, 0, -373065*a + 493920]);
  gens = [[2, 0, 0], [a + 2, 0, 0], [2444, 1, 0], [1483099852//1249*a + 3752341632//1249, 606833//1249*a + 1535328//1249, 0], [7//10*a + 24781//30, 0, 1//30], [13124//15*a + 30950477//30, 0, 1//37470*a + 1559951//37470]]
  L50 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L50)) == res[50]
  D = matrix(K, 3, 3, [8, 0, 0, 0, 1, 0, 0, 0, -56]);
  gens = [[1//2, 0, 0], [1//2, 0, 0], [1//2, 2, 0], [1//4*a, a, 0], [1//4*a, 3//2*a, 1//4], [3//4, 9//2, 3//8*a]]
  L51 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L51)) == res[51]
  D = matrix(K, 3, 3, [2, 0, 0, 0, -1, 0, 0, 0, 14]);
  gens = [[1, 0, 0], [1//2*a, 0, 0], [0, 2, 0], [0, a, 0], [0, 1//2*a, 1//2], [0, 1//2*a, 1//2]]
  L52 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L52)) == res[52]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[2, 0, 0], [3*a, 0, 0], [0, 2, 0], [0, 3*a, 0], [1//2*a + 1, 0, 1//4], [1//2*a + 1, 0, 1//4]]
  L53 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L53)) == res[53]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 2, 0], [0, 2, 0], [0, 1, 1//4], [0, 1, 1//4]]
  L54 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L54)) == res[54]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[2, 0, 0], [3*a + 2, 0, 0], [1, 2, 0], [1, 2, 0], [1, a + 3, 1//4], [3//2*a, 9//2*a + 3, 3//8*a]]
  L55 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L55)) == res[55]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[2, 0, 0], [3*a + 2, 0, 0], [0, 4, 0], [0, 2*a, 0], [0, a + 5//2, 1//8], [0, a + 5//2, 1//8]]
  L56 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L56)) == res[56]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[2, 0, 0], [a, 0, 0], [0, 4, 0], [0, 2*a, 0], [1, a + 3//2, 1//8], [1, a + 3//2, 1//8]]
  L57 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L57)) == res[57]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[2, 0, 0], [a, 0, 0], [1, 2, 0], [1, 2, 0], [0, 3, 1//4], [0, 9//2*a, 3//8*a]]
  L58 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L58)) == res[58]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[2, 0, 0], [3*a, 0, 0], [0, 4, 0], [0, 2*a, 0], [0, 1//2, 1//8], [0, 1//2, 1//8]]
  L59 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L59)) == res[59]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[2, 0, 0], [3*a, 0, 0], [0, 2, 0], [0, a, 0], [1, 1, 1//4], [1, 1, 1//4]]
  L60 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L60)) == res[60]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 4, 0], [0, 14*a + 4, 0], [1, a + 1, 1//4], [3//2*a, 3//2*a + 3, 3//8*a]]
  L61 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L61)) == res[61]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[1, 0, 0], [1, 0, 0], [0, 4, 0], [0, 4, 0], [1//2*a, a + 7//2, 1//8], [1//2*a, a + 7//2, 1//8]]
  L62 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L62)) == res[62]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[1, 0, 0], [1//2*a, 0, 0], [0, 4, 0], [0, 4*a + 12, 0], [0, 2*a + 1, 1//4], [0, 3//2*a + 6, 3//8*a]]
  L63 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L63)) == res[63]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[2, 0, 0], [2*a + 2, 0, 0], [1, 1, 0], [1, 1, 0], [1//2*a + 1, 0, 1//4], [1//2*a + 1, 0, 1//4]]
  L64 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L64)) == res[64]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[1, 0, 0], [1, 0, 0], [1, 2, 0], [1//2*a, a, 0], [1, 0, 1//2], [1//2*a, 0, 1//4*a]]
  L65 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L65)) == res[65]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[1, 0, 0], [1, 0, 0], [1//2*a, 2, 0], [1//2*a, 2, 0], [1//2*a, 1, 1//4], [1//2*a, 1, 1//4]]
  L66 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L66)) == res[66]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[1, 0, 0], [1//2*a, 0, 0], [0, 4, 0], [0, 6*a, 0], [0, 1, 1//4], [0, 1, 1//4]]
  L67 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L67)) == res[67]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[2, 0, 0], [a, 0, 0], [0, 2, 0], [0, 2, 0], [1, 1, 1//4], [3//2*a, 3//2*a, 3//8*a]]
  L68 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L68)) == res[68]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[2, 0, 0], [3*a, 0, 0], [0, 2, 0], [0, 2, 0], [a, a + 3, 1//4], [3, 9//2*a + 3, 3//8*a]]
  L69 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L69)) == res[69]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[2, 0, 0], [3*a, 0, 0], [a, 4, 0], [1, 2*a, 0], [1//2*a + 1, a + 7//2, 1//8], [1//2*a + 1, a + 7//2, 1//8]]
  L70 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L70)) == res[70]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[1, 0, 0], [1, 0, 0], [1//2*a, 2, 0], [1//2*a, 2, 0], [1//2*a, a + 1, 1//4], [1//2*a, a + 1, 1//4]]
  L71 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L71)) == res[71]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[2, 0, 0], [3*a + 2, 0, 0], [a, 4, 0], [1, 2*a, 0], [1//2*a + 1, a + 5//2, 1//8], [1//2*a + 1, a + 5//2, 1//8]]
  L72 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L72)) == res[72]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[1, 0, 0], [1, 0, 0], [1//2*a, 4, 0], [1//2*a, 4, 0], [0, a + 3//2, 1//8], [0, a + 3//2, 1//8]]
  L73 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L73)) == res[73]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[1, 0, 0], [1, 0, 0], [1//2*a, 4, 0], [1//2*a, 4, 0], [0, 3*a + 5//2, 1//8], [0, 3*a + 5//2, 1//8]]
  L74 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L74)) == res[74]
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -16]);
  gens = [[1, 0, 0], [1//2*a, 0, 0], [0, 8, 0], [0, 4*a + 16, 0], [0, a + 15//2, 1//8], [0, a + 15//2, 1//8]]
  L75 = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L75)) == res[75]

  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  f = x^2 - 2;
  K, a = number_field(f)
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -2]);
  gens = [[1, 0, 0], [1//2*a, 0, 0], [0, 2, 0], [0, a, 0], [0, 1//2*a, 1//2], [0, 1//2*a, 1//2]]
  L = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L)) == 1

  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  f = x^2 - 2;
  K, a = number_field(f)
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, -8]);
  gens = [[2, 0, 0], [a, 0, 0], [a, 2, 0], [1, a, 0], [0, 1//2*a, 1//4], [0, 1//2*a, 1//4]]
  L = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L)) == 1

  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  f = x^2 - 2;
  K, a = number_field(f)
  D = matrix(K, 3, 3, [2, 0, 0, 0, 1, 0, 0, 0, 16]);
  gens = [[2, 0, 0], [2, 0, 0], [2, 2, 0], [a, a, 0], [a + 2, 1, 1//4], [3*a + 3, 3//2*a, 3//8*a]]
  L = quadratic_lattice(K, gens, gram = D)
  @test length(genus_representatives(L)) == 3
end

@testset "Genus Representatives Number Field Binary" begin
  R, x = polynomial_ring(QQ,:x)
  F,a = number_field(x^2-2,:a)
  OF = maximal_order(F)
  pl = real_places(F)

  sig = Dict([(pl[1],0),(pl[2],0)])
  for d in 1:2:12
    [representatives(g) for g in Hecke.quadratic_genera(F,rank=2,det=d*OF,signatures=sig)]
  end

  # Indefinite not implemented for K != QQ
  # sig = Dict([(pl[1],1),(pl[2],2)])
  # for d in 1:12
  #   [representatives(g) for g in Hecke.quadratic_genera(F,rank=2,det=d*OF,signatures=sig)]
  # end

  # sig = Dict([(pl[1],1),(pl[2],1)])
  # for d in 1:12
  #   [representatives(g) for g in Hecke.quadratic_genera(F,rank=2,det=d*OF,signatures=sig)]
  # end
end

@testset "Genus Representatives non-full rank, definite" begin
  B = matrix(FlintQQ, 5, 8 ,[0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0, 0, 31//2, 3//2, 1//2, 1, 0, 0, 0, 0, 5//2, 3//2, 0, 0, 1//2]);
  G = matrix(FlintQQ, 8, 8 ,[16, -8, 0, 0, 0, 0, 0, 0, -8, 16, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 6]);
  L = Zlattice(B, gram = G);
  Ns = @inferred genus_representatives(L) #this uses the automorphisms

  L2 = Hecke._to_number_field_lattice(L)
  @test rank(L2) != degree(L2)
  Ns2 = @inferred genus_representatives(L2, use_auto = false)
  @test length(Ns2) == length(Ns)
end
