@testset "Lattices" begin
  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  f = x^2-2
  K, a = number_field(f,"a")
  D = matrix(K, 3, 3, [1//64, 0, 0, 0, 1//64, 0, 0, 0, 1//64])
  gens = [[32, 0, 0], [944*a+704, 0, 0], [16, 16, 0], [72*a+96, 72*a+96, 0], [4*a, 4*a+8, 8], [20*a+32, 52*a+72, 32*a+40]]
  L = @inferred quadratic_lattice(K, generators = gens, gram_ambient_space = D)
  D = matrix(K, 3, 3, [1//64, 0, 0, 0, 1//64, 0, 0, 0, 1//64])
  gens = [[32, 0, 0], [720*a+448, 0, 0], [16, 16, 0], [152*a+208, 152*a+208, 0], [4*a+24, 4*a, 8], [116*a+152, 20*a+32, 32*a+40]]
  M = @inferred quadratic_lattice(K, generators = gens, gram_ambient_space = D)
  p = prime_decomposition(base_ring(L), 2)[1][1]
  @test @inferred islocally_isometric(L, M, p)

  fl = false
  while !fl
    fl, Lover = Hecke.ismaximal_integral(L)
    @test ambient_space(Lover) === ambient_space(L)
    L = Lover
  end
  @test Hecke.ismaximal_integral(L, p )[1]

  @test ambient_space(dual(L)) === ambient_space(L)
  @test ambient_space(Hecke.lattice_in_same_ambient_space(L,pseudo_matrix(L))) === ambient_space(L)

  # printing
  @test sprint(show, L) isa String

  # Smoke test for genus symbol
  Qx, x = PolynomialRing(FlintQQ, "x")
  K, a = NumberField(x^2 - 2, "a")
  L = @inferred quadratic_lattice(K, identity_matrix(K, 10), gram_ambient_space = 35*identity_matrix(K, 10))
  P = prime_decomposition(maximal_order(K), 5)[1][1]
  #GM = @inferred Hecke._genus_symbol_kirschmer(L, P)
  #@test GM._genus_symbol_kirschmer(L, P).data == [(10, 1, 1)]

  #P = prime_decomposition(maximal_order(K), 2)[1][1]
  #GS = @inferred Hecke._genus_symbol_kirschmer(L, P)
  #@test GS.data[1] == [10]
  #@test GS.data[2] == [0]
  #@test GS.data[3] == [2]
  #@test GS.data[4] == [35]
  #@test GS.data[5] == []

  Qx, x = FlintQQ["x"];
  K, a = number_field(x^2 - 2, cached = true);
  Kt, t = K["t"];
  L, b = number_field(t^2 + 11, "b", check = true)
  p = prime_decomposition(maximal_order(K), 2)[1][1]
  P = prime_decomposition(maximal_order(L), p)[1][1]
  H = @inferred Hecke.lattice(hermitian_space(K, 2 * identity_matrix(K, 3)), pseudo_matrix(identity_matrix(K, 3), [p, p, p]))
  #@test Hecke._genus_symbol_kirschmer(H, fmpz(2)) == Any[(3, 4, true, 4, -64)]
  @test @inferred islocally_isometric(H, H, fmpz(2))

  H = Hecke.lattice(hermitian_space(L, L(elem_in_nf(uniformizer(p))) * identity_matrix(L, 3)), pseudo_matrix(identity_matrix(L, 3), [P, P, P]))
  #@test Hecke._genus_symbol_kirschmer(H, p) == Any[(3, 3, false)]
  @test @inferred islocally_isometric(H, H, p)
  GH = @inferred genus(H, p)
  GH2 = @inferred genus(HermLat, L, p, [(3, 3, -1)])
  @test GH == GH2

  V = @inferred hermitian_space(L, L(a) * identity_matrix(L, 3))
  M = @inferred Hecke.maximal_integral_lattice(V)
  GM = @inferred genus(M, p)
  GM2 = @inferred genus(HermLat, L, p, [(0, 2, 1), (1, 1, -1)])
  @test GM == GM2
  q = prime_decomposition(maximal_order(K), 11)[1][1]
  @test Hecke.genus(M, q) == genus(HermLat, L, q, [(-1, 2, 1), (0, 1, 1)])

  L, _ = number_field(t^2 - gen(K) * t + 1)
  V = hermitian_space(L, L(a) * identity_matrix(L, 3))
  M = @inferred Hecke.maximal_integral_lattice(V)
  @test Hecke.genus(M, p) == genus(HermLat, L, p, [(-2, 2, 1, 0), (0, 1, -1, 0)])

  V = hermitian_space(L, L(10) * identity_matrix(L, 3))
  M = @inferred Hecke.maximal_integral_lattice(V)
  @test Hecke.genus(M, p) == genus(HermLat, L, p, [(-2, 2, 1, 0), (0, 1, 1, 0)])

  Qx, x = QQ["x"]
  f = x^3-39*x-65
  K, a = CyclotomicRealSubfield(8, "a")
  Kt, t = K["t"]
  E, b = number_field(t^2 - a * t + 1, "b")
  p = prime_decomposition(maximal_order(K), 2)[1][1]
  P = prime_decomposition(maximal_order(E), p)[1][1]
  ME = maximal_order(E)
  pm = pseudo_matrix(matrix(E, 3, 3, [1, 0, 0, b, 1, 0, 0, 0, 1]), [one(E)*ME, inv(P)^2, one(E)*ME])
  V = @inferred hermitian_space(E, identity_matrix(E, 3))
  L = @inferred lattice(V, pm)
  o = @inferred Hecke.automorphism_group_order(L)
  @test o == 1536
end

@testset "Misc" begin
  Qx, x = FlintQQ["x"]
  K, a = NumberField(x - 1, "a")
  Kt, t = K["t"]
  E, b = NumberField(t^2 - 2, "b")
  p = prime_decomposition(maximal_order(K), 2)[1][1]
  u = @inferred Hecke._non_norm_rep(E, K, p)
  @test parent(u) === K
  @test @inferred !islocal_norm(E, u, p)
  @test valuation(u - 1, p) == @inferred normic_defect(E, u, p)
end

@testset "Jordan decomposition" begin
  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  f = x - 1;
  K, a = number_field(f)
  D = matrix(K, 3, 3, [3, 2, 1, 2, 3, 1, 1, 1, 1]);
  gens = [[1, -1, 0], [1, -1, 0], [0, 1, -1], [0, 1, -1]]
  L = quadratic_lattice(K, generators = gens, gram_ambient_space = D)
  p = prime_decomposition(maximal_order(K), 2)[1][1]
  B, B, S = jordan_decomposition(L, p)
  @test length(S) == 1
end
