@testset "Lattices" begin
  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  f = x^2-2
  K, a = number_field(f)
  D = matrix(K, 3, 3, [1//64, 0, 0, 0, 1//64, 0, 0, 0, 1//64])
  gens = [[32, 0, 0], [944*a+704, 0, 0], [16, 16, 0], [72*a+96, 72*a+96, 0], [4*a, 4*a+8, 8], [20*a+32, 52*a+72, 32*a+40]]
  L = quadratic_lattice(K, generators = gens, gram_ambient_space = D)
  D = matrix(K, 3, 3, [1//64, 0, 0, 0, 1//64, 0, 0, 0, 1//64])
  gens = [[32, 0, 0], [720*a+448, 0, 0], [16, 16, 0], [152*a+208, 152*a+208, 0], [4*a+24, 4*a, 8], [116*a+152, 20*a+32, 32*a+40]]
  M = quadratic_lattice(K, generators = gens, gram_ambient_space = D)
  p = prime_decomposition(base_ring(L), 2)[1][1]
  @test islocally_isometric(L, M, p)

  # Smoke test for genus symbol
  Qx, x = PolynomialRing(FlintQQ, "x")
  K, a = NumberField(x^2 - 2, "a")
  L = quadratic_lattice(K, identity_matrix(K, 10), gram_ambient_space = 35*identity_matrix(K, 10))
  P = prime_decomposition(maximal_order(K), 5)[1][1]
  @test Hecke._genus_symbol_kirschmer(L, P).data == [(10, 1, 1)]

  P = prime_decomposition(maximal_order(K), 2)[1][1]
  GS = Hecke._genus_symbol_kirschmer(L, P)
  @test GS.data[1] == [10]
  @test GS.data[2] == [0]
  @test GS.data[3] == [2]
  @test GS.data[4] == [35]
  @test GS.data[5] == []

  Qx, x = FlintQQ["x"];
  K, a = number_field(x^2 - 2, cached = true);
  Kt, t = K["t"];
  L, b = number_field(t^2 + 11, "b", check = true)
  p = prime_decomposition(maximal_order(K), 2)[1][1]
  P = prime_decomposition(maximal_order(L), p)[1][1]
  H = Hecke.lattice(hermitian_space(K, 2 * identity_matrix(K, 3)), pseudo_matrix(identity_matrix(K, 3), [p, p, p]))
  @test Hecke._genus_symbol_kirschmer(H, fmpz(2)) == Any[(3, 4, true, 4, -64)]
  @test islocally_isometric(H, H, fmpz(2))

  H = Hecke.lattice(hermitian_space(L, L(elem_in_nf(uniformizer(p))) * identity_matrix(L, 3)), pseudo_matrix(identity_matrix(L, 3), [P, P, P]))
  @test Hecke._genus_symbol_kirschmer(H, p) == Any[(3, 3, false)]
  @test islocally_isometric(H, H, p)
  @test Hecke.genus(H, p) == genus(HermLat, L, p, [(3, 3, -1)])

  V = hermitian_space(L, L(a) * identity_matrix(L, 3))
  M = Hecke.maximal_integral_lattice(V)
  @test Hecke.genus(M, p) == genus(HermLat, L, p, [(0, 2, 1), (1, 1, -1)])
  q = prime_decomposition(maximal_order(K), 11)[1][1]
  @test Hecke.genus(M, q) == genus(HermLat, L, q, [(-1, 2, 1), (0, 1, 1)])

  L, _ = number_field(t^2 - gen(K) * t + 1)
  V = hermitian_space(L, L(a) * identity_matrix(L, 3))
  M = Hecke.maximal_integral_lattice(V)
  @test Hecke.genus(M, p) == genus(HermLat, L, p, [(-2, 2, 1, 0), (0, 1, -1, 0)])
  
  V = hermitian_space(L, L(10) * identity_matrix(L, 3))
  M = Hecke.maximal_integral_lattice(V)
  @test Hecke.genus(M, p) == genus(HermLat, L, p, [(-2, 2, 1, 0), (0, 1, 1, 0)])


  Qx, x = QQ["x"]
  f = x^3-39*x-65
  K, a = MaximalRealSubfield(8, "a")
  Kt, t = K["t"]
  E, b = number_field(t^2 - a * t + 1, "b")
  p = prime_decomposition(maximal_order(K), 2)[1][1]
  P = prime_decomposition(maximal_order(E), p)[1][1]
  pm = pseudo_matrix(matrix(E, 3, 3, [1, 0, 0, b, 1, 0, 0, 0, 1]), [P^0, inv(P)^2, P^0])
  V = hermitian_space(E, identity_matrix(E, 3))
  L = lattice(V, pm)
  o = Hecke.automorphism_group_order(L)
  @test o == 1536
end

@testset "Misc" begin
  Qx, x = FlintQQ["x"]
  K, a = NumberField(x - 1, "a")
  Kt, t = K["t"]
  E, b = NumberField(t^2 - 2, "b")
  p = prime_decomposition(maximal_order(K), 2)[1][1]
  u = Hecke._non_norm_rep(E, K, p)
  @test parent(u) == K
  @test !islocal_norm(E, u, p)
  @test valuation(u - 1, p) == normic_defect(E, u, p)
end
