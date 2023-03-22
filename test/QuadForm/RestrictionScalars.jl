@testset "Restriction of scalars: AbstractSpace" begin
  E, b = cyclotomic_field_as_cm_extension(7, cached = false)
  V = hermitian_space(E, 4)
  L = lattice(V)
  Vres, VrestoV = restrict_scalars(ambient_space(L), QQ)
  @test domain(VrestoV) === Vres
  @test codomain(VrestoV) === ambient_space(L)
  Lres = restrict_scalars(L, FlintQQ)
  @test ambient_space(Lres) === Vres
  @test all(v -> VrestoV(VrestoV\v) == v, generators(L))


  Qx, x = polynomial_ring(FlintQQ, "x")
  f = x - 1
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2 + 2
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [-2*b - 2, b + 6, 0]), map(E, [0, 1, 1]), map(E, [b - 6, -6*b + 6, 0])]
  gens2 = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [-2*b - 2, b + 6, 0]), map(E, [0, 1, 1])]
  L = hermitian_lattice(E, gens, gram = D)
  M = hermitian_lattice(E, gens2, gram = D)

  Qx, x = polynomial_ring(FlintQQ, "x")
  f = x - 1
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2 + 1
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  gens = Vector{Hecke.NfRelElem{nf_elem}}[map(E, [-1, -4*b + 6, 0]), map(E, [16*b - 2, -134*b - 71, -2*b - 1]), map(E, [3*b - 92, -1041//2*b + 1387//2, -15//2*b + 21//2])]
  O = hermitian_lattice(E, gens, gram = D)

  Lres, f = restrict_scalars_with_map(L, FlintQQ)
  Mres = restrict_scalars(M, f)
  @test Lres == restrict_scalars(L, f)
  @test issublattice(Lres, Mres)
  @test_throws ArgumentError restrict_scalars(O, f)
end

@testset "Trace equivalence" begin
  E8 = rescale(root_lattice(:E,8),-6)
  f = matrix(QQ, 8, 8, [ 1  0  0  0  0  0  0  0;
                         0  1  0  0  0  0  0  0;
                         1  2  4  4  3  2  1  2;
                        -2 -4 -6 -5 -4 -3 -2 -3;
                         2  4  6  4  3  2  1  3;
                        -1 -2 -3 -2 -1  0  0 -2;
                         0  0  0  0  0 -1  0  0;
                        -1 -2 -3 -3 -2 -1  0 -1])

  g = matrix(QQ, 8, 8, [-1 -1  0  0  0  0  0  0;
                         1  0  0  0  0  0  0  0;
                         0  1  1  0  0  0  0  0;
                         0  0  0  1  0  0  0  0;
                         0  0  0  0  1  0  0  0;
                         0  0  0  0  0  1  1  0;
                        -2 -4 -6 -5 -4 -3 -2 -3;
                        0  0  0  0 0  0  0  1])

  for h in [f, g]
    n = multiplicative_order(h)
    M = kernel_lattice(E8, cyclotomic_polynomial(n)(h))
    hM = solve_left(basis_matrix(M), basis_matrix(M)*h)
    @test is_cyclotomic_polynomial(minpoly(hM))
    M = Zlattice(gram = gram_matrix(M))
    H, res = hermitian_structure(M, hM)
    @test rank(H) == divexact(rank(M), euler_phi(n))
    @test domain(res) === ambient_space(M)
    @test codomain(res) === ambient_space(H)
    M2, h2 = trace_lattice(H, res)
    @test M2 == M
    @test h2 == hM
    H2, _ = hermitian_structure(M2, h2, res = res)
    @test H2 == H
    M2, h2, res2 = trace_lattice_with_map(H)
    mb = block_diagonal_matrix([absolute_representation_matrix(gen(base_field(H))) for j in 1:rank(H)])
    @test h2 == mb
    @test genus(M2) == genus(M)
    E = base_field(H)
    OE = maximal_order(E)
    DKQ = different(base_ring(OE))*OE
    DEK = different(OE)
    DEQ = DEK*DKQ
    @test is_integral(DEQ*scale(H))                     # M is integral
    @test is_integral(different(base_ring(OE))*norm(H)) # M is even
    H2 = inv(DEQ)*dual(H)
    Mv, h2 = trace_lattice(H2, res)
    @test h2 == hM
    @test Mv == dual(M)
  end

  L, f = trace_lattice(E8)
  @test isone(-f)
  L, f = trace_lattice(E8, order = 1)
  @test isone(f)
  @test_throws ArgumentError trace_lattice(E8, order = 3)
end

