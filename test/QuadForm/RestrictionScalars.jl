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

