@testset "CPath" begin
  using Hecke.RiemannSurfaces
  Kxy, (x, y) = polynomial_ring(QQ, ["x", "y"])
  RS = riemann_surface(x^5 + x^4 + x^3 - x + 4 - y^2, 100, integration_method = "heuristic")

  d = RS.discriminant_points_high_prec[1]
  r = parent(d)(RS.safe_radii[1])
  # a line through the safe disc around d is led around it on an arc
  gamma = RiemannSurfaces.c_line(d - 2*r, d + 2*r)
  paths = find_path_on_sheet(gamma, RS)
  @test RiemannSurfaces.path_type.(paths) == [0, 1, 0]
  @test overlaps(RiemannSurfaces.start_point(paths[1]), RiemannSurfaces.start_point(gamma))
  @test overlaps(RiemannSurfaces.end_point(paths[3]), RiemannSurfaces.end_point(gamma))
  @test all(overlaps(RiemannSurfaces.end_point(paths[i]), RiemannSurfaces.start_point(paths[i + 1])) for i in 1:2)
end

@testset "CChain" begin
  using Hecke.RiemannSurfaces
  Kxy, (x, y) = polynomial_ring(QQ, ["x", "y"])
  RS = riemann_surface(x^5 + x^4 + x^3 - x + 4 - y^2, 100, integration_method = "heuristic")
  chain = RS.closed_chains[1]

  @test length((chain^1).paths) == length(chain.paths)
  @test length((chain^2).paths) == 2 * length(chain.paths)
  c = chain^0
  @test length(c.paths) == 1
  @test overlaps(RiemannSurfaces.start_point(c), RiemannSurfaces.start_point(chain))
  @test overlaps(RiemannSurfaces.end_point(c), RiemannSurfaces.start_point(chain))

  # the exponent is a variable: a literal negative exponent is lowered to a
  # power of inv(chain) by Base.literal_pow
  for k in 1:2
    c = chain^(-k)
    d = inv(chain)^k
    @test length(c.paths) == k * length(chain.paths)
    @test RiemannSurfaces.path_type.(c.paths) == RiemannSurfaces.path_type.(d.paths)
    @test [p.orientation for p in c.paths] == [p.orientation for p in d.paths]
    @test all(overlaps(RiemannSurfaces.start_point(p), RiemannSurfaces.start_point(q)) for (p, q) in zip(c.paths, d.paths))
    @test all(overlaps(RiemannSurfaces.end_point(p), RiemannSurfaces.end_point(q)) for (p, q) in zip(c.paths, d.paths))
    @test RiemannSurfaces.permutation(c) == RiemannSurfaces.permutation(d)
  end
end
