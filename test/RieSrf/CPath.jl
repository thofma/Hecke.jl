@testset "CPath" begin
end

@testset "CChain" begin
  using Hecke.RiemannSurfaces
  Kxy, (x, y) = polynomial_ring(QQ, ["x", "y"])
  RS = riemann_surface(x^5 + x^4 + x^3 - x + 4 - y^2, 100, integration_method = "heuristic")
  chain = RS.closed_chains[1]

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
