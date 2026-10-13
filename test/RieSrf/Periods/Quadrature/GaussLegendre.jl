@testset "Gauss-Legendre" begin
  RR = ArbField(128)
  for N in (7, 10)
    x, w = RSM._gauss_legendre_nodes(N, 128)
    @test length(x) == N && length(w) == N
    @test contains(sum(w), RR(2))
    # exact for polynomials of degree <= 2N - 1
    @test overlaps(sum(w[i]*x[i]^(2N - 2) for i in 1:N), RR(2)//(2N - 1))
    @test overlaps(sum(w[i]*x[i]^(2N - 1) for i in 1:N), zero(RR))
  end
  x, w = RSM._gauss_chebyshev_nodes(9, 128)
  @test length(x) == 9 && overlaps(sum(w), const_pi(RR))
  # more nodes for a smaller ellipse or a smaller error
  err = RR(2)^-100
  @test RSM._gauss_legendre_parameters(RR(2), err) < RSM._gauss_legendre_parameters(RR(1.1), err)
  @test RSM._gauss_legendre_parameters(RR(2), err) < RSM._gauss_legendre_parameters(RR(2), err^2)
end
