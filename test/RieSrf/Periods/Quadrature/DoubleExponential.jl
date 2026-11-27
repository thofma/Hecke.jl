@testset "Double exponential" begin
  RR = ArbField(128)
  CC = AcbField(128)
  lambda = const_pi(RR)/2
  # 1/(1 + x^2) has poles at x = ±i, which lie on the boundary of the burger
  # with strip parameter pi/6: the quadrature needs r < pi/6
  @test overlaps(RSM._burger_parameter(onei(CC), lambda), const_pi(RR)/6)
  N, h = RSM._double_exponential_parameters(RR(1//2), 100)
  x, w = RSM._tanh_sinh_nodes(N, h)
  @test length(x) == 2*N + 1
  integral = sum(w[i]/(1 + x[i]^2) for i in eachindex(x))
  @test abs(integral - const_pi(RR)/2) < RR(2)^-80
end
