@testset "RiemannSurface" begin
  using Hecke.RiemannSurfaces
  K = QQ

  Kxy, (x,y) = polynomial_ring(K, ["x","y"])

  f = x^6 - 15*x^5 + 85*x^4 - 225*x^3 + 274*x^2 - 120*x - y^2
  RS = riemann_surface(f, 1000, integration_method = "heuristic")
  
  CC = AcbField(130)
  RR = ArbField(130)
  P1 = RS([CC(2),CC(0)])
  P2 = RS([CC(3),CC(0)])

  #Check if Abel-Jacobi map of 2-torsion point is computed correctly. 
  @test contains(abel_jacobi_map(P1, P2, "swap", "real"), matrix(RR, 4, 1,[RR(-1/2), RR(0),RR(1/2), RR(0)])) || contains(abel_jacobi_map(P1, P2, "swap", "real"), matrix(RR, 4, 1,[RR(1/2), RR(0),RR(-1/2), RR(0)]))
  @test contains(abel_jacobi_map(P1, P2, "direct", "real"), matrix(RR, 4, 1,[RR(-1/2), RR(0),RR(1/2), RR(0)])) || contains(abel_jacobi_map(P1, P2, "swap", "real"), matrix(RR, 4, 1,[RR(1/2), RR(0),RR(-1/2), RR(0)]))

  f = x^5 + x^4 + x^3 - x + 4 - y^2
  RS = riemann_surface(f, 200, integration_method = "heuristic")
  CC = AcbField(200)
  P = RS([CC(0),CC(2)])
  Q = infinite_points(RS)[1]

  output = matrix(CC, 2, 1 ,[CC("-0.34781227501889333","-0.07840042397622207"), CC("0.25656567212560769","-0.39010990343942806")])
  @test contains(abel_jacobi_map(P+Q), output)

end
