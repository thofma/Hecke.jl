@testset "RiemannSurface" begin
  using Hecke.RiemannSurfaces
  K = QQ

  Kxy, (x,y) = polynomial_ring(K, ["x","y"])

  f = x^6 - 15*x^5 + 85*x^4 - 225*x^3 + 274*x^2 - 120*x - y^2
  RS = riemann_surface(f, 150, integration_method = "heuristic")
  
  CC = AcbField(130)
  RR = ArbField(130)
  P1 = RS([CC(2),CC(0)])
  P2 = RS([CC(3),CC(0)])

  #Check if Abel-Jacobi map of 2-torsion point is computed correctly. 
  @test contains(map(abs, abel_jacobi_map(P1, P2, "swap", "real")), matrix(RR, 4, 1,[RR(1/2), RR(0),RR(1/2), RR(0)]))

  P1 = RS([CC(2),CC(0)])
  P2 = RS([CC(3),CC(0)])
  @test contains(map(abs, abel_jacobi_map(P1, P2, "direct", "real")), matrix(RR, 4, 1,[RR(1/2), RR(0),RR(1/2), RR(0)]))

  f = x^5 + x^4 + x^3 - x + 4 - y^2
  RS = riemann_surface(f, 200, integration_method = "heuristic")
  CC = complex_field(RS)
  C_test = AcbField(80)
  P = RS([CC(0),CC(2)])
  Q = infinite_points(RS)[1]

  output = matrix(CC, 2, 1 ,[CC("-0.34781227501889333","-0.07840042397622207"), CC("0.25656567212560769","-0.39010990343942806")])
  @test contains(abel_jacobi_map(P+Q), output)

  f = y^3 - x^7 + 2*x^3*y
  RS = riemann_surface(f, 150, integration_method = "heuristic")

  x0 = CC(1)*(1+I)
  P =  RS([x0, fiber(complex_defining_polynomial(RS), x0)[1]])
  test = matrix(C_test, 2,1, [CC("-0.121848276812733020974022789825", "0.223242453609770789623874925721")
CC("-0.484395642136563119330851381017", "0.126552674914678682266531663309")])
  @test contains(test, abel_jacobi_map(P))

  P = infinite_points(RS)[1]
  test = matrix(C_test, 2, 1, [CC("-0.1642484220725167347817321015", "0.1467169704444451388980875892"),
CC("0.1385649800756489459168881967", "-0.0423491426578706199581039534")])
@test contains(test, abel_jacobi_map(P))

  P = critical_points(RS)[2]
  test = matrix(C_test, 2, 1, [CC("0.185696912016327597351920275", "0.007741546107339857939107464"),
CC("-0.3481142761226288464446057291", "-0.0039372800912825851553880150")])
@test contains(test, abel_jacobi_map(P))




end
