@testset "AbelJacobi" begin
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
  @test contains(map(abs, abel_jacobi_map(P1, P2, "swap", "real")), matrix(RR, 4, 1,[RR(1/2), RR(0), RR(1/2), RR(0)]))

  P1 = RS([CC(2),CC(0)])
  P2 = RS([CC(3),CC(0)])
  @test contains(map(abs, abel_jacobi_map(P1, P2, "direct", "real")), matrix(RR, 4, 1,[RR(1/2), RR(0), RR(1/2), RR(0)]))

  f = x^5 + x^4 + x^3 - x + 4 - y^2
  RS = riemann_surface(f, 200, integration_method = "heuristic")
  CC = complex_field(RS)
  P = RS([CC(0),CC(2)])
  Q = infinite_points(RS)[1]

  test = matrix(CC, 2, 1 ,[CC("-0.347812275018893329432585425011078188019289536723529862998673","-0.0784004239762220673407092597615014331309833339336703321104797"), 
  CC("0.256565672125607694035812638002370809812311219462476029106274","-0.390109903439428059302987558739677857206947775603455209179383")])
  @test contains(abel_jacobi_map(P+Q), test)

  f = y^3 - x^7 + 2*x^3*y
  RS = riemann_surface(f, 150, integration_method = "heuristic")

  #Take test value in higher precision than what abel_jacobi computes to check if 
  #the correct approximated value (with higher precision) is contained in the computed interval
  CC = AcbField(170)
  I = onei(CC)
  x0 = CC(1)*(1+I)
  P =  RS([x0, fiber(complex_defining_polynomial(RS), x0)[1]])
  test = matrix(CC, 2,1, [CC("-0.121848276812733020974022789825026423234284154539924183207047", "0.223242453609770789623874925720806117226671991657890226766088")
CC("-0.484395642136563119330851381017440019525919257931467413181402", "0.126552674914678682266531663308976495174815608774839531015516")])
  @test contains(abel_jacobi_map(P), test)

  #abel_jacobi_map computes the value to a slightly 
  P = infinite_points(RS)[1]
  test = matrix(CC, 2, 1, [CC("-0.1642484220725167347817321014980286004800602246282506959680641945751441119467872720677596748407155158", " 0.146716970444445138898087589217840531407178155866531307723663701716156587479447162443734147770535379"),
CC("0.1385649800756489459168881966615255492613790022247407064192627969114757357260041643810901348025823631", 
"-0.04234914265787061995810395338777393179406948325834398968723431499892552513355260587703346562897074976")])
@test contains(abel_jacobi_map(P), test)


  P = critical_points(RS)[2]
  test = matrix(CC, 2, 1, [CC("0.18569691201632759735192027533036435914398645042548845799737712269", "0.00774154610733985793910746367939325353524867244972733483506777316"),
CC("-0.34811427612262884644460572908754853091761673196042049119769168128", "-0.00393728009128258515538801496114472957863493415512252654272896004")])
@test contains(abel_jacobi_map(P), test)




end
