@testset "AbelJacobi" begin
  K = QQ

  Kxy, (x,y) = polynomial_ring(K, ["x","y"])

  f = x^6 - 15*x^5 + 85*x^4 - 225*x^3 + 274*x^2 - 120*x - y^2
  RS = RSM.riemann_surface(f, 150, integration_method = :heuristic)
  
  CC = AcbField(130)
  RR = ArbField(130)
  P1 = RS([CC(2),CC(0)])
  P2 = RS([CC(3),CC(0)])

  # P1 - P2 (two Weierstrass points) is a 2-torsion point: in real
  # coordinates (R^2g / Z^2g) all entries are 0 or 1/2, two of them 1/2. (Which
  # two depends on the symplectic basis, e.g. of the superelliptic model.)
  function is_two_torsion(V)
    v = map(abs, V)
    zero_or_half = all(contains(v[i, 1], RR(0)) || contains(v[i, 1], RR(1//2)) for i in 1:4)
    return zero_or_half && count(i -> contains(v[i, 1], RR(1//2)), 1:4) == 2
  end
  @test is_two_torsion(RSM.abel_jacobi_map(P1, P2, "swap", "real"))

  P1 = RS([CC(2),CC(0)])
  P2 = RS([CC(3),CC(0)])
  @test is_two_torsion(RSM.abel_jacobi_map(P1, P2, "direct", "real"))

  # (the reference values refer to the bases of the general algorithm)
  # The reference values below are balls of their own (some ~2^-200 wide);
  # the computed values can be more accurate than them, so they are compared
  # by overlap, not containment.
  f = x^5 + x^4 + x^3 - x + 4 - y^2
  RS = RSM.riemann_surface(f, 200, integration_method = :heuristic, superelliptic = false)
  CC = complex_field(RS)
  P = RS([CC(0),CC(2)])
  Q = RSM.infinite_points(RS)[1]

  # Reference: the same computation at 400 bits (the earlier reference value,
  # from a 200-bit run, claimed a too small radius in two entries). It is
  # much more accurate than the computed value, which must contain it.
  C256 = AcbField(256)
  test = matrix(C256, 2, 1, [
    C256("-0.347812275018893329432585425011078188019289536723529862998672569518511 +/- 1e-69",
       "-0.0784004239762220673407092597615014331309833339336703321104796814921102 +/- 1e-69"),
    C256("0.256565672125607694035812638002370809812311219462476029106273535268892 +/- 1e-69",
       "-0.390109903439428059302987558739677857206947775603455209179383362811467 +/- 1e-69")])
  V = RSM.abel_jacobi_map(P+Q)
  @test all(contains(V[i, 1], test[i, 1]) for i in 1:2)

  f = y^3 - x^7 + 2*x^3*y
  RS = RSM.riemann_surface(f, 150, integration_method = :heuristic)

  #Take test value in higher precision than what abel_jacobi computes to check if 
  #the correct approximated value (with higher precision) is contained in the computed interval
  CC = AcbField(170)
  I = onei(CC)
  x0 = CC(1)*(1+I)
  P =  RS([x0, RSM.fiber(RSM.complex_defining_polynomial(RS), x0)[1]])
  test = matrix(CC, 2,1, [CC("-0.121848276812733020974022789825026423234284154539924183207047", "0.223242453609770789623874925720806117226671991657890226766088")
CC("-0.484395642136563119330851381017440019525919257931467413181402", "0.126552674914678682266531663308976495174815608774839531015516")])
  @test _overlap(RSM.abel_jacobi_map(P), test)

  #abel_jacobi_map computes the value to a slightly 
  P = RSM.infinite_points(RS)[1]
  test = matrix(CC, 2, 1, [CC("-0.1642484220725167347817321014980286004800602246282506959680641945751441119467872720677596748407155158", " 0.146716970444445138898087589217840531407178155866531307723663701716156587479447162443734147770535379"),
CC("0.1385649800756489459168881966615255492613790022247407064192627969114757357260041643810901348025823631", 
"-0.04234914265787061995810395338777393179406948325834398968723431499892552513355260587703346562897074976")])
@test _overlap(RSM.abel_jacobi_map(P), test)


  # the reference value is the Abel-Jacobi image of one of the critical
  # points (their order is not fixed)
  test = matrix(CC, 2, 1, [CC("0.18569691201632759735192027533036435914398645042548845799737712269", "0.00774154610733985793910746367939325353524867244972733483506777316"),
CC("-0.34811427612262884644460572908754853091761673196042049119769168128", "-0.00393728009128258515538801496114472957863493415512252654272896004")])
@test any(_overlap(RSM.abel_jacobi_map(P), test) for P in RSM.critical_points(RS))




end

@testset "AbelJacobiMap (principal divisors, special points)" begin
  @testset "Abel–Jacobi map of principal divisors" begin
    for (name, f, g) in FAST_CURVES[[2, 5, 8, 12]]      # e5, f2, g3, f1
      @testset "$name" begin
        test_abel_jacobi_principal(_rs(f, 100); ntests = 1)
      end
    end
  end

  # div(x - a) = 3 P_a - 3 P_inf on y^3 = x^4 + 2x + 1 (totally ramified at every
  # branch point a, one point at infinity), with the "direct" method: every
  # critical point needs the chain around its own discriminant point
  # (regression test for the index into the closed chains).
  # A node with trivial monodromy: y^2 = x^2 (x-1)(x-2)(x-3) (genus 1). The two
  # points N+, N- over the node (0, 0) are zeros of x, the point at infinity a
  # double pole: div(x) = N+ + N- - 2 P_inf.
  @testset "Singular point with trivial monodromy" begin
    RS = _rs(y^2 - x^2*(x - 1)*(x - 2)*(x - 3), 100; model = :original)
    @test RSM.genus(RS) == 1
    C = RSM.computational_model(RS)
    CC = RSM.complex_field(RS)
    RSM.big_period_matrix(RS)
    @test !any(ch -> contains(RSM.center(ch), zero(CC)), C.closed_chains)   # trivial monodromy at 0
    nodes = filter(P -> contains(P.coordx, zero(CC)), RSM.critical_points(RS))
    @test length(nodes) == 2 && all(P -> P.is_singular, nodes)
    @test sort(vcat([P.sheets for P in nodes]...)) == [1, 2]
    tol = ArbField(precision(CC))(2)^(-50)
    Inf1 = only(RSM.infinite_points(RS))
    D = RSM.divisor([nodes[1], nodes[2], Inf1], [1, 1, -2])
    @test all(_is_small(v, tol) for v in RSM.abel_jacobi_map(D, "direct", "complex"))
  end

  @testset "Abel–Jacobi map at the ramification points" begin
    RS = _rs(y^3 - (x^4 + 2*x + 1), 100)
    C = RSM.computational_model(RS)
    CC = RSM.complex_field(RS)
    tol = ArbField(precision(CC))(2)^(-50)
    Inf1 = only(RSM.infinite_points(RS))
    crit = RSM.critical_points(RS)
    @test length(crit) == 4
    for P in crit
      D = RSM.divisor([P, Inf1], [3, -3])
      @test all(_is_small(v, tol) for v in RSM.abel_jacobi_map(D, "direct", "complex"))
    end
  end

  # Critical points are integrated into on the swapped surface (method
  # :swap), which carries the differentials of the original model. Tested
  # with a Baker basis and with a basis from the function field.
  @testset "Abel–Jacobi via the swapped surface: $name" for (name, f, baker) in [
      ("e5", FAST_CURVES[2][2], true),
      ("node", y^2 - (x - 1)^2*(x^3 + 2), false)]
    RS = _rs(f, 100; model = :original)
    O = RSM.original_model(RS)
    P = first(Q for Q in RSM.ramification_points(RS) if RSM.is_finite(Q) && !Q.is_singular)
    D = _divisor_of_x_minus(RS, P)
    @test RSM.degree(D) == 0
    @test O.baker_basis == baker
    V = RSM.abel_jacobi_map(D, :swap, :complex)
    @test isdefined(O, :swapped_surface)
    tol = ArbField(100)(2)^(-50)
    @test all(_is_small(v, tol) for v in V)
  end

  @long_test begin
    @testset "Long: Abel–Jacobi, larger genus" begin
      for (name, f, g) in LONG_CURVES[[1, 2]]
        @testset "$name" begin
          test_abel_jacobi_principal(_rs(f, 100); ntests = 1)
        end
      end
    end
  end
end
