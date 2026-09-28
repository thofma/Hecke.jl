@testset "RiemannSurface" begin
  using Hecke.RiemannSurfaces
  K = QQ

  Kxy, (x,y) = polynomial_ring(K, ["x","y"])

  # (the reference tau refers to the symplectic basis of the general
  # algorithm; the superelliptic algorithm is compared up to Sp_2g(ZZ))
  f = x^5 + x^4 + x^3 - x + 4 - y^2
  RS = riemann_surface(f, 1000, integration_method = "heuristic", superelliptic = false)
  tau = small_period_matrix(RS)


  #Compare against a matrix computed with higher precision.
  CC = AcbField(1500)
  test_tau = matrix(CC, [[CC("0.51134384258384050289395050220549143264926289122590724831832059271561695701292456552235229385804768870472567010149694153954136438482647826645176859606548746111913509107091386121276102964925489024560286072386293400498398449316360188612392015680804815968295587539136899134789650609324879205986437757966016199806658717675650222624433215686560967413177878791925851513979314332668995843812835206946937534708511457860196173637305969073658849339342378578046109848283010419524114562586195743303154442103769449", "0.37938453074852943158058409005312754137258333273801315940627872423901885472579119757338770206249548797032549765605942959048425145613841892521683580854372271258007964829424205086159878749765808740451759869011983130735023662599757290466295546118427841626321755414625295507201711503909421700035787202102317250768905760316502736987738121046122907723734469270109887008248162384738022550684961905914969909930860712559788359096210615753513582939201028224004181826319329241578479575808335506577416041116229030"), CC("0.37968242378136137665536570000043319730031830802699722389056685841164707153714655287372793984714424841388589077160092267745580940762916054888104212607496127937935506768356493691315411425965847615053273071159000378341843497847106118828797330858085385807624837588390770516755837964887205303955594311118325391420270505658627741759325911936329129910892148301227661286011119367729275215477666582269698184899296775955454437706672461316566626495997549878221062559718793289561657329448289431918608030743805903", "0.019319366399966029033283668469893812764410948527987950322204644584666046271410472189219286368899565517472643218415041368042241917508989640619776201126307005232169253592367312924811988102710409594970390200105043593999679254884888967591317987437456825548230559105596387820333348402021579228811482465769161041260302960786380750491659551283658039349450854449839194164662866108417028656632526109172871293849509001410079024132330580400575142167479161059471899996029567125486430009746647927947194936353649116")], [CC("0.37968242378136137665536570000043319730031830802699722389056685841164707153714655287372793984714424841388589077160092267745580940762916054888104212607496127937935506768356493691315411425965847615053273071159000378341843497847106118828797330858085385807624837588390770516755837964887205303955594311118325391420270505658627741759325911936329129910892148301227661286011119367729275215477666582269698184899296775955454437706672461316566626495997549878221062559718793289561657329448289431918608030743805903", "0.019319366399966029033283668469893812764410948527987950322204644584666046271410472189219286368899565517472643218415041368042241917508989640619776201126307005232169253592367312924811988102710409594970390200105043593999679254884888967591317987437456825548230559105596387820333348402021579228811482465769161041260302960786380750491659551283658039349450854449839194164662866108417028656632526109172871293849509001410079024132330580400575142167479161059471899996029567125486430009746647927947194936353649116"), CC("0.55156668042084222593827637302267324573959572172857168598394524866033380894841137017021751474788797010139556209926699228400362738992442836090551391212229263921747468354702952536017617937030917327712220048209456180848713520796840506403279678626167414722791385371102674407160169124276468961905551275311551883721062085635340929693017782680477352103539288956440829717318834981641950502646779226488611069868464542458564664840780366660963854417061042600168169632737417601465790129127701708945734878049382332", "0.79891312458534926300066263507909579929208977457835785581787386883504757452108795062042557936207155274735031048747874793415205716514712946142447039490658320744447885260694088363736411279158622443592252941916818365403436759671907000657218254471906549097791443562262503309487278252627128833749132479315209967721821620845506015804882211773721297028087544029780467615626760362060836529345288018244970006990095857865203231165134744477380087044957954974626683071810281301918677053937060150493841167636584805")]])

  @test contains(tau, test_tau)
  @test sprint(show, "text/plain", RS) isa String
  tau_se = small_period_matrix(riemann_surface(f, 200, integration_method = "heuristic"))
  @test _period_matrices_isomorphic(change_base_ring(base_ring(tau_se), tau), tau_se)

  # an Elliptic curve
  f = x^3 + 1 - y^2
  RS = riemann_surface(f)
  tau = small_period_matrix(RS)

  R = base_ring(tau)
  t = R("0.5 +/- 1e-10") + R("0.86602540378443864676372317 +/- 1.91e-10")*im
  # tau = exp(2 pi i/3) up to SL_2(ZZ): here tau or tau + 1
  @test contains(t, tau[1,1]) || contains(t, tau[1,1] + 1)

  # the same but different
  f = x^3-1 - y^2
  RS = riemann_surface(f)
  small_period_matrix(RS)

  f = x^8 + 2 * x^7 + 2 * x^6 + x^5 - 10 * x + 1 + x^3 * y^2 - y^3 + 2 * y^8
  RS = riemann_surface(f, 500  ,integration_method = "heuristic")
  small_period_matrix(RS)
end

@testset "RiemannSurface (models, output)" begin
  # With the default parameters the superelliptic curves use the algorithm for
  # superelliptic curves: same genus, Riemann relations.
  @testset "Default algorithm: $name" for (name, f, g) in FAST_CURVES
    RS = RSM.riemann_surface(f, 100)
    C = RSM.computational_model(RS)
    RSM._superelliptic_form(f) === nothing && continue
    @test C isa RSM.SuperellipticModel
    @test RSM.genus(RS) == g
    tau = RSM.small_period_matrix(RS)
    @test _is_symmetric(tau)
    @test _is_positive_definite(imag(tau))
  end

  @testset "Plane models" begin
    # Different models of the same curve: same genus, isomorphic period
    # lattices, same Abel-Jacobi map of principal divisors.
    M1 = matrix(QQ, [1 2 0; 0 1 1; 1 0 1])
    for (name, f, g, models) in [("e5", FAST_CURVES[2][2], 1, [:swapped, M1]),
                                 ("f2", FAST_CURVES[5][2], 2, [:swapped]),
                                 ("q1", FAST_CURVES[11][2], 3, [:swapped, M1])]
      @testset "$name" begin
        RSo = _computed(_rs(f, 200; model = :original))
        tau_o = RSM.small_period_matrix(RSo)
        for model in models
          RSm = _computed(_rs(f, 200; model = model))
          @test RSM.computational_model(RSm) !== RSM.original_model(RSm)
          test_sanity(RSm; expected_genus = g)
          @test _period_matrices_isomorphic(tau_o, RSM.small_period_matrix(RSm))
        end
      end
    end

    # monodromy without periods (on the original model) equals the by-product
    # of the period computation
    f = FAST_CURVES[11][2]                                   # q1
    RSs = _rs(f, 100; model = :swapped)
    mon = RSM.monodromy_representation(RSs)
    @test !isdefined(RSM.original_model(RSs), :big_period_matrix)
    @test mon == RSM.monodromy_representation(_computed(_rs(f, 100; model = :original)))
    @test length(RSM.ramification_points(RSs)) > 0          # no periods needed

    # Abel-Jacobi map: points of the curve as given, periods on another model
    test_abel_jacobi_principal(RSs; ntests = 1)
    test_abel_jacobi_principal(_rs(f, 100; model = M1); ntests = 1)
    # not yet supported: a point at infinity of the input curve on the swapped model
    P = first(RSM.infinite_points(RSs))
    @test_throws ArgumentError RSM.abel_jacobi_map(RSM.divisor([P], [1]))

    # model = :auto: both candidates costed; with_integration_parameters keeps the choice
    RSa = _rs(FAST_CURVES[5][2], 100)
    C = RSM.computational_model(RSa)
    @test length(RSa.model_costs) == 2
    @test all(c > 0 for (_, c) in RSa.model_costs)
    RSb = RSM.with_integration_parameters(RSa; adaptive = false)
    @test string(RSM.computational_model(RSb).defining_polynomial) == string(C.defining_polynomial)
    @test_throws ArgumentError _rs(f, 100; model = :projective)
    @test_throws ArgumentError _rs(f, 100; model = matrix(QQ, [1 0 0; 0 1 0; 0 0 0]))
  end

  # ComplexField / RealField at the public boundary (internally AcbField):
  # riemann_surface(f, ComplexField()) returns every numerical output in
  # ComplexField and accepts ComplexFieldElem input; same numbers as the
  # AcbField surface of precision(Balls).
  @testset "ComplexField output" begin
    f = x^3*y + y^3 + x                                  # Klein quartic, genus 3
    set_precision!(Balls, 128) do
      RSc = RSM.riemann_surface(f, ComplexField(); superelliptic = false)
      RSa = _rs(f, 128)
      @test RSM.precision(RSc) == 128
      P = RSM.big_period_matrix(RSc)
      Pa = RSM.big_period_matrix(RSa)
      @test P isa ComplexMatrix && Pa isa AcbMatrix
      @test all(overlaps(P[i, j], RSM._to_complex(Pa[i, j])) for i in 1:3, j in 1:6)
      tau = RSM.small_period_matrix(RSc)
      @test tau isa ComplexMatrix
      @test eltype(RSM.discriminant_points(RSc)) == ComplexFieldElem
      @test RSM.complex_field(RSc) isa ComplexField
      # a point given with ComplexFieldElem coordinates, its Abel-Jacobi image
      xc = ComplexField()(QQ(1, 3), QQ(1, 5))
      ys, mults = RSM.fiber_with_multiplicities(RSc, xc)
      @test eltype(ys) == ComplexFieldElem && all(==(1), mults)
      Qc = RSc([xc, ys[1]])
      Qa = RSa([RSM._to_acb(xc, 128), RSM._to_acb(ys[1], 128)])
      V = RSM.abel_jacobi_map(Qc)
      Va = RSM.abel_jacobi_map(Qa)
      @test V isa ComplexMatrix
      @test all(overlaps(V[i, j], RSM._to_complex(Va[i, j])) for i in 1:nrows(V), j in 1:ncols(V))
      # theta functions
      z = [ComplexField()(0) for _ in 1:3]
      th = theta(z, tau)
      tha = theta(RSM._to_acb(z, 128), RSM.small_period_matrix(RSa))
      @test th[1] isa ComplexFieldElem && overlaps(th[1], RSM._to_complex(tha[1]))
      # endomorphisms: the same number of generators as for AcbField input
      gens = RSM.geometric_endomorphism_representation(P)
      @test length(gens) == length(RSM.geometric_endomorphism_representation(Pa))
      @test gens[1][1] isa ComplexMatrix
    end
    @test RSM._default_output() === :acb
  end
end
