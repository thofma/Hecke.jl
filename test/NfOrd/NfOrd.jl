@testset "Orders" begin

  @test elem_type(parent_type(NfOrdElem)) === NfOrdElem
  @test parent_type(elem_type(NfOrd)) === NfOrd

  @testset "Construction" begin
     Qx, x = PolynomialRing(FlintQQ, "x")

     K1, a1 = NumberField(x^3 - 2, "a")
    O1 = EquationOrder(K1, true)

    @test @inferred nf(O1) == K1


     K2, a2 = NumberField(x - 2, "a")
    O2 = EquationOrder(K2, true)

    @test @inferred nf(O2) == K2


    f3 = x^64 - 64*x^62 +
         1952*x^60 - 37760*x^58 +
         520144*x^56 - 5430656*x^54 +
         44662464*x^52 - 296854272*x^50 +
         1623421800*x^48 - 7398867840*x^46 +
         28362326720*x^44 - 92043777280*x^42 +
         254005423840*x^40 - 597659820800*x^38 +
         1200442440064*x^36 - 2057901325824*x^34 +
         3006465218196*x^32 - 3732682723968*x^30 +
         3922021702720*x^28 - 3467892873984*x^26 +
         2561511781920*x^24 - 1565841089280*x^22 +
         782920544640*x^20 - 315492902400*x^18 +
         100563362640*x^16 - 24754058496*x^14 +
         4559958144*x^12 - 602516992*x^10 +
         53796160*x^8 - 2968064*x^6 +
         87296*x^4 - 1024*x^2 +
         2

    K3, a3 = NumberField(f3, "a")
    O3 = Order(K3, [ a3^i for i in 0:63])

    @test nf(O3) == K3

     K4, a4 = NumberField(x^2 - 5, "a")
    O4 = Order(K4, Hecke.FakeFmpqMat(FlintZZ[1 0; 0 2], fmpz(1)))
    O44 = Order(K4, FlintQQ[1 0; 0 2])
    O444 = Order(K4, FlintZZ[1 0; 0 2])

    @test nf(O4) == K4

    #@test O4 == O44
    #@test O44 == O444
#    @test O4 === O44
#    @test O44 === O444

    K6, a6 = NumberField(x^2 - 180, "a")
    O6 = EquationOrder(K6)

    @test nf(O6) == K6

    O7 = Order(K6, Hecke.FakeFmpqMat(FlintZZ[6 0; 0 1], FlintZZ(6)), check = true, cached = false)
    O77 = Order(K6, FlintQQ[1 0; 0 1//6])

    #@test O7 == O77
    #@test !(O7 === O77)

    O8 = Order(K6, [a1])
    @test O8 == EquationOrder(K1)

    @test_throws ErrorException Order(K1, [a1, a1, a1], isbasis = true)
    #@test_throws ErrorException Order(K1, [1, a1, a1])
    #@test_throws ErrorException Order(K1, [1.0, a1, a1])
    @test_throws ErrorException Order(K6, Hecke.FakeFmpqMat(FlintZZ[0 0; 0 0], FlintZZ(6)))
    @test_throws ErrorException Order(K6, Hecke.FakeFmpqMat(FlintZZ[0 2; 2 0], FlintZZ(6)))
    @test_throws ErrorException Order(K6, Hecke.FakeFmpqMat(FlintZZ[0 0], FlintZZ(6)))
  end

  Qx, x = PolynomialRing(FlintQQ, "x")

  K1, a1 = NumberField(x^3 - 2, "a")
  O1 = EquationOrder(K1)

  K2, a2 = NumberField(x - 2, "a")
  O2 = EquationOrder(K2)

  f3 = x^64 - 64*x^62 +
       1952*x^60 - 37760*x^58 +
       520144*x^56 - 5430656*x^54 +
       44662464*x^52 - 296854272*x^50 +
       1623421800*x^48 - 7398867840*x^46 +
       28362326720*x^44 - 92043777280*x^42 +
       254005423840*x^40 -
       597659820800*x^38 +
       1200442440064*x^36 - 2057901325824*x^34 +
       3006465218196*x^32 - 3732682723968*x^30 +
       3922021702720*x^28 -
       3467892873984*x^26 +
       2561511781920*x^24 - 1565841089280*x^22 +
       782920544640*x^20 - 315492902400*x^18 +
       100563362640*x^16 -
       24754058496*x^14 +
       4559958144*x^12 - 602516992*x^10 +
       53796160*x^8 -
       2968064*x^6 +
       87296*x^4 - 1024*x^2 + 2

  K3, a3 = NumberField(f3, "a")
  O3 = Order(K3, [ a3^i for i in 0:63])

  K4, a4 = NumberField(x^2 - 5, "a")
  O4 = Order(K4, Hecke.FakeFmpqMat(FlintZZ[1 0; 0 2], fmpz(1)))

  K6, a6 = NumberField(x^2 - 180, "a")
  O6 = EquationOrder(K6)

  O7 = Order(K6, Hecke.FakeFmpqMat(FlintZZ[6 0; 0 1], FlintZZ(6)))

  O5 = @inferred deepcopy(O2)

  @testset "Deepcopy" begin
    O5 = @inferred deepcopy(O2)
    @test nf(O2) == nf(O5)
  end

  @testset "Field access" begin
    b = @inferred parent(O2)
    @test b == @inferred parent(O5)

    @test K1 == @inferred nf(O1)
    @test K2 == @inferred nf(O2)
    @test K3 == @inferred nf(O3)

    @test @inferred isequation_order(O1)
    @test @inferred isequation_order(O2)
    @test @inferred !isequation_order(O3)
    @test @inferred !isequation_order(O4)
    @test @inferred isequation_order(O5)

    b = @inferred basis(O1)
    @test b == [ O1(1), O1(a1), O1(a1^2) ]

    b = @inferred basis(O2)
    @test b == [ O2(1) ]

    b = @inferred basis(O3)
    @test b == [ O3(a3^i) for i in 0:63]

    b = @inferred basis(O4)
    @test b == [ O4(1), O4(2*a4) ]

    @test O1.basis_nf == [ a1^0, a1, a1^2]

    @test O2.basis_nf == [ K2(1) ]

    @test O3.basis_nf == [ a3^i for i in 0:63]

    @test O4.basis_nf == [ a4^0, 2*a4 ]

    b = @inferred basis_matrix(O1)
    @test b == Hecke.FakeFmpqMat(one(MatrixSpace(FlintZZ, 3, 3)), one(FlintZZ))

    b = @inferred basis_matrix(O2)
    @test b == Hecke.FakeFmpqMat(one(MatrixSpace(FlintZZ, 1, 1)), one(FlintZZ))

    b = @inferred basis_matrix(O3)
    @test b == Hecke.FakeFmpqMat(one(MatrixSpace(FlintZZ, 64, 64)), one(FlintZZ))

    b = @inferred basis_matrix(O4)
    @test b == Hecke.FakeFmpqMat(FlintZZ[1 0; 0 2], one(FlintZZ))

    b = @inferred basis_mat_inv(O1)
    @test b == Hecke.FakeFmpqMat(one(MatrixSpace(FlintZZ, 3, 3)), one(FlintZZ))

    b = @inferred basis_mat_inv(O2)
    @test b == Hecke.FakeFmpqMat(one(MatrixSpace(FlintZZ, 1, 1)), one(FlintZZ))

    b = @inferred basis_mat_inv(O3)
    @test b == Hecke.FakeFmpqMat(one(MatrixSpace(FlintZZ, 64, 64)), one(FlintZZ))

    b = @inferred basis_mat_inv(O4)
    @test b == Hecke.FakeFmpqMat(FlintZZ[2 0; 0 1], FlintZZ(2))
  end

  @testset "Index" begin
    b = @inferred gen_index(O1)
    @test b == 1
    b = @inferred index(O1)
    @test b == 1

    b = @inferred gen_index(O2)
    @test b == 1
    b = @inferred index(O2)
    @test b == 1

    b = @inferred gen_index(O3)
    @test b == 1
    b = @inferred index(O3)
    @test b == 1

    b = @inferred gen_index(O4)
    @test b == FlintQQ(1, 2)
    @test_throws ErrorException index(O4)

    b = @inferred gen_index(O7)
    @test b == FlintQQ(6)
    b = @inferred index(O7)
    @test b == 6

    @test !@inferred isindex_divisor(O1, 2)
    @test !@inferred isindex_divisor(O1, 3)
    @test @inferred isindex_divisor(O7, 2)
    @test @inferred isindex_divisor(O7, fmpz(3))
    @test !@inferred isindex_divisor(O7, 5)
  end

  @testset "Discriminant" begin
    b = @inferred discriminant(O1)
    @test b == -108

    b = @inferred discriminant(O2)
    @test b == 1

    b = @inferred discriminant(O3)
    @test b == fmpz(2)^447

    b = @inferred discriminant(O4)
    @test b == fmpz(80)
  end

  @testset "Signature" begin
    @test 3 == @inferred degree(O1)
    @test 1 == @inferred degree(O2)
    @test 64 == @inferred degree(O3)
    @test 2 == @inferred degree(O4)

    @test (1, 1) == @inferred signature(O1)
    @test (1, 0) == @inferred signature(O2)
    @test (64, 0) == @inferred signature(O3)
    @test (2, 0) == @inferred signature(O4)
  end

  # minkowski mat

  @testset "Minkowski matrix" begin
    RR = ArbField(64)

    b = RR[ RR(1) Base.sqrt(RR(2)) RR(0); (exp(1//RR(3) * log(RR(2)))) (-exp(-1//RR(6) * log(RR(2)))) (Base.sqrt(RR(3)) * exp(-1//RR(6) * log(RR(2)))); (exp(1//RR(3) * log(RR(4)))) (-exp(1//RR(6) * log(RR(2)))) (-exp(1//RR(6) * log(RR(54)))) ]
    bb = @inferred minkowski_matrix(O1, 256)

    @test overlaps(b, bb)
    for i in 1:3
      for j in 1:3
        @test Hecke.radiuslttwopower(bb[i, j], -256)
      end
    end

    b = one(MatrixSpace(RR, 1, 1))

    bb = @inferred minkowski_matrix(O2, 1024)

    @test overlaps(b, bb)
    for i in 1:1
      for j in 1:1
        @test Hecke.radiuslttwopower(bb[i, j], -1024)
      end
    end

    bb = @inferred minkowski_matrix(O3, 1024)

    for i in 1:64
      for j in 1:64
        @test Hecke.radiuslttwopower(bb[i, j], -1024)
      end
    end

    @test contains(RR("19063561108769878656033240617946635072004849200892084525390959717509 +/- 1"), det(bb))

    b = RR[ RR(1) RR(1); -2*Base.sqrt(RR(5)) 2*Base.sqrt(RR(5))]

    bb = @inferred minkowski_matrix(O4, 1024)

    @test overlaps(b, bb) ||
    for i in 1:2
      for j in 1:2
        @test Hecke.radiuslttwopower(bb[i, j], -1024)
      end
    end
  end

  @testset "Element inclusion" begin
    b = @inferred in(a1, O1)
    @test b

    b = @inferred in(a1//2, O1)
    @test !b

    b = @inferred in(a2, O2)
    @test b

    b = @inferred in(a2//3, O2)
    @test !b

    b = @inferred in(a3^4, O3)
    @test b

    b = @inferred in(a3^3//2, O3)
    @test !b

    b = @inferred in(2*a4, O4)
    @test b

    b = @inferred in(a4, O4)
    @test !b
  end

  @testset "Denoninator of elements" begin
    b = @inferred denominator(a1, O1)
    @test b == 1
    b = @inferred denominator(a1//7, O1)
    @test b == 7

    b = @inferred denominator(a2, O2)
    @test b == 1
    b = @inferred denominator(a2//4, O2)
    @test b == 2

    b = @inferred denominator(a3, O3)
    @test b == 1
    b = @inferred denominator(a3^3//2, O3)
    @test b == 2

    b = @inferred denominator(a4, O4)
    @test b == 2
    b = @inferred denominator(a4//2, O4)
    @test b == 4
  end

  @testset "Addition" begin
    O6_2 = Order(K6, Hecke.FakeFmpqMat(FlintZZ[2 0; 0 1], FlintZZ(2)))
    O6_3 = Order(K6, Hecke.FakeFmpqMat(FlintZZ[3 0; 0 1], FlintZZ(3)))

    b = @inferred O6_2 +
 O6_3
    @test basis_matrix(b) == Hecke.FakeFmpqMat(FlintZZ[6 0; 0 1], FlintZZ(6))

    @test discriminant(b) == 20

    @test O4 +
 O4 == O4
    @test (@inferred O6_2 +
 O6_2) isa NfOrd
  end

  @testset "Maximal Order" begin
    f = x^18 - 78*x^17 + 2613*x^16 - 49085*x^15 + 567645*x^14 - 4204473*x^13 +
        20464879*x^12 - 68501589*x^11 + 169973505*x^10 - 322856306*x^9 +
        493384242*x^8 - 631138365*x^7 + 698201471*x^6 - 646804899*x^5 +
        437728161*x^4 - 236413590*x^3 + 186076059*x^2 - 128459175*x + 34393321

    KK, _a = NumberField(f, "a")
    O_KK = maximal_order(KK)
    @test discriminant(O_KK) == -82506874955368517242637353371059355648

    f = 1//9*x^3 - 1//3*x^2 - 2*x + 1//3
    K, a = number_field(f, "a", cached = false)
    OK = maximal_order(K)
    @test discriminant(OK) == 81
  end

  @testset "Conductor" begin
    f = x^7 - 1000*x^2 +
 1000*x - 1000
    K, a = NumberField(f,"a");
    E = Order(K, [1, a, a^2, a^3, a^4, 1//5*a^5, 1//5*a^6])
    lP = prime_ideals_over(E, 5)
    @test length(lP) == 1
    P = lP[1]
    Emult = ring_of_multipliers(P)
    @test conductor(E, Emult) == P
  end

  @testset "Maximal order" begin
    R, x = PolynomialRing(QQ, "x")
    K, a = NumberField(x^6+
28153176769513638533819953494763742552095011029795886647010626985097770493447390786573312647386923245326294607649641017067997516829897062369182892772219258562789629151345178233470976*x^3+
1087544917378569497489782414087715308104486063970662361708698298449681758488800617355980998085309157797376460545454402571140078116543476905649892273803228466894270759398058362231343906313018663670599695143861422721141563129150845697850601640755649472530205143222723244300807912375953120815029721479769822383312924719424335970141907758846596430457135098855468040192)
    OK = maximal_order(K)
    @test discriminant(OK) == -119313478467

    f = x^90 + x^89 + 139*x^88 + 16*x^87 + 13000*x^86 - 13519*x^85 +
        1078293*x^84 + 2633390*x^83 + 92487856*x^82 + 393094246*x^81 +
        7222691559*x^80 + 31283828160*x^79 + 525642325551*x^78 +
        1906118141542*x^77 + 24142920697938*x^76 + 79592960305643*x^75 +
        838232263382574*x^74 + 2605205454422475*x^73 + 24565284675046150*x^72 +
        70981918657774030*x^71 + 641054201228592185*x^70 +
        1734903783394973997*x^69 + 15495356543087563190*x^68 +
        39815058831494401595*x^67 + 351972255697672269132*x^66 +
        866446351271000834294*x^65 + 7284533695483449887998*x^64 +
        17310091691172075064430*x^63 + 138014403907097344715092*x^62 +
        319531558981947613441596*x^61 + 2432983198793549715316980*x^60 +
        5537442057649408847724145*x^59 + 40353958424069616834295637*x^58 +
        91189158071575880360579441*x^57 + 630882000691368461628228052*x^56 +
        1426949379857810145631112646*x^55 + 9191277133196734164680125413*x^54 +
        20936479304104710085619569433*x^53 +
        121768939504529059537357333060*x^52 +
        282225207669417888617305419272*x^51 +
        1489116602266612601694514162250*x^50 +
        3575945005138761320856117912851*x^49 +
        17164847522041015077655408370625*x^48 +
        42976766590065978771098613115446*x^47 +
        187379014275610179328765967451591*x^46 +
        475473622955094214940457104660388*x^45 +
        1896630292418425674557616994097027*x^44 +
        4786262605115919786887499815170419*x^43 +
        17566207321216073635035685715922302*x^42 +
        43773152173553287850271978082326015*x^41 +
        147775843312592510816445892573039009*x^40 +
        364156831732168021153677336060084118*x^39 +
        1148364731883924421483992652903748666*x^38 +
        2814173723179416944720903218947851786*x^37 +
        8370895098052989610201994338666933651*x^36 +
        20335120855907700603368948666313561209*x^35 +
        57191564053538817508053945073081662538*x^34 +
        135304635916981244542647469115790850307*x^33 +
        359383434312823007038048150273521606192*x^32 +
        821421357892644116033093024760854538434*x^31 +
        2056171975482900664138431337583736236244*x^30 +
        4525199297879762701714763342916145435279*x^29 +
        10655343037792823051732240005537546194512*x^28 +
        22564853818976494627910633580257703577086*x^27 +
        50585339451073312597225459076970160344892*x^26 +
        103452321959460929932356709588965504292221*x^25 +
        222172495601221219568072025269247279927175*x^24 +
        438613264120019860458734291413052278175159*x^23 +
        901458132693788891552332320726664567329313*x^22 +
        1707646397658877477253883641684185925797073*x^21 +
        3330870516863020523555754829288437639122463*x^20 +
        5995774963002859372517541963472316198304780*x^19 +
        10937690315526981049730770722588234629451558*x^18 +
        18397884839319476713252646941576626221504135*x^17 +
        30840950974613175936235711714044753512673008*x^16 +
        47298339147633856095770166049706593255403057*x^15 +
        72756707268928051732879416098688485637375580*x^14 +
        99816001337810516846999075794028329288871096*x^13 +
        137026341136579547060038851139186650530322630*x^12 +
        162829510840980663554383571672105374172785379*x^11 +
        189916439827327580895122778870820162123007285*x^10 +
        193379308189454962043349038812422861136194833*x^9 +
        193931005081361082482626409836137017187820153*x^8 +
        132835684951238038126841006782845727573364179*x^7 +
        101387674327323669504054265029073554782913385*x^6 -
        12293053226599581249247685498068796993543192*x^5 +
        1490584272544043051357580914905419718739398*x^4 -
        180650443636285117226206582673575773019341*x^3 +
        21986977593862597199128608447146928784347*x^2 -
        2582145971030886336723659422476783673912*x +
        373314295307719514165340295548734564161
    K, a  = NumberField(f)
    OK = maximal_order(K)
    @test discriminant(OK) == fmpz(-433519477469849528885640700564673233219511150913137737329060579658434898165433013265562669560753409280699168496240715845396318429302546131097709041385796139906003892672353215342275020339552080857504679294774632493735263848953550532754501053167215366669706956865463)

    f = 1//6*x^4 - 1//2*x^3 - x^2 + x + 5//2
    K, a = number_field(f, cached = false)
    OK = maximal_order(K)
    @test discriminant(OK) == -563787


  end

  @testset "Another torsion unit" begin
    f = x^16 + 43*x^14 + 655*x^12 + 4278*x^10 + 12259*x^8 + 14667*x^6 + 5765*x^4 + 732*x^2 + 16
    K, a = NumberField(f)
    A, mA = torsion_unit_group(K)
    @assert order(A) == 4
  end

  @testset "Norm change const" begin
    f = x^40 + 1862*x^39 - 1112668826*x^38 - 2991512355894*x^37 + 566993681952202373*x^36 + 2017441405228030707586*x^35 - 175156040975066159587067328*x^34 - 785005126131774557853164582116*x^33 + 36557780851133638195906242592234801*x^32 + 200587082590489185309985631868100635012*x^31 - 5429757747829349016956750367584542284978228*x^30 - 36009847003996154525451877761268398961149527548*x^29 + 587071015371981980470934282455569475736243334592406*x^28 + 4720577122440159274921751893425144676887926994772075508*x^27 - 46180889136357411449592882635819819439915825946455876164672*x^26 - 461839341971493927192034139717310092285999944476104917304279576*x^25 + 2555510467448915039452463274807074340660884849865135550568713989169*x^24 + 34056605646463969801311436797728928914804586902032964105831687030128610*x^23 - 87661907920385711527299103576691660391231601737017407280726180296239164110*x^22 - 1891465196932217852898236407753131526913804157508123118757370189523333822889778*x^21 + 683732008940227049521067389660855055661816296241012390352733859313644550473220787*x^20 + 78068735280216975036640738160865083802110999435759754467376977066564648847359420262910*x^19 + 113778679498782804182002473069010236030689029461107488253929580757039432903686310314816584*x^18 - 2314570810207081789983024763998834178521142294121220202555771365292306040011121404690356419860*x^17 - 7425633812696135863928497328540579634621418874242744461899019503102763977556011588204285646832029*x^16 + 45360958839104937751976352637564911862262579788425871367123506070848343065835304798839966763238814188*x^15 + 249558716653920287241851992798175797844279782828713176105084617666436573549346254187542027024217960335196*x^14 - 437337615653063054814035505110159390235864235626029284997494752883492649947062024660014888910910462526268364*x^13 - 5131386880357026716563915807491962130268349295415833045464279410466699353904204190121732992126111084501222078050*x^12 - 3029393293850928694675392920391397659961396646458990275329136616804251555445078568461814939417797589235068329263876*x^11 + 61024591136968743733681067386602950129365133831090208010213049691275080650169695576710468106059358989416187661109364632*x^10 + 150818901356049810203568377517359017547145720132304060134164296226122670894533050555495249540278005079589521085510144527200*x^9 - 280867793108728886225739567020272658197948159815237732186958415769189099817716680255787793511637347855916561448229255902832493*x^8 - 1739761918427858410184860696267579547757521718466485249769015778645139642009039356056995784299253474956534283272838862557433178914*x^7 - 1713028698120925519537270506073059322775328573486251557685060938064616184071748703372231670104865295385229641668021312021992725775114*x^6 + 5388949446161509546871884250929319541242914992563817315185291005326234199685779776381390261239632464701467822432508674680878580176419930*x^5 + 18334570658995165446575207636442129027514001547007993911000333638121946753743412963404667688799017037983585611422812509219547658673829278845*x^4 + 24411220867980361995510524128840509475031800160188729383943666670907190141187720131373965236021098644275746743177410299231744640956975399225658*x^3 + 17049943832108038517023123509096388521580837288719623844936279514984821192784380632368183202324308212972742112681567236456001651249317285087074440*x^2 + 6132129880898294160271663709906600419410645105514768565916936856541632446845384482893703843539135982686346361169562726353897490737602044166997016420*x + 893439077326279341035471655728440623212462019375269821867473723830962022156998380069397504281330173585050150201296580695995249378607394062499378598947;
    K, a = NumberField(f, "a")
    E = equation_order(K)
    @test (@inferred norm_change_const(E)) isa Tuple{BigFloat, BigFloat}
  end
end
