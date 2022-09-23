@testset "Test composition order" begin
  Qx, x = FlintQQ["x"]
  K, a = NumberField(x^6 + 108, "a")
  A = automorphism_list(K)
  for f in A
    for g in A
      @test g(f(a)) == compose(f, g)(a)
      @test g(f(a)) == (f * g)(a)
    end
  end
end

@testset "Induce image" begin
  Qx, x = FlintQQ["x"]
  K, a = NumberField(x^6 + 108, "a")
  A = automorphism_list(K)
  OK = maximal_order(K)
  lP = prime_decomposition(OK, 7)
  lP1 = [x[1] for x in lP]
  for i = 1:length(lP)
    I_new = A[2](lP1[1])
    id = findfirst(isequal(I_new), lP1)
    @test id != nothing
  end
  f = hom(K, K, a^4//12+a//2)
  E = EquationOrder(K)
  I = ideal(E, E(a))
  @test_throws ErrorException Hecke.induce_image(f, I)

end


@testset "Automorphisms" begin
  Qx, x = FlintQQ["x"]
  f = x^32 - 217*x^28 + 42321*x^24 - 999502*x^20 + 18913054*x^16 - 80959662*x^12 + 277668081*x^8 - 115322697*x^4 + 43046721
  K, a = number_field(f, cached = false, check = false)
  auts = Hecke._automorphisms(K, is_abelian = true)
  auts1 = Hecke._automorphisms(K)
  @test Set(auts) == Set(auts1)

  f = x^4 + 4*x^2 + 2
  K, a = number_field(f, cached = false, check = false)
  G, mG = automorphism_group(K)
  @test order(G) == 4
  fl, tau = Hecke.is_cm_field(K)
  @test fl

  f = x^40 + 1862*x^39 - 1112668826*x^38 - 2991512355894*x^37 + 566993681952202373*x^36 + 2017441405228030707586*x^35 - 175156040975066159587067328*x^34 - 785005126131774557853164582116*x^33 + 36557780851133638195906242592234801*x^32 + 200587082590489185309985631868100635012*x^31 - 5429757747829349016956750367584542284978228*x^30 - 36009847003996154525451877761268398961149527548*x^29 + 587071015371981980470934282455569475736243334592406*x^28 + 4720577122440159274921751893425144676887926994772075508*x^27 - 46180889136357411449592882635819819439915825946455876164672*x^26 - 461839341971493927192034139717310092285999944476104917304279576*x^25 + 2555510467448915039452463274807074340660884849865135550568713989169*x^24 + 34056605646463969801311436797728928914804586902032964105831687030128610*x^23 - 87661907920385711527299103576691660391231601737017407280726180296239164110*x^22 - 1891465196932217852898236407753131526913804157508123118757370189523333822889778*x^21 + 683732008940227049521067389660855055661816296241012390352733859313644550473220787*x^20 + 78068735280216975036640738160865083802110999435759754467376977066564648847359420262910*x^19 + 113778679498782804182002473069010236030689029461107488253929580757039432903686310314816584*x^18 - 2314570810207081789983024763998834178521142294121220202555771365292306040011121404690356419860*x^17 - 7425633812696135863928497328540579634621418874242744461899019503102763977556011588204285646832029*x^16 + 45360958839104937751976352637564911862262579788425871367123506070848343065835304798839966763238814188*x^15 + 249558716653920287241851992798175797844279782828713176105084617666436573549346254187542027024217960335196*x^14 - 437337615653063054814035505110159390235864235626029284997494752883492649947062024660014888910910462526268364*x^13 - 5131386880357026716563915807491962130268349295415833045464279410466699353904204190121732992126111084501222078050*x^12 - 3029393293850928694675392920391397659961396646458990275329136616804251555445078568461814939417797589235068329263876*x^11 + 61024591136968743733681067386602950129365133831090208010213049691275080650169695576710468106059358989416187661109364632*x^10 + 150818901356049810203568377517359017547145720132304060134164296226122670894533050555495249540278005079589521085510144527200*x^9 - 280867793108728886225739567020272658197948159815237732186958415769189099817716680255787793511637347855916561448229255902832493*x^8 - 1739761918427858410184860696267579547757521718466485249769015778645139642009039356056995784299253474956534283272838862557433178914*x^7 - 1713028698120925519537270506073059322775328573486251557685060938064616184071748703372231670104865295385229641668021312021992725775114*x^6 + 5388949446161509546871884250929319541242914992563817315185291005326234199685779776381390261239632464701467822432508674680878580176419930*x^5 + 18334570658995165446575207636442129027514001547007993911000333638121946753743412963404667688799017037983585611422812509219547658673829278845*x^4 + 24411220867980361995510524128840509475031800160188729383943666670907190141187720131373965236021098644275746743177410299231744640956975399225658*x^3 + 17049943832108038517023123509096388521580837288719623844936279514984821192784380632368183202324308212972742112681567236456001651249317285087074440*x^2 + 6132129880898294160271663709906600419410645105514768565916936856541632446845384482893703843539135982686346361169562726353897490737602044166997016420*x + 893439077326279341035471655728440623212462019375269821867473723830962022156998380069397504281330173585050150201296580695995249378607394062499378598947
  K, a = number_field(f)
  A = automorphism_list(K)
  @test length(A) == 40

  K, a = number_field(x^2+x+1)
  Kt, t = PolynomialRing(K)
  L, b = number_field(t^3-2)
  Ly, y = PolynomialRing(L)
  F, c = number_field(y^3-5)
  G, mG = automorphism_group(F, K)
  @test order(G) == 9
  Gabs, mGabs = absolute_automorphism_group(L)
  @test order(Gabs) == 6

end

@testset "CM" begin
  Qx, x = FlintQQ["x"]
  f = x^20 + 6*x^19 + 33*x^18 + 109*x^17 + 332*x^16 + 706*x^15 + 1299*x^14 + 1910*x^13 + 3303*x^12 + 7116*x^11 + 14445*x^10 + 24009*x^9 + 30102*x^8 + 37094*x^7 + 54187*x^6 + 82991*x^5 + 119418*x^4 + 148247*x^3 + 185442*x^2 + 184250*x + 112225
  K, a = NumberField(f, "a", cached = false)
  G, mG = automorphism_group(K)
  @test order(center(G)[1]) == 2
  fl, tau = Hecke.is_cm_field(K)
  @test fl

  f = x^16 + 1488*x^14 + 792240*x^12 + 196892096*x^10 + 24165834080*x^8 + 1427570443008*x^6 + 40942926058240*x^4 + 522149874492416*x^2 + 2045677637972224
  K, a = number_field(f, "a", cached = false)
  fl, tau = Hecke.is_cm_field(K)
  @test fl
  fl, tau = Hecke.is_cm_field(K)
  @test fl
end
