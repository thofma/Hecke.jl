@testset "Height functions for elliptic curves" begin
  E1 = elliptic_curve([1, -1, 1, -2063758701246626370773726978, 32838647793306133075103747085833809114881])
  P = E1([-30987785091199, 258909576181697016447])

  Rx, x = polynomial_ring(QQ, "x")
  K, a = number_field(x^3 - x^2 + 1)
  E1_nf = elliptic_curve(K, [0, a-1, a+1, 0, -a])
  P_nf = E1_nf([-a+1, -1])


  @testset "Naive height" begin
    nh = @inferred naive_height(P, 10)
    @test overlaps(nh, parent(nh)("31.0646142134475839"))
    nh2 = @inferred naive_height(P, 1000)
    @test Hecke.radiuslttwopower(nh2, -1000)
    @test contains(nh, nh2)

    nh = @inferred naive_height(P_nf, 10)
    @test overlaps(nh, parent(nh)("0.187466382881974564341367176045"))
    nh2 = @inferred naive_height(P_nf, 1000)
    @test Hecke.radiuslttwopower(nh2, -1000)
    @test contains(nh, nh2)

    nh = @inferred naive_height(5*P_nf, 10)
    @test overlaps(nh, parent(nh)("1.17277096435854037697531906768"))
    nh2 = @inferred naive_height(5*P_nf, 1000)
    @test Hecke.radiuslttwopower(nh2, -1000)
    @test contains(nh, nh2)

    nh = @inferred naive_height(8*P_nf, 10)
    @test overlaps(nh, parent(nh)("2.19813781991659283457412571041"))
    nh2 = @inferred naive_height(8*P_nf, 1000)
    @test Hecke.radiuslttwopower(nh2, -1000)
    @test contains(nh, nh2)

  end

  @testset "Non-archimedean local heights" begin
    lh = @inferred local_height(P, 17)
    @test overlaps(lh, parent(lh)("-1.8888088960374773868330230785820843570588020083904965248648251585"))
    lh2 = @inferred local_height(P, 17, 1000)
    @test Hecke.radiuslttwopower(lh2, -1000)
    @test contains(lh, lh2)

    lh = @inferred local_height(P, 3)
    @test overlaps(lh, parent(lh)("-1.09861228866810969139524523692252570464749055782274945173469433363749429321860"))
    lh2 = @inferred local_height(P, 3, 1000)
    @test Hecke.radiuslttwopower(lh2, -1000)
    @test contains(lh, lh2)

    lh = local_height(infinity(E1), 0)
    @test lh == 0
    lh2 = local_height(infinity(E1), 0, 1000)
    @test Hecke.radiuslttwopower(lh2, -1000)

    lh = local_height(infinity(E1), 2)
    @test lh == 0
    lh2 = local_height(infinity(E1), 2, 1000)
    @test Hecke.radiuslttwopower(lh2, -1000)

    E3 = elliptic_curve([1, -2])
    P3 = E3([1, 0])
    lh = local_height(P3, 2)
    @test overlaps(lh, ArbField(300, cached = false)("-0.6931471805599453094172321214581765680755001343602552541206800094933936219696947156058633269964186876"))
    lh2 = local_height(P3, 2, 1000)
    @test Hecke.radiuslttwopower(lh2, -1000)
    @test contains(lh, lh2)

    E4 = elliptic_curve([1, 0, 1, -171, -874]);
    P4 = E4([15, -8]);
    lh = local_height(P4, 2)
    @test overlaps(lh, -9//2 * log(parent(lh)(2)))
    lh2 = local_height(P4, 2, 1000)
    @test Hecke.radiuslttwopower(lh2, -1000)
    @test contains(lh, lh2)

    E5 = elliptic_curve([0, 1, 0, -1, 0])
    P5 = E5([1, -1])
    lh = local_height(P5, 2)
    @test overlaps(lh, -2//3 * log(parent(lh)(2)))
    lh2 = local_height(P5, 2, 1000)
    @test Hecke.radiuslttwopower(lh2, -1000)
    @test contains(lh, lh2)

    E6 = elliptic_curve([1, 1, 1, -8, 192]);
    P6 = E6([68647415735927212584//3943314364572900625,519963951463804725273032226752//7830547010835704571633765625])
    lh = local_height(P6, 44851, 3)
    @test overlaps(lh, 2 * log(parent(lh)(44851)))
    lh2 = local_height(P6, 44851, 1000)
    @test contains(lh, lh2)

    L, a = number_field(x^2 - x - 1)
    OL = ring_of_integers(L)
    E7 = elliptic_curve(L, [1, 1, 1, -10, -10])
    P7 = E7([-3*a + 2, 3])
    I = prime_ideals_over(OL, 3)[1]
    lh = local_height(P7, I)
    @test overlaps(lh, -3//2 * log(parent(lh)(3)))
    lh2 = local_height(P7, I, 1000)
    @test Hecke.radiuslttwopower(lh2, -1000)
    @test contains(lh, lh2)

    I = prime_ideals_over(OL, 5)[1]
    lh = local_height(P7, I)
    @test overlaps(lh, -7//8 * log(parent(lh)(5)))
    lh2 = local_height(P7, I, 1000)
    @test Hecke.radiuslttwopower(lh2, -1000)
    @test contains(lh, lh2)

  end

  @testset "Archimedean local heights" begin
     lh = @inferred local_height(P, 0)
     @test overlaps(lh, parent(lh)("31.81286785798043275682637979803303125935036048926542077924848835239766790624470"))
     lh2 = @inferred local_height(P, 0, 1000)
     @test Hecke.radiuslttwopower(lh2, -1000)
     @test contains(lh, lh2)

     let E, P
       E = elliptic_curve([1, 1, 1, -8, 192])
       P = E([160, 1951])
       lh = local_height(P, 0)
       @test overlaps(lh, parent(lh)("5.09938848480892702329774919790347687480904873916673130299681898045318895190447456165258858608067967267678445290736965906099"))
       lh2 = @inferred local_height(P, 0, 1000)
       @test Hecke.radiuslttwopower(lh2, -1000)
       @test contains(lh, lh2)
     end

     let E, P
       E = elliptic_curve([-98, 50])
       P = E([25//49, 125//343])
       # x-coordinates "close" to 1//2
       # Use low precision to make the abs(x) <= 1//2 check increase precision
       lh = local_height(P, 0, 1)
       @test overlaps(lh, parent(lh)("2.288529620287974"))
     end

     let E, P
       K, a = number_field(x^3 - x^2 + 1)
       E = elliptic_curve(K, [a, 1 + a , a, a, 0])
       P = E([-a^2, -a])
       vr = real_places(K)
       vc = complex_places(K)

       lh = local_height(P, vr[1])
       @test overlaps(lh, parent(lh)("0.108320455052207035871828595437522752570417527"))
       lh2 = @inferred local_height(P, vr[1], 1000)
       @test Hecke.radiuslttwopower(lh2, -1000)
       @test contains(lh, lh2)

       lh = local_height(P, vc[1])
       @test overlaps(lh, parent(lh)("0.348199250582421575714275535587785533596191574936015954771442"))
       lh2 = @inferred local_height(P, vc[1], 1000)
       @test Hecke.radiuslttwopower(lh2, -1000)
       @test contains(lh, lh2)
     end

  end



  @testset "Canonical height" begin
     ch = @inferred canonical_height(P)
     @test overlaps(ch, parent(ch)("25.860317067546190743868840740735110323098872903844416215577171041783572"))
     ch2 = @inferred canonical_height(P, 1000)
     @test Hecke.radiuslttwopower(ch2, -1000)
     @test contains(ch, ch2)



  end

  @testset "Neron-Tate height" begin
    # this is just an alias
    ch = @inferred canonical_height(P)
    nth = @inferred neron_tate_height(P)
    @test overlaps(ch, nth)
  end

  E2 = elliptic_curve([0, 0, 1, -7, 6])
  P1 = E2([2, 0])
  P2 = E2([8, 21])
  P3 = E2([-1, 3])

  E_nf = elliptic_curve(K, [0, a^2 - 1, 1, -a^2, 0])

  P1_nf = E_nf([-a + 1, -a^2 + a - 1])
  P2_nf = E_nf([-a^2 + 1 , -a^2])


   @testset "Height pairing" begin
    hp = @inferred height_pairing(P1, P2)
    @test overlaps(hp, parent(hp)("-0.30977229996416302844985467774415903355780764325353906868295275334"))
    hp2 = @inferred height_pairing(P1, P2, 1000)
    @test Hecke.radiuslttwopower(hp2, -1000)
    @test contains(hp, hp2)

    reg = @inferred regulator([P1, P2])
    @test overlaps(reg, parent(reg)("1.5396040638588101189412785764780847431246576764753034126540923984068891435"))
    reg2 = @inferred regulator([P1, P2], 1000)
    @test Hecke.radiuslttwopower(reg2, -1000)
    @test contains(reg, reg2)

    reg = @inferred regulator([P1, P2, P3])
    @test overlaps(reg, parent(reg)("0.417143558758383969817119544618093396749810106098498386724736819756177702534"))
    reg2 = @inferred regulator([P1, P2, P3], 1000)
    @test Hecke.radiuslttwopower(reg2, -1000)
    @test contains(reg, reg2)

    hp = @inferred height_pairing(P1_nf, P2_nf)
    @test overlaps(hp, parent(hp)("-0.19530844654221841913259932348283442414096794603756"))
    hp2 = @inferred height_pairing(P1_nf, P2_nf, 1000)
    @test Hecke.radiuslttwopower(hp2, -1000)
    @test contains(hp, hp2)

    reg = @inferred regulator([P1_nf, P2_nf])
    @test overlaps(reg, parent(reg)("0.0091525485170209087192739142429696454145410168245515"))
    reg2 = @inferred regulator([P1_nf, P2_nf], 1000)
    @test Hecke.radiuslttwopower(reg2, -1000)
    @test contains(reg, reg2)

  end

  @testset "CPS Height Bounds" begin
    #Coercing into a field with less precision as the checks only need to hold
    #up to (number of complex embeddings)*0.001 anyway.
    Rc = ArbField(100)

    #Both embeddings
    K, a = number_field(x^3 - x^2 + 1)
    E = elliptic_curve(K, [a, 1 + a , a, a, 0])

    a, b = @inferred CPS_height_bounds(E)
    #Could not check if lower bound is similar to Magma as Magma has a bug.
    @test overlaps(Rc(a), Rc("-0.834713682617350127906563342771"))
    #@test overlaps(Rc(a), Rc("-0.03553834647476913862120457958938"))
    @test overlaps(Rc(b), Rc("0.754821686518685316960441193763"))

    #Only complex embeddings
    K, a = number_field(x^2 - x + 3)
    E = elliptic_curve(K, [0, -1, 0, -10, -20])
    a, b = @inferred CPS_height_bounds(E)

    #In this case the lower bound coincides with Magma as there is no real contribution
    @test overlaps(Rc(a), Rc("-1.76776830268635858368843907776208"))
    @test overlaps(Rc(b), Rc("0.55364518671729453447085398655621"))

    #Only real embeddings
    K, a = number_field(x^2 - x -1)
    E = elliptic_curve(K, [1, 1, 1, -135, -660])
    a, b = @inferred CPS_height_bounds(E)
    #Could not check if lower bound is similar to Magma as Magma has a bug.
    @test overlaps(Rc(a), Rc("-0.58265890145564377871651026519043"))
    @test overlaps(Rc(b), Rc("4.6890929222858463207551031144912"))

    # Test a rational curve
    E = elliptic_curve([1, 2, 3, 4, 5])
    a, b = @inferred CPS_height_bounds(E)
    # Seems to be the for the lower bound as Magma
    @test overlaps(Rc(a), Rc("-1.54490966274321192358953410502"))
    @test overlaps(Rc(b), Rc("0.119124519092509817076007944328"))

    # Same curve over a number field
    E = elliptic_curve(K, [1, 2, 3, 4, 5])
    a, b = @inferred CPS_height_bounds(E)
    # Seems to be the for the lower bound as Magma
    @test overlaps(Rc(a), Rc("-1.54490966274321192358953410502"))
    @test overlaps(Rc(b), Rc("0.119124519092509817076007944328"))
  end
end
