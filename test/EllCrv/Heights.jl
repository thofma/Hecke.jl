@testset "Height functions for elliptic curves" begin
  E1 = EllipticCurve([1, -1, 1, -2063758701246626370773726978, 32838647793306133075103747085833809114881])
  P = E1([-30987785091199, 258909576181697016447])

  @testset "Naive height" begin
    nh = @inferred naive_height(P, 10)
    @test overlaps(nh, parent(nh)("31.0646142134475839"))
    nh2 = @inferred naive_height(P, 1000)
    @test Hecke.radiuslttwopower(nh2, -1000)
    @test contains(nh, nh2)
  end

  @testset "Local heights" begin
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

    E3 = EllipticCurve([1, -2])
    P3 = E3([1, 0])
    lh = local_height(P3, 2)
    @test overlaps(lh, ArbField(300, cached = false)("-0.6931471805599453094172321214581765680755001343602552541206800094933936219696947156058633269964186876"))
    lh2 = local_height(P3, 2, 1000)
    @test Hecke.radiuslttwopower(lh2, -1000)
    @test contains(lh, lh2)

    E4 = EllipticCurve([1, 0, 1, -171, -874]);
    P4 = E4([15, -8]);
    lh = local_height(P4, 2)
    @test overlaps(lh, -9//2 * log(parent(lh)(2)))
    lh2 = local_height(P4, 2, 1000)
    @test Hecke.radiuslttwopower(lh2, -1000)
    @test contains(lh, lh2)

    E5 = EllipticCurve([0, 1, 0, -1, 0])
    P5 = E5([1, -1])
    lh = local_height(P5, 2)
    @test overlaps(lh, -2//3 * log(parent(lh)(2)))
    lh2 = local_height(P5, 2, 1000)
    @test Hecke.radiuslttwopower(lh2, -1000)
    @test contains(lh, lh2)

    E6 = EllipticCurve([1, 1, 1, -8, 192]);
    P6 = E6([68647415735927212584//3943314364572900625,519963951463804725273032226752//7830547010835704571633765625])
    lh = local_height(P6, 44851, 3)
    @test overlaps(lh, 2 * log(parent(lh)(44851)))
    lh2 = local_height(P6, 44851, 1000)
    @test contains(lh, lh2)
  end

  @testset "Real height" begin
     lh = @inferred local_height(P, 0)
     @test overlaps(lh, parent(lh)("31.81286785798043275682637979803303125935036048926542077924848835239766790624470"))
     lh2 = @inferred local_height(P, 0, 1000)
     @test Hecke.radiuslttwopower(lh2, -1000)
     @test contains(lh, lh2)

     let E, P
       E = EllipticCurve([1, 1, 1, -8, 192])
       P = E([160, 1951])
       lh = local_height(P, 0)
       @test overlaps(lh, parent(lh)("5.09938848480892702329774919790347687480904873916673130299681898045318895190447456165258858608067967267678445290736965906099"))
       lh2 = @inferred local_height(P, 0, 1000)
       @test Hecke.radiuslttwopower(lh2, -1000)
       @test contains(lh, lh2)
     end

     let E, P
       E = EllipticCurve([-98, 50])
       P = E([25//49, 125//343])
       # x-coordinates "close" to 1//2
       # Use low precision to make the abs(x) <= 1//2 check increase precision
       lh = local_height(P, 0, 1)
       @test overlaps(lh, parent(lh)("2.288529620287974"))
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

  E2 = EllipticCurve([0, 0, 1, -7, 6])
  P1 = E2([2, 0])
  P2 = E2([8, 21])
  P3 = E2([-1, 3])

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
  end
end
