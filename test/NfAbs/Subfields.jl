@testset "Fixed fields" begin
  Qx,x = QQ["x"]

  @testset "FixedField: absolute" begin
    f = x^8+236*x^6+12158*x^4+201788*x^2+779689
    K, a = number_field(f, "a");
    s = hom(K, K, 43//339072*a^7 + 9265//339072*a^5 + 336481//339072*a^3 + 2429659//339072*a);
    t = hom(K, K, -115//1356288*a^7 - 26257//1356288*a^5 - 1190665//1356288*a^3 - 13355755//1356288*a);

    @test degree(fixed_field(K,t)[1])     == 4
    @test degree(fixed_field(K,s)[1])     == 4
    @test degree(fixed_field(K,[s,t])[1]) == 2
  end

  @testset "FixedField: relative" begin
    K,b     = number_field(x-1,"b")
    Ky,y    = K["y"]
    f = y^8+236*y^6+12158*y^4+201788*y^2+779689
    L,a     = number_field(f,"a")
    s = hom(L, L, 43//339072*a^7 + 9265//339072*a^5 + 336481//339072*a^3 + 2429659//339072*a);
    t = hom(L, L, -115//1356288*a^7 - 26257//1356288*a^5 - 1190665//1356288*a^3 - 13355755//1356288*a);

    @test degree(fixed_field(L,t)[1])     == 4
    @test degree(fixed_field(L,s)[1])     == 4
    @test degree(fixed_field(L,[s,t])[1]) == 2
  end
end

@testset "Subfields" begin
  Qx, x = QQ["x"]
  f_1 = x^6 + 108;
  K_1,_ = number_field(f_1);
  #(C_2)^3
  f_2 = x^8 - 12*x^6 + 23*x^4 - 12*x^2 + 1;
  K_2,_ = number_field(f_2);
  #2xD_4
  f_3 = x^8 - 10*x^4 + 1;
  K_3,_ = number_field(f_3);
  #[2^4]_4
  f_4 = x^8 + 4*x^6 + 10*x^4 + 12*x^2 + 7;
  K_4,_ = number_field(f_4);
  #(3^2):2
  f_5 = x^9 - 18*x^8 + 117*x^7 - 348*x^6 + 396*x^5 + 288*x^4 + 3012*x^3 +576*x^2 + 576*x - 512;
  K_5,_ = number_field(f_5);
  #(2^4):5
  f_6 = x^10 + 38*x^9 - 99*x^8 + 1334*x^7 - 4272*x^6 + 9244*x^5 - 8297*x^4 + 1222*x^3 + 1023*x^2 - 74*x + 1;
  K_6,_ = number_field(f_6);
  #(2^4):D_5
  f_7 = x^10 -20*x^9 + 80*x^8 + 200*x^7 - 3770*x^6 + 872*x^5 + 29080*x^4 + 36280*x^3 - 456615*x^2 + 541260*x - 517448;
  K_7,_ = number_field(f_7);
  #((5^2):4):2
  f_8 = x^10 - 10*x^8 + 20*x^7 + 235*x^6 + 606*x^5 +800*x^4 + 600*x^3 + 270*x^2 + 70*x + 16;
  K_8,_ = number_field(f_8);
  #S_3xS_4
  f_9 = x^12 + 6*x^9 + 4*x^8 + 8*x^6 - 4*x^5 - 12*x^4 + 8*x^3 - 8*x + 8;
  K_9,_ = number_field(f_9);
  #3xD_4
  f_10 = x^12 + 9*x^11 + 3*x^10 - 73*x^9 - 177*x^8 - 267*x^7 - 315*x^6 - 267*x^5 - 177*x^4 - 73*x^3 + 3*x^2 + 9*x + 1;
  K_10,_ = number_field(f_10);
  #A_4
  f_11 = x^12 - 34734*x^11 + 401000259*x^10 - 1456627492885*x^9 - 2537142937228035*x^8 + 18762072755679375516*x^7 - 812368636358864062944*x^6 - 70132863629758257512231931*x^5 + 25834472514893102332821062085*x^4 + 76623280610352450247247939584745*x^3 - 45080885015422662132515763499758450*x^2 - 2070499552240812214288316981071818900*x - 550505759097778545485364826246753544;
  K_11,_ = number_field(f_11);
  #((5^2):4)S_3
  f_12 = x^15 + 20*x^12 + 125*x^11 + 503*x^10 + 1650*x^9 + 3430*x^8 + 4690*x^7 + 4335*x^6 + 2904*x^5 + 1400*x^4 + 485*x^3 +100*x^2 + 15*x + 1;
  K_12,_ = number_field(f_12);

  ### Ex.Tommy ###

  # Normal mit vielen Teilkoerpern #
  #(C_2^3)
  f_13 = x^8 - x^4 + 1;
  K_13,_ = number_field(f_13);
  #(C_2^4)
  f_14 = x^16 - 7*x^12 + 48*x^8 - 7*x^4 + 1;
  K_14,_ = number_field(f_14);
  #(C_2^5)              <--- cmpr runtime fact()
  f_15 = x^32+64*x^30+3072*x^28+78336*x^26+957696*x^24+17534976*x^22+72056832*x^20-10020814848*x^18+102596173824*x^16-271505948672*x^14-53842389499904*x^12-211197100032000*x^10+6793926729007104*x^8+34848900900716544*x^6+79559795278872576*x^4-159748047218147328*x^2+62856539035140096;
  K_15,_ = number_field(f_15);
  # Normal mit wenig Teilkoerpern #
  #(Q_8)
  f_16 = x^8 + 12*x^6 + 36*x^4 + 36*x^2 + 9;
  K_16,_ = number_field(f_16);
  #(Q_8)
  f_17 = x^8 + 3*x^7 + 22*x^6 + 60*x^5 + 201*x^4 + 450*x^3 + 1528*x^2 + 3069*x + 4561;
  K_17,_ = number_field(f_17);
  #(Q_8)
  f_18 = x^8 + 60*x^6 + 900*x^4 + 4500*x^2 + 5625;
  K_18,_ = number_field(f_18);
  #(Q_8)
  f_19 = x^8 + 84*x^6 + 1764*x^4 + 12348*x^2 + 21609;
  K_19,_ = number_field(f_19);
  #(Q_8)
  f_20 = x^8 + 44*x^6 + 308*x^4 + 484*x^2 + 121;
  K_20, _ = number_field(f_20);
  #(C_16)
  f_21 = x^16 - x^15 + x^14 - x^13 + x^12 - x^11 + x^10 - x^9 + x^8 - x^7 + x^6 - x^5 + x^4 - x^3 + x^2 - x + 1;
  K_21, _ = number_field(f_21);
  #(C_32)        <---- cmpr runtime fact() 28sek
  f_22 = x^32+32*x^30+464*x^28+4032*x^26+23400*x^24+95680*x^22+283360*x^20+615296*x^18+980628*x^16+1136960*x^14+940576*x^12+537472*x^10+201552*x^8+45696*x^6+5440*x^4+256*x^2+2;
  K_22, _ = number_field(f_22);
  # Nicht normal mit vielen Teilkoerpern #
  #(C_2^2 x S_3)
  f_23 = x^12 - 4*x^6 + 1;
  K_23, _ = number_field(f_23);
  # Nicht normal mit wenig Teilkoerpern #
  #(S_8)
  f_24 = x^8 - x^7 + 2*x^6 - 3*x^5 + 3*x^4 - 3*x^3 + 3*x^2 - 2*x + 1;
  K_24, _ = number_field(f_24);
  #(S_8)
  f_25 = x^8 - 2*x^7 + 3*x^6 - 3*x^5 + x^4 + 1;
  K_25, _ = number_field(f_25);
  #(S_18)
  f_26 = x^18 - 2*x^17 + x^16 + 3*x^15 - 5*x^14 + x^13 + 5*x^12 - 8*x^11 + 2*x^10 + 7*x^9 - 11*x^8 + 2*x^7 + 9*x^6 - 8*x^5 + x^4 + 5*x^3 - 2*x^2 + 1;
  K_26, _ = number_field(f_26);
  #(18T111)
  f_27 = x^18 - x^17 - x^16 + x^14 - 2*x^13 + x^12 + 5*x^11 + 6*x^10 - 8*x^9 - 6*x^8 - 3*x^7 + 5*x^6 + 6*x^5 + 2*x^4 - 5*x^3 - x^2 + 1;
  K_27, _ = number_field(f_27);

  ### Ex.Hoeij ###

  #r=6
  #vH, K, N 2011: Total time: 30.690 seconds, Total memory usage: 93.44MB
  #Klueners 1998: Total time:  1.340 seconds, Total memory usage: 12.72MB
  f_28 = x^36-30*x^30+1197*x^24-25218*x^18+256770*x^12+15552*x^6+729;

  #r=7
  # vH, K, N 2011: Total time: 453.240 seconds, Total memory usage: 50.31MB
  # Klueners 1998: Total time:  75.230 seconds, Total memory usage: 23.66MB
  f_29 =  x^75+5*x^70-2535*x^65+17325*x^60+588650*x^55-456974*x^50+9905000*x^45-750608135*x^40-21267217530*x^35+
  3806950040*x^30-26676882954*x^25-3032520830*x^20-685818980*x^15-23381430*x^10-11997545*x^5-1;

  #explicit subfields
  K0 = subfields(K_4);
  L1,_ = number_field(x^4 + 4*x^3 + 10*x^2 + 12*x + 7, "l1");
  L2,_ = number_field(x^2 + 6*x + 7, "l2");

  @testset "Fields [2^4]_4" begin
    @test any(L -> is_isomorphic(L[1],L1), K0)
    @test any(L -> is_isomorphic(L[1],L2), K0)
  end

  ###testing .degree of fields##

  @testset "S_3" begin
    @test length(subfields(K_1)) == 6
    @test length(subfields(K_1, degree =6)) == 1
    @test length(subfields(K_1, degree =3)) == 3
    @test length(subfields(K_1, degree =2)) == 1
    @test length(subfields(K_1, degree =1)) == 1
  end

  @testset "(C_2)^3" begin
    @test length(subfields(K_2)) == 16
    @test length(subfields(K_2, degree =8)) == 1
    @test length(subfields(K_2, degree =4)) == 7
    @test length(subfields(K_2, degree =2)) == 7
    @test length(subfields(K_2, degree =1)) == 1
  end

  @testset "2xD_4" begin
    @test length(subfields(K_3)) == 8
    @test length(subfields(K_3, degree =8)) == 1
    @test length(subfields(K_3, degree =4)) == 3
    @test length(subfields(K_3, degree =2)) == 3
    @test length(subfields(K_3, degree =1)) == 1
  end

  @testset "[2^4]_4" begin
    @test length(subfields(K_4)) == 4
    @test length(subfields(K_4, degree =8)) == 1
    @test length(subfields(K_4, degree =4)) == 1
    @test length(subfields(K_4, degree =2)) == 1
    @test length(subfields(K_4, degree =1)) == 1
  end

  @testset "(3^2):2" begin
    @test length(subfields(K_5)) == 6
    @test length(subfields(K_5, degree =9)) == 1
    @test length(subfields(K_5, degree =3)) == 4
    @test length(subfields(K_5, degree =1)) == 1
  end

  @testset "(2^4):5" begin
    @test length(subfields(K_6)) == 3
    @test length(subfields(K_6, degree =10)) == 1
    @test length(subfields(K_6, degree =5)) == 1
    @test length(subfields(K_6, degree =1)) == 1
  end

  @testset "(2^4):D_5" begin
    @test length(subfields(K_7)) == 3
    @test length(subfields(K_7, degree =10)) == 1
    @test length(subfields(K_7, degree =5)) == 1
    @test length(subfields(K_7, degree =1)) == 1
  end

  @testset "((5^2):4):2" begin
    @test length(subfields(K_8)) == 3
    @test length(subfields(K_8, degree =10)) == 1
    @test length(subfields(K_8, degree =2)) == 1
    @test length(subfields(K_8, degree =1)) == 1
  end

  @testset "S_3xS_4" begin
    @test length(subfields(K_9)) == 4
    @test length(subfields(K_9, degree =12)) == 1
    @test length(subfields(K_9, degree =3)) == 1
    @test length(subfields(K_9, degree =4)) == 1
    @test length(subfields(K_9, degree =1)) == 1
  end

  @testset "3xD_4" begin
    @test length(subfields(K_10)) == 6
    @test length(subfields(K_10, degree =12)) == 1
    @test length(subfields(K_10, degree =6)) == 1
    @test length(subfields(K_10, degree =4)) == 1
    @test length(subfields(K_10, degree =3)) == 1
    @test length(subfields(K_10, degree =2)) == 1
    @test length(subfields(K_10, degree =1)) == 1
  end

  @testset "A_4" begin
    @test length(subfields(K_11)) == 10
    @test length(subfields(K_11, degree =12)) == 1
    @test length(subfields(K_11, degree =6)) == 3
    @test length(subfields(K_11, degree =4)) == 4
    @test length(subfields(K_11, degree =3)) == 1
    @test length(subfields(K_11, degree =1)) == 1
  end

  @testset "((5^2):4)S_3" begin
    @test length(subfields(K_12)) == 3
    @test length(subfields(K_12, degree =15)) == 1
    @test length(subfields(K_12, degree =3)) == 1
    @test length(subfields(K_12, degree =1)) == 1
  end
  #Normal many#
  @testset "(C_2^3)" begin
    @test length(subfields(K_13)) == 16
    @test length(subfields(K_13, degree =8)) == 1
    @test length(subfields(K_13, degree =4)) == 7
    @test length(subfields(K_13, degree =2)) == 7
    @test length(subfields(K_13, degree =1)) == 1
  end

  @testset "(C_2^4)" begin
    @test length(subfields(K_14)) == 67
    @test length(subfields(K_14, degree =16)) == 1
    @test length(subfields(K_14, degree =8)) == 15
    @test length(subfields(K_14, degree =4)) == 35
    @test length(subfields(K_14, degree =2)) == 15
    @test length(subfields(K_14, degree =1)) == 1
  end

  # @testset "(C_2^5)" begin      <--- cmpr runtime fact()
  #     @test length(subfields(f_15,32)) == 1
  #     @test length(subfields(f_15,16)) == 31
  #     @test length(subfields(f_15,8)) == 155
  #     @test length(subfields(f_15,4)) == 155
  #     @test length(subfields(f_15,2)) == 31
  #     @test length(subfields(f_15,1)) == 1
  # end
  #Normal few#
  @testset "(Q_8)" begin
    @test length(subfields(K_16)) == 6
    @test length(subfields(K_16, degree =8)) == 1
    @test length(subfields(K_16, degree =4)) == 1
    @test length(subfields(K_16, degree =2)) == 3
    @test length(subfields(K_16, degree =1)) == 1
  end

  @testset "(Q_8)" begin
    @test length(subfields(K_17)) == 6
    @test length(subfields(K_17, degree =8)) == 1
    @test length(subfields(K_17, degree =4)) == 1
    @test length(subfields(K_17, degree =2)) == 3
    @test length(subfields(K_17, degree =1)) == 1
  end

  @testset "(Q_8)" begin
    @test length(subfields(K_18)) == 6
    @test length(subfields(K_18, degree =8)) == 1
    @test length(subfields(K_18, degree =4)) == 1
    @test length(subfields(K_18, degree =2)) == 3
    @test length(subfields(K_18, degree =1)) == 1
  end

  @testset "(Q_8)" begin
    @test length(subfields(K_19)) == 6
    @test length(subfields(K_19, degree =8)) == 1
    @test length(subfields(K_19, degree =4)) == 1
    @test length(subfields(K_19, degree =2)) == 3
    @test length(subfields(K_19, degree =1)) == 1
  end

  @testset "(Q_8)" begin
    @test length(subfields(K_20)) == 6
    @test length(subfields(K_20, degree =8)) == 1
    @test length(subfields(K_20, degree =4)) == 1
    @test length(subfields(K_20, degree =2)) == 3
    @test length(subfields(K_20, degree =1)) == 1
  end

  @testset "(C_16)" begin
    @test length(subfields(K_21)) == 5
    @test length(subfields(K_21, degree =16)) == 1
    @test length(subfields(K_21, degree =8)) == 1
    @test length(subfields(K_21, degree =4)) == 1
    @test length(subfields(K_21, degree =2)) == 1
    @test length(subfields(K_21, degree =1)) == 1
  end

  @testset "(C_32)" begin
    @test length(subfields(K_22)) == 6
    # @test length(subfields(f_22,32)) == 1
    # @test length(subfields(f_22,16)) == 1
    # @test length(subfields(f_22,8)) == 1
    # @test length(subfields(f_22,4)) == 1
    # @test length(subfields(f_22,2)) == 1
    # @test length(subfields(f_22,1)) == 1
  end
  #Non normal many#
  @testset "(C_2^2 x S_3)" begin
    @test length(subfields(K_23)) == 10
    @test length(subfields(K_23, degree =12)) == 1
    @test length(subfields(K_23, degree =6)) == 3
    @test length(subfields(K_23, degree =4)) == 1
    @test length(subfields(K_23, degree =3)) == 1
    @test length(subfields(K_23, degree =2)) == 3
    @test length(subfields(K_23, degree =1)) == 1
  end
  #Non normal few#
  @testset "(S_8)" begin
    @test length(subfields(K_24)) == 2
    @test length(subfields(K_24, degree =8)) == 1
    @test length(subfields(K_24, degree =4)) == 0
    @test length(subfields(K_24, degree =2)) == 0
    @test length(subfields(K_24, degree =1)) == 1
  end

  @testset "(S_8)" begin
    @test length(subfields(K_25)) == 2
    @test length(subfields(K_25, degree =8)) == 1
    @test length(subfields(K_25, degree =4)) == 0
    @test length(subfields(K_25, degree =2)) == 0
    @test length(subfields(K_25, degree =1)) == 1
  end

  @testset "(S_18)" begin
    @test length(subfields(K_26)) == 2
    @test length(subfields(K_26, degree =18)) == 1
    @test length(subfields(K_26, degree =9)) == 0
    @test length(subfields(K_26, degree =6)) == 0
    @test length(subfields(K_26, degree =4)) == 0
    @test length(subfields(K_26, degree =3)) == 0
    @test length(subfields(K_26, degree =2)) == 0
    @test length(subfields(K_26, degree =1)) == 1
  end

  @testset "(18T111)" begin
    @test length(subfields(K_27)) == 6
    @test length(subfields(K_27, degree =18)) == 1
    @test length(subfields(K_27, degree =9)) == 1
    @test length(subfields(K_27, degree =6)) == 1
    @test length(subfields(K_27, degree =3)) == 2
    @test length(subfields(K_27, degree =2)) == 0
    @test length(subfields(K_27, degree =1)) == 1
  end

  @testset "Trivial fields" begin
    f = x - 1
    K, a = number_field(f, "a")
    l = subfields(K)
    @test length(l) == 1
    @test degree(l[1][1]) == 1
    @test is_isomorphic(l[1][1], K)
  end

  @testset "relative fields" begin
    K, a = number_field(x^2 +1, "a")
    Kx, x = K["x"]
    f = x^12 - 34734*x^11 + 401000259*x^10 - 1456627492885*x^9 - 2537142937228035*x^8 + 18762072755679375516*x^7 - 812368636358864062944*x^6 - 70132863629758257512231931*x^5 + 25834472514893102332821062085*x^4 + 76623280610352450247247939584745*x^3 - 45080885015422662132515763499758450*x^2 - 2070499552240812214288316981071818900*x - 550505759097778545485364826246753544;
    L, u = number_field(f)

    @test length(subfields(L)) == 10
    @test length(subfields(L, degree = 6)) == 3
  end

  @testset "Subfields" begin
    Qx,x = polynomial_ring(QQ,"x")
    K,a = number_field(x^3 + x + 1)

    F,phi = Hecke.subfield(K,[one(K)])
    @test degree(F) == 1
    @test parent(phi(one(F))) === K

    F,_ = Hecke.subfield(K,[K(1),K(2),K(3)])
    @test degree(F) == 1

    F,_ = Hecke.subfield(K,[gen(K)])
    @test degree(F) == 3

    F,_ = Hecke.subfield(K,[gen(K), gen(K)+1])
    @test degree(F) == 3

    Qx,x = polynomial_ring(QQ,"x")
    K,a3 = number_field(x^2 - 3)
    Ky,y = polynomial_ring(K,"y")
    L,a5 = number_field(y^2 - 5)

    F,phi = Hecke.subfield(K,[one(K)])
    @test degree(F) == 1
    @test parent(phi(one(F))) === K

    F,_ = Hecke.subfield(K,[gen(K)])
    @test degree(F) == 2

    Labs, psi = absolute_simple_field(L)
    phi = restrict(inv(psi), base_field(L))


    F,_ = Hecke.subfield(Labs,[phi(a3)])
    @test degree(F) == 2

    F,_ = Hecke.subfield(Labs,[preimage(psi,a5)])
    @test degree(F) == 2

    F,_ = Hecke.subfield(Labs,[phi(a3), preimage(psi,a5)])
    @test degree(F) == 4
  end

  Qx, x = QQ["x"]
  K, a = number_field(x^2 + 1)
  L, mL = Hecke.subfield(K, [a//2])
  @test isone(denominator(defining_polynomial(L)))
  @test mL(gen(L))^2 == mL(gen(L)^2)
end
@testset "Subfields" begin
  @testset "Relative_Subfields" begin
    Qx,x = polynomial_ring(QQ,"x")
    k,a = number_field(x^3 + x + 1)
    kt, t = polynomial_ring(k, "t")
    K, b = number_field(t^6+a)

    @test length(subfields(K)) == 4
    @test length(Hecke.principal_subfields(K)) == 4
  end
end

let
  Qx, x = QQ[:x]
  L, a = number_field(x^4 + 6*x^2 + 4, :a)
  LL, b = number_field(x^2 + 1, :b)
  @test_throws ArgumentError Hecke.subfield(L, [b])
end
