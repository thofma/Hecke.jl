@testset "Height functions for elliptic curves" begin
  E1 = EllipticCurve([1, -1, 1, -2063758701246626370773726978, 32838647793306133075103747085833809114881])
  

  P = E1([-30987785091199, 258909576181697016447])
  R = ArbField(100)
  @testset "Naive height" begin
 
    @test contains( R(3106461421344758392571240556046391//100000000000000000000000000000000) , @inferred naive_height(P))

  end

  @testset "Local heights" begin
    @test contains( R(-1888808896037477386833023078582084//1000000000000000000000000000000000) , @inferred local_height(P, 17))
    @test contains( R(-1098612288668109691395245236922525//1000000000000000000000000000000000) , @inferred local_height(P, 3))
  end

  @testset "Real height" begin
     @test contains( R(31812867857980432756826379798033//1000000000000000000000000000000) , @inferred real_height(P))
  end

  @testset "Canonical height" begin
    @test  contains( R(25860317067546190743868840740735//1000000000000000000000000000000) , @inferred canonical_height(P))
  end
  
  E2 = EllipticCurve([0, 0, 1, -7, 6])
  P1 = E2([2, 0])
  P2 = E2([8, 21])
  P3 = E2([-1, 3])

   @testset "Height pairing" begin
    @test contains( R(-3097722999641630284498546777441590//10000000000000000000000000000000000) , @inferred height_pairing(P1, P2))
    @test contains( R(153960406385881011894127857647808//100000000000000000000000000000000) , @inferred regulator([P1, P2]))
    @test contains( R(41714355875838396981711954461809//100000000000000000000000000000000) , @inferred regulator([P1, P2, P3]))
  end


end
