@testset "Height functions for elliptic curves" begin
  E = EllipticCurve([1, -1, 1, -2063758701246626370773726978, 32838647793306133075103747085833809114881])


  P = E([-30987785091199, 258909576181697016447])
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


end
