function test_EllCrv_Finite()
  println("test_EllCrv_Finite() ... ")

  R1 = ResidueRing(FlintZZ, 23)
  R2, a2 = FlintFiniteField(23, 1, "a")
  R3, a3 = FlintFiniteField(fmpz(23), 1, "a")
  R4, a4 = FlintFiniteField(23, 2, "a")

  E1 = EllipticCurve(map(R1, [2, 3]))
  E2 = EllipticCurve(map(R2, [2, 3]))
  E3 = EllipticCurve(map(R3, [2, 3]))
  E4 = EllipticCurve(map(R4, [2, 3]))

  print(" Random point ... ")
    @inferred rand(E1)
    @inferred rand(E2)
    @inferred rand(E3)
    @inferred rand(E4)
  println("done")

  print("  Order via Legendre ... ")
    @test 24 == @inferred order_via_legendre(E1)
  println("done")

  print("  Order via BSGS ... ")
    @test 24 in @inferred order_via_bsgs(E1)
    @test 24 in @inferred order_via_bsgs(E2)
    @test 24 in @inferred order_via_bsgs(E3)
    @test 576 in @inferred order_via_bsgs(E4)
  println("done")

  print("  Hasse interval ... ")
    l = @inferred hasse_interval(E1)
    @test l[1] <= 24 && 24 <= l[2]
    l = @inferred hasse_interval(E2)
    @test l[1] <= 24 && 24 <= l[2]
    l = @inferred hasse_interval(E3)
    @test l[1] <= 24 && 24 <= l[2]
    l = @inferred hasse_interval(E4)
    @test l[1] <= 576 && 576 <= l[2]
  println("DONE")

  print("  Schoof's algorithm ... ")
    @test 24 == @inferred order_via_schoof(E1)
    @test 24 == @inferred order_via_schoof(E2)
    @test 24 == @inferred order_via_schoof(E3)
    @test 576 == @inferred order_via_schoof(E4)
  println("DONE")

  print("  Point counting ... ")
    RR = ResidueRing(ZZ, 2)
    E = EllipticCurve([RR(1), RR(1), RR(0), RR(0), RR(1)])
    @test 2 == @inferred order(E)
    RR = ResidueRing(ZZ, 3)
    E = EllipticCurve([RR(1), RR(1)])
    @test 4 == @inferred order(E)

    @test 24 == @inferred order(E1)
    @test 24 == @inferred order(E2)
    @test 24 == @inferred order(E3)
    @test 576 == @inferred order(E4)
  println("DONE")

	println("done")
end
