#using Hecke.Random
#using Hecke.RandomExtensions

@testset "Elliptic curves over finite fields" begin

  R1 = GF(23)
  R2, a2 = Native.finite_field(23, 1, "a")
  R3, a3 = Native.finite_field(ZZRingElem(23), 1, "a")
  R4, a4 = Native.finite_field(23, 2, "a")
  R4_, a4_ = finite_field(23, 2, "a")

  E1 = elliptic_curve(R1, [2, 3])
  E2 = elliptic_curve(R2, [2, 3])
  E3 = elliptic_curve(R3, [2, 3])
  E4 = elliptic_curve(R4, [2, 3])
  E4_ = elliptic_curve(R4_, [2, 3])
  E5 = elliptic_curve(R4, [1, 2, 3, 0, 6])

  @testset "Random point construction" begin
    @inferred rand(E1)
    @inferred rand(E2)
    @inferred rand(E3)
    @inferred rand(E4)
    @inferred rand(E4_)
    @inferred rand(E5)

    T = EllipticCurvePoint{elem_type(R1)}
    @test rand(rng, E1) isa T
    @test rand(rng, E1, 3) isa Vector{T}

    @test reproducible(E1)
  end

  @testset "Order computation (Exhaustive_search)" begin
    @test 24 == @inferred Hecke.order_via_exhaustive_search(E1)
  end


  @testset "Order computation (Legendre)" begin
    @test 24 == @inferred Hecke.order_via_legendre(E1)
  end

  @testset "Order computation (BSGS)" begin
    @test 24 in @inferred Hecke.order_via_bsgs(E1)
    @test 24 in @inferred Hecke.order_via_bsgs(E2)
    @test 24 in @inferred Hecke.order_via_bsgs(E3)
    @test 576 in @inferred Hecke.order_via_bsgs(E4)
    @test 576 in @inferred Hecke.order_via_bsgs(E4_)
  end

  @testset "Hasse interval" begin
    l = @inferred hasse_interval(E1)
    @test l[1] <= 24 && 24 <= l[2]
    l = @inferred hasse_interval(E2)
    @test l[1] <= 24 && 24 <= l[2]
    l = @inferred hasse_interval(E3)
    @test l[1] <= 24 && 24 <= l[2]
    l = @inferred hasse_interval(E4)
    @test l[1] <= 576 && 576 <= l[2]
    l = @inferred hasse_interval(E4_)
    @test l[1] <= 576 && 576 <= l[2]

  end

  @testset "Trace of Frobenius" begin
   E = elliptic_curve(GF(7,2), [1, 2, 3, 4, 5])
   @test -13 == @inferred trace_of_frobenius(E)
   @test 71 == @inferred trace_of_frobenius(E,2)
   @test -286 == @inferred trace_of_frobenius(E,3)
   E = elliptic_curve_from_j_invariant(GF(2, 4)(0))
   @test trace_of_frobenius(E, 2) == 32
   @test trace_of_frobenius(E, 3) == 128

   R,x = polynomial_ring(GF(59))
   E = elliptic_curve(x^3+54*x+31,x)
   @test trace_of_frobenius(E) == 15
  end

  @testset "Schoofs algorithm" begin
    @test 24 == @inferred Hecke.order_via_schoof(E1)
    @test 24 == @inferred Hecke.order_via_schoof(E2)
    @test 24 == @inferred Hecke.order_via_schoof(E3)
    @test 576 == @inferred Hecke.order_via_schoof(E4)
    @test 576 == @inferred Hecke.order_via_schoof(E4_)
  end

  @testset "Point counting" begin
    RR = GF(2)
    E = elliptic_curve(RR,[1, 1, 0, 0, 1])
    @test 2 == @inferred order(E)
    RR = GF(3)
    E = elliptic_curve(RR, [1, 1])
    @test 4 == @inferred order(E)

    RR = GF(3,6)
    E = elliptic_curve(RR, [1,2,0,1,1])
    @test 784 == @inferred order(E)

    @test 24 == @inferred order(E1)
    @test 24 == @inferred order(E2)
    @test 24 == @inferred order(E3)
    @test 576 == @inferred order(E4)
    @test 576 == @inferred order(E4_)
  end

  @testset "Point counting for ordinary curves in characteristic 2 (Subfield Curves)" begin
    _, X = polynomial_ring(GF(2), "X")
    R,t = finite_field(X^32 + X^15 + X^9 + X^7 + X^4 + X^3 + 1, "t") # Conway polynomial
    # alpha is a generator of an F_4 subfield
    alpha = t^30 + t^29 + t^24 + t^21 + t^20 + t^19 + t^18 + t^17 + t^14 + t^9 + t^8 + t^6 + t^5 + t^4 + t^3 + t+ 1
    E = elliptic_curve(R, [1,0,0,0,alpha])
    @test 4295048640 == @inferred Hecke._order_ordinary_char2(E)

    E = elliptic_curve(GF(2, 50), [1,0,0,0,1])
    @test 1125899954494568 == @inferred Hecke._order_ordinary_char2(E)

    E = elliptic_curve(GF(2, 100), [1,0,0,0,1])
    @test ZZ("1267650600228229382588845215376") == @inferred Hecke._order_ordinary_char2(E)

    E = elliptic_curve(GF(2, 150), [1,0,0,0,1])
    @test ZZ("1427247692705959881058233219127481757976150136") == @inferred Hecke._order_ordinary_char2(E)

    E = elliptic_curve(GF(2, 200), [1,0,0,0,1])
    @test ZZ("1606938044258990275541962092343697546215565682541130425732128") == @inferred Hecke._order_ordinary_char2(E)

    # test the coordinates transform
    # y^2 + xy + t*y = x^3 + t^2*x^2 + t^2*x + t, where t is the generator for F_16
    # j-invariant is 1
    R, t = finite_field(2, 4)
    E = elliptic_curve(R, [1, t^2, t, t^2, t])
    @test 16 == @inferred Hecke._order_ordinary_char2(E)
  end

  @testset "AGM in characteristic 2 (Large Exponent)" begin
    function test_agm_subfield(d, N)
      RB,x = finite_field(2, d, "X")
      q = 2^d

      t_1 = Hecke._trace_of_frobenius_char2_agm(x)
      t_prev = 2; t_cur = t_1
      for n in 2:N
        t_cur, t_prev = t_1*t_cur - q*t_prev, t_cur

        R,_ = finite_field(2, d*n, "Y")
        z = embed(RB, R)(x)
        t = Hecke._trace_of_frobenius_char2_agm(z)

        if t != t_cur
          println("Wrong frobenius trace for $z over $R ($x over $RB)")
          return false
        end
      end

      return true
    end

    # check the comment in _trace_of_frobenius_char2_agm
    # we cannot go past the exponent 92 currently
    @test test_agm_subfield(3, 30)
    @test test_agm_subfield(4, 20)
    @test test_agm_subfield(5, 15)
  end

  @testset "AGM in characteristic 2 (Exhaustive d=3..6)" begin
    # do a brute-force enumeration: for a fixed exponent d, enumerate all (non-zero) a_6
    # compare _trace_of_frobenius_char2_agm to the trace computed from order_via_exhaustive_search
    # note that the order_via_exhaustive_search is pretty slow, so we limit ourselves in the range of d
    function test_agm_exhaustive(max_degree)::Bool
      for d in 3:max_degree
        R = GF(2, d, "t")
        q = order(R)
        for a6 in R
          a6^4 == a6 && continue
          E = elliptic_curve(R, [1,0,0,0,a6])
          if q + 1 - Hecke._trace_of_frobenius_char2_agm(a6) != Hecke.order_via_exhaustive_search(E)
            println("Wrong point count for ordinary curve $E over $R")
            return false
          end
        end
      end
      return true
    end

    @test test_agm_exhaustive(6)
  end

  @testset "Point counting for ordinary curves in characteristic 2 (Exhaustive d=1..6)" begin
    # do a brute-force enumeration: for a fixed exponent d, enumerate all a_2 and non-zero a_6
    # compare _order_ordinary_char2 to order_via_exhaustive_search
    # note that the order_via_exhaustive_search is pretty slow, so we need to limit ourselves in the range of d
    function test_ordinary_exhaustive(max_degree)::Bool
      for d in 1:max_degree
        R = GF(2, d, "t")
        for a6 in R
          iszero(a6) && continue
          for a2 in R
            E = elliptic_curve(R, [1,a2,0,0,a6])
            if Hecke._order_ordinary_char2(E) != Hecke.order_via_exhaustive_search(E)
              println("Wrong point count for ordinary curve $E over $R")
              return false
            end
          end
        end
      end
      return true
    end

    @test test_ordinary_exhaustive(6)
  end

  @testset "Point counting for supersingular curves in characteristic 2" begin
    function _order_of(K::Field, a3, a4, a6)::ZZRingElem
      return Hecke._order_supersingular_char2(elliptic_curve(elem_type(K)[K(0),K(0),K(a3),K(a4),K(a6)]))
    end

    # the representatives of isomorphism classes taken from Menezes
    # we make sure we exercise all the choices made computing the number of points
    R1 = GF(2, 1)
    @test 3 == @inferred _order_of(R1, 1,0,0) # d = 1, y^2 + y = x^3
    @test 5 == @inferred _order_of(R1, 1,1,0) # d = 1, y^2 + y = x^3 + x
    @test 1 == @inferred _order_of(R1, 1,1,1) # d = 1, y^2 + y = x^3 + x + 1

    R3 = GF(2, 3)
    @test 9 == @inferred _order_of(R3, 1,0,0)  # d = 3, y^2 + y = x^3
    @test 5 == @inferred _order_of(R3, 1,1,0)  # d = 3, y^2 + y = x^3 + x
    @test 13 == @inferred _order_of(R3, 1,1,1) # d = 3, y^2 + y = x^3 + x + 1

    R5 = GF(2, 5)
    @test 33 == @inferred _order_of(R5, 1,0,0)  # d = 5, y^2 + y = x^3
    @test 25 == @inferred _order_of(R5, 1,1,0)  # d = 5, y^2 + y = x^3 + x
    @test 41 == @inferred _order_of(R5, 1,1,1)  # d = 5, y^2 + y = x^3 + x + 1

    R7 = GF(2, 7)
    @test 129 == @inferred _order_of(R7, 1,0,0)  # d = 7, y^2 + y = x^3
    @test 145 == @inferred _order_of(R7, 1,1,0)  # d = 7, y^2 + y = x^3 + x
    @test 113 == @inferred _order_of(R7, 1,1,1)  # d = 7, y^2 + y = x^3 + x + 1

    R2, c1_R2 = finite_field(2, 2, "x"); c2_R2 = c1_R2 + one(R2)
    @test 3 == @inferred _order_of(R2, c1_R2,0,0) # d = 2, y^2 + c_1*y = x^3
    @test 7 == @inferred _order_of(R2, c1_R2,0,1) # d = 2, y^2 + c_1*y = x^3 + 1
    @test 3 == @inferred _order_of(R2, c2_R2,0,0) # d = 2, y^2 + c_2*y = x^3
    @test 7 == @inferred _order_of(R2, c2_R2,0,1) # d = 2, y^2 + c_2*y = x^3 + 1
    @test 5 == @inferred _order_of(R2, 1,1,0)     # d = 2, y^2 + y = x^3 + x
    @test 9 == @inferred _order_of(R2, 1,0,0)     # d = 2, y^2 + y = x^3
    @test 1 == @inferred _order_of(R2, 1,0,c1_R2) # d = 2, y^2 + y = x^3 + c_1

    R4, c1_R4 = finite_field(2, 4, "x"); c2_R4 = c1_R4 + one(R4);
    @test 21 == @inferred _order_of(R4, c1_R4,0,0) # d = 4, y^2 + c_1*y = x^3
    @test 13 == @inferred _order_of(R4, c1_R4,0,1) # d = 4, y^2 + c_1*y = x^3 + 1
    @test 21 == @inferred _order_of(R4, c2_R4,0,0) # d = 4, y^2 + c_2*y = x^3
    @test 13 == @inferred _order_of(R4, c2_R4,0,1) # d = 4, y^2 + c_2*y = x^3 + 1
    @test 9  == @inferred _order_of(R4, 1,0,0)     # d = 4, y^2 + y = x^3
    # d = 4, y^2 + y = x^3 + omega, with tr(omega) = 1. Take omega = c1^3
    @test 25 == @inferred _order_of(R4, 1,0,c1_R4^3)

    # test the coordinate transform when a_2 != 0
    E1 = elliptic_curve(R1, [0,1,1,0,0]) # y^2 + y = x^3 + x^2
    @test @inferred Hecke._order_supersingular_char2(E1) == @inferred Hecke.order_via_exhaustive_search(E1)
    E2 = elliptic_curve(R2, [0,1,1,0,0]) # y^2 + y = x^3 + x^2
    @test @inferred Hecke._order_supersingular_char2(E2) == @inferred Hecke.order_via_exhaustive_search(E2)
    E3 = elliptic_curve(R3, [0,1,1,1,0]) # y^2 + y = x^3 + x^2 + x
    @test @inferred Hecke._order_supersingular_char2(E3) == @inferred Hecke.order_via_exhaustive_search(E3)
    E4 = elliptic_curve(R5, [0,1,1,1,1]) # y^2 + y = x^3 + x^2 + x + 1
    @test @inferred Hecke._order_supersingular_char2(E4) == @inferred Hecke.order_via_exhaustive_search(E4)
  end

  @testset "Point counting for supersingular curves in characteristic 2 (Exhaustive d=1..4)" begin
    # do a brute-force enumeration: for a fixed exponent d, enumerate all a_3,a_4,a_6 with a_3 non-zero
    # compare _order_supersingular_char2 to order_via_exhaustive_search
    # note that the order_via_exhaustive_search is pretty slow, so we need to limit ourselves in the range of d
    function test_supersingular_exhaustive(max_degree)::Bool
      for d in 1:max_degree
        R = GF(2, d, "t")
        for a3 in R
          if iszero(a3) continue end

          for (a4, a6) in Iterators.product(R, R)
            E = elliptic_curve(R, [0,0,a3,a4,a6])
            if Hecke._order_supersingular_char2(E) != Hecke.order_via_exhaustive_search(E)
              println("Wrong point count for supersingular curve $E over $R")
              return false
            end
          end
        end
      end
      return true
    end

    @test test_supersingular_exhaustive(4)
  end

  @testset "Point counting for ordinary curves in characteristic 3 (Subfield Curves)" begin
    _, X = polynomial_ring(GF(3), "X")
    R,t = finite_field(X^32 + 2*X^12 + 2*X^11 + 2*X^6 + X^5 + 2*X^4 + X^3 + X + 2 , "t") # Conway polynomial
    # alpha is a generator of an F_9 subfield
    alpha = t^31 + t^29 + t^28 + t^27 + t^26 + 2*t^23 + t^22 + t^21 + 2*t^20 + 2*t^19 + 2*t^17 + t^16 + t^14 + 2*t^11 + t^10 + t^8 + t^7 + t^6 + t^5 + 2*t^4 + t^2 + t
    E = elliptic_curve(R, [0,-1,0,0,R(1)/alpha])
    @test ZZ("1853020134712320") == @inferred Hecke._order_ordinary_char3(E)

    E = elliptic_curve(GF(3, 50), [0,-1,0,0,1])
    @test ZZ("717897987691032781755375") == @inferred Hecke._order_ordinary_char3(E)

    E = elliptic_curve(GF(3, 50), [0,-1,0,0,-1])
    @test ZZ("717897987693209835025932") == @inferred Hecke._order_ordinary_char3(E)

    # test the coordinates transform
    # y^2 + 2*t*xy + 2*t*y = x^3 + (2*t^2+1)*x^2 + (t^2+2t)*x + (t^3+2), where t is the generator for F_81
    # j-invariant is 1
    R, t = finite_field(3, 4)
    E = elliptic_curve(R, [2*t, 2*t^2+1 ,2*t, t^2+2*t, t^3+2])
    @test 75 == @inferred Hecke._order_ordinary_char3(E)
  end

  @testset "AGM in characteristic 3 (Large Exponent)" begin
    function test_agm_subfield(d, N)
      RB,x = finite_field(3, d, "X")
      q = 3^d

      t_1 = Hecke._trace_of_frobenius_char3_agm(x)
      t_prev = 2; t_cur = t_1
      for n in 2:N
        t_cur, t_prev = t_1*t_cur - q*t_prev, t_cur

        R,_ = finite_field(3, d*n, "Y")
        z = embed(RB, R)(x)
        t = Hecke._trace_of_frobenius_char3_agm(z)

        if t != t_cur
          println("Wrong frobenius trace for $z over $R ($x over $RB)")
          return false
        end
      end

      return true
    end

    # check the comment in _trace_of_frobenius_char3_agm
    # we cannot go past the exponent 58 currently
    @test test_agm_subfield(3, 18)
    @test test_agm_subfield(4, 12)
    @test test_agm_subfield(5, 10)
  end

  @testset "AGM in characteristic 3 (Exhaustive d=3..6)" begin
    # do a brute-force enumeration: for a fixed exponent d, enumerate all (non-zero) a_6
    # compare _trace_of_frobenius_char3_agm to the trace computed from order_via_exhaustive_search
    # note that the order_via_exhaustive_search is pretty slow, so we limit ourselves in the range of d
    function test_agm_exhaustive(max_degree)::Bool
      for d in 3:max_degree
        R = GF(3, d, "t")
        q = order(R)
        for a6 in R
          a6^9 == a6 && continue
          E = elliptic_curve(R, [0,1,0,0,a6])
          if q + 1 - Hecke._trace_of_frobenius_char3_agm(-inv(a6)) != Hecke.order_via_exhaustive_search(E)
            println("Wrong point count for ordinary curve $E over $R")
            return false
          end
        end
      end
      return true
    end

    @test test_agm_exhaustive(6)
  end

  @testset "Point counting for supersingular curves in characteristic 3" begin
    function _order_of(K::Field, a4, a6)::ZZRingElem
      return Hecke._order_supersingular_char3(elliptic_curve(elem_type(K)[K(0),K(0),K(0),K(a4),K(a6)]))
    end

    # the representatives of all isogeny classes with small d

    R2, t = finite_field(3, 2)  # d = 2 mod 4
    # y^2 = x^3 - x + 1     | 1 fourth power: gamma = 1, Tr(1) = -1   | q + 1 - sqrt(q)
    @test 7 == @inferred _order_of(R2, -1, 1)
    # y^2 = x^3 - x         | 1 fourth power: gamma = 1, Tr(0) = 0    | q + 1 + 2*sqrt(q)
    @test 16 == @inferred _order_of(R2, -1, 0)
    # y^2 = x^3 - t^2*x + 1 | t^2 square: gamma = t, Tr(t^(-3)) = -1  | q + 1 + sqrt(q)
    @test 13 == @inferred _order_of(R2, -t^2, 1)
    # y^2 = x^3 - t^2*x     | t^2 square: gamma = t, Tr(0) = 0        | q + 1 - 2*sqrt(q)
    @test 4 == @inferred _order_of(R2, -t^2, 0)
    # y^2 = x^3 - t*x       | t not a square                          | q + 1
    @test 10 == @inferred _order_of(R2, -t, 0)

    R3, t = finite_field(3, 3)  # d = 3 mod 4
    # y^2 = x^3 - x         | 1 fourth power: gamma = 1, Tr(0) = 0    | q + 1
    @test 28 == @inferred _order_of(R3, -1, 0)
    # y^2 = x^3 - x - t^2   | 1 fourth power: gamma = 1, Tr(-t^2) = 1 | q + 1 - sqrt(3*q)
    @test 19 == @inferred _order_of(R3, -1, -t^2)
    # y^2 = x^3 - x + t^2   | 1 fourth power: gamma = 1, Tr(t^2) = -1 | q + 1 + sqrt(3*q)
    @test 37 == @inferred _order_of(R3, -1, t^2)
    # y^2 = x^3 - t*x       | t not a square                          | q + 1
    @test 28 == @inferred _order_of(R3, -t, 0)

    R4, t = finite_field(3, 4) # d = 0 mod 4
    # y^2 = x^3 - x + 1     | 1 fourth power: gamma = 1, Tr(1) = 1    | q + 1 + sqrt(q)
    @test 91 == @inferred _order_of(R4, -1, 1)
    # y^2 = x^3 - x         | 1 fourth power: gamma = 1, Tr(0) = 0    | q + 1 - 2*sqrt(q)
    @test 64 == @inferred _order_of(R4, -1, 0)
    # y^2 = x^3 - t^2*x + t^4 | t^2 square: gamma = t, Tr(t) = 1      | q + 1 - sqrt(q)
    @test 73 == @inferred _order_of(R4, -t^2, t^4)
    # y^2 = x^3 - t^2*x     | t^2 square: gamma = t, Tr(0) = 0        | q + 1 + 2*sqrt(q)
    @test 100 == @inferred _order_of(R4, -t^2, 0)
    # y^2 = x^3 - t*x       | t not a square                          | q + 1
    @test 82 == @inferred _order_of(R4, -t, 0)

    R5, t = finite_field(3, 5)  # d = 1 mod 4
    # y^2 = x^3 - x         | 1 fourth power: gamma = 1, Tr(0) = 0    | q + 1
    @test 244 == @inferred _order_of(R5, -1, 0)
    # y^2 = x^3 - x - 1     | 1 fourth power: gamma = 1, Tr(-1) = 1   | q + 1 + sqrt(3*q)
    @test 271 == @inferred _order_of(R5, -1, -1)
    # y^2 = x^3 - x + 1     | 1 fourth power: gamma = 1, Tr(1) = -1   | q + 1 - sqrt(3*q)
    @test 217 == @inferred _order_of(R5, -1, 1)
    # y^2 = x^3 - t*x       | t not a square                          | q + 1
    @test 244 == @inferred _order_of(R5, -t, 0)

    # test the coordinates transform
    # y^2 + xy = x^3 - x^2 + x + 1
    E1 = elliptic_curve(R2, [1,-1,0,1,1])
    @test @inferred Hecke._order_supersingular_char3(E1) == @inferred Hecke.order_via_exhaustive_search(E1)
    E2 = elliptic_curve(R3, [1,-1,0,1,1])
    @test @inferred Hecke._order_supersingular_char3(E2) == @inferred Hecke.order_via_exhaustive_search(E2)
    E3 = elliptic_curve(R4, [1,-1,0,1,1])
    @test @inferred Hecke._order_supersingular_char3(E3) == @inferred Hecke.order_via_exhaustive_search(E3)
    E4 = elliptic_curve(R5, [1,-1,0,1,1])
    @test @inferred Hecke._order_supersingular_char3(E4) == @inferred Hecke.order_via_exhaustive_search(E4)
  end

  @testset "Point counting for supersingular curves in characteristic 3 (Exhaustive d=1..4)" begin
    # do a brute-force enumeration: for a fixed exponent d, enumerate all a_4,a_6 with a_4 non-zero
    # compare _order_supersingular_char3 to order_via_exhaustive_search
    # note that the order_via_exhaustive_search is pretty slow, so we need to limit ourselves in the range of d
    function test_supersingular_exhaustive(max_degree)::Bool
      for d in 1:max_degree
        R = GF(3, d, "t")
        for a4 in R
          iszero(a4) && continue

          for a6 in R
            E = elliptic_curve(R, [0,0,0,a4,a6])
            if Hecke._order_supersingular_char3(E) != Hecke.order_via_exhaustive_search(E)
              println("Wrong point count for supersingular curve $E over $R")
              return false
            end
          end
        end
      end
      return true
    end

    @test test_supersingular_exhaustive(4)
  end

  @testset "Supersingular" begin
    g = @inferred supersingular_polynomial(2)
    R = parent(g)
    J = gen(R)
    g == J

    g = @inferred supersingular_polynomial(193)
    R = parent(g)
    J = gen(R)
    f = J^16 + 60*J^15 + 22*J^14 + 101*J^13 + 126*J^12 + 173*J^11 + 72*J^10 + 49*J^9 + 132*J^8 + 44*J^7 + 124*J^6 + 141*J^5 + 108*J^4 + 15*J^3 + 26*J^2 + 48*J + 23
    @test g == f

    for K in [GF(193), GF(ZZ(193)), GF(193, 1),
              GF(193, 1), GF(ZZ(193), 1), GF(193, 4), GF(ZZ(193), 3),
              GF(193, 3), GF(ZZ(193), 3)]

      E = elliptic_curve_from_j_invariant(K(169))
      @test @inferred is_supersingular(E) == true
      @inferred is_probable_supersingular(E)

      E = elliptic_curve_from_j_invariant(K(170))
      @test @inferred is_ordinary(E) == true
    end

    K = GF(193, 3)
    a = gen(K)
    E = elliptic_curve_from_j_invariant(a)
    @test @inferred is_supersingular(E) == false
    @inferred is_probable_supersingular(E)
  end

  @testset "Order of points" begin
    K = GF(103)
    E = elliptic_curve(K, [1, 18])
    P = E([33, 91])
    @test order(P) == 19
    @test Hecke._order_elem_via_fac(P) == 19
    P = E([38, 82])
    @test order(P) == 114
    @test Hecke._order_elem_via_fac(P) == 114
  end

  @testset "Abelian group structure and disc log" begin
    E = elliptic_curve(GF(11), [2, 5])
    A, = abelian_group(E)
    @test elementary_divisors(A) == [10]
    P = rand(E)
    Q = rand(1:10) * P
    m = disc_log(P, Q)
    @test m * P == Q

    E = elliptic_curve(GF(41), [2, 5])
    A, = abelian_group(E)
    @test elementary_divisors(A) == [2, 22]
    P = rand(E)
    Q = rand(1:22) * P
    m = disc_log(P, Q)
    @test m * P == Q

    # trivial group
    E = elliptic_curve(GF(2), [0, 0, 1, 1, 1])
    A, = abelian_group(E)
    @test elementary_divisors(A) == []
    P = rand(E)
    Q = rand(E)
    m = disc_log(P, Q)
    @test m * P == Q

    F = GF(3)
    Fx, x = F["x"]
    f = x^6 + 2*x^4 + x^2 + 2*x + 2
    F, a = finite_field(f)
    E = elliptic_curve([a^4 + a^3 + 2*a^2 + 2*a, 2*a^5 + 2*a^3 + 2*a^2 + 1])
    A, = abelian_group(E)
    @test elementary_divisors(A) == [26, 26]
    P = rand(E)
    Q = rand(1:26) * P
    m = disc_log(P, Q)
    @test m * P == Q

    F = GF(101)
    Fx, x = F["x"]
    f = x^3 + 3*x + 99
    F, a = finite_field(f)
    E = elliptic_curve([2*a^2 + 48*a + 27, 89*a^2 + 76*a + 24])
    A, = abelian_group(E)
    @test elementary_divisors(A) == [1031352]
    P = rand(E)
    Q = rand(1:1031352) * P
    m = disc_log(P, Q)
    @test m * P == Q
  end
end
