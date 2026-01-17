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
    # do a bruteforce enumeration: for a fixed exponent d, enumerate all a_3,a_4,a_6 with a_3 non-zero
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
