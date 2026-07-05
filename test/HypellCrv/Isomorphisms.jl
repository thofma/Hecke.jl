@testset "Isomorphisms of hyperelliptic curves" begin

  Qx, x = polynomial_ring(QQ, "x")

  @testset "transform_polynomial" begin
    # x^4 + 1 under [1,1,0,1] (x -> x+1) should give (x+1)^4 + 1
    f = x^4 + 1
    g = Hecke._transform_polynomial(f, 4, QQFieldElem[1, 1, 0, 1])
    @test g == (x + 1)^4 + 1

    # Under [0,1,1,0] (x -> 1/x) of degree 4: x^4 * f(1/x) = 1 + x^4
    g2 = Hecke._transform_polynomial(f, 4, QQFieldElem[0, 1, 1, 0])
    @test g2 == x^4 + 1
  end

  @testset "is_isomorphic: same curve" begin
    f = x^6 + 3*x^4 - 2*x^3 + x^2 - 5
    C = hyperelliptic_curve(f)
    fl, m = is_isomorphic_with_isomorphism(C, C)
    @test fl
    @test domain(m) == C
    @test codomain(m) == C
  end

  @testset "is_isomorphic: isomorphic genus-2 curves over QQ" begin
    # C2: apply x -> x+1 to C1, which gives an isomorphic curve
    f1 = x^6 - x^4 + 2*x^2 - 1
    C1 = hyperelliptic_curve(f1)
    # Manually compute the twist: f2(x) = f1(x-1) (shift x -> x-1, so x -> x+1 is the isom)
    f2 = evaluate(f1, x - 1)
    lc = leading_coefficient(f2)
    f2 = f2 * inv(QQ(lc))
    C2 = hyperelliptic_curve(f2)
    fl, m = is_isomorphic_with_isomorphism(C1, C2)
    @test fl
    @test domain(m) == C1
    @test codomain(m) == C2
  end

  @testset "is_isomorphic: non-isomorphic genus-2 curves over QQ" begin
    f1 = x^6 + x + 1
    f2 = x^6 + 3*x^2 + 7
    C1 = hyperelliptic_curve(f1)
    C2 = hyperelliptic_curve(f2)
    fl = is_isomorphic(C1, C2)
    @test !fl
  end

  @testset "is_isomorphic: different genus" begin
    f1 = x^6 + x + 1
    f2 = x^8 + x + 1
    C1 = hyperelliptic_curve(f1)
    C2 = hyperelliptic_curve(f2)
    fl = is_isomorphic(C1, C2)
    @test !fl
  end

  @testset "is_isomorphic: over QQ with irreducible cubic factors (d=3 path)" begin
    # f1 = (x^3 - 2) * (x^3 + 3x + 1) — two irreducible cubics over QQ
    f1 = (x^3 - 2) * (x^3 + 3*x + 1)
    C1 = hyperelliptic_curve(f1)
    # C2: apply the transformation x -> x+1 (GL2 matrix [1,1,0,1])
    f2 = evaluate(f1, x + 1)
    C2 = hyperelliptic_curve(f2)
    fl, m = is_isomorphic_with_isomorphism(C1, C2)
    @test fl
    @test domain(m) == C1
    @test codomain(m) == C2
  end

  @testset "is_isomorphic: over a number field" begin
    K, a = number_field(x^2 - 2, "a")
    Kx, t = polynomial_ring(K, "t")
    # f1 over K: monic degree-6 with two irreducible cubic factors over K
    f1 = (t^3 - a) * (t^3 + 3*t + 1)
    C1 = hyperelliptic_curve(f1)
    # Isomorphic via t -> t+1
    f2 = evaluate(f1, t + 1)
    C2 = hyperelliptic_curve(f2)
    fl, m = is_isomorphic_with_isomorphism(C1, C2)
    @test fl
    @test domain(m) == C1
    @test codomain(m) == C2
  end

  @testset "is_isomorphic: isomorphic genus-2 over GF(7), rational roots (d=1 path)" begin
    F = GF(7)
    Fx, t = polynomial_ring(F, "t")
    # f1 with six distinct rational roots over GF(7): (t-1)(t-2)(t-3)(t-4)(t-5)(t-6)
    f1 = prod(t - F(i) for i in 1:6)
    C1 = hyperelliptic_curve(f1)
    # Isomorphic via t -> t+1 (shifts all roots by 1 mod 7)
    f2 = evaluate(f1, t + 1)
    C2 = hyperelliptic_curve(f2)
    fl, m = is_isomorphic_with_isomorphism(C1, C2)
    @test fl
    @test domain(m) == C1
    @test codomain(m) == C2
  end

  @testset "is_isomorphic: isomorphic genus-2 over GF(7), irreducible cubic factors (d=3 path)" begin
    F = GF(7)
    Fx, t = polynomial_ring(F, "t")
    # t^3 + 2t + 1 and t^3 - 3 are both irreducible over GF(7)
    # (neither 2 nor 3 is a cube mod 7, so t^3-2, t^3-3 are irreducible;
    #  t^3+2t+1 has no root in GF(7) and is not a product of two factors)
    f_irred = t^3 + 2*t + 1   # irreducible over GF(7)
    g_irred = t^3 - 3         # irreducible over GF(7): 3^((7-1)/3) = 9 = 2 ≠ 1 mod 7
    f1 = f_irred * g_irred
    C1 = hyperelliptic_curve(f1)
    # Isomorphic via t -> t+1
    f2 = evaluate(f1, t + 1)
    lc = leading_coefficient(f2)
    f2 = f2 * inv(lc)
    C2 = hyperelliptic_curve(f2)
    fl, m = is_isomorphic_with_isomorphism(C1, C2)
    @test fl
    @test domain(m) == C1
    @test codomain(m) == C2
  end

  @testset "is_isomorphic: non-isomorphic genus-2 over GF(7)" begin
    F = GF(7)
    Fx, t = polynomial_ring(F, "t")
    f1 = t^6 + t + 1
    f2 = t^6 + 3*t^2 + 2
    C1 = hyperelliptic_curve(f1)
    C2 = hyperelliptic_curve(f2)
    fl = is_isomorphic(C1, C2)
    @test !fl
  end

  @testset "is_isomorphic: isomorphic genus-2 over GF(3^2), irreducible cubic (d=3 path)" begin
    F, _ = finite_field(3, 2, "u")
    Fx, t = polynomial_ring(F, "t")
    # x^3 + x + 1 is irreducible over GF(3), and over GF(3^2) — check needed
    # Use two irreducible degree-3 factors over GF(9)
    # GF(9) = GF(3)[u]/(u^2+1); use t^3 - u and t^3 + t + 2 (irreducible over GF(9))
    f1 = (t^3 + t + 2) * (t^3 + 2*t + 2)
    # Only proceed if both factors are irreducible
    fac = collect(factor(f1))
    if all(degree(p) == 3 for (p, _) in fac) && length(fac) == 2
      C1 = hyperelliptic_curve(f1)
      f2 = evaluate(f1, t + 1)
      lc = leading_coefficient(f2)
      f2 = f2 * inv(lc)
      C2 = hyperelliptic_curve(f2)
      fl, m = is_isomorphic_with_isomorphism(C1, C2)
      @test fl
      @test domain(m) == C1
      @test codomain(m) == C2
    end
  end

  @testset "is_isomorphic: non-isomorphic genus-2 over GF(3^2)" begin
    F, _ = finite_field(3, 2, "u")
    Fx, t = polynomial_ring(F, "t")
    f1 = t^6 + t + 1
    f2 = t^6 + 2*t^2 + 2
    C1 = hyperelliptic_curve(f1)
    C2 = hyperelliptic_curve(f2)
    fl = is_isomorphic(C1, C2)
    @test !fl
  end

  @testset "isomorphism_data, apply to finite point, inv, compose" begin
    F = GF(7)
    Fx, t = polynomial_ring(F, "t")
    f1 = prod(t - F(i) for i in 1:6)
    C1 = hyperelliptic_curve(f1)
    f2 = evaluate(f1, t + 1)
    C2 = hyperelliptic_curve(f2)
    fl, m = is_isomorphic_with_isomorphism(C1, C2)
    @test fl

    # isomorphism_data accessor
    a, b, c, d, u, v = isomorphism_data(m)
    @test a * d - b * c != F(0)
    @test iszero(v)

    # apply to finite point: f1(1) = 0, so (1, 0) is on C1
    P = C1([F(1), F(0)])
    Q = m(P)
    @test parent(Q) == C2

    # applying to a point on the wrong curve should throw
    @test_throws ArgumentError m(Q)

    # inv
    m_inv = inv(m)
    @test domain(m_inv) == C2
    @test codomain(m_inv) == C1

    # compose: m then m_inv = identity on C1
    m_id = compose(m, m_inv)
    @test domain(m_id) == C1
    @test codomain(m_id) == C1
    @test m_id(P) == P
  end

  @testset "apply isomorphism to point at infinity (c=0 branch)" begin
    F = GF(7)
    Fx, t = polynomial_ring(F, "t")
    f = prod(t - F(i) for i in 1:6)
    C = hyperelliptic_curve(f)
    # Manually construct identity isomorphism so c=0 is guaranteed
    m_ident = Hecke.HypellCrvIsom{FqFieldElem}(C, C, F(1), F(0), F(0), F(1), F(1), zero(Fx))
    P_inf = C([F(1), F(1), F(0)]; check = false)
    @test is_infinite(P_inf)
    Q_inf = m_ident(P_inf)
    @test is_infinite(Q_inf)
    @test Q_inf[2] == F(1) * P_inf[2]  # u * P[2]
  end

  @testset "@req and error handling" begin
    F = GF(7)
    Fx, t = polynomial_ring(F, "t")
    f = prod(t - F(i) for i in 1:6)
    C = hyperelliptic_curve(f)

    # HypellCrvIsom constructor: singular matrix should throw
    @test_throws ArgumentError Hecke.HypellCrvIsom{FqFieldElem}(
      C, C, F(1), F(0), F(0), F(0), F(1), zero(Fx))

    # inv with non-zero v should throw
    m_v = Hecke.HypellCrvIsom{FqFieldElem}(C, C, F(1), F(0), F(0), F(1), F(1), t)
    @test_throws ArgumentError inv(m_v)

    # compose with non-zero v should throw
    @test_throws ArgumentError compose(m_v, m_v)

    # _adjoin_root with unsupported field type should error
    Zx, z = polynomial_ring(ZZ, "z")
    @test_throws ErrorException Hecke._adjoin_root(ZZ, z^2 + 1)

    # _coords with unsupported field type should error
    @test_throws ErrorException Hecke._coords(ZZ(1), ZZ, ZZ)

    # is_isomorphic in characteristic 2 should throw
    F2 = GF(2)
    F2x, t2 = polynomial_ring(F2, "t")
    f_g1 = t2^3 + t2 + 1  # genus 1
    C_g1 = hyperelliptic_curve(f_g1)
    @test_throws ArgumentError is_isomorphic(C_g1, C_g1)

    # is_gl2_equivalent with n < 4 should throw
    Qx, x = polynomial_ring(QQ, "x")
    @test_throws ArgumentError Hecke.is_gl2_equivalent(x^2 + 1, x^2 + 1, 3)
  end

  @testset "d == 2, d1 == 2 path (three irreducible quadratics over QQ)" begin
    Qx, x = polynomial_ring(QQ, "x")
    f1 = (x^2 + 1) * (x^2 + 2) * (x^2 + 3)
    C1 = hyperelliptic_curve(f1)
    f2 = evaluate(f1, x + 1)
    C2 = hyperelliptic_curve(f2)
    fl, m = is_isomorphic_with_isomorphism(C1, C2)
    @test fl
    @test domain(m) == C1
    @test codomain(m) == C2
  end

  @testset "d == 2, d1 == 1 path over QQ (one irred quad + linears)" begin
    Qx, x = polynomial_ring(QQ, "x")
    f1 = (x^2 + 1) * (x - 1) * (x - 2) * (x - 3) * (x - 4)
    C1 = hyperelliptic_curve(f1)
    f2 = evaluate(f1, x + 1)
    C2 = hyperelliptic_curve(f2)
    fl, m = is_isomorphic_with_isomorphism(C1, C2)
    @test fl
    @test domain(m) == C1
    @test codomain(m) == C2
  end

  @testset "flip path: both curves have odd-degree f (genus 2)" begin
    Qx, x = polynomial_ring(QQ, "x")
    # degree-5 f with no root at 0 (so the reversed polynomial has nonzero leading coeff)
    f1 = (x - 1) * (x - 2) * (x - 3) * (x - 4) * (x - 5)
    f2 = evaluate(f1, x - 1)  # (x-2)(x-3)(x-4)(x-5)(x-6); iso via x -> x-1
    C1 = hyperelliptic_curve(f1)
    C2 = hyperelliptic_curve(f2)
    fl, m = is_isomorphic_with_isomorphism(C1, C2)
    @test fl
    @test domain(m) == C1
    @test codomain(m) == C2
  end

  @testset "h != 0 branch (completing the square, char != 2)" begin
    Qx, x = polynomial_ring(QQ, "x")
    # y^2 + y = x^5 + 1; h = 1, f = x^5 + 1; 4f + h^2 = 4x^5 + 5 (squarefree)
    f = x^5 + 1
    h = one(Qx)
    C = hyperelliptic_curve(f, h)
    fl, m = is_isomorphic_with_isomorphism(C, C)
    @test fl
    @test domain(m) == C
    @test codomain(m) == C
  end

  @testset "g != 2, genus 3 curves over GF(7)" begin
    F = GF(7)
    Fx, t = polynomial_ring(F, "t")
    # t^2 + 1 is irreducible over GF(7) since -1 is not a QR mod 7
    f1 = prod(t - F(i) for i in 1:6) * (t^2 + 1)  # degree 8, genus 3
    C1 = hyperelliptic_curve(f1)
    f2 = evaluate(f1, t + 1)
    C2 = hyperelliptic_curve(f2)
    fl, m = is_isomorphic_with_isomorphism(C1, C2)
    @test fl
    @test domain(m) == C1
    @test codomain(m) == C2
  end

  @testset "is_gl2_equivalent: degree(f2) < n covers virtual-infinity branches" begin
    Qx, x = polynomial_ring(QQ, "x")

    # d=1 path with degree(f2) < n: rootsf2 gains the virtual point at infinity
    f1_d1 = (x - 1) * (x - 2) * (x - 3) * (x - 4) * (x - 5)  # degree 5, n=6
    f2_d1 = evaluate(f1_d1, x + 1)  # x*(x-1)*(x-2)*(x-3)*(x-4), degree 5 < 6
    fl_d1, _ = Hecke.is_gl2_equivalent(f1_d1, f2_d1, 6)
    @test fl_d1

    # d=2, d1=1 path with degree(f2) < n: the infinity sub-branch inside the loop
    f1_d2 = (x^2 + 1) * (x - 1) * (x - 2) * (x - 3)  # degree 5, n=6
    f2_d2 = evaluate(f1_d2, x + 1)  # (x^2+2x+2)*x*(x-1)*(x-2), degree 5 < 6
    fl_d2, _ = Hecke.is_gl2_equivalent(f1_d2, f2_d2, 6)
    @test fl_d2
  end

  @testset "is_gl2_equivalent: degree multisets differ, early return" begin
    Qx, x = polynomial_ring(QQ, "x")
    # f1 has factor degrees [1,2], f2 has factor degrees [1,1,1]; with n=4 both
    # gain a virtual infinity, giving multisets [1,1,2] vs [1,1,1,1].
    f1 = (x - 1) * (x^2 + 1)
    f2 = (x - 1) * (x - 2) * (x - 3)
    fl, list = Hecke.is_gl2_equivalent(f1, f2, 4)
    @test !fl
    @test isempty(list)
  end

  @testset "apply isomorphism to point at infinity (c != 0, happy path)" begin
    Qx, x = polynomial_ring(QQ, "x")
    # C1 (odd-degree) and C2 (even-degree) are isomorphic via the flip x -> 1/x,
    # whose matrix is [0,1,1,0], so c = 1 != 0.  Applying to the point at infinity
    # of C1 should give the finite point (0:0:1) on C2.
    C1 = hyperelliptic_curve(x^5 + 1)
    C2 = hyperelliptic_curve(x^6 + x)
    fl, m = is_isomorphic_with_isomorphism(C1, C2)
    @test fl
    a, b, c, d, u, v = isomorphism_data(m)
    @test !iszero(c)
    Pinf = C1([1, 0, 0])
    @test is_infinite(Pinf)
    Q = m(Pinf)
    @test !is_infinite(Q)
    @test Q == C2([QQ(0), QQ(0)])
  end

  @testset "apply isomorphism to point at infinity (c != 0, no rational y error)" begin
    Qx, x = polynomial_ring(QQ, "x")
    # Construct a HypellCrvIsom with c=1 (a=0, b=1, c=1, d=0) mapping the
    # point at infinity of C1 to x0 = a/c = 0 on C2.  Since f2(0) = -1 < 0,
    # the equation t^2 + 1 = 0 has no rational root, so the error branch fires.
    # C1 has odd degree so (1:0:0) is its unique rational infinity point.
    C1 = hyperelliptic_curve(x^5 + x + 1)
    C2 = hyperelliptic_curve(x^6 - 1)
    m = HypellCrvIsom{QQFieldElem}(C1, C2, QQ(0), QQ(1), QQ(1), QQ(0), QQ(1), zero(Qx))
    Pinf = C1([1, 0, 0])
    @test_throws ErrorException m(Pinf)
  end

  @testset "is_isomorphic: non-isomorphic genus-3 curves, exhausts GL2 candidates" begin
    Qx, x = polynomial_ring(QQ, "x")
    # Two degree-8 genus-3 curves with all rational roots (d=1, n=8).
    # Their root sets {1..8} and {1..7,9} have different cross-ratios, so no
    # Mobius transform maps one to the other.  GL2 search exhausts all candidates
    # and returns false, reaching the final "return false, dummy" branch.
    f1 = prod(x - QQ(i) for i in 1:8)
    f2 = prod(x - QQ(i) for i in [1, 2, 3, 4, 5, 6, 7, 9])
    C1 = hyperelliptic_curve(f1)
    C2 = hyperelliptic_curve(f2)
    @test !is_isomorphic(C1, C2)
  end

  @testset "g = 2, equal Igusa-Clebsch invariants" begin
    F = GF(9)
    o = gen(F)
    R, x = polynomial_ring(F)
    f5 = hyperelliptic_curve(x^5 + (o + 1)*x)
    f6 = hyperelliptic_curve(o*x^5 + (2*o + 1)*x)
    @test is_isomorphic(f5, f6)
  end
end
