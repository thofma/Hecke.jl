@testset "G2 Reconstruction" begin

  @testset "Reconstruct genus 2 curve from Igusa invariants" begin

    Qx, x = polynomial_ring(QQ, "x")
    f1 = x^6+3*x+5
    h1 = x+2
    C = hyperelliptic_curve(f1, h1)
    ig_invs = igusa_invariants(C)

    D = reconstruct_from_igusa(ig_invs)
    f, h = hyperelliptic_polynomials(D)

    #Testing to see if the defining polynomial is sufficiently reduced.
    @test maximum(collect(coefficients(f)))<=1500

    @test weighted_equality(igusa_invariants(C), igusa_invariants(D), [2, 4, 6, 8, 10])

    K, a = number_field(x^2 + 1, :a)
    R, t = polynomial_ring(K, :t)
    C = hyperelliptic_curve(t^5 - a*t + a, R(0))
    ig_invs = igusa_invariants(C)
    D = reconstruct_from_igusa(ig_invs)
    ig_invs2 = igusa_invariants(D)
    @test weighted_equality(ig_invs, ig_invs2, [2, 4, 6, 8, 10])

    K, s = rational_function_field(QQ)
    R, t = polynomial_ring(K, :t)
    C = hyperelliptic_curve(t^5 - s*t + 1, R(0))
    ig_invs = igusa_invariants(C)
    D = reconstruct_from_igusa(ig_invs)
    ig_invs2 = igusa_invariants(D)
    @test weighted_equality(ig_invs, ig_invs2, [2, 4, 6, 8, 10])


    F = GF(7)
    Fx, x = polynomial_ring(F, "x")

    f1 = x^6+3*x^5-4*x^4+3*x^2+2*x-1
    C = hyperelliptic_curve(f1)
    ig_invs = igusa_invariants(C)

    D = reconstruct_from_igusa(ig_invs)

    @test weighted_equality(igusa_invariants(C), igusa_invariants(D), [2, 4, 6, 8, 10])

    
    T = [ [QQ(0), QQ(0), QQ(0)], [QQ(50000), QQ(3750), QQ(-125)], [6400000//3, 440000//9, -32000//81 ], 
    [QQ(4455516), 160381//2, -18083//36],  [6436343//36, 2859245//288, -10051//64], [ 2907867136//529, 93386304//529, 4069120//529 ]]
    for t in T
      @test g2_invariants(reconstruct_from_g2(t)) == t
    end

    F, t = rational_function_field(GF(3), :t)
    T = [ [F(0), F(0), F(0)], [F(50000), F(3750), F(-125)], [2*t^3, F(0), F(1)], [t, t-1, 2*t], [t, t-1, t^2]]
    for t in T
      @test g2_invariants(reconstruct_from_g2(t)) == t
    end

    F, t = rational_function_field(GF(5), :t)
    T = [ [F(0), F(0), F(0)], [3/(t^5 + 3*t^4 + 3*t^3 + t^2), 2/(t^4 + 2*t^3 + t^2), 4/(t^3 + t^2)], [2/(t^5 + 2*t^4 + t^3),
    (2*t + 3)/(t^5 + 2*t^4 + t^3), 1/t^3], [t, t-1, 2*t], [t, t-1, t^2]]
    for t in T
      @test g2_invariants(reconstruct_from_g2(t)) == t
    end

    F, t = rational_function_field(GF(7), :t)
    T = [
      [F(0), F(0), F(0)], [F(50000), F(3750), F(-125)], 
      [(4*t^5 + 3*t^4 + 3*t^3 + 5*t^2 + 3*t + 1)/(t^5 + t^4 + 5*t^3 + 6*t^2),(4*t^4 + t^2 + 3*t + 1)/(t^4 + 3*t^3 + 4*t^2),(t^3 + 4*t^2 + 5*t + 6)/(t^3 + 5*t^2)],
      [(6*t^5 + t^4 + t^3 + 4*t^2 + t + 5)/(t^5 + 3*t^4 + 4*t^3),(5*t^5 + 5*t^4 + 4*t^3 + 3*t^2 + 4*t + 4)/(t^5 + 3*t^4 + 4*t^3),(t^3 + 2*t^2 + 3*t + 2)/t^3],
      [t, t-1, 2*t], 
      [t, t-1, t^2]
      ]
    for t in T
      @test g2_invariants(reconstruct_from_g2(t)) == t
    end
  end
end
