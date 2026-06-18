@testset "G2Twists" begin

  @testset "Compute twists of genus 2 curves" begin

    F = GF(2^3)
    t = gen(F)
    T = [ [F(0), F(0), F(0)], [t*(t+1), t^2+t, t], [t^3, t^2, t], [F(0), F(0), 2*t], [t, t-1, t^2]]
    lengths = [3, 2, 6, 3, 2]
    for i in (1:5)
      H = Hecke.models_from_igusa_invariants(igusa_from_g2(T[i]), true)
      length(H) == lengths[i]
      for C in H
        g2_invariants(C) == T[i]
      end
    end
    
    F = GF(2^4)
    t = gen(F)
    T = [ [F(0), F(0), F(0)], [t*(t+1), t^2+t, t], [t^3, t^2, t], [F(0), F(0), 2*t], [t, t-1, t^2]]
    lengths = [13, 2, 6, 13, 2]
    for i in (1:5)
      H = Hecke.models_from_igusa_invariants(igusa_from_g2(T[i]), true)
      length(H) == lengths[i]
      for C in H
        g2_invariants(C) == T[i]
      end
    end


    #=while true
      a = rand(F)
      b = rand(F)
      c = rand(F)
      gs = [a,b,c]
      J2, J4, J6, _, J10 = igusa_from_g2(gs)
       R = J2^6*J6^3 - 2*J2^5*J4^2*J6^2 - 72*J2^5*J4*J6*J10 - 432*J2^5*J10^2 + J2^4*J4^4*J6 +
    8*J2^4*J4^3*J10 - 72*J2^4*J4*J6^3 - 48*J2^4*J6^2*J10 + 136*J2^3*J4^3*J6^2 +
    4816*J2^3*J4^2*J6*J10 + 28800*J2^3*J4*J10^2 + 216*J2^3*J6^4 -
    64*J2^2*J4^5*J6 - 512*J2^2*J4^4*J10 + 1080*J2^2*J4^2*J6^3 -
    12960*J2^2*J4*J6^2*J10 - 96000*J2^2*J6*J10^2 - 2304*J2*J4^4*J6^2 -
    84480*J2*J4^3*J6*J10 - 512000*J2*J4^2*J10^2 - 7776*J2*J4*J6^4 -
    129600*J2*J6^3*J10 + 1024*J4^6*J6 + 8192*J4^5*J10 + 6912*J4^3*J6^3 +
    691200*J4^2*J6^2*J10 + 11520000*J4*J6*J10^2 + 11664*J6^5 + 51200000*J10^3
      if R == F(0)
        println([a,b,c])
        break
      end
    end=#

    F = GF(3^2)
    o = gen(F)
    T = [ [F(0), F(0), F(0)], [F(50000), F(3750), F(-125) ], [2*o^3, F(0), F(1)], [F(1), 2*o + 1, o], [2*o + 2, F(1), o], [F(1), o, o^2]]


    lengths = [2, 8, 6, 3, 2, 2]
    for i in (1:6)
      H = Hecke.models_from_igusa_invariants(igusa_from_g2(T[i]), true)
      println(length(H) == lengths[i])
      println(length(H))
      for C in H
        g2_invariants(C) == T[i]
      end
    end


    F, t = rational_function_field(GF(5), :t)
    T = [ [F(0), F(0), F(0)], [3/(t^5 + 3*t^4 + 3*t^3 + t^2), 2/(t^4 + 2*t^3 + t^2), 4/(t^3 + t^2)], [2/(t^5 + 2*t^4 + t^3),
    (2*t + 3)/(t^5 + 2*t^4 + t^3), 1/t^3], [t, t-1, 2*t], [t, t-1, t^2]]
    for t in T
      @test g2_invariants(reconstruct_from_g2(t)) == t
    end

    F, t = rational_function_field(GF(7), :t)
    T = [
      [K(0), K(0), K(0)], [K(50000), K(3750), K(-125)], 
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
