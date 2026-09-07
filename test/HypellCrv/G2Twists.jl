@testset "G2 Twists" begin

  @testset "Compute twists of genus 2 curves characteristic 2" begin


    F = GF(2)
    T = [ [F(0), F(0), F(0)], [F(0), F(0), F(1)], [F(1), F(1), F(1)], [F(1), F(0), F(1)], [F(0), F(1), F(1)]]
    lengths = [3, 3, 4, 2, 2]
    for i in  (1:length(lengths))
      H = Hecke.models_from_igusa_invariants(igusa_from_g2(T[i]), true)
      @test length(H) == lengths[i]
      for C in H
        @test g2_invariants(C) == T[i]
      end
    end

    F = GF(2^2)
    t = gen(F)
    T = [ [F(0), F(0), F(0)], [t*(t+1), t^2+t, t], [t^3, t^2, t],  [F(0), F(0), t], [t, t-1, t^2], [t*(t+1), t + 1, t], [F(0), t, F(1)]]
    lengths = [5, 2, 4, 2, 2, 4, 2]
    for i in  (1:length(lengths))
      H = Hecke.models_from_igusa_invariants(igusa_from_g2(T[i]), true)
      @test length(H) == lengths[i]
      for C in H
        @test g2_invariants(C) == T[i]
      end
    end

    F = GF(2^3)
    t = gen(F)
    T = [ [F(0), F(0), F(0)], [t*(t+1), t^2+t, t], [t^3, t^2, t],  [F(0), F(0), t], [t, t-1, t^2], [t*(t+1), t + 1, t], [F(0), t, F(1)], [t^2, t^2 + 1, F(0)], [F(0),t^2, F(0)]]
    lengths = [3, 2, 6, 3, 2, 4, 2, 2, 2]
    for i in (1:length(lengths))
      H = Hecke.models_from_igusa_invariants(igusa_from_g2(T[i]), true)
      @test length(H) == lengths[i]
      for C in H
        @test g2_invariants(C) == T[i]
      end
    end
    
    F = GF(2^4)
    t = gen(F)
    T = [ [F(0), F(0), F(0)], [t*(t+1), t^2+t, t], [t^3, t^2, t],  [F(0), F(0), t], [t, t-1, t^2], [t*(t+1), t + 1, t], [F(0), t, F(1)]]
    lengths = [13, 2, 6, 5, 2, 4, 2]
    for i in  (1:length(lengths))
      H = Hecke.models_from_igusa_invariants(igusa_from_g2(T[i]), true)
      @test length(H) == lengths[i]
      for C in H
        @test g2_invariants(C) == T[i]
      end
    end
  end
  @testset "Compute twists of genus 2 curves characteristic 3" begin
    F = GF(3)
    o = F(1)
    T = [ [F(0), F(0), F(0)], [F(50000), F(3750), F(-125) ], [2*o^3, F(0), F(1)], [F(1), 2*o + 1, o], [2*o + 2, F(1), o], [F(1), o, o^2]]

    lengths = [2, 8, 8, 6, 2, 2]
    for i in  (1:length(lengths))
      H = Hecke.models_from_igusa_invariants(igusa_from_g2(T[i]), true)
      @test length(H) == lengths[i]
      @test length(Hecke.filter_g2_isomorphism_classes(H)) == lengths[i]
      for C in H
        @test g2_invariants(C) == T[i]
      end
    end

    F = GF(3^2)
    o = gen(F)
    T = [ [F(0), F(0), F(0)], [F(50000), F(3750), F(-125) ], [2*o^3, F(0), F(1)], [F(1), 2*o + 1, o], [2*o + 2, F(1), o], [F(1), o, o^2], [F(0), 2*o, 2*o + 2]]
   

    lengths = [2, 8, 6, 3, 2, 2, 4]
    for i in (1:length(lengths))
      H = Hecke.models_from_igusa_invariants(igusa_from_g2(T[i]), true)
      @test length(H) == lengths[i]
      @test length(Hecke.filter_g2_isomorphism_classes(H)) == lengths[i]
      for C in H
        @test g2_invariants(C) == T[i]
      end
    end

    F = GF(3^3)
    o = gen(F)
    T = [ [F(0), F(0), F(0)], [F(50000), F(3750), F(-125) ], [2*o^3, F(0), F(1)], [F(1), 2*o + 1, o], [2*o + 2, F(1), o], [F(1), o, o^2]]


    lengths = [2, 8, 6, 2, 2, 2]
    for i in  (1:length(lengths))
      H = Hecke.models_from_igusa_invariants(igusa_from_g2(T[i]), true)
      @test length(H) == lengths[i]
      @test length(Hecke.filter_g2_isomorphism_classes(H)) == lengths[i]
      for C in H
        @test g2_invariants(C) == T[i]
      end
    end


    F = GF(3^4)
    o = gen(F)
    T = [ [F(0), F(0), F(0)], [F(50000), F(3750), F(-125) ], [2*o^3, F(0), F(1)], [F(1), 2*o + 1, o], [2*o + 2, F(1), o], [F(1), o, o^2]]


    lengths = [10, 8, 6, 2, 2, 2]
    for i in  (1:length(lengths))
      H = Hecke.models_from_igusa_invariants(igusa_from_g2(T[i]), true)
      @test length(H) == lengths[i]
      @test length(Hecke.filter_g2_isomorphism_classes(H)) == lengths[i]
      for C in H
        @test g2_invariants(C) == T[i]
      end
    end
  end
  @testset "Compute twists of genus 2 curves characteristic 5" begin

    F = GF(5)
    T = [ [F(1), F(3), F(2)], [F(3), F(3), F(4)], [F(1), F(2), F(2)]]

    lengths = [6, 4, 4]
    for i in  (1:length(lengths))
      H = Hecke.models_from_igusa_invariants(igusa_from_g2(T[i]), true)
      @test length(Hecke.filter_g2_isomorphism_classes(H)) == lengths[i]
      for C in H
        @test g2_invariants(C) == T[i]
      end
    end


    F = GF(5^2)
    o = gen(F)

    T = [ [F(0), F(0), F(0)], [4*o + 3, o + 1, 3*o + 2], [4*o + 1, F(1), 2*o + 4], [F(4), o + 2, F(2)], [F(1), o + F(1), 2*o + F(1)], [F(0),2*o,2*o]
] 
    lengths = [12, 4, 3, 2, 2, 2]
    for i in  (1:length(lengths))
      H = Hecke.models_from_igusa_invariants(igusa_from_g2(T[i]), true)
      @test length(Hecke.filter_g2_isomorphism_classes(H)) == lengths[i]
      for C in H
        @test g2_invariants(C) == T[i]
      end
    end

    F = GF(5^3)
    o = gen(F)
    T = [ [F(0), F(0), F(0)], [4*o + 3, o + 1, 3*o + 2], [4*o + 1, F(1), 2*o + 4], [F(4), o + 2, F(2)]
] 
    lengths = [8, 2, 2, 2]
    for i in  (1:length(lengths))
      H = Hecke.models_from_igusa_invariants(igusa_from_g2(T[i]), true)
      @test length(H) == lengths[i]
      @test length(Hecke.filter_g2_isomorphism_classes(H)) == lengths[i]
      for C in H
        @test g2_invariants(C) == T[i]
      end
    end

    F = GF(5^4)
    o = gen(F)
    T = [ [F(0), F(0), F(0)], [4*o + 3, o + 1, 3*o + 2], [4*o + 1, F(1), 2*o + 4], [F(4), o + 2, F(2)]
] 
    lengths = [12, 2, 2, 2]
    for i in  (1:length(lengths))
      H = Hecke.models_from_igusa_invariants(igusa_from_g2(T[i]), true)
      @test length(H) == lengths[i]
      @test length(Hecke.filter_g2_isomorphism_classes(H)) == lengths[i]
      for C in H
        @test g2_invariants(C) == T[i]
      end
    end
  end

  @testset "Compute twists of genus 2 curves characteristic 11" begin

    F = GF(11)
    o = F(1)
    T = [ [F(0), F(0), F(0)], [ F(6400000)/3, F(440000)/9, F(-32000)/81 ],  [F(50000), F(3750), F(-125) ], [30*o + F(35), 17*o + F(19), 25*o + F(34)], [19*o + F(12), 6*o + F(36), 12*o + F(30)], [o, o+1, 2*o - F(3)]
] 
    lengths = [10, 7, 8, 4, 2, 2]
    for i in  (1:length(lengths))
      H = Hecke.models_from_igusa_invariants(igusa_from_g2(T[i]), true)
      @test length(Hecke.filter_g2_isomorphism_classes(H)) == lengths[i]
      for C in H
        @test g2_invariants(C) == T[i]
      end
    end
  end
  @testset "Compute twists of genus 2 curves characteristic 37" begin

    F = GF(37^2)
    o = gen(F)
    T = [ [F(0), F(0), F(0)], [ F(6400000)/3, F(440000)/9, F(-32000)/81 ],  [F(50000), F(3750), F(-125) ], [30*o + F(35), 17*o + F(19), 25*o + F(34)], [19*o + F(12), 6*o + F(36), 12*o + F(30)], [o, o+1, 2*o - F(3)]
] 
    lengths = [2, 9, 8, 5, 4, 2]
    for i in  (1:length(lengths))
      H = Hecke.models_from_igusa_invariants(igusa_from_g2(T[i]), true)
      @test length(Hecke.filter_g2_isomorphism_classes(H)) == lengths[i]
      for C in H
        @test g2_invariants(C) == T[i]
      end
    end

    F = GF(37^3)
    o = gen(F)
    T = [ [F(0), F(0), F(0)], [ F(6400000)/3, F(440000)/9, F(-32000)/81 ],  [F(50000), F(3750), F(-125) ], [30*o + F(35), 17*o + F(19), 25*o + F(34)], [19*o + F(12), 6*o + F(36), 12*o + F(30)], [o, o+1, 2*o - F(3)]
] 
    lengths = [2, 9, 6, 2, 2, 2]
    for i in  (1:length(lengths))
      H = Hecke.models_from_igusa_invariants(igusa_from_g2(T[i]), true)
      @test length(Hecke.filter_g2_isomorphism_classes(H)) == lengths[i]
      for C in H
        @test g2_invariants(C) == T[i]
      end
    end

    F = GF(37^4)
    o = gen(F)
    T = [ [F(0), F(0), F(0)], [ F(6400000)/3, F(440000)/9, F(-32000)/81 ],  [F(50000), F(3750), F(-125) ], [30*o + F(35), 17*o + F(19), 25*o + F(34)], [19*o + F(12), 6*o + F(36), 12*o + F(30)], [o, o+1, 2*o - F(3)]
] 
    lengths = [10, 9, 8, 2, 2, 2]
    for i in  (1:length(lengths))
      H = Hecke.models_from_igusa_invariants(igusa_from_g2(T[i]), true)
      @test length(Hecke.filter_g2_isomorphism_classes(H)) == lengths[i]
      for C in H
        @test g2_invariants(C) == T[i]
      end
    end
  end
  @testset "Compute twists of genus 2 curves rational function fields" begin
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
