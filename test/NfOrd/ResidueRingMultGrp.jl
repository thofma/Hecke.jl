@testset "ResidueRingMultGrp" begin

  function verify_order(g::Hecke.AbsSimpleNumFieldOrderQuoRingElem,o)
    g == 0 && return false
    g^o == 1 || return false
    for l in keys(factor(o).fac)
      g^div(o,l) == 1 && return false
    end
    return true
  end

  function verify_order(g,i,o)
    iszero(g) && return false
    powermod(g,o,i.gen_one) - 1 in i || return false
    for l in keys(factor(o).fac)
      powermod(g,div(o,l),i.gen_one) - 1  in i && return false
    end
    return true
  end


  @testset "multiplicative_group" begin
     Qx,  x = polynomial_ring(QQ, "x");

    @testset "K = Q" begin
      K,  a = number_field(x,"a");
      O = maximal_order(K)

      @testset "m0 = <$n>" for n in 1:50
        m0 = O(n)*O
        Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O, m0)
        G, M = multiplicative_group(Q)
        @test is_snf(G)
        SNF = G.snf
        gens = M.generators
        @test length(SNF) == length(gens)
        for i in 1:length(gens)
          @test verify_order(gens[i],SNF[i])
        end
        H = Hecke.multgrp_of_cyclic_grp(n)
        @test Hecke.is_isomorphic(G, H)
        @test M(G(G.snf)) == Q(1)
        for g in gens
          for exp in -5:10
            el = g^exp
            @test M(M\el) == el
          end
        end
      end

      @testset "m0 = <1361>^3000" begin
        m0 = ideal(O,O(1361))^100
        Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O,m0)
        G, M = multiplicative_group(Q)
        @test is_snf(G)
        SNF = G.snf
        gens = M.generators
        @test length(SNF) == length(gens)
        for i in 1:length(gens)
          @test verify_order(gens[i],SNF[i])
        end
        @test M(G(G.snf)) == Q(O(1))
        for g in gens
          for exp in -5:10
            el = g^exp
            @test M(M\el) == el
          end
        end
      end

    end

    @testset "K = Q[√2]" begin
       K,  a = number_field(x^2 - 2,"a")
      O = maximal_order(K)

      @testset "m0 = <$n>" for n in 1:100
        m0 = ideal(O,O(n))
        Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O,m0)
        G, M = multiplicative_group(Q)
        @test is_snf(G)
        SNF = G.snf
        gens = M.generators
        @test length(SNF) == length(gens)
        for i in 1:length(gens)
          @test verify_order(gens[i], SNF[i])
        end
        @test M(G(G.snf)) == Q(O(1))
        for g in gens
          for exp in -5:10
            el = g^exp
            @test M(M\el) == el
          end
        end
      end
    end

    @testset "f = x^2-x+15" begin
      f = x^2-x+15
       K,  a = number_field(f,"a");
      O = maximal_order(K)

      @testset "m0 = <2>" begin
        m0 = ideal(O,O(2))
        Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O,m0)
        G, M = multiplicative_group(Q)
        @test is_snf(G)
        SNF = G.snf
        gens = M.generators
        @test length(SNF) == length(gens)
        for i in 1:length(gens)
          @test verify_order(gens[i],SNF[i])
        end
        @test order(G) == 3
        H = abelian_group([ 3 ])
        @test Hecke.is_isomorphic(G,H)
        @test M(G(G.snf)) == Q(O(1))
        for g in gens
          for exp in -5:10
            el = g^exp
            @test M(M\el) == el
          end
        end
      end

      @testset "m0 = <4>" begin
        m0 = ideal(O,O(4))
        Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O,m0)
        G, M = multiplicative_group(Q)
        @test is_snf(G)
        SNF = G.snf
        gens = M.generators
        @test length(SNF) == length(gens)
        for i in 1:length(gens)
          @test verify_order(gens[i],SNF[i])
        end
        @test order(G) == 12
        H = abelian_group([ 3, 2, 2 ])
        @test Hecke.is_isomorphic(G,H)
        @test M(G(G.snf)) == Q(O(1))
        for g in gens
          for exp in -5:10
            el = g^exp
            @test M(M\el) == el
          end
          el = g^(-8)
          @test M(M\el) == el
        end
      end

      @testset "m0 = <5>" begin
        m0 = ideal(O,O(5))
        Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O,m0)
        G, M = multiplicative_group(Q)
        @test is_snf(G)
        SNF = G.snf
        gens = M.generators
        @test length(SNF) == length(gens)
        for i in 1:length(gens)
          @test verify_order(gens[i], SNF[i])
        end
        @test M(G(G.snf)) == Q(O(1))
        @test order(G) == 16
        H = abelian_group([4, 4])
        @test Hecke.is_isomorphic(G,H)
        for g in gens
          for exp in [ -3, 2, 4 ]
            el = g^exp
            @test M(M\el) == el
          end
        end
      end

      @testset "m0 = <20>" begin
        m0 = ideal(O,O(20))
        Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O,m0)
        G, M = multiplicative_group(Q)
        @test is_snf(G)
        SNF = G.snf
        gens = M.generators
        @test length(SNF) == length(gens)
        for i in 1:length(gens)
          @test verify_order(gens[i],SNF[i])
        end
        @test M(G(G.snf)) == Q(O(1))
        @test order(G) == 192
        H = abelian_group([3, 2, 2, 4, 4])
        @test Hecke.is_isomorphic(G,H)
        for g in gens
          for exp in [ -4, 1, 7 ]
            el = g^exp
            @test M(M\el) == el
          end
        end
      end
    end

    @testset "x^12+..." begin
      #= f = x^12+7*x^11-97*x^10-859*x^9+2558*x^8+38839*x^7+30012*x^6-710649*x^5-2189082*x^4+2534629*x^3+25314673*x^2+43623088*x+28168151 =#
      #=  K,  a = number_field(f,"a"); =#
      #= O = maximal_order(K) =#

      #= @testset "m0 = <3>" begin =#
      #=   println("m0 = <3>") =#
      #=   m0 = ideal(O,O(3)) =#
      #=   Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O,m0) =#
      #=   G = domain(Hecke.multiplicative_group(Q)) =#
      #=   println(snf(G)[1].snf) =#
      #=   @test order(G) == 512000 =#
      #=   structt = [80,80,80] =#
      #=   H = abelian_group(structt) =#
      #=   @test Hecke.is_isomorphic(G,H) =#
      #=   @test M(G(G.snf)) == Q(O(1)) =#
      #=   for g in gens =#
      #=     for exp in -5:10 =#
      #=       el = g^exp =#
      #=       @assert M(M\el) == el =#
      #=     end =#
      #=   end =#
      #= end =#

      #= @testset "m0 = <4>" begin =#
      #=   println("m0 = <4>") =#
      #=   m0 = ideal(O,O(4)) =#
      #=   Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O,m0) =#
      #=   G = domain(Hecke.multiplicative_group(Q)) =#
      #=   println(snf(G)[1].snf) =#
      #=   @test order(G) == 14745600 =#
      #=   structt = [15,2,2,2,2,15,4,4,4,4,2,2,2,2] =#
      #=   H = abelian_group(structt) =#
      #=   @test Hecke.is_isomorphic(G,H) =#
      #=   @test M(G(G.snf)) == Q(O(1)) =#
      #=   for g in gens =#
      #=     for exp in -5:10 =#
      #=       el = g^exp =#
      #=       @assert M(M\el) == el =#
      #=     end =#
      #=   end =#
      #= end =#

      #= @testset "m0 = <5>" begin =#
      #=   println("m0 = <5>") =#
      #=   m0 = ideal(O,O(5)) =#
      #=   Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O,m0) =#
      #=   G = domain(Hecke.multiplicative_group(Q)) =#
      #=   println(snf(G)[1].snf) =#
      #=   @test order(G) == 187500000 =#
      #=   structt = [24,5,5,5,5,5,5,4,5,5,5] =#
      #=   H = abelian_group(structt) =#
      #=   @test Hecke.is_isomorphic(G,H) =#
      #=   @test M(G(G.snf)) == Q(O(1)) =#
      #=   for g in gens =#
      #=     for exp in -5:10 =#
      #=       el = g^exp =#
      #=       @assert M(M\el) == el =#
      #=     end =#
      #=   end =#
      #= end =#

      #= @testset "m0 = <60>" begin =#
      #=   println("m0 = <60>") =#
      #=   m0 = ideal(O,O(60)) =#
      #=   Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O,m0) =#
      #=   G = domain(Hecke.multiplicative_group(Q)) =#
      #=   println(snf(G)[1].snf) =#
      #=   @test order(G) == 14155776*ZZRingElem(10)^14 =#
      #=   structt = [15,2,2,2,2,15,4,4,4,4,2,2,2,2,80,80,80,24,5,5,5,5,5,5,4,5,5,5] =#
      #=   H = abelian_group(structt) =#
      #=   @test Hecke.is_isomorphic(G,H) =#
      #=   @test M(G(G.snf)) == Q(O(1)) =#
      #=   for g in gens =#
      #=     for exp in -5:10 =#
      #=       el = g^exp =#
      #=       @assert M(M\el) == el =#
      #=     end =#
      #=   end =#
      #= end =#
    end
  end

  @testset "_multgrp_mod_pv" begin
     Qx,  x = polynomial_ring(QQ, "x");

    @testset "K = Q" begin
       K,  a = number_field(x,"a");
      O = maximal_order(K)

      @testset "i = <$pnum>^$v" for (pnum,v) in [(pnum,v) for pnum in [ x for x in 1:50 if is_prime(ZZRingElem(x))], v in [1,2,4,17]]
        #p = ideal(O,O(pnum))
        p = prime_decomposition(O, pnum)[1][1]
        #p = collect(keys(factor(p)))[1]
        pv = p^v
        G, mG = Hecke._multgrp_mod_pv(p, v, pv)
        S, StoG, mS = snf(G, mG)
        gens = mS.generators
        d = S.snf
        @test length(gens) == length(d)
        for i in 1:length(gens)
          @test verify_order(gens[i].elem, pv, d[i])
        end
        H = Hecke.multgrp_of_cyclic_grp(ZZRingElem(pnum)^v)
        @test Hecke.is_isomorphic(S, H)
        # Test discrete logarithm
        Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O, pv)
        for g in mG.generators
          for exp in [ -1, 1, 6 ]
            el = g^exp
            @test mG(mG\el) == el
          end
        end
      end
    end

    @testset "f = x^2-x+15" begin
      f = x^2-x+15
       K,  a = number_field(f,"a");
      O = maximal_order(K)
      I = O(20)*O

      @testset "p = <$(p.gen_one),$(p.gen_two)>, v = $v" for (p,v) in factor(I)
        pv = p^v
        G, mG = Hecke._multgrp_mod_pv(p, v, pv)
        S, StoG, mS = snf(G, mG)
        gens = mS.generators
        structure = S.snf
        @test length(gens) == length(structure)
        for i in 1:length(gens)
          @test verify_order(gens[i].elem, pv, structure[i])
        end
        # Test discrete logarithm
        Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O, pv)
        for g in mG.generators
          for exp in [ -1, 0, 1, 2 ]
            el = g^exp
            @test mG(mG\el) == el
          end
        end
      end
    end

    @testset "f = x^3+8*x^2+6*x-17" begin
      f = x^3+8*x^2+6*x-17
       K,  a = number_field(f,"a");
      O = maximal_order(K)
      p = O(3)*O
      p = collect(keys(factor(p)))[1]
      structures = Vector{ZZRingElem}[[26],[26,3,3,3],[26,9,9,9],[26,27,27,27]]
      @testset "v = $v" for v in 1:length(structures)
        pv = p^v
        G, mG = Hecke._multgrp_mod_pv(p, v, pv)
        S, StoG, mS = snf(G, mG)
        gens = mS.generators
        d = S.snf
        @test length(gens) == length(d)
        for i in 1:length(gens)
          @test verify_order(gens[i].elem, pv, d[i])
        end
        @test order(G) == prod(structures[v])
        H = abelian_group(structures[v])
        @test Hecke.is_isomorphic(S, H)
        # Test discrete logarithm
        Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O, pv)
        for g in mG.generators
          for exp in [ -2, 1, 3 ]
            el = g^exp
            @test mG(mG\el) == el
          end
        end
      end
    end

    @testset "f = x^4+11*x^3-19*x^2-8*x+7" begin
      f = x^4+11*x^3-19*x^2-8*x+7
       K,  a = number_field(f,"a");
      O = maximal_order(K)
      p = ideal(O, ZZRingElem(3), O(2+a+a^2))
      p = collect(keys(factor(p)))[1]
      structures = Vector{ZZRingElem}[[8],[8,3,3],[8,3,3,3,3],[8,3,3,3,3,9],[8,3,3,9,9,9],[8,3,9,9,9,27]]
      @testset "v = $v" for v in 1:length(structures)
        pv = p^v
        G, mG = Hecke._multgrp_mod_pv(p, v, pv)
        S, StoG, mS = snf(G, mG)
        gens = mS.generators
        d = S.snf
        @test length(gens) == length(d)
        for i in 1:length(gens)
          @test verify_order(gens[i].elem, pv, d[i])
        end
        @test order(G) == prod(structures[v])
        H = abelian_group(structures[v])
        @test Hecke.is_isomorphic(S, H)
        # Test discrete logarithm
        Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O,pv)
        for g in mG.generators
          for exp in [ -4, 1, 6 ]
            el = g^exp
            @test mG(mG\el) == el
          end
        end
      end
    end

    @testset "f = x^6+6x^5-12*x^4-x^3-6*x^2+9*x+20" begin
      f = x^6+6x^5-12*x^4-x^3-6*x^2+9*x+20
       K,  a = number_field(f,"a");
      O = maximal_order(K)
      p = ideal(O, ZZRingElem(3), O(2+2*a+a^2))
      p = collect(keys(factor(p)))[1]
      structures = Vector{ZZRingElem}[[8],[8,3,3],[8,3,3,3,3],[8,9,9,3,3],[8,9,9,3,3,3,3],[8,9,9,9,9,3,3]]
      @testset "v = $v" for v in 1:length(structures)
        pv = p^v
        G, mG = Hecke._multgrp_mod_pv(p, v, pv)
        S, StoG, mS = snf(G, mG)
        gens = mS.generators
        d = S.snf
        @test length(gens) == length(d)
        for i in 1:length(gens)
          @test verify_order(gens[i].elem, pv, d[i])
        end
        @test order(G) == prod(structures[v])
        H = abelian_group(structures[v])
        @test Hecke.is_isomorphic(S, H)
        # Test discrete logarithm
        Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O, pv)
        for g in mG.generators
          for exp in [ -1, 0, 1, 6 ]
            el = g^exp
            @test mG(mG\el) == el
          end
        end
      end
    end
  end

  @testset "_multgrp_mod_p" begin
     Qx,  x = polynomial_ring(QQ, "x");

    @testset "K = Q" begin
       K,  a = number_field(x, "a");
      O = maximal_order(K)

      @testset "p = <$(pnum)>" for pnum in [ x for x in 1:50 if is_prime(ZZRingElem(x))]
        p = O(pnum)*O
        @test is_prime(p)
        #p = collect(keys(factor(p)))[1]
        G, mG = Hecke._multgrp_mod_p(p)
        @test length(mG.generators) == 1
        g = mG.generators[1]
        n = exponent(G)
        @test n == pnum - 1
        @test verify_order(g, p, n)
        for exp in [ 0, 1, 2, n - 2, n - 1, n, 3234239 ]
          @test mG.discrete_logarithm(g^exp)[1] == mod(ZZRingElem(exp), n)
        end
      end
    end

    @testset "K = Q[√2]" begin
       K,  a = number_field(x^2-2,"a");
      O = maximal_order(K)

      primeideals = Vector{Hecke.AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
      for pnum in [ x for x in 1:40 if is_prime(ZZRingElem(x))]
        append!(primeideals, collect(keys(factor(O(pnum)*O))))
      end

      @testset "p = <$(p.gen_one), $(p.gen_two)>" for p in primeideals
        @test is_prime(p)
        G, mG = Hecke._multgrp_mod_p(p)
        @test length(mG.generators) == 1
        g = mG.generators[1]
        n = exponent(G)
        @test !iszero(g)
        @test !(g in p)
        @test verify_order(g, p, n)
        Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O, p)
        for exp in [ 0, 1, 2, n - 2, n - 1, n ]
          @test mG.discrete_logarithm((Q(g)^exp).elem)[1] == mod(ZZRingElem(exp), n)
        end
      end
    end

    @testset "K = Q[x]/<x^6+6*x^5-12*x^4-x^3-6*x^2+9*x+20>" begin
       K,  a = number_field(x^6+6*x^5-12*x^4-x^3-6*x^2+9*x+20,"a");
      O = maximal_order(K)

      primeideals = Vector{Hecke.AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
      for pnum in [ x for x in 1:20 if is_prime(ZZRingElem(x)) ]
        append!(primeideals, collect(keys(factor(O(pnum)*O))))
      end

      @testset "p = <$(p.gen_one), $(p.gen_two)>" for p in primeideals
        @test is_prime(p)
        G, mG = Hecke._multgrp_mod_p(p)
        @test length(mG.generators) == 1
        g = mG.generators[1]
        n = exponent(G)
        @test !iszero(g)
        @test !(g in p)
        @test verify_order(g, p, n)
        Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O, p)
        for exp in [ 24, n - 345 ]
          @test mG.discrete_logarithm((Q(g)^exp).elem)[1] == mod(ZZRingElem(exp), n)
        end
      end
    end

    @testset "K = Q[x]/<x^10-x^9+x^8-x^7+x^6-x^5+x^4-x^3+x^2-x+1>" begin
       K,  a = number_field(x^10-x^9+x^8-x^7+x^6-x^5+x^4-x^3+x^2-x+1,"a");
      O = maximal_order(K)

      primeideals = Vector{Hecke.AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
      for pnum in [ 2, 3, 5, 11 ]
        append!(primeideals, collect(keys(factor(O(pnum)*O))))
      end

      @testset "p = <$(p.gen_one), $(p.gen_two)>" for p in primeideals
        @test is_prime(p)
        G, mG = Hecke._multgrp_mod_p(p)
        @test length(mG.generators) == 1
        g = mG.generators[1]
        n = exponent(G)
        @test !iszero(g)
        @test !(g in p)
        @test verify_order(g, p, n)
        Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O, p)
        for exp in [ 50, n - 30 ]
          @test mG.discrete_logarithm((Q(g)^exp).elem)[1] == mod(ZZRingElem(exp), n)
        end
      end
    end
  end

  @testset "_1_plus_p_mod_1_plus_pv" begin
     Qx,  x = polynomial_ring(QQ, "x");

    @testset "Method: $method" for method in [:quadratic,:artin_hasse,:p_adic]

      @testset "K = Q" begin
         K,  a = number_field(x,"a");
        O = maximal_order(K)

        @testset "p = <$(pnum)>, v = $(v)" for pnum in [ x for x in 1:30 if is_prime(ZZRingElem(x))], v in [1,2,3,4,11,30]
          p = O(pnum)*O
          @test is_prime(p)
          pv = p^v
          #p = collect(keys(factor(i)))[1]
          G, mG = Hecke._1_plus_p_mod_1_plus_pv(p, v, pv, ZZRingElem(pnum)^v; method = method)
          @test is_snf(G)
          @test length(mG.generators) == ngens(G)
          # Test generators
          for i in 1:length(mG.generators)
            if G.snf[i] != 1
              @test parent(mG.generators[i]) == O
              @test mG.generators[i] - 1 in p
              @test verify_order(mG.generators[i], pv, G.snf[i])
            end
          end
          # Test structure/relations
          H = Hecke.multgrp_of_cyclic_grp(ZZRingElem(pnum)^v)
          I = Hecke._multgrp_mod_p(p)[1]
          @test order(G) == div(order(H), order(I))
          check, J = Hecke._1_plus_pa_mod_1_plus_pb_structure(p, 1, v)
          if check
            @test Hecke.is_isomorphic(G, J)
          end
          # Test discrete logarithm
          Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O, pv)
          for g in mG.generators
            for exp in -1:2
              el = Q(g)^exp
              @test Q(mG(mG\el.elem)) == el
            end
          end
        end
      end

      @testset "K = Q[√2]" begin
         K,  a = number_field(x^2 - 2,"a")
        O = maximal_order(K)

        primeideals = Vector{Hecke.AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
        for pnum in [2,3,5,7,19]
          fac = factor(ideal(O,O(pnum)))
          ks = collect(keys(fac))
          vs = collect(values(fac))
          all(isone,vs) && append!(primeideals,ks)
        end

        @testset "p = <$(p.gen_one), $(p.gen_two)>, v = $(v)" for p in primeideals, v in [1,4,11]
          pv = p^v
          G, mG = Hecke._1_plus_p_mod_1_plus_pv(p, v, pv, minimum(p, copy = false)^v; method = method)
          @test is_snf(G)
          @test length(mG.generators) == ngens(G)
          # Test generators
          for i in 1:length(mG.generators)
            if G.snf[i] != 1
              @test parent(mG.generators[i]) == O
              @test mG.generators[i] - 1 in p
              @test verify_order(mG.generators[i], pv, G.snf[i])
            end
          end
          # Test structure
          check, J = Hecke._1_plus_pa_mod_1_plus_pb_structure(p, 1, v)
          if check
            @test Hecke.is_isomorphic(G, J)
          end
          # Test discrete logarithm
          Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O, pv)
          for g in mG.generators
            for exp in [ -1, 1, 2 ]
              el = Q(g)^exp
              @test Q(mG(mG\el.elem)) == el
            end
          end
        end
      end

      @testset "K = Q[x]/<f = x^6+...>" begin
        f = x^6 + 6*x^5 - 12*x^4 - x^3 - 6*x^2 + 9*x + 20
         K,  a = number_field(f,"a")
        O = maximal_order(K)

        primeideals = Vector{Hecke.AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
        for pnum in [2,11,13]
          fac = factor(ideal(O,O(pnum)))
          ks = collect(keys(fac))
          vs = collect(values(fac))
          all(isone,vs) && append!(primeideals,ks)
        end

        @testset "p = <$(p.gen_one), $(p.gen_two)>, v = $(v)" for p in primeideals, v in [2,9]
          pv = p^v
          G, mG = Hecke._1_plus_p_mod_1_plus_pv(p, v, pv, minimum(p, copy = false)^v; method = method)
          @test is_snf(G)
          @test length(mG.generators) == ngens(G)
          # Test generators
          for i in 1:length(mG.generators)
            if G.snf[i] != 1
              @test parent(mG.generators[i]) == O
              @test mG.generators[i] - 1 in p
              @test verify_order(mG.generators[i], pv, G.snf[i])
            end
          end
          # Test structure
          check, J = Hecke._1_plus_pa_mod_1_plus_pb_structure(p, 1, v)
          if check
            @test Hecke.is_isomorphic(G, J)
          end
          # Test discrete logarithm
          Q = Hecke.AbsSimpleNumFieldOrderQuoRing(O, pv)
          for g in mG.generators
            for exp in [-1, 2]
              el = Q(g)^exp
              @test Q(mG(mG\el.elem)) == el
            end
          end
        end
      end
    end
  end

  @testset "Non-maximal orders" begin
    Qx, x = QQ["x"]

    K1, a1 = number_field(x^3 - 2, "a1")
    OK1 = maximal_order(K1)
    O1 = order(K1, [K1(1), 10*a1, 100*a1^2])
    F1 = conductor(O1, OK1)
    Q1, mQ1 = quo(O1, F1)
    G1, mG1 = multiplicative_group(Q1)
    @test G1.snf == [ ZZRingElem(2), ZZRingElem(10), ZZRingElem(20) ]
    for i = 1:10
      g = G1(map(ZZRingElem, rand(-100:100, ngens(G1))))
      h = G1(map(ZZRingElem, rand(-100:100, ngens(G1))))
      @test mG1(g)*mG1(h) == mG1(g + h)
    end

    K2, a2 = number_field(x^3 - 12*x^2 - 6324*x + 459510, "a2")
    O2 = equation_order(K2)
    OK2 = maximal_order(O2)
    F2 = conductor(O2, OK2)
    Q2, mQ2 = quo(O2, F2)
    G2, mG2 = multiplicative_group(Q2)
    @test G2.snf == [ ZZRingElem(2), ZZRingElem(4), ZZRingElem(4), ZZRingElem(4368) ]
    for i = 1:10
      g = G2(map(ZZRingElem, rand(-100:100, ngens(G2))))
      h = G2(map(ZZRingElem, rand(-100:100, ngens(G2))))
      @test mG2(g)*mG2(h) == mG2(g + h)
    end

    K3, a3 = number_field(x^5 - 1389*x^4 + 512066*x^3 - 11859166*x^2 + 83453925*x - 211865821, "a3")
    OK3 = maximal_order(K3)
    O3 = equation_order(K3)
    F3 = conductor(O3, OK3)
    Q3, mQ3 = quo(O3, F3)
    G3, mG3 = multiplicative_group(Q3)
    @test G3.snf == [ ZZRingElem(2), ZZRingElem(2), ZZRingElem(2), ZZRingElem(2), ZZRingElem(4), ZZRingElem(36100148955782880) ]
    for i = 1:10
      g = G3(map(ZZRingElem, rand(-100:100, ngens(G3))))
      h = G3(map(ZZRingElem, rand(-100:100, ngens(G3))))
      @test mG3(g)*mG3(h) == mG3(g + h)
    end
  end

  # zero-rings
  K, a = rationals_as_number_field()
  OK = maximal_order(K)
  I = ideal(OK, 1)
  Q, mQ = quo(OK, I)
  @test is_unit(zero(Q))
  @test divides(zero(Q), zero(Q))[1]
end
