@testset "ResidueRingMultGrp" begin

  function verify_order(g::Hecke.NfMaxOrdQuoRingElem,o)
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
    Qx, x = PolynomialRing(QQ, "x");

    @testset "K = Q" begin
      K, a = NumberField(x,"a");
      O = maximal_order(K)

      @testset "m0 = <$n>" for n in 1:50
        m0 = ideal(O,O(n))
        Q = NfMaxOrdQuoRing(O,m0)
        M = multiplicative_group(Q)
        G = domain(M)
        @test isa(G,Hecke.FinGenGrpAbSnf)
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
            @assert M(M\el) == el
          end
        end
      end

      @testset "m0 = <1361>^3000" begin
        m0 = ideal(O,O(1361))^100
        Q = NfMaxOrdQuoRing(O,m0)
        M = multiplicative_group(Q)
        G = domain(M)
        @test isa(G,Hecke.FinGenGrpAbSnf)
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
            @assert M(M\el) == el
          end
        end
      end

    end

    @testset "f = x^2-x+15" begin
      f = x^2-x+15
      K, a = NumberField(f,"a");
      O = maximal_order(K)

      @testset "m0 = <2>" begin
        m0 = ideal(O,O(2))
        Q = NfMaxOrdQuoRing(O,m0)
        M = multiplicative_group(Q)
        G = domain(M)
        @test isa(G,Hecke.FinGenGrpAbSnf)
        SNF = G.snf
        gens = M.generators
        @test length(SNF) == length(gens)
        for i in 1:length(gens)
          @test verify_order(gens[i],SNF[i])
        end
        @test order(G) == 3
        structt = [3]
        H = DiagonalGroup(structt)
        @test Hecke.isisomorphic(G,H)
        @test M(G(G.snf)) == Q(O(1))
        for g in gens
          for exp in -5:10
            el = g^exp
            @assert M(M\el) == el
          end
        end
      end

      @testset "m0 = <4>" begin
        m0 = ideal(O,O(4))
        Q = NfMaxOrdQuoRing(O,m0)
        M = multiplicative_group(Q)
        G = domain(M)
        @test isa(G,Hecke.FinGenGrpAbSnf)
        SNF = G.snf
        gens = M.generators
        @test length(SNF) == length(gens)
        for i in 1:length(gens)
          @test verify_order(gens[i],SNF[i])
        end
        @test order(G) == 12
        structt = [3,2,2]
        H = DiagonalGroup(structt)
        @test Hecke.isisomorphic(G,H)
        @test M(G(G.snf)) == Q(O(1))
        for g in gens
          for exp in -5:10
            el = g^exp
            @assert M(M\el) == el
          end
        end
      end

    end

    @testset "x^12+..." begin
      #= f = x^12+7*x^11-97*x^10-859*x^9+2558*x^8+38839*x^7+30012*x^6-710649*x^5-2189082*x^4+2534629*x^3+25314673*x^2+43623088*x+28168151 =#
      #= K, a = NumberField(f,"a"); =#
      #= O = maximal_order(K) =#

      #= @testset "m0 = <3>" begin =#
      #=   println("m0 = <3>") =#
      #=   m0 = ideal(O,O(3)) =#
      #=   Q = NfMaxOrdQuoRing(O,m0) =#
      #=   G = domain(Hecke.multiplicative_group(Q)) =#
      #=   println(snf(G)[1].snf) =#
      #=   @test order(G) == 512000 =#
      #=   structt = [80,80,80] =#
      #=   H = DiagonalGroup(structt) =#
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
      #=   Q = NfMaxOrdQuoRing(O,m0) =#
      #=   G = domain(Hecke.multiplicative_group(Q)) =#
      #=   println(snf(G)[1].snf) =#
      #=   @test order(G) == 14745600 =#
      #=   structt = [15,2,2,2,2,15,4,4,4,4,2,2,2,2] =#
      #=   H = DiagonalGroup(structt) =#
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
      #=   Q = NfMaxOrdQuoRing(O,m0) =#
      #=   G = domain(Hecke.multiplicative_group(Q)) =#
      #=   println(snf(G)[1].snf) =#
      #=   @test order(G) == 187500000 =#
      #=   structt = [24,5,5,5,5,5,5,4,5,5,5] =#
      #=   H = DiagonalGroup(structt) =#
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
      #=   Q = NfMaxOrdQuoRing(O,m0) =#
      #=   G = domain(Hecke.multiplicative_group(Q)) =#
      #=   println(snf(G)[1].snf) =#
      #=   @test order(G) == 14155776*fmpz(10)^14 =#
      #=   structt = [15,2,2,2,2,15,4,4,4,4,2,2,2,2,80,80,80,24,5,5,5,5,5,5,4,5,5,5] =#
      #=   H = DiagonalGroup(structt) =#
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

  @testset "_multgrp" begin
    Qx, x = PolynomialRing(QQ, "x");

    @testset "K = Q" begin
      K, a = NumberField(x,"a");
      O = maximal_order(K)

      @testset "m0 = <$n>" for n in 1:150
        m0 = ideal(O,O(n))
        Q = NfMaxOrdQuoRing(O,m0)
        gens, structure, disc_log = Hecke._multgrp(Q)
        @test length(gens) == length(structure)
        @test typeof(gens) == Vector{NfMaxOrdQuoRingElem}
        for i in 1:length(gens)
          @test verify_order(gens[i],structure[i])
        end
        G = DiagonalGroup(structure)
        H = Hecke.multgrp_of_cyclic_grp(n)
        @test Hecke.isisomorphic(G,H)
        #= # Test discrete logarithm =#
        for bas in gens
          for exp in [-1,0,1,6]
            el = bas^exp
            dlog = disc_log(el)
            prod = 1
            for j in 1:length(gens)
              prod *= gens[j]^dlog[j]
            end
            @test el == prod
          end
        end
      end
    end

    @testset "K = Q[√2]" begin
      K, a = NumberField(x^2 - 2,"a")
      O = maximal_order(K)

      @testset "m0 = <$n>" for n in 1:100
        m0 = ideal(O,O(n))
        Q = NfMaxOrdQuoRing(O,m0)
        gens, structure, disc_log = Hecke._multgrp(Q)
        @test length(gens) == length(structure)
        for i in 1:length(gens)
          @test verify_order(gens[i],structure[i])
        end
        #= # Test discrete logarithm =#
        for bas in gens
          for exp in [-1,0,1,8]
            el = bas^exp
            dlog = disc_log(el)
            prod = 1
            for j in 1:length(gens)
              prod *= gens[j]^dlog[j]
            end
            @test el == prod
          end
        end
      end
    end

    @testset "f = x^2-x+15" begin
      f = x^2-x+15
      K, a = NumberField(f,"a");
      O = maximal_order(K)

      @testset "m0 = <2>" begin
        m0 = ideal(O,O(2))
        Q = NfMaxOrdQuoRing(O,m0)
        gens, structure, disc_log = Hecke._multgrp(Q)
        @test length(gens) == length(structure)
        for i in 1:length(gens)
          @test verify_order(gens[i],structure[i])
        end
        G = DiagonalGroup(structure)
        @test order(G) == 3
        H = DiagonalGroup([3])
        @test Hecke.isisomorphic(G,H)
        #= # Test discrete logarithm =#
        for bas in gens
          for exp in [-11,4,12]
            el = bas^exp
            dlog = disc_log(el)
            prod = 1
            for j in 1:length(gens)
              prod *= gens[j]^dlog[j]
            end
            @test el == prod
          end
        end
      end

      @testset "m0 = <4>" begin
        m0 = ideal(O,O(4))
        Q = NfMaxOrdQuoRing(O,m0)
        gens, structure, disc_log = Hecke._multgrp(Q)
        @test length(gens) == length(structure)
        for i in 1:length(gens)
          @test verify_order(gens[i],structure[i])
        end
        G = DiagonalGroup(structure)
        @test order(G) == 12
        H = DiagonalGroup([3,2,2])
        @test Hecke.isisomorphic(G,H)
        #= # Test discrete logarithm =#
        for bas in gens
          for exp in [-8,0,2]
            el = bas^exp
            dlog = disc_log(el)
            prod = 1
            for j in 1:length(gens)
              prod *= gens[j]^dlog[j]
            end
            @test el == prod
          end
        end
      end

      @testset "m0 = <5>" begin
        m0 = ideal(O,O(5))
        Q = NfMaxOrdQuoRing(O,m0)
        gens, structure, disc_log = Hecke._multgrp(Q)
        @test length(gens) == length(structure)
        for i in 1:length(gens)
          @test verify_order(gens[i],structure[i])
        end
        G = DiagonalGroup(structure)
        @test order(G) == 16
        H = DiagonalGroup([4,4])
        @test Hecke.isisomorphic(G,H)
        #= # Test discrete logarithm =#
        for bas in gens
          for exp in [-3,2,4]
            el = bas^exp
            dlog = disc_log(el)
            prod = 1
            for j in 1:length(gens)
              prod *= gens[j]^dlog[j]
            end
            @test el == prod
          end
        end
      end

      @testset "m0 = <20>" begin
        m0 = ideal(O,O(20))
        Q = NfMaxOrdQuoRing(O,m0)
        gens, structure, disc_log = Hecke._multgrp(Q)
        @test length(gens) == length(structure)
        for i in 1:length(gens)
          @test verify_order(gens[i],structure[i])
        end
        G = DiagonalGroup(structure)
        @test order(G) == 192
        H = DiagonalGroup([3,2,2,4,4])
        @test Hecke.isisomorphic(G,H)
        #= # Test discrete logarithm =#
        for bas in gens
          for exp in [-4,1,7]
            el = bas^exp
            dlog = disc_log(el)
            prod = 1
            for j in 1:length(gens)
              prod *= gens[j]^dlog[j]
            end
            @test el == prod
          end
        end
      end

    end

  end

  @testset "_multgrp_mod_pv" begin
    Qx, x = PolynomialRing(QQ, "x");

    @testset "K = Q" begin
      K, a = NumberField(x,"a");
      O = maximal_order(K)

      @testset "i = <$pnum>^$v" for (pnum,v) in [(pnum,v) for pnum in [ x for x in 1:50 if isprime(fmpz(x))], v in [1,2,4,17]]
        p = ideal(O,O(pnum))
        g , d , disc_log = Hecke._multgrp_mod_pv(p,v)
        @test length(g) == length(d)
        for i in 1:length(g)
          @test verify_order(g[i],p^v,d[i])
        end
        G = DiagonalGroup(d)
        H = Hecke.multgrp_of_cyclic_grp(fmpz(pnum)^v)
        @test Hecke.isisomorphic(G,H)
        # Test discrete logarithm
        Q = NfMaxOrdQuoRing(O,p^v)
        for bas in g
          for exp in [-1,1,6]
            el = Q(bas)^exp
            dlog = disc_log(el.elem)
            prod = 1
            for j in 1:length(g)
              prod *= Q(g[j])^dlog[j]
            end
            @test el == prod
          end
        end
      end
    end

    @testset "f = x^2-x+15" begin
      f = x^2-x+15
      K, a = NumberField(f,"a");
      O = maximal_order(K)
      i = ideal(O,O(20))

      @testset "p = <$(p.gen_one),$(p.gen_two)>, v = $v" for (p,v) in factor(i)
        gens , structure , disc_log = Hecke._multgrp_mod_pv(p,v)
        @test length(gens) == length(structure)
        for i in 1:length(gens)
          @test verify_order(gens[i],p^v,structure[i])
        end
        # Test discrete logarithm
        Q = NfMaxOrdQuoRing(O,p^v)
        for bas in gens
          for exp in [-1,0,1,2]
            el = Q(bas)^exp
            dlog = disc_log(el.elem)
            prod = 1
            for j in 1:length(gens)
              prod *= Q(gens[j])^dlog[j]
            end
            @test el == prod
          end
        end
      end
    end

    @testset "f = x^3+8*x^2+6*x-17" begin
      f = x^3+8*x^2+6*x-17
      K, a = NumberField(f,"a");
      O = maximal_order(K)
      p = ideal(O,O(3))
      structures = Vector{fmpz}[[26],[26,3,3,3],[26,9,9,9],[26,27,27,27]]
      @testset "v = $v" for v in 1:length(structures)
        g , d , disc_log = Hecke._multgrp_mod_pv(p,v)
        @test length(g) == length(d)
        for i in 1:length(g)
          @test verify_order(g[i],p^v,d[i])
        end
        G = DiagonalGroup(d)
        @test order(G) == prod(structures[v])
        H = DiagonalGroup(structures[v])
        @test Hecke.isisomorphic(G,H)
        # Test discrete logarithm
        Q = NfMaxOrdQuoRing(O,p^v)
        for bas in g
          for exp in [-2,1,3]
            el = Q(bas)^exp
            dlog = disc_log(el.elem)
            prod = 1
            for j in 1:length(g)
              prod *= Q(g[j])^dlog[j]
            end
            @test el == prod
          end
        end
      end
    end

    @testset "f = x^4+11*x^3-19*x^2-8*x+7" begin
      f = x^4+11*x^3-19*x^2-8*x+7
      K, a = NumberField(f,"a");
      O = maximal_order(K)
      p = ideal(O,fmpz(3),O(2+a+a^2))
      structures = Vector{fmpz}[[8],[8,3,3],[8,3,3,3,3],[8,3,3,3,3,9],[8,3,3,9,9,9],[8,3,9,9,9,27]]
      @testset "v = $v" for v in 1:length(structures)
        g , d , disc_log = Hecke._multgrp_mod_pv(p,v)
        @test length(g) == length(d)
        for i in 1:length(g)
          @test verify_order(g[i],p^v,d[i])
        end
        G = DiagonalGroup(d)
        @test order(G) == prod(structures[v])
        H = DiagonalGroup(structures[v])
        @test Hecke.isisomorphic(G,H)
        # Test discrete logarithm
        Q = NfMaxOrdQuoRing(O,p^v)
        for bas in g
          for exp in [-4,1,6]
            el = Q(bas)^exp
            dlog = disc_log(el.elem)
            prod = 1
            for j in 1:length(g)
              prod *= Q(g[j])^dlog[j]
            end
            @test el == prod
          end
        end
      end
    end

    @testset "f = x^6+6x^5-12*x^4-x^3-6*x^2+9*x+20" begin
      f = x^6+6x^5-12*x^4-x^3-6*x^2+9*x+20
      K, a = NumberField(f,"a");
      O = maximal_order(K)
      p = ideal(O,fmpz(3),O(2+2*a+a^2))
      structures = Vector{fmpz}[[8],[8,3,3],[8,3,3,3,3],[8,9,9,3,3],[8,9,9,3,3,3,3],[8,9,9,9,9,3,3]]
      @testset "v = $v" for v in 1:length(structures)
        g , d , disc_log = Hecke._multgrp_mod_pv(p,v)
        @test length(g) == length(d)
        for i in 1:length(g)
          @test verify_order(g[i],p^v,d[i])
        end
        G = DiagonalGroup(d)
        @test order(G) == prod(structures[v])
        H = DiagonalGroup(structures[v])
        @test Hecke.isisomorphic(G,H)
        # Test discrete logarithm
        Q = NfMaxOrdQuoRing(O,p^v)
        for bas in g
          for exp in [-1,0,1,6]
            el = Q(bas)^exp
            dlog = disc_log(el.elem)
            prod = 1
            for j in 1:length(g)
              prod *= Q(g[j])^dlog[j]
            end
            @test el == prod
          end
        end
      end
    end
  end

  @testset "_multgrp_mod_p" begin
    Qx, x = PolynomialRing(QQ, "x");

    @testset "K = Q" begin
      K, a = NumberField(x,"a");
      O = maximal_order(K)

      @testset "p = <$(pnum)>" for pnum in [ x for x in 1:50 if isprime(fmpz(x))]
        p = ideal(O,O(pnum))
        g , n , dlog = Hecke._multgrp_mod_p(p)
        @test isa(g,NfOrdElem{NfMaxOrd})
        @test isa(n,fmpz)
        @test order(p) == O
        @test n == pnum-1
        @test verify_order(g,p,n)
        for exp in [0,1,2,n-2,n-1,n,3234239]
          @test dlog(g^exp) == mod(fmpz(exp),n)
        end
      end
    end

    @testset "K = Q[√2]" begin
      K, a = NumberField(x^2-2,"a");
      O = maximal_order(K)

      primeideals = Vector{Hecke.NfMaxOrdIdl}()
      for pnum in [ x for x in 1:40 if isprime(fmpz(x))]
        append!(primeideals,collect(keys(factor(ideal(O,O(pnum))))))
      end

      @testset "p = <$(p.gen_one), $(p.gen_two)>" for p in primeideals
        g , n , dlog = Hecke._multgrp_mod_p(p)
        @test isa(g,NfOrdElem{NfMaxOrd})
        @test order(p) == O
        @test isa(n,fmpz)
        @test !iszero(g)
        @test !(g in p)
        @test verify_order(g,p,n)
        Q = NfMaxOrdQuoRing(O,p)
        for exp in [0,1,2,n-2,n-1,n]
          @test dlog((Q(g)^exp).elem) == mod(fmpz(exp),n)
        end
      end
    end

    @testset "K = Q[x]/<x^6+6*x^5-12*x^4-x^3-6*x^2+9*x+20>" begin
      K, a = NumberField(x^6+6*x^5-12*x^4-x^3-6*x^2+9*x+20,"a");
      O = maximal_order(K)

      primeideals = Vector{Hecke.NfMaxOrdIdl}()
      for pnum in [ x for x in 1:20 if isprime(fmpz(x)) ]
        append!(primeideals,collect(keys(factor(ideal(O,O(pnum))))))
      end

      @testset "p = <$(p.gen_one), $(p.gen_two)>" for p in primeideals
        g , n , dlog = Hecke._multgrp_mod_p(p)
        @test isa(g,NfOrdElem{NfMaxOrd})
        @test order(p) == O
        @test isa(n,fmpz)
        @test !iszero(g)
        @test !(g in p)
        @test verify_order(g,p,n)
        Q = NfMaxOrdQuoRing(O,p)
        for exp in [24,n-345]
          @test dlog((Q(g)^exp).elem) == mod(fmpz(exp),n)
        end
      end
    end

    @testset "K = Q[x]/<x^10-x^9+x^8-x^7+x^6-x^5+x^4-x^3+x^2-x+1>" begin
      K, a = NumberField(x^10-x^9+x^8-x^7+x^6-x^5+x^4-x^3+x^2-x+1,"a");
      O = maximal_order(K)

      primeideals = Vector{Hecke.NfMaxOrdIdl}()
      for pnum in [2,3,5,11]
        append!(primeideals,collect(keys(factor(ideal(O,O(pnum))))))
      end

      @testset "p = <$(p.gen_one), $(p.gen_two)>" for p in primeideals
        g , n , dlog = Hecke._multgrp_mod_p(p)
        @test isa(g,NfOrdElem{NfMaxOrd})
        @test isa(n,fmpz)
        @test order(p) == O
        @test !iszero(g)
        @test !(g in p)
        @test verify_order(g,p,n)
        Q = NfMaxOrdQuoRing(O,p)
        for exp in [50,n-30]
          @test dlog((Q(g)^exp).elem) == mod(fmpz(exp),n)
        end
      end
    end
  end

  @testset "_1_plus_p_mod_1_plus_pv" begin
    Qx, x = PolynomialRing(QQ, "x");

    @testset "Method: $method" for method in [:quadratic,:artin_hasse,:p_adic]

      @testset "K = Q" begin
        K, a = NumberField(x,"a");
        O = maximal_order(K)

        @testset "p = <$(pnum)>, v = $(v)" for pnum in [ x for x in 1:30 if isprime(fmpz(x))], v in [1,2,3,4,11,30]
          i = ideal(O,O(pnum))
          p = collect(keys(factor(i)))[1]
          g, D , disc_log = Hecke._1_plus_p_mod_1_plus_pv(p,v;method=method)
          @test length(g) == length(D)
          # Test generators
          for i in 1:length(g)
            if(D[i] != 1)
              @test isa(g[i],NfOrdElem{NfMaxOrd})
              @test parent(g[i]) == O
              @test g[i]-1 in p
              @test verify_order(g[i],p^v,D[i])
            end
          end
          # Test structure/relations
          G = DiagonalGroup(D)
          H = Hecke.multgrp_of_cyclic_grp(fmpz(pnum)^v)
          I = DiagonalGroup([Hecke._multgrp_mod_p(p)[2]])
          @test order(G) == div(order(H), order(I))
          check, J = Hecke._1_plus_pa_mod_1_plus_pb_structure(p,1,v)
          if check
            @test Hecke.isisomorphic(G,J)
          end
          # Test discrete logarithm
          Q = NfMaxOrdQuoRing(O,p^v)
          for bas in g
            for exp in -1:2
              el = Q(bas)^exp
              dlog = disc_log(el.elem)
              prod = 1
              for j in 1:length(g)
                prod *= Q(g[j])^dlog[j]
              end
              @test el == prod
            end
          end
        end
      end

      @testset "K = Q[√2]" begin
        K, a = NumberField(x^2 - 2,"a")
        O = maximal_order(K)

        primeideals = Vector{Hecke.NfMaxOrdIdl}()
        for pnum in [2,3,5,7,19]
          fac = factor(ideal(O,O(pnum)))
          ks = collect(keys(fac))
          vs = collect(values(fac))
          all(isone,vs) && append!(primeideals,ks)
        end

        @testset "p = <$(p.gen_one), $(p.gen_two)>, v = $(v)" for p in primeideals, v in [1,4,11]
          g, D, disc_log = Hecke._1_plus_p_mod_1_plus_pv(p,v;method=method)
          @test length(g) == length(D)
          # Test generators
          for i in 1:length(g)
            if(D[i] != 1)
              @test isa(g[i],NfOrdElem{NfMaxOrd})
              @test parent(g[i]) == O
              @test g[i]-1 in p
              @test verify_order(g[i],p^v,D[i])
            end
          end
          # Test structure
          check, J = Hecke._1_plus_pa_mod_1_plus_pb_structure(p,1,v)
          if check
            G = DiagonalGroup(D)
            @test Hecke.isisomorphic(G,J)
          end
          # Test discrete logarithm
          Q = NfMaxOrdQuoRing(O,p^v)
          for bas in g
            for exp in [-1,1,2]
              el = Q(bas)^exp
              dlog = disc_log(el.elem)
              prod = 1
              for j in 1:length(g)
                prod *= Q(g[j])^dlog[j]
              end
              @test el == prod
            end
          end
        end
      end

      @testset "K = Q[x]/<f = x^6+...>" begin
        f = x^6 + 6*x^5 - 12*x^4 - x^3 - 6*x^2 + 9*x + 20
        K, a = NumberField(f,"a")
        O = maximal_order(K)

        primeideals = Vector{Hecke.NfMaxOrdIdl}()
        for pnum in [2,11,13]
          fac = factor(ideal(O,O(pnum)))
          ks = collect(keys(fac))
          vs = collect(values(fac))
          all(isone,vs) && append!(primeideals,ks)
        end

        @testset "p = <$(p.gen_one), $(p.gen_two)>, v = $(v)" for p in primeideals, v in [2,9]
          g, D, disc_log = Hecke._1_plus_p_mod_1_plus_pv(p,v;method=method)
          @test length(g) == length(D)
          # Test generators
          for i in 1:length(g)
            if(D[i] != 1)
              @test isa(g[i],NfOrdElem{NfMaxOrd})
              @test parent(g[i]) == O
              @test g[i]-1 in p
              @test verify_order(g[i],p^v,D[i])
            end
          end
          # Test structure
          check, J = Hecke._1_plus_pa_mod_1_plus_pb_structure(p,1,v)
          if check
            G = DiagonalGroup(D)
            @test Hecke.isisomorphic(G,J)
          end
          # Test discrete logarithm
          Q = NfMaxOrdQuoRing(O,p^v)
          for bas in g
            for exp in [-1,2]
              el = Q(bas)^exp
              dlog = disc_log(el.elem)
              prod = 1
              for j in 1:length(g)
                prod *= Q(g[j])^dlog[j]
              end
              @test el == prod
            end
          end
        end
      end
    end
  end

end
