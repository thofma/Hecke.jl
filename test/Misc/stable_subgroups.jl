@testset "ZpnGModules" begin

  @testset "Minimal Submodules" begin

    F, a = finite_field(3,1,"a")
    R = residue_ring(ZZ,9)[1]

    V=abelian_group([3,3,9,9])

    l=[1,1,3,0,2,1,3,3,1,1,1,1,0,0,0,1]
    l1=[1,1,1,0,2,1,1,1,0,0,1,1,0,0,0,1]
    A=matrix_space(R,4,4)(l)
    A1=matrix_space(F,4,4)(l1)

    M = ZpnGModule(V,[A])
    M1 = Hecke.Amodule([A1])

    ls = minimal_submodules(M)
    ls1 = minimal_submodules(M1)

    @test length(ls) == length(ls1)
    for y in ls
      @test Hecke.is_submodule(M,y)
    end

    ls = maximal_submodules(M)
    ls1 = minimal_submodules(M1)

    @test length(ls) == length(ls1)
    for y in ls
      @test Hecke.is_submodule(M,y)
    end
  end


  @testset "Dual Module" begin

    R=residue_ring(ZZ,9)[1]
    V=abelian_group([3,3,9,9])
    V.is_snf=true
    V.snf=[3,3,9,9]
    l=[1,1,3,0,2,1,3,3,1,1,1,1,0,0,0,1]
    A=matrix_space(R,4,4)(l)
    M=ZpnGModule(V,[A])
    N= Hecke.dual_module(M)
    ls=submodules(N)
    v=ZZRingElem[3,3,1,1]
    for y in ls
      @test Hecke.is_submodule(M,Hecke._dualize(y,V,v))
    end
    @test length(ls) == 16
    @test issetequal(howell_form.(ls), map(x -> matrix(R, 4, 4, x),
      [[0 0 0 0; 0 0 0 0; 0 0 0 0; 0 0 0 0],
       [0 0 3 0; 0 0 0 0; 0 0 0 0; 0 0 0 0],
       [1 0 3 0; 0 1 6 0; 0 0 0 0; 0 0 0 0],
       [1 0 0 0; 0 1 0 0; 0 0 3 0; 0 0 0 0],
       [1 2 1 0; 0 0 3 0; 0 0 0 0; 0 0 0 0],
       [1 2 1 3; 0 0 3 0; 0 0 0 0; 0 0 0 0],
       [1 2 1 6; 0 0 3 0; 0 0 0 0; 0 0 0 0],
       [0 0 3 0; 0 0 0 3; 0 0 0 0; 0 0 0 0],
       [1 0 0 0; 0 1 0 0; 0 0 1 0; 0 0 0 0],
       [1 0 0 0; 0 1 0 0; 0 0 1 3; 0 0 0 0],
       [1 0 0 0; 0 1 0 0; 0 0 1 6; 0 0 0 0],
       [1 0 0 0; 0 1 0 0; 0 0 3 0; 0 0 0 3],
       [1 2 1 0; 0 0 3 0; 0 0 0 3; 0 0 0 0],
       [1 0 0 0; 0 1 0 0; 0 0 1 0; 0 0 0 3],
       [1 2 0 2; 0 0 1 1; 0 0 0 3; 0 0 0 0],
       [1 0 0 0; 0 1 0 0; 0 0 1 0; 0 0 0 1]]
     ))
  end


  @testset "submodules with given structure" begin

    R=residue_ring(ZZ,8)[1]
    V=abelian_group([2,4,8,8])
    V.is_snf=true
    V.snf=[2,4,8,8]
    l=[1,2,4,0,1,1,0,2,1,1,1,1,0,2,0,1]
    l1=[1,0,0,0,0,3,4,2,1,0,0,1,0,0,1,0]
    l2=[1,0,0,4,1,1,0,0,0,2,1,0,1,1,1,1]
    A=matrix_space(R,4,4)(l)
    B=matrix_space(R,4,4)(l1)
    C=matrix_space(R,4,4)(l2)
    M=ZpnGModule(V,[A,B,C])
    ls=submodules(M,typesub=[2,3])
    y=subgroups(V,quotype=[4,8])

    mp1=Hecke.FinGenAbGroupHom(V,V,lift(A))
    mp2=Hecke.FinGenAbGroupHom(V,V,lift(B))
    mp3=Hecke.FinGenAbGroupHom(V,V,lift(C))
    act=[mp1,mp2,mp3]

    i=0
    for el in y
      if Hecke.is_stable(act,el[2])
        i+=1
      end
    end
    @test i==length(ls)

    ls=submodules(M,typesub=[3])
    y=subgroups(V,quotype=[8])
    i=0
    for el in y
      if Hecke.is_stable(act,el[2])
        i+=1
      end
    end
    @test i==length(ls)

  end

  @testset "submodules" begin

    R=residue_ring(ZZ,4)[1]
    V=abelian_group([2,2,4])
    V.is_snf=true
    V.snf=[2,2,4]
    A=matrix_space(R,3,3)(1)
    M=ZpnGModule(V,[A])
    ls=submodules(M)
    lsub=subgroups(V)
    @test length(collect(ls))==length(collect(lsub))

  end

  let # cornercase
    A = abelian_group()
    g = id_hom(A)
    l = stable_subgroups(A,[g])
    ll = collect(l)
    @test length(ll) == 1
  end

  let # cornercase
    A = abelian_group([4,4])
    endo = hom(A,A,[2*i for i in gens(A)])
    s = stable_subgroups(A,[endo])
    @test length(s) == 15
  end

  @testset "Given subtype" begin
    for invariants in ([2, 2, 2], [4, 4], [2, 4, 12], [3, 2, 4])
      A = abelian_group(invariants)
      acts = [id_hom(A), hom(A, A, [zero(A); gens(A)[2:end]])]
      for t in (Int[], [1], [2], [2, 2], [4], [3, 2], invariants, [8], [5], [2, 2, 2, 2])
        expected = [(S, m) for (S, m) in subgroups(A, subtype = t) if Hecke.is_stable(acts, m)]
        actual = collect(stable_subgroups(A, acts, subtype = t))
        @test length(actual) == length(expected)
        @test all(is_isomorphic(S, abelian_group(t)) for (S, _) in actual)
        @test all(Hecke.is_stable(acts, m) for (_, m) in actual)
        @test Set(Set(m.(collect(S))) for (S, m) in actual) ==
              Set(Set(m.(collect(S))) for (S, m) in expected)
      end
    end

    A = abelian_group([4, 4])
    act = [id_hom(A)]
    t = [4, 2]
    collect(stable_subgroups(A, act, subtype = t))
    @test t == [4, 2]
    @test length(collect(stable_subgroups(A, act, subtype = [4], op = quo))) == 6
    B = abelian_group()
    @test length(collect(stable_subgroups(B, [id_hom(B)], subtype = Int[]))) == 1
    @test_throws ArgumentError stable_subgroups(A, act, subtype = [2], quotype = [2])
    @test_throws ArgumentError stable_subgroups(A, act, subtype = [2], order = 2)
    @test_throws ArgumentError stable_subgroups(A, act, subtype = [2], minimal = true)
    @test_throws ArgumentError stable_subgroups(A, act, subtype = [0])
    @test_throws ArgumentError stable_subgroups(A, act, subtype = [-2])
  end

  @testset "Quotient with trivial primary part" begin
    for invariants in ([4, 3], [4, 4, 3])
      A = abelian_group(invariants)
      quotients = collect(stable_subgroups(A, [id_hom(A)]; quotype = [3], op = quo))
      @test length(quotients) == 1
      @test order(only(quotients)[1]) == 3
    end
  end

  @testset "Given order" begin
    for invariants in ([2, 2, 2], [4, 4], [2, 4, 12], [3, 2, 4])
      A = abelian_group(invariants)
      act = [hom(A, A, [zero(A); gens(A)[2:end]])]
      for n in divisors(order(A))
        expected = [(S, m) for (S, m) in subgroups(A, order = n) if Hecke.is_stable(act, m)]
        actual = collect(stable_subgroups(A, act, order = n))
        @test length(actual) == length(expected)
        @test all(order(S) == n for (S, _) in actual)
        @test Set(Set(m.(collect(S))) for (S, m) in actual) ==
              Set(Set(m.(collect(S))) for (S, m) in expected)
      end
    end

    B = abelian_group()
    @test length(collect(stable_subgroups(B, [id_hom(B)], order = 1))) == 1
    B = abelian_group(fill(2, 70))
    s = collect(stable_subgroups(B, [id_hom(B)], order = 1))
    @test length(s) == 1
    @test order(first(s)[1]) == 1

    A = abelian_group([4, 4])
    g = id_hom(A)

    s = collect(stable_subgroups(A, [g], order = 4))
    @test length(s) == length(collect(subgroups(A, order = 4)))
    @test all(order(S) == 4 for (S, _) in s)

    s = collect(stable_subgroups(A, [g], order = 1))
    @test length(s) == 1
    @test order(first(s)[1]) == 1

    s = collect(stable_subgroups(A, [g], order = ZZ(4)))
    @test length(s) == length(collect(subgroups(A, order = 4)))

    s = collect(stable_subgroups(A, [g], order = 16))
    @test length(s) == 1
    @test order(first(s)[1]) == 16

    @test isempty(stable_subgroups(A, [g], order = 3))
    @test length(collect(stable_subgroups(A, [g], order = 4, op = quo))) == 7
    @test_throws ArgumentError stable_subgroups(A, [g], order = 0)
    @test_throws ArgumentError stable_subgroups(A, [g], order = 4, minimal = true)
    @test_throws ArgumentError stable_subgroups(A, [g], quotype = [4], order = 4)
  end

  @testset "Quotient type with primes not dividing the order" begin
    A = abelian_group([4, 4])
    g = hom(A, A, [3*a for a in gens(A)])
    @test isempty(collect(stable_subgroups(A, [g], quotype = [12])))
  end

  @testset "Empty action list with filters" begin
    for d in (2, 4)
      A = abelian_group([d, d])
      act = FinGenAbGroupHom[]
      f = hom(abelian_group([d]), A, [A[1]])
      for (gram, avoid) in ((zero_matrix(ZZ, 2, 2), FinGenAbGroupHom[]),
                            (identity_matrix(ZZ, 2), FinGenAbGroupHom[]),
                            (nothing, [f]), (identity_matrix(ZZ, 2), [f]))
        is_iso(m) = gram === nothing || all(is_divisible_by((x.coeff*gram*transpose(y.coeff))[1, 1], d) for x in m.(gens(domain(m))) for y in m.(gens(domain(m))))
        contains_image(m, h) = all(a -> has_preimage_with_preimage(m, h(a))[1], gens(domain(h)))
        expected = [(S, m) for (S, m) in subgroups(A) if is_iso(m) && !any(h -> contains_image(m, h), avoid)]
        actual = collect(stable_subgroups(A, act; gram = gram, avoid = avoid))
        @test length(actual) == length(expected)
        @test Set(Set(m.(collect(S))) for (S, m) in actual) ==
              Set(Set(m.(collect(S))) for (S, m) in expected)
      end
      @test isempty(act)
    end
  end

  @testset "Trivial quotient type with filters" begin
    for d in (2, 4)
      A = abelian_group([d, d])
      gram = zero_matrix(ZZ, 2, 2)
      for act in (FinGenAbGroupHom[], [id_hom(A)], [hom(A, A, [zero(A), A[2]])]),
          quotype in (Int[], [1])
        actual = collect(stable_subgroups(A, act; quotype = quotype, gram = gram))
        @test order(only(actual)[1]) == order(A)
        actual = collect(stable_subgroups(A, act; quotype = quotype, gram = gram, op = quo))
        @test isone(order(only(actual)[1]))
        @test isempty(collect(stable_subgroups(A, act; quotype = quotype, gram = identity_matrix(ZZ, 2))))
        @test isempty(collect(stable_subgroups(A, act; quotype = quotype, avoid = [id_hom(A)])))
      end
    end
  end

  @testset "Isotropic subgroups avoiding subgroups" begin
    # discriminant groups with the bilinear form scaled to integer values
    for (L, f) in ((rescale(root_lattice(:A, 3), 2), 2), (rescale(root_lattice(:D, 4), 4), -1),
                   (direct_sum(rescale(root_lattice(:A, 2), 3), rescale(root_lattice(:A, 1), 4))[1], 5))
      T = discriminant_group(L)
      A = abelian_group(T)
      e = exponent(A)
      gram = map_entries(ZZ, gram_matrix_bilinear(T)*e)
      is_iso(m) = all(is_divisible_by((x.coeff*gram*transpose(y.coeff))[1, 1], e) for x in m.(gens(domain(m))) for y in m.(gens(domain(m))))
      contains_image(m, h) = all(a -> has_preimage_with_preimage(m, h(a))[1], gens(domain(h)))
      a = A[1]
      b = A[ngens(A)]
      # cyclic subgroups to avoid of prime power order and of mixed order
      avoids = [FinGenAbGroupHom[], [hom(abelian_group([order(a)]), A, [a])], [hom(abelian_group([order(a + b)]), A, [a + b])]]
      for act in ([id_hom(A)], [hom(A, A, [f*x for x in gens(A)])]), avoid in avoids
        for kw in ((;), (; minimal = true), (; order = 4), (; order = 3), (; subtype = [2]), (; quotype = [2]))
          expected = [(S, m) for (S, m) in stable_subgroups(A, act; kw...) if is_iso(m) && !any(h -> contains_image(m, h), avoid)]
          actual = collect(stable_subgroups(A, act; kw..., gram = gram, avoid = avoid))
          @test length(actual) == length(expected)
          @test Set(Set(m.(collect(S))) for (S, m) in actual) ==
                Set(Set(m.(collect(S))) for (S, m) in expected)
        end
      end
    end

    A = abelian_group([2, 4])
    @test_throws ArgumentError stable_subgroups(A, [id_hom(A)], gram = ZZ[1 0; 0 1])
    @test_throws ArgumentError stable_subgroups(A, [id_hom(A)], gram = ZZ[0 2; 0 0])
    @test_throws ArgumentError stable_subgroups(A, [id_hom(A)], avoid = [id_hom(abelian_group([2, 4]))])
    @test isempty(collect(stable_subgroups(A, [id_hom(A)], avoid = [hom(abelian_group([1]), A, [zero(A)])])))
  end
end
