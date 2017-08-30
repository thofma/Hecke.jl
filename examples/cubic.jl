using Hecke


#Note: this is not optimised, but hopefully correct.
#if you need more, analyse Hasse...

function induce_action(phi::Hecke.NfToNfMor, mR::T) where T <: Map{GrpAbFinGen, 
Hecke.FacElemMon{Hecke.NfOrdIdlSet}}
#function induce_action(phi::Hecke.NfToNfMor, mR::Hecke.MapRayClassGrpFacElem{Hecke.GrpAbFinGen})
  lp, x = Hecke.find_gens(
        Hecke.MapFromFunc(x->preimage(mR, FacElem(Dict(x=>1))),
                          base_ring(codomain(mR)),
                          domain(mR)),
        PrimesSet(100, -1))
  return hom(x, GrpAbFinGenElem[preimage(mR, Hecke.induce_image(p, phi)) for p = lp])
end

function s3_with_discriminant(I::NfOrdIdl)
  lI = factor(I)
  #we need deccompositions I = df^2
  #and f is squarefree - exccept at 3
  #there can only be wild ramification at primes dividing the degree
  #similarly: d is squarefree outside 2...
  all_poss = Array{Tuple{NfOrdIdl, NfOrdIdl}, 1}()
  l23 = []
  f = ideal(order(I), 1)
  d = ideal(order(I), 1)
  for (i, e) = lI
    if minimum(i) == 2
      l = [(i^e, ideal(order(i), 1))]
      if e>=2
        push!(l, (i^(e-2), i))
      end
      push!(l23, l)
      continue
    end
    if minimum(i) == 3
      if iseven(e)
        f *= i^div(e, 2)
      end
      if isodd(e)
        d *= i
        f *= i^div(e-1, 2)
      end
      continue
    end

    if e==1
      d *= i
    elseif e==2
      f *= i
    elseif e==3
      f *= i
      d *= i
    else
      println("expo too large at wrong prime, no S3-disc")
      return []
    end
  end

  res = []
  println("23: $l23")
  C = CartesianRange(Tuple(length(i) for i=l23))
  #Tommy: use Base.product(l23,...) or similar....
  for c = C
    if length(c) == 0
      D = d
      F = f
    else
      D = d*prod(l23[i][c[i]][1] for i=1:length(c))
      F = f*prod(l23[i][c[i]][2] for i=1:length(c))
    end
    println("need to try $D and $F as conductors")
    #all quadratics with conductor D:
    r, mr = ray_class_group_p_part(2, D)
    println(r)
    for s in index_p_subgroups(r, fmpz(2), (A,x) -> quo(A, x)[2])
      a = ray_class_field(mr*inv(s))
#      println(a, " with cond ", conductor(a))
      if conductor(a)[1] != D
        continue
      end
      K = number_field(a)
#      println("have K: $K")
      @assert length(K) == 1
      Kr = number_field(K[1])[1]
      @assert degree(Kr) == 2
      @assert Hecke.ispure_extension(Kr)
      conj = Hecke.NfRelToNfRelMor(Kr, Kr, -gen(Kr))
      k = base_ring(Kr)
      Ka, m1, m2 = absolute_field(Kr)
      sigma = Hecke.NfToNfMor(Ka, Ka, m1(conj(preimage(m1, gen(Ka))))) 
      #m1: Kr -> Ka, m2: base_ring(Kr) -> Ka
      println("Field: ", Ka)
      M = lll(maximal_order(Ka))
      FF = ideal(M, F.gen_one, M(m2(k(F.gen_two))))
      R, mR = ray_class_group_p_part(3, FF)
      R, mq = quo(R, 3)
      mR = mR*inv(mq) 
      if order(R) == 1
        println("RCG empty")
        continue
      end

      sigma_R = induce_action(sigma, mR)
#      println(sigma_R)
      
#      for S = Hecke.stable_index_p_subgroups(mR, 1, [Hecke.MapFromFunc(x->x, R, R), sigma_R])
      for S = Hecke.stable_index_p_subgroups(R, 1, [sigma_R], quo)
        @assert order(S[1]) == 3
        s, ms = snf(S[1])
        if ms(S[2](sigma_R(S[2](ms\s[1])))) == s[1]
          #TODO: factor out the part with trivial action
          # ie. kern(sigma_R-I)
          println("action is trivial, no S3")
          continue
        end
        A = ray_class_field(mR*inv(S[2]))
#        println(A, " with cond ", conductor(A))
        if conductor(A)[1] != FF
          println("wrong conductor")
          continue
        end
        B = number_field(number_field(A)[1])[1]
        BB = number_field(Kr["t"][1]([m1\coeff(B.pol, i) for i=0:degree(B)]))[1]
        Ba = absolute_field(BB)[1]
        r = roots(Ba.pol, Ba)
        @assert degree(Ba) == 6
        @assert length(r) == 6
        for rr = r
          if rr == gen(Ba)
            continue
          end
          h = Hecke.NfRelToNfRelMor(Ba, Ba, rr)
          if h(h(gen(Ba))) == gen(Ba)
            #found auto or order 2!
            g = gen(Ba) + h(gen(Ba))
            mg = minpoly(g)
            i = 0
            while degree(mg) < 3
              g = (gen(Ba)+i)*(h(gen(Ba))+i)
              mg = minpoly(g)
              i+=1
            end
            @assert degree(mg) == 3
            push!(res, mg)
            break;
          end
        end
      end
    end
  end
  return res
end



