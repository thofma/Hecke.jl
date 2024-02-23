using Hecke

function ideals_with_pp_norm(lp::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}, k::Int)
  l = [degree(x) for x= lp]
#  println("pp with $l and $k")
  #need sum([e[i]*l[i] == k, e[i] >= 0])
  C = cartesian_product_iterator([0:div(k, l[j]) for j = 1:length(l)], inplace = true)
  r = [prod(lp[i]^c[i] for i=1:length(l)) for c = C if sum(c[i]*l[i] for i=1:length(l)) == k]
#  println("r: $r")
  return r
end

function ideals_with_norm(i::ZZRingElem, M::AbsSimpleNumFieldOrder)
  @assert M.is_maximal == 1
  if isone(i)
    return [ideal(M, 1)]
  end
  lf = factor(i)
  lp = [ideals_with_pp_norm([x[1] for x = prime_decomposition(M, k)], v) for (k, v) = lf.fac]
#  println(lp)
  return [prod(lp[i][x[i]] for i=1:length(lf.fac)) for x = cartesian_product_iterator([1:length(lp[i]) for i=1:length(lp)], inplace = true)]
end

function orbit_reps(I::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}, s::Hecke.NumFieldHom{AbsSimpleNumField, AbsSimpleNumField})
  O = Set([I[1], Hecke.induce_image(I[1], s)])
  R = [I[1]]
  for i=I
    if i in O
      continue
    end
    push!(R, i)
    push!(O, i)
    push!(O, Hecke.induce_image(i, s))
  end
  return R
end

#Note: this is not optimised, but hopefully correct.
#if you need more, analyse Hasse...

function induce_action(phi::Hecke.NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}, mR::T) where T <: Map{FinGenAbGroup,
Hecke.FacElemMon{Hecke.AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}}
#function induce_action(phi::Hecke.NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}, mR::Hecke.MapRayClassGrpFacElem{Hecke.FinGenAbGroup})
  lp, x = Hecke.find_gens(
        Hecke.MapFromFunc(base_ring(codomain(mR)),
                          domain(mR),
                          x->preimage(mR, FacElem(Dict(x=>1)))),
        PrimesSet(100, -1))
  return hom(x, FinGenAbGroupElem[preimage(mR, Hecke.induce_image(p, phi)) for p = lp])
end

function s3_with_discriminant(I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  lI = factor(I)
  kx = polynomial_ring(order(I).nf)[1]
  #we need deccompositions I = df^2
  #and f is squarefree - exccept at 3
  #there can only be wild ramification at primes dividing the degree
  #similarly: d is squarefree outside 2...
  all_poss = Vector{Tuple{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}}()
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
      if norm(f) % 3 != 1
        println("no 3 in the prime, cannot work")
        return []
      end
      f *= i
    elseif e==3
      if norm(f) % 3 != 1
        println("no 3 in the prime, cannot work")
        return []
      end
      f *= i
      d *= i
    else
      println("expo too large at wrong prime, no S3-disc")
      return []
    end
  end

  res = []
  println("23: $l23")
  C = cartesian_product_iterator([1:length(i) for i in l23], inplace = true)
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
    r, mr = ray_class_group(D, n_quo = 2)

    for s in index_p_subgroups(r, ZZRingElem(2), (A,x) -> quo(A, x)[2])
      a = ray_class_field(mr*pseudo_inv(s))
#      println(a, " with cond ", conductor(a))
      if conductor(a)[1] != D
        continue
      end
      K = number_field(a)
      println("have K: $K")
      @assert length(gens(K)) == 1
      Kr = K
      @assert degree(Kr) == 2
#      @assert Hecke.is_radical_extension(Kr)
      conj = Hecke.rel_auto(a.cyc[1])
      Kr = a.cyc[1].A
      k = base_ring(Kr)
      Ka, m1 = absolute_simple_field(Kr)
      m2 = restrict(inv(m1), k)
      sigma = hom(Ka, Ka, m1\(conj(m1(gen(Ka)))))
      #m1: Kr -> Ka, m2: base_ring(Kr) -> Ka
      M = lll(maximal_order(Ka))
      FF = ideal(M, F.gen_one, M(m2(k(F.gen_two))))
      R, mR = ray_class_group(FF, n_quo = 3)
      if order(R) == 1
        println("RCG empty")
        continue
      end

      sigma_R = induce_action(sigma, mR)
#      println(sigma_R)

      for S = Hecke.stable_subgroups(R, [3], [sigma_R], op=quo)
        @assert order(S[1]) == 3
        s, ms = snf(S[1])
        if ms\(S[2](sigma_R(S[2]\(ms(s[1]))))) == s[1]
          #TODO: factor out the part with trivial action
          # ie. kern(sigma_R-I)
          println("action is trivial, no S3")
          continue
        end
        A = ray_class_field(mR*pseudo_inv(S[2]))
#        println(A, " with cond ", conductor(A))
        if conductor(A)[1] != FF
          println("wrong conductor")
          continue
        end
        B = number_field(A)
        Tau = Hecke.extend_aut(A, sigma)
        g = gens(B)[1]
        g += Tau(g)
        if iszero(g)
          g = gens(B)[1]
          g *= Tau(g)
        end
        mg = minpoly(g)
        @assert degree(mg) == 3
        mg = kx([coeff(m1\coeff(mg, i), 0) for i=0:4])
        push!(res, mg)
      end
    end
  end
  return res
end


function Gunter_Qi(r::Range, pref="Qi.new")
  Qt, t = FlintQQ["t"]
  k, a = number_field(t^2+1, "k.1")
  s = Hecke.NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}(k, k, -a)
  M = maximal_order(k)
  kx, x = k["kx.1"]
  f = open("/tmp/$pref", "a")
  g = open("/tmp/$pref.err", "a")
  err_cnt = 0

  for i = r
    try
      I = ideals_with_norm(ZZRingElem(i), M)
      if length(I)==0
        continue
      end
      I = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[I[x] for x = linearindices(I)]
      R = orbit_reps(I, s)
      for r in R
        z = s3_with_discriminant(r)
        if length(z)==0
          continue
        end
        for j=z
          println(f, "<$i, $(kx([coeff(j, jj) for jj=0:3]))>, ")
        end
      end
    catch e
      rethrow(e)
      err_cnt += 1
      println("i: $i")
      println(e)
      println(g, "i: $i")
      println(g, e)
      if err_cnt > 10
        rethrow(e)
      end
    end
  end
  close(f)
end



