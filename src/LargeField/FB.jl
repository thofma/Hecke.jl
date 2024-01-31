#Aim: have map operate on FB

#Probably to be moved to AbstractAlgebra
function orbits(v::Vector{Perm{Int}})
  orbs = Vector{Vector{Int}}()
  n = length(v[1].d)
  found = falses(n)
  for i = 1:n
    if found[i]
      continue
    end
    found[i] = true
    orbit = Vector{Int}()
    push!(orbit, i)
    ind = 1
    while ind <= length(orbit)
      for j in v
        new = j[orbit[ind]]
        if !found[new]
          found[new] = true
          push!(orbit, new)
        end
      end
      ind += 1
    end
    push!(orbs, orbit)
  end
  return orbs
end

@doc raw"""
    induce_action(primes::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}, A::Map) -> Perm{Int}

Given a set of prime ideals invariant under the action of $A$, this function
returns the corresponding permutation induced by $A$.
"""
function induce_action(primes::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}, A::Map)
  K = domain(A)
  f = A(gen(K)) # essentially a polynomial in the primitive element

  O = order(primes[1])
  prm = Vector{Tuple{Int, Int}}()

  G = SymmetricGroup(length(primes))
  if f == gen(K)
    return one(G)
  end

  primes_underneath = Set{ZZRingElem}([minimum(x, copy = false) for x in primes])
  for p in primes_underneath
    indices = [i for i in 1:length(primes) if minimum(primes[i], copy = false) == p]
    lp = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[primes[i] for i in indices]
    prm_p = _induce_action_p(lp, A)
    for (i, j) in prm_p
      push!(prm, (indices[i], indices[j]))
    end
  end
  sort!(prm, by = a -> a[1])
  return G([x[2] for x = prm])
end

#As above, but assumes that the prime ideals are lying over the same prime number p.
function _induce_action_p(lp::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}, A::Map)
  O = order(lp[1])
  K = nf(O)
  prm = Tuple{Int, Int}[]
  p = minimum(lp[1], copy = false)

  if length(lp) < 3 || is_index_divisor(O, p) || !fits(Int, p)
    #TODO: Put some more thought. At least, do not check ideals that have already been found!
    found = falses(length(lp))
    for (i, P) in enumerate(lp)
      Q = induce_image(A, P)
      id = 0
      for j = 1:length(lp)
        if found[j]
          continue
        end
        if lp[j] == Q
          found[j] = true
          id = j
          break
        end
      end
      @assert !iszero(id)
      push!(prm, (i, id))
    end
  else
    px = polynomial_ring(Native.GF(Int(p), cached=false), "x", cached=false)[1]
    fpx = px(A(gen(K)))
    gpx = px(K.pol)
    #idea/ reason
    # if p is no index divisor, then a second generator is just
    #   an irreducible factor of gpx (Kummer/ Dedekind)
    # an ideal is divisible by P iff the canonical 2nd generator of the prime ideal
    # divides the 2nd generator of the target (CRT)
    # so
    lpols = fpPolyRingElem[gcd(px(K(P.gen_two)), gpx) for P in lp]
    # this makes lp canonical (should be doing nothing actually)

    for (i, P) in enumerate(lp)
      hp = px(K(P.gen_two))
      if degree(hp)==1
        im = fpx + coeff(hp, 0)
      else
        im = compose_mod(hp, fpx, gpx)
        # the image, directly mod p...
      end
      im = Hecke.gcd!(im, gpx, im)
      # canonical
      push!(prm, (i, findfirst(isequal(im), lpols)))
      # and find it!
    end
  end
  return prm
end



function induce(FB::Hecke.NfFactorBase, A::Map)
  K = domain(A)
  f = A(gen(K)) # essentially a polynomial in the primitive element

  O = order(FB.ideals[1])
  prm = Vector{Tuple{Int, Int}}()

  G = SymmetricGroup(length(FB.ideals))
  if f == gen(K)
    return one(G)
  end

  for p in FB.fb_int.base
    FP = FB.fb[p]
    lp = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[x[2] for x = FP.lp]
    prm_p = _induce_action_p(lp, A)
    for (a, b) in prm_p
      push!(prm, (FP.lp[a][1], FP.lp[b][1]))
    end
  end
  sort!(prm, by = a -> a[1])
  return G([x[2] for x = prm])
end

#= implementation from Butler's Fundamntal Algorithm for Permutation Groups
  Algo 4: Dimino
  Tested for cyclic groups - unfortunately only.
  I still need to generate other input
=#
#function orbit_in_FB(op::Vector{Tuple{Map, Generic.Perm}}, a::AbsSimpleNumFieldElem, s::SRow)
function orbit_in_FB(op::Array, a::AbsSimpleNumFieldElem, s::SRow)
  function op_smat(n::SRow, p::Generic.Perm)
    r = [(p[i], v) for (i,v) = n]
    sort!(r, lt = (a,b)->a[1]<b[1])
    return typeof(n)(r)
  end

  Ss = Dict{AbsSimpleNumFieldElem, typeof(s)}()
#  Ss = Dict{typeof(s), AbsSimpleNumFieldElem}()
  Ss[a] = s
  # start with the cyclic group be op[1]
  n = s
  b = op[1][1](a)
  while b != a
    n = op_smat(n, op[1][2])
    Ss[b] = n
    b = op[1][1](b)
  end

  for i=2:length(op)
    bb = op[i][1](a)
    if haskey(Ss, bb)
      continue
    end
    old = collect(Ss)
    for (bb, n) in old # one redundant - step
      Ss[op[i][1](bb)] = op_smat(n, op[i][2])
    end
    while true
      done = true
      for j = 1:length(op)
        bb = op[j][1](b)
        if haskey(Ss, bb)
          continue;
        end
        done = false
        b = bb
        for (bbb, n) in old
          # TODO: What is going on with the b's?
          Ss[op[j][1](bbb)] = op_smat(n, op[j][2])
        end
      end
      if done
        break
      end
    end
  end
  return Ss
end

function generated_subgroup(op::Array) #pairs: permutations and Map
  elt = Vector{Any}()
  push!(elt, (x->x, parent(op[1][2])()))
  ord = 1
  g = op[1]
  while g[2] != parent(op[1][2])()
    let c_g = g
      push!(elt, c_g)
#      g = (x->op[1][1](c_g[1](x)), op[1][2]*c_g[2])
      g = (x->op[1][1](c_g[1](x)), c_g[2]*op[1][2])
    end
  end
  ord = length(elt)

  for i=2:length(op)
    c_i = i
    if op[i][2] in [x[2] for x=elt]
      continue
    end
    pord = ord
    push!(elt, op[i])
    for j=2:pord
      c_j = j
#      push!(elt, (x->elt[c_j][1](op[c_i][1](x)), elt[c_j][2]*op[c_i][2]))
      push!(elt, (x->elt[c_j][1](op[c_i][1](x)), op[c_i][2]*elt[c_j][2]))
    end
    ord = length(elt)
    rpos = pord + 1
    while true
      for s in op
        let c_rpos = rpos, c_s = s
#          g = (x->elt[c_rpos][1](c_s[1](x)), elt[c_rpos][2]*c_s[2])
          g = (x->elt[c_rpos][1](c_s[1](x)), c_s[2]*elt[c_rpos][2])
          if g[2] in [x[2] for x=elt]
            continue
          end
        end
        let c_g = g
          push!(elt, c_g)
          for j = 2:pord
            c_j = j
#            push!(elt, (x->elt[c_j][1](c_g[1](x)), elt[c_j][2]*c_g[2]))
            push!(elt, (x->elt[c_j][1](c_g[1](x)), c_g[2]*elt[c_j][2]))
          end
        end
        ord = length(elt)
      end
      rpos += pord
      if rpos > length(elt)
        break
      end
    end
  end
  return elt
end


function class_group_add_auto(ctx::ClassGrpCtx, auts::Vector{<:NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}})
  #I am assuming that auts contains all the automorphisms of K
  K = domain(auts[1])
  p = 11
  R = Native.GF(p, cached = false)
  Rx, x = polynomial_ring(R, "x", cached = false)
  fmod = Rx(K.pol)
  while degree(fmod) != degree(K) || !is_squarefree(fmod)
    p = next_prime(p)
    R = Native.GF(p, cached = false)
    Rx, x = polynomial_ring(R, "x", cached = false)
    fmod = Rx(K.pol)
  end
  S = small_generating_set(auts)

  Dpols = Dict{fpPolyRingElem, automorphism_type(K)}()
  for i = 1:length(auts)
    Dpols[Rx(image_primitive_element(auts[i]))] = auts[i]
  end
  Gperm = SymmetricGroup(length(ctx.FB.ideals))

  elements = Vector{Tuple{automorphism_type(K), Generic.Perm{Int}}}(undef, length(auts))
  elements[1] = (id_hom(K), one(Gperm))
  if length(auts) == 1
    return elements
  end
  ind_elem = 3
  pols = fpPolyRingElem[x, Rx(image_primitive_element(S[1]))]
  perms = Generic.Perm{Int}[one(Gperm), induce(ctx.FB, S[1])]
  elements[2] = (S[1], perms[2])
  gperm = perms[2]*perms[2]
  gpol = compose_mod(pols[2], pols[end], fmod)
  while gpol != pols[1]
    elements[ind_elem] = (Dpols[gpol], gperm)
    @hassert :ClassGroup 1 induce(ctx.FB, elements[ind_elem][1]) == elements[ind_elem][2]
    ind_elem += 1
    push!(pols, gpol)
    push!(perms, gperm)
    gperm = perms[2]*gperm
    gpol = compose_mod(pols[2], pols[end], fmod)
  end
  if length(pols) == length(auts)
    return elements
  end

  for i in 2:length(S)
    pi = Rx(image_primitive_element(S[i]))
    if !(pi in pols)
      permi = induce(ctx.FB, S[i])
      previous_order = length(pols)
      elements[ind_elem] = (S[i], permi)
      push!(pols, pi)
      push!(perms, permi)
      ind_elem += 1
      for j in 2:previous_order
        push!(pols, compose_mod(pols[j], pi, fmod))
        push!(perms, perms[j]*permi)
        elements[ind_elem] = (Dpols[pols[end]], perms[end])
        @hassert :ClassGroup 1 induce(ctx.FB, elements[ind_elem][1]) == elements[ind_elem][2]
        ind_elem += 1
      end
      if length(pols) == length(auts)
        return elements
      end
      rep_pos = previous_order + 1
      while rep_pos <= length(pols)
        for k in 1:i
          s = S[k]
          po = Rx(image_primitive_element(s))
          permo = elements[1][2]
          for l = 1:length(elements)
            if s == elements[l][1]
              permo = elements[l][2]
              break
            end
          end
          permatt = perms[rep_pos]*permo
          att = compose_mod(pols[rep_pos], po, fmod)
          if !(att in pols)
            push!(perms, permatt)
            push!(pols, att)
            elements[ind_elem] = (Dpols[pols[end]], perms[end])
            @hassert :ClassGroup 1 induce(ctx.FB, elements[ind_elem][1]) == elements[ind_elem][2]
            ind_elem += 1
            for j in 2:previous_order
              push!(pols, compose_mod(pols[j], att, fmod))
              push!(perms, perms[j]*permatt)
              elements[ind_elem] = (Dpols[pols[end]], perms[end])
              @hassert :ClassGroup 1 induce(ctx.FB, elements[ind_elem][1]) == elements[ind_elem][2]
              ind_elem += 1
            end
            if length(pols) == length(elements)
              return elements
            end
          end
        end
        rep_pos = rep_pos + previous_order
      end
    end
  end
  return elements
end
