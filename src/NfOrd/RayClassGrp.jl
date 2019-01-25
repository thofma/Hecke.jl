
export ray_class_group

add_verbose_scope(:RayFacElem)
add_assert_scope(:RayFacElem)

###############################################################################
#  
#  Map Type
#
###############################################################################


mutable struct MapRayClassGrp{T} <: Map{T, FacElemMon{Hecke.NfOrdIdlSet}, HeckeMap, MapRayClassGrp}
  header::Hecke.MapHeader
  defining_modulus::Tuple{NfOrdIdl, Array{InfPlc, 1}}
  modulus_fin::NfOrdIdl #The finite part of the modulus
  modulus_inf::Array{InfPlc,1} #The infinite part of the modulus
  fact_mod::Dict{NfOrdIdl, Int} #The factorization of the finite part of the modulus
  
  #Dictionaries to cache preimages. Used in the action on the ray class group
  prime_ideal_preimage_cache::Dict{NfOrdIdl, GrpAbFinGenElem} 
  prime_ideal_cache::Array{NfOrdIdl, 1}
  
  
  quots::Array  #Quotients of the ring by p^n for p dividing the modulus
  quots_nquo::Vector{Tuple{NfOrdIdl, NfOrdIdl}}
  idemps::Array{Tuple{NfOrdQuoRingElem, NfOrdQuoRingElem}, 1} #Idempotents for discrete logarithm
  coprime_elems::Array{nf_elem, 1}
  
  
  tame_mult_grp::Dict{NfOrdIdl, GrpAbFinGenToNfAbsOrdMap} #The multiplicative group, tame part
  wild_mult_grp::Dict{NfOrdIdl, GrpAbFinGenToNfAbsOrdMap} #Multiplicative group, wild part
  disc_log_inf_plc::Dict{InfPlc, GrpAbFinGenElem} #The infinite places and the corresponding discrete logarithm.
  
  function MapRayClassGrp{T}() where {T}
    z = new{T}()
    z.prime_ideal_preimage_cache = Dict{NfOrdIdl, GrpAbFinGenElem}()
    return z
  end
end


###############################################################################
#
#  Ray Class Group interface
#
###############################################################################

@doc Markdown.doc"""
    ray_class_group(m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[]; n_quo)
    
> Given a modulus with finite part $m$ and infinite part $inf_plc$, it returns
> the Ray Class Group $Cl_m$. If $n_quo$ is given,
>  it will return the quotient of the Ray Class Group by n

"""
function ray_class_group(m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[]; n_quo=0)

  if n_quo!=0
    return ray_class_group_quo(n_quo,m,inf_plc)
  else 
    return ray_class_group_fac_elem(m, inf_plc)
  end

end

###############################################################################
#
#  Functions for the evaluation of factored elements
#
###############################################################################

#
#  Multiple elements evaluation
#


function fac_elems_eval(O::NfOrd, Q::NfOrdQuoRing, elems::Array{FacElem{nf_elem, AnticNumberField},1}, lp::Dict{NfOrdIdl, Int}, exponent::fmpz)

  @vtime :RayFacElem :3 newelems = _preproc(O,elems,exponent)
  quots = []
  idemps = Tuple{NfOrdQuoRingElem, NfOrdQuoRingElem}[]
  el = [one(Q) for i=1:length(newelems)]
  I = ideal(O,1)
  aux = zero(Q)
  for (p, vp) in lp
    q = p^vp
    y, Qn = _eval_quo(O, newelems, p, q, anti_uniformizer(p), vp, exponent)
    push!(quots, Qn)
    a,b = idempotents(I, q)
    id1 = Q(a)
    id2 = Q(b)
    push!(idemps, (id1, id2))
    for i=1:length(el)
      mul!(aux, Q(y[i]), id1)
      mul!(el[i], el[i], id2)
      add!(el[i], el[i], aux)
      #el[i]=Q(y[i])*Q(a)+el[i]*Q(b)
    end
    I=I*q
  end
  return el, quots, idemps

end

function _preproc(O::NfOrd, elems::Array{FacElem{nf_elem, AnticNumberField},1}, exponent::fmpz)
  
  newelems = FacElem{NfOrdElem, NfOrd}[]
  for el in elems
    x = Dict{NfOrdElem, fmpz}()
    for (f,k) in el.fac
      l = mod(k,exponent)
      if iszero(l)
        continue
      end
      n = numerator(f)
      d = denominator(f)
      if !isone(denominator(f))
        el = O(d)
        if haskey(x,el)
          x[el] = mod(x[el]-l, exponent)
        else
          x[el]= mod(-l, exponent)
        end
      end
      el1 = O(n)
      if haskey(x,el1)
        x[el1] = mod(x[el1]+l, exponent)
      else
        x[el1] = l
      end
    end
    if !isempty(x)
      push!(newelems, FacElem(x))
    else 
      push!(newelems,FacElem(Dict(O(1)=> 1)))
    end
  end
  return newelems

end


function _eval_quo(O::NfOrd, elems::Array{FacElem{NfOrdElem, NfOrd},1}, p::NfOrdIdl, q::NfOrdIdl, anti_uni::nf_elem, mult::Int, exp::fmpz)
  
  if mult==1 
    if nbits(p.minimum)<64
      @vtime :RayFacElem 2 Q, mQ=ResidueFieldSmall(O, p)
      el=[Q(1) for i=1:length(elems)]
      for i=1:length(elems)
        J=elems[i]
        for (f,k) in J.fac
          act_el=f
          el1 = mQ(act_el)
          if el1 != 0
            mul!(el[i], el[i], el1^k)
            continue
          end
          val = valuation(act_el,p)
          anti_val = anti_uni^val
          mul!(anti_val, anti_val, act_el.elem_in_nf)
          act_el=O(anti_val, false)
          mul!(el[i], el[i], mQ(act_el)^k)
        end
      end
    else
      @vtime :RayFacElem 2 Q, mQ = ResidueField(O, p)
      el=[Q(1) for i=1:length(elems)]
      for i=1:length(elems)
        J=elems[i]
        for (f, k) in J.fac
          el1 = mQ(f)
          if el1 != 0
            mul!(el[i], el[i], el1^k)
            continue
          end
          val = valuation(f, p)
          ant_val = anti_uni^val
          mul!(ant_val, ant_val, f.elem_in_nf)
          act_el = O(ant_val, false)
          mul!(el[i], el[i], mQ(act_el)^k)
        end
      end
    end
    return [mQ\el[i] for i=1:length(el)], (Q, mQ)
  else
    @vtime :RayFacElem 2 Q, mQ = quo(O, q)
    el = [Q(1) for i=1:length(elems)]
    for i=1:length(elems)
      J = elems[i]
      for (f,k) in J.fac
        act_el=f
        if mod(act_el, p)!=0
          mul!(el[i], el[i], Q(act_el)^k)
          continue
        end
        val = valuation(act_el, p)
        ant_val = anti_uni^val 
        mul!(ant_val, ant_val, act_el.elem_in_nf)
        act_el = O(ant_val, false)
        mul!(el[i], el[i], Q(act_el)^k)
      end
    end
    return [el[i].elem for i=1:length(el)], Q
  end
 
end


#
#  Single element evaluation (for the disclog)
#


function _fac_elem_evaluation(O::NfOrd, Q::NfOrdQuoRing, quots::Array, idemps::Array{Tuple{NfOrdQuoRingElem, NfOrdQuoRingElem}}, J::FacElem{nf_elem,AnticNumberField}, primes::Dict{NfOrdIdl, Int}, exponent::fmpz)
  
  element = Q(1)
  i = 0
  #Reduce the exponents and reduce to elements in O
  x=Dict{NfOrdElem, fmpz}()
  for (f,k) in J.fac
    l = mod(k,exponent)
    if iszero(l)
      continue
    end
    n = numerator(f)
    d = denominator(f)
    if !isone(denominator(f))
      el = O(d)
      if haskey(x,el)
        x[el] = mod(x[el]-l, exponent)
      else
        x[el]=mod(-l, exponent)
      end
    end
    el1 = O(n)
    if haskey(x,el1)
      x[el1] = mod(x[el1]+l, exponent)
    else
      x[el1] = l
    end
  end
  if isempty(x)
    return element.elem
  end
  tobeeval=FacElem(x)
  aux = one(Q)
  for (p, vp) in primes
    i += 1
    y = _eval_quo(O, quots[i], tobeeval, p, anti_uniformizer(p), vp)
    a,b = idemps[i]
    mul!(element, element, b)
    mul!(aux, Q(y), a)
    add!(element, aux, element)
  end
  return element.elem

end

function _eval_quo(O::NfOrd, Q1, J::FacElem{NfOrdElem, NfOrd}, p::NfOrdIdl, anti_uni::nf_elem,  mult::Int)
  if mult==1
    Q=Q1[1]
    mQ=Q1[2]
    el=Q(1)
    for (f,k) in J.fac
      act_el=f
      if mQ(act_el)!=0
        el*=mQ(act_el)^k
        continue
      end
      val=valuation(act_el,p)
      act_el=O(act_el*(anti_uni^val),false)
      el*= mQ(act_el)^k
    end
    return mQ\el
  else
    Q=Q1
    el=Q(1)
    for (f,k) in J.fac
      act_el=f
      if mod(act_el, p)!=0
        el*=Q(act_el)^k
        continue
      end
      val=valuation(act_el,p)
      act_el=O(act_el*(anti_uni^val),false)
      el*= Q(act_el)^k
    end
    return el.elem
  end
 
end

###############################################################################
#
#  New evaluation: used only in the quo version of the ray_class_grp
#
###############################################################################

function _crt_normalization(O::NfOrd, Q::NfOrdQuoRing, elems::Vector{NfOrdElem}, lp::Dict{NfOrdIdl, Int})

  quots = Tuple{NfOrdIdl, NfOrdIdl}[]
  idemps = Tuple{NfOrdQuoRingElem, NfOrdQuoRingElem}[]
  el = NfOrdQuoRingElem[one(Q) for i = 1:length(elems)]
  I = ideal(O, 1)
  aux = zero(Q)
  for (p,vp) in lp
    q = p^vp
    @vtime :RayFacElem 3 y = _new_eval_quo(O, elems, p, q)
    push!(quots, (p, q))
    @vtime :RayFacElem 3 a, b = idempotents(I, q)
    id1 = Q(a)
    id2 = Q(b)
    push!(idemps, (id1, id2))
    for i=1:length(el)
      mul!(aux, Q(y[i]), id1)
      mul!(el[i], el[i], id2)
      add!(el[i], el[i], aux)
      #el[i]=Q(y[i])*Q(a)+el[i]*Q(b)
    end
    I = I*q
  end
  return el, quots, idemps

end


function _units_andprincgens_eval(O::NfOrd, Q::NfOrdQuoRing, elems::Array{FacElem{nf_elem, AnticNumberField},1}, lp::Dict{NfOrdIdl, Int}, exponent::fmpz)

  if !isempty(elems)
    @vtime :RayFacElem :3 newelems = _new_preproc(elems, exponent)
    @vtime :RayFacElem :3 to_be_normalized = [O(evaluate(newelems[i]), false) for i=1:length(newelems)]
  else
    to_be_normalized = Vector{NfOrdElem}()
  end
  return _crt_normalization(O, Q, to_be_normalized, lp)

end

function _new_preproc(elems::Array{FacElem{nf_elem, AnticNumberField},1}, exponent::fmpz)
  
  FacElemParent = parent(elems[1])
  K = base_ring(FacElemParent)
  newelems = Vector{FacElem{nf_elem, AnticNumberField}}(undef, length(elems))
  for i = 1:length(newelems)
    x = Dict{nf_elem, fmpz}()
    for (f, k) in elems[i].fac
      l = mod(k, exponent)
      if iszero(l)
        continue
      end
      d = denominator(f)
      n = numerator(f)
      if haskey(x, n)
        x[n] = mod(x[n] + l, exponent)
      else
        x[n] = l
      end
      if !isone(d)
        el = K(d)
        if haskey(x, el)
          x[el] = mod(x[el] - l, exponent)
        else
          x[el] = mod(-l, exponent)
        end
      end
    end
    if !isempty(x)
      newelems[i] = FacElem(x)
    else 
      newelems[i] = FacElemParent()
    end
  end
  return newelems

end

function _new_eval_quo(O::NfOrd, elems::Array{NfOrdElem, 1}, p::NfOrdIdl, q::NfOrdIdl)
  
  anti_uni = anti_uniformizer(p)
  el = Vector{NfOrdElem}(undef, length(elems))
  if p.gen_one == q.gen_one && p.gen_two == q.gen_two 
    if nbits(p.minimum)<64
      @vtime :RayFacElem 2 Q, mQ = ResidueFieldSmall(O, q)
      for i=1:length(elems)
        f = elems[i]
        el1 = mQ(f)
        if !iszero(el1)
          el[i] = mQ\(el1)
          continue
        end
        val = valuation(f, q)
        anti_val = anti_uni^val
        mul!(anti_val, anti_val, f.elem_in_nf)
        act_el = O(anti_val, false)
        el[i] = mQ\(mQ(act_el))
      end
    else
      @vtime :RayFacElem 2 Q, mQ = ResidueField(O, q)
      for i=1:length(elems)
        f = elems[i]
        el1 = mQ(f)
        if !iszero(el1)
          el[i] = mod(f, q)
          continue
        end
        val = valuation(f, q)
        anti_val = anti_uni^val
        mul!(anti_val, anti_val, f.elem_in_nf)
        act_el = O(anti_val, false)
        el[i] = mQ\(mQ(act_el))
      end
    end
  else
    for i=1:length(elems)
      f = elems[i]
      if !iszero(mod(f, p))
        el[i] = mod(f, q)
        continue
      end
      @vtime :RayFacElem 3 val = valuation(f, p)
      ant_val = anti_uni^val 
      mul!(ant_val, ant_val, f.elem_in_nf)
      act_el = O(ant_val, false)
      el[i] = mod(act_el, q)
    end
  end
  return el
  
end

function _fac_elem_evaluation(O::NfOrd, Q::NfOrdQuoRing, quots::Vector{Tuple{NfOrdIdl, NfOrdIdl}}, idemps::Vector{Tuple{NfOrdQuoRingElem, NfOrdQuoRingElem}}, J::FacElem{nf_elem,AnticNumberField}, exponent::fmpz)
  
  K = nf(O)
  element = Q(1)
  i = 0
  #Reduce the exponents and reduce to elements in O
  x=Dict{nf_elem, fmpz}()
  for (f, k) in J.fac
    l = mod(k, exponent)
    if iszero(l)
      continue
    end
    n = numerator(f)
    d = denominator(f)
    if haskey(x, n)
      x[n] = mod(x[n]+l, exponent)
    else
      x[n] = l
    end
    if !isone(d) 
      el = K(d)
      if haskey(x, el)
        x[el]=mod(x[el]-l,exponent)
      else
        x[el] = mod(-l, exponent)
      end
    end
  end
  if isempty(x)
    return element.elem
  end
  tobeeval = O(evaluate(FacElem(x)))
  aux = one(Q)
  for pq in quots
    i += 1
    y = _eval_single(O, tobeeval, pq[1], pq[2])
    a, b = idemps[i]
    mul!(element, element, b)
    mul!(aux, Q(y), a)
    add!(element, element, aux)
  end
  return element.elem

end

function _eval_single(O::NfOrd, J::NfOrdElem, p::NfOrdIdl, q::NfOrdIdl)

  if p.gen_two == q.gen_two
    att = mod(J, p)
    if !iszero(att)
      return att
    end
    anti_uni = anti_uniformizer(p)
    val = valuation(J, p)
    act_el = anti_uni^val
    mul!(act_el, act_el, J.elem_in_nf)  
    act_el
    return mod(O(act_el), p)
  else
    if !iszero(mod(J, p))
      return mod(J, q)
    end
    anti_uni = anti_uniformizer(p)
    val = valuation(J, p)
    act_el = anti_uni^val
    mul!(act_el, act_el, J.elem_in_nf)  
    return mod(O(act_el), q)
  end
 
end

###############################################################################
#
#  Ray Class Group - Auxiliary functions
#
###############################################################################

#
# Function that finds the generators of the infinite part
#
function carlos_units(O::NfOrd)
  try
    c = _get_carlos_units_of_order(O)
    return c
  catch
    K= O.nf
    p = real_places(K)
    S = DiagonalGroup([2 for i=1:length(p)])

    function logS(x::Array{Int, 1})
      return S([x[i] > 0 ? 0 : 1 for i=1:length(x)])
    end
  
    s = typeof(S[1])[]
    g = elem_type(O)[]
    u, mu = sub(S, s, false)
    b = 10
    cnt = 0
    while b > 0
      a = rand(O, b)
      if a==0
        continue
      end
      emb = signs(K(a), p)
      ar = [0 for i = 1:length(p)]
      for i=1:length(p)
        if emb[p[i]] == -1
          ar[i] = 1
        end
      end
      t = S(ar)
      if !Hecke.haspreimage(mu, t)[1]
        push!(s, t)
        push!(g, a)
        u, mu = sub(S, s, false)
        if order(u) == order(S)
          break
        end
      else
        cnt += 1
        if cnt > 1000 
          b *= 2
          cnt = 0
        end
      end
    end
    if b <= 0
      b = 10
      cnt = 0
      bas = lll_basis(O)
      while true
        @assert b>0
        a = rand(bas, 1:b)
        if a==0
          continue
        end
        emb=signs(a,p)
        ar = [0 for i = 1:length(p)]
        for i=1:length(p)
          if emb[p[i]] == -1
            ar[i] = 1
          end
        end
        t = S(ar)
        if !Hecke.haspreimage(mu, t)[1]
          push!(s, t)
          push!(g, O(a,false))
          u, mu = sub(S, s, false)
          if order(u) == order(S)
            break
          end
        else
          cnt += 1
          if cnt > 1000 
            b *= 2
            cnt = 0
          end
        end
      end
    end
    hS = Hecke.GrpAbFinGenMap(S, S, vcat([x.coeff for x in s]))   # Change of coordinates so that the canonical basis elements are mapped to the elements found above
    r = elem_type(O)[]
    for i=1:length(p)
      y = haspreimage(hS,S[i])[2]
      push!(r, prod([g[i]^Int(y[i]) for i=1:length(p)]))
    end
  
    function exp(A::GrpAbFinGenElem)
      
      s=O(1)
      if iszero(A.coeff)
        return s
      end  
      for i=1:length(p)
        if Int(A.coeff[1,i]) == 1
          s=s*r[i]
        end 
      end
      return s
    end 

    function log(B::nf_elem)
      emb = Hecke.signs(B, p)
      res = Int[0 for i=1:length(p)]
      for i=1:length(p)
        if emb[p[i]] == -1
          res[i] = 1
        end
      end
      return S(res)
    end 
    
    function log(B::FacElem{nf_elem})
      emb = Hecke.signs(B, p)
      res = Int[0 for i=1:length(p)]
      for i=1:length(p)
        if emb[p[i]] == -1
          res[i] = 1
        end
      end
      return S(res)
    end 
    
    _set_carlos_units_of_order(O, (S,exp,log))
    return (S,exp,log)
  end
end


function _infinite_primes(O::NfOrd, p::Array{InfPlc,1}, m::NfOrdIdl)
    
    K = nf(O)
    if p == real_places(K)
      S, exp1, log1 = carlos_units(O)
      function exp2(a::GrpAbFinGenElem)
        return m.gen_one*exp1(a)
      end
      return S, exp2, log1
    end

    S=DiagonalGroup([2 for i=1:length(p)])

    function logS(x::Array{Int, 1})
      return S([x[i] > 0 ? 0 : 1 for i=1:length(x)])
    end
  
    s = typeof(S[1])[]
    g = elem_type(O)[]
    u, mu = sub(S, s, false)
    b = 10
    cnt = 0
    while true
      @assert b > 0
      a = rand(m, b)
      if a==0
        continue
      end
      emb=signs(K(a), p)
      ar = [0 for i = 1:length(p)]
      for i=1:length(p)
        if emb[p[i]] == -1
          ar[i] = 1
        end
      end
      t = S(ar)
      if !Hecke.haspreimage(mu, t)[1]
        push!(s, t)
        push!(g, a)
        u, mu = sub(S, s, false)
        if order(u) == order(S)
          break
        end
      else
        cnt += 1
        if cnt > 1000 
          b *= 2
          cnt = 0
        end
        if b <= 0
          b = 10
          cnt = 0
          bas = lll_basis(O)
          while true
            @assert b>0
            a = rand(bas, 1:b)
            if a==0
              continue
            end
            emb=signs(a,p)
            ar = [0 for i = 1:length(p)]
            for i=1:length(p)
              if emb[p[i]] == -1
                ar[i] = 1
              end
            end
            t = S(ar)
            if !Hecke.haspreimage(mu, t)[1]
              push!(s, t)
              push!(g, O(a, false))
              u, mu = sub(S, s, false)
              if order(u) == order(S)
                break
              end
            else
              cnt += 1
              if cnt > 1000 
                b *= 2
                cnt = 0
              end
            end
          end
        end
      end
    end
    hS = Hecke.GrpAbFinGenMap(S, S, vcat([x.coeff for x in s]))   # Change of coordinates so that the canonical basis elements are mapped to the elements found above
    r = elem_type(O)[]
    for i=1:length(p)
      y = haspreimage(hS,S[i])[2]
      push!(r, prod([g[i]^Int(y[i]) for i=1:length(p)]))
    end
  
    function exp(A::GrpAbFinGenElem)
      
      s=O(m.gen_one)
      if iszero(A.coeff)
        return s
      end  
      for i=1:length(p)
        if Int(A.coeff[1,i]) == 1
          s=s*r[i]
        end 
      end
      return s
    end 

    function log(B::nf_elem)
      emb=Hecke.signs(B,p)
      ar = [0 for i = 1:length(p)]
      for i=1:length(p)
        if emb[p[i]] == -1
          ar[i] = 1
        end
      end
      return S(ar)
    end 
    
    function log(B::FacElem{nf_elem})
      emb=Hecke.signs(B,p)
      ar = [0 for i = 1:length(p)]
      for i=1:length(p)
        if emb[p[i]] == -1
          ar[i] = 1
        end
      end
      return S(ar)
    end 
  return S, exp, log
  
end

#
#  Function that stores the principal generators element of the powers of the generators
#  in the class group map
#

function _assure_princ_gen(mC::MapClassGrp)

  if isdefined(mC, :princ_gens)
    return true
  end
  C=domain(mC)
  mC.princ_gens=Array{Tuple{FacElem{NfOrdIdl, NfOrdIdlSet}, FacElem{nf_elem, AnticNumberField}},1}(undef, ngens(C))
  for i=1:ngens(C)
    I=FacElem(Dict(mC(C[i])=> fmpz(1)))
    pr=principal_gen_fac_elem(I^C.snf[i])
    mC.princ_gens[i]=(I,pr)
  end
  return true

end


#
#  Changes the exponential map of the class group so that the chosen representatives are coprime to the modulus
#

function _elements_to_coprime_ideal(C::GrpAbFinGen, mC::MapClassGrp, m::NfOrdIdl)
 
  O = order(m)
  K = nf(O)
  L = Array{NfOrdIdl,1}(undef, ngens(C))
  el = Array{nf_elem,1}(undef, ngens(C))

  for i=1:ngens(C)
    a = first(keys(mC.princ_gens[i][1].fac))
    if iscoprime(a, m)
      L[i] = a
      el[i] = K(1)
    else  
      J=inv(a)
      s=K(rand(J.num,5))//J.den  # Is the bound acceptable?
      I=s*a
      simplify(I)
      I = numerator(I)
      while !iscoprime(I,m)
        s=K(rand(J.num,5))//J.den  
        I=s*a
        simplify(I)
        I = numerator(I)
      end
      L[i] = I
      el[i] = s
    end
  end

  function exp(a::GrpAbFinGenElem)  
    e = Dict{NfOrdIdl,fmpz}()
    for i = 1:ngens(C)
      if Int(a.coeff[1,i])!= 0
        e[L[i]]= a.coeff[1,i]
      end
    end
    if isempty(e)
      e[ideal(O,1)]=1
    end
    return FacElem(e)
  end
  
  return exp, el

end 

function empty_ray_class(m::NfOrdIdl)
  O=order(parent(m))
  X=DiagonalGroup(Int[])
  function exp(a::GrpAbFinGenElem)
    return FacElem(Dict(ideal(O,1) => fmpz(1)))
  end
  
  function disclog(J::Union{NfOrdIdl, FacElem{NfOrdIdl}})
    return X(Int[])
  end
  
  mp=Hecke.MapRayClassGrp{typeof(X)}()
  mp.header = Hecke.MapHeader(X, FacElemMon(parent(m)) , exp, disclog)
  mp.modulus_fin=ideal(O,1)
  mp.modulus_inf=InfPlc[]
  mp.defining_modulus = (m, mp.modulus_inf)
  
  return X,mp

end

function class_as_ray_class(C::GrpAbFinGen, mC::MapClassGrp, exp_class::Function,  m::NfOrdIdl, n::Integer)

  O=order(m)
  X,_=quo(C, n,false)
  function exp(a::GrpAbFinGenElem)
    return exp_class(a)
  end
  
  function disclog(J::NfOrdIdl)
    return X((mC\J).coeff)
  end
  
  function disclog(J::FacElem)
    a= X([0 for i=1:ngens(X)])
    for (f,k) in J.fac
      a+=k*disclog(f)
    end
    return a
  end
    
  mp=Hecke.MapRayClassGrp{typeof(X)}()
  mp.header = Hecke.MapHeader(X, FacElemMon(parent(m)) , exp, disclog)
  mp.modulus_fin=ideal(O,1)
  mp.modulus_inf=Array{InfPlc, 1}()
  mp.fact_mod=Dict{NfOrdIdl, Int}()
  mp.defining_modulus = (mp.modulus_fin, mp.modulus_inf)
    
  return X,mp
end

function class_as_ray_class(C::GrpAbFinGen, mC::MapClassGrp, exp_class::Function,  m::NfOrdIdl)

    O=order(m)
    X=deepcopy(C)
    function exp(a::GrpAbFinGenElem)
      return exp_class(a)
    end
    
    function disclog(J::NfOrdIdl)
      return X((mC\J).coeff)
    end
    
    function disclog(J::FacElem)
      a= X([0 for i=1:ngens(X)])
      for (f,k) in J.fac
        a+=k*disclog(f)
      end
      return a
    end
    
    mp=Hecke.MapRayClassGrp{typeof(X)}()
    mp.header = Hecke.MapHeader(X, FacElemMon(parent(m)) , exp, disclog)
    mp.modulus_fin=ideal(O,1)
    mp.modulus_inf=Array{InfPlc, 1}()
    mp.fact_mod=Dict{NfOrdIdl, Int}()
    mp.defining_modulus = (mp.modulus_fin, mp.modulus_inf)
    return X, mp

end

###################################################################################
#
#  Ray Class Group
#
###################################################################################


function ray_class_group_fac_elem(m::NfOrdIdl, inf_plc::Array{InfPlc, 1} = Array{InfPlc, 1}())

#
# We compute the group using the sequence U -> (O/m)^* _> Cl^m -> Cl -> 1
# First of all, we compute all these groups with their own maps
#  

  O=parent(m).order
  K=nf(O)
  
  C, mC = class_group(O)
  _assure_princ_gen(mC)
  exp_class, Kel = Hecke._elements_to_coprime_ideal(C, mC, m)
  U, mU = unit_group_fac_elem(O)
  Q, pi = quo(O,m)
  G, mG = _multgrp_ray(Q)
  
  lp = Q.factor
  
  p = [ x for x in inf_plc if isreal(x) ]
  if !isempty(p)
    H, eH, lH = Hecke._infinite_primes(O, p, m)
    T = G
    G = direct_product(G, H)[1]
  end
  
  @vprint :RayFacElem 1 "The multiplicative group is $G \n"
  @vprint :RayFacElem 1 "The class group is $C \n"
  @vprint :RayFacElem 1 "The units are $U \n"
    
  expon = exponent(G)

#
# We construct the relation matrix and evaluate units and relations with the class group in the quotient by m
# Then we compute the discrete logarithms
#

  R=zero_matrix(FlintZZ, ngens(C)+ngens(U)+ngens(G), ngens(C)+ngens(G))
  for i=1:ngens(C)
    R[i,i] = C.snf[i]
  end
  if issnf(G)
    for i = 1:ngens(G)
      R[i+ngens(C), i+ngens(C)] = G.snf[i]
    end
  else
    for i = 1:ngens(G)
      R[i+ngens(C), i+ngens(C)] = G.rels[i,i]
    end 
  end
 

  @vprint :RayFacElem 1 "Collecting elements to be evaluated; first, units \n"
  evals = []
  tobeeval = FacElem{nf_elem, AnticNumberField}[]
  if U.snf[1] == 2
    push!(evals, O(-1))
  else
    push!(tobeeval, mU(U[1]))
  end
  append!(tobeeval,[mU(U[i]) for i=2:ngens(U)])
  
  @vprint :RayFacElem 1 "then principal ideal generators \n"
  princ_gens = []
  for i = 1:ngens(C)
    @vtime :RayFacElem 1 push!(princ_gens, Hecke.principal_gen_fac_elem((exp_class(C[i]))^(Int(order(C[i])))))
  end
  append!(tobeeval, princ_gens)
  
  @vprint :RayFacElem 1 "Time for elements evaluation: "
  @vtime :RayFacElem 1 ev,quots,idemps = fac_elems_eval(O,Q,tobeeval,lp,fmpz(expon))
  append!(evals,ev)
  @vprint :RayFacElem 1 "\n"
  
  for i=1:ngens(U)
    @vprint :RayFacElem 1 "Disclog of unit $i \n"
    a=(mG\Q(evals[i])).coeff
    if !isempty(p)
      if i==1
        a=hcat(a, matrix(FlintZZ,1,length(p), [1 for i in p]))
      else
        b=lH(mU(U[i]))
        a=hcat(a, b.coeff)
      end
    end
    for j=1:ngens(G)
      R[i+ngens(G)+ngens(C),ngens(C)+j]=a[1,j]
    end
  end 

#
# We compute the relation between generators of Cl and (O/m)^* in Cl^m
#

  for i = 1: ngens(C)
    @vprint :RayFacElem 1 "Disclog of class group element $i \n"
    a=((mG\Q(evals[i+ngens(U)]))).coeff
    if !isempty(p)
      b=lH(princ_gens[i])
      a=hcat(a, b.coeff)
    end
    for j=1: ngens(G)
      R[i,ngens(C)+j]=-a[1,j]
    end 
  end
  
  X=AbelianGroup(R)

#
# Discrete logarithm
#


  function disclog(J::FacElem)
    
    @vprint :RayFacElem 1 "Disc log of element $J \n"
    a= X([0 for i=1:ngens(X)])
    for (f,k) in J.fac
      a+=k*disclog(f)
    end
    return a
  end
 
 
  function disclog(J::NfOrdIdl)

    if isone(J)
    @vprint :RayFacElem 1 "J is one \n"
      return X([0 for i=1:ngens(X)])
    else
      L=mC\J
      @vprint :RayFacElem 1 "Disc log of element J in the Class Group: $(L.coeff) \n"
      s=exp_class(L)
      I=J* inv(s)
      @vprint :RayFacElem 1 "This ideal is principal: $I \n"
      z=principal_gen_fac_elem(I)
      el=_fac_elem_evaluation(O,Q,quots,idemps,z,lp,expon)
      @vprint :RayFacElem 1 "and 'generated' by $el \n"
      y=(mG\Q(el)).coeff
      @vprint :RayFacElem 1 "in the unit group, $y \n"
      if !isempty(p)
        b=lH(z)
        @vprint :RayFacElem 1 "the signs are $b \n"
        y=hcat(y, b.coeff)
      end 
      return X(hcat(L.coeff,y))
    end
  end 

#
# Exp map
#

  function expo(a::GrpAbFinGenElem)
    b=C([a.coeff[1,i] for i=1:ngens(C)])
    if isempty(p)
      c=G([a.coeff[1,i] for i=ngens(C)+1:ngens(X)])
      return exp_class(b)*ideal(O,pi\(mG(c)))
    else 
      c=T([a.coeff[1,i] for i=ngens(C)+1:ngens(T)+ngens(C)])
      d=H([a.coeff[1,i] for i=ngens(T)+ngens(C)+1:ngens(X)])
      el=pi\(mG(c))
      @vprint :RayFacElem 1 "I have the element $el \n"
      @vprint :RayFacElem 1 "I want $(d.coeff) \n"
      # I need to modify $el$ so that it has the correct sign at the embeddings contained in primes
      vect=(lH(K(el))).coeff
      if vect==d.coeff
        return exp_class(b)*ideal(O,el)
      else 
        correction=eH(d)
        while vect!=d.coeff
          el=el+correction
          vect=(lH(K(el))).coeff
        end
        return exp_class(b)*ideal(O,el)
      end 
    end
  end 

  mp = MapRayClassGrp{typeof(X)}()
  mp.header = Hecke.MapHeader(X, FacElemMon(parent(m)), expo, disclog)
  mp.modulus_fin = m
  mp.modulus_inf = p
  mp.fact_mod = Q.factor
  mp.coprime_elems = Kel
  if isdefined(mG, :tame)
    mp.tame_mult_grp = mG.tame
  end
  if isdefined(mG, :wild)
    mp.wild_mult_grp = mG.wild
  end
  mp.defining_modulus = (m, inf_plc)
  return X, mp
  
end

#####################################################################################################
#
#  Quotient by n of the Ray Class Group
#
#####################################################################################################


function _class_group_mod_n(C::GrpAbFinGen, mC::Hecke.MapClassGrp, n::Integer)
  
  @assert issnf(C)
  O = order(codomain(mC))
  K = nf(O)
  if gcd(C.snf[ngens(C)],n)==1
    G=DiagonalGroup(Int[])
    function exp1(a::GrpAbFinGenElem)
      return ideal(O, O(1))
    end
    function disclog1(I::NfOrdIdl)
      return G(Int[])
    end
    mp=Hecke.MapClassGrp{typeof(G)}()
    mp.header=Hecke.MapHeader(G, mC.header.codomain,exp1,disclog1)
    mp.princ_gens = Tuple{FacElem{NfOrdIdl, NfOrdIdlSet}, FacElem{nf_elem, AnticNumberField}}[(FacElem(Dict(ideal(O,1)=> fmpz(1))), FacElem(Dict(K(1)=> 1)))]
    return G, mp, fmpz[]
  
  else
    
    ind=1
    while gcd(order(C[ind]),n)==1
      ind+=1
    end
    
    vect=[gcd(C.snf[ind+j], n) for j=0:ngens(C)-ind]
    G = DiagonalGroup(vect)
    G.issnf = true
    G.snf = vect
    princ_gens = Vector{Tuple{FacElem{NfOrdIdl, NfOrdIdlSet}, FacElem{nf_elem, AnticNumberField}}}(undef, length(vect))
    if isdefined(mC, :princ_gens)
      for i = 1:length(princ_gens)
        princ_gens[i] = mC.princ_gens[ind+i-1] 
      end
    else
      for i = 1:ngens(G)
        I = FacElem(Dict(mC(C[i+ind-1])=> fmpz(1)))
        pr = principal_gen_fac_elem(I^C.snf[i+ind-1])
        princ_gens[i]=(I, pr)
      end
    end
    
    function exp2(a::GrpAbFinGenElem)
      x = ideal(O, 1)
      for i=1:ngens(G)
        if a[i]!=0
          x*=numerator(evaluate(princ_gens[i][1]))^(Int(a[i]))
        end
      end
      return x
    end 
    
    function disclog2(I::NfOrdIdl)
      y = G([0 for j=1:ngens(G)])
      if I.is_principal == 1
        return y
      end
      x=mC\I
      for i=ind:ngens(C)
        y.coeff[1,i-ind+1]=x.coeff[1,i]
      end 
      return y
    end
  
    mp=Hecke.MapClassGrp{typeof(G)}()
    mp.header=Hecke.MapHeader(G, mC.header.codomain, exp2, disclog2)
    mp.princ_gens = princ_gens

    
    return G,mp, [divexact(C.snf[ind+j],gcd(C.snf[ind+j],n)) for j=0:ngens(C)-ind]
  end
end 


function ray_class_group_quo(n::Integer, m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[])

  #
  #  Take the relevant part of the modulus
  #
  fac=factor(m)
  y1=Dict{NfOrdIdl,Int}()
  y2=Dict{NfOrdIdl,Int}()
  for (q,e) in fac
    if gcd(norm(q)-1,n)!=1
      y1[q]=Int(1)
      if gcd(norm(q),n)!=1 && e>=2
        y2[q]=Int(e)
      end
    elseif gcd(norm(q),n)!=1 && e>=2
      y2[q]=Int(e)
    end
  end
  return ray_class_group_quo(n, m, y1, y2, inf_plc)
  
end

function ray_class_group_quo(O::NfOrd, n_quo::Int, m::Int, wprimes::Dict{NfOrdIdl,Int}=Dict{NfOrdIdl, Int}(), inf_plc::Array{InfPlc,1} = Array{InfPlc, 1}())
  
  K=nf(O)
  d1=Dict{NfOrdIdl, Int}()
  lp=factor(m)
  for q in keys(lp.fac)
    lq=prime_decomposition(O,q) 
    for (P,e) in lq
      d1[P]=1
    end   
  end
  return ray_class_group_quo(n_quo, length(wprimes) == 0 ? ideal(O, m) : m*numerator(evaluate(FacElem(wprimes), coprime = true)), d1, wprimes, inf_plc, check_expo=true)
  
end

function ray_class_group_quo(O::NfOrd, n::Int, y::Dict{NfOrdIdl, Int}, inf_plc::Array{InfPlc, 1} = Array{InfPlc, 1}())
  
  y1=Dict{NfOrdIdl,Int}()
  y2=Dict{NfOrdIdl,Int}()
  for (q,e) in y
    if gcd(norm(q)-1,n)!=1
      y1[q]=Int(1)
      if gcd(norm(q),n)!=1 && e>=2
        y2[q]=Int(e)
      end
    elseif gcd(norm(q),n)!=1 && e>=2
      y2[q]=Int(e)
    end
  end
  I=ideal(O,1)
  for (q,vq) in y1
    I*=q
  end
  for (q,vq) in y2
    I*=q^vq
  end
  return ray_class_group_quo(n, I, y1, y2, inf_plc)

end


function ray_class_group_quo(n::Integer, m::NfOrdIdl, y1::Dict{NfOrdIdl,Int}, y2::Dict{NfOrdIdl,Int}, inf_plc::Array{InfPlc,1}=Array{InfPlc, 1}(); check_expo=false)
  # check_expo checks, before the computation of the units, if the exponent of the group can be n.
  # if it is lower for sure, it returns the trivial group.
  # I HAVE TO FIND A BETTER METHOD. 
  O=parent(m).order
  K=nf(O)
  @assert length(y1) + length(y2) == 0 || !isone(m)
  
  # Compute the modulus of the quotient
  I=ideal(O,1)
  for (q,vq) in y1
    I*=q
  end
  for (q,vq) in y2
    I*=q^vq
  end
  lp=merge(max,y1,y2)
  
  Q,pi=quo(O,I)
  Q.factor=lp
  C, mC = class_group(O)
  _assure_princ_gen(mC)
  @vtime :RayFacElem 1 G, mG, tame, wild= _mult_grp_mod_n(Q,y1,y2,n)
  if mod(n,2)==0 
    pr = [ x for x in inf_plc if isreal(x) ]
    if !isempty(pr)
      @vtime :RayFacElem 1 H, eH, lH = Hecke._infinite_primes(O, pr, I)
      T = G
      G = Hecke.direct_product(G, H)[1]
    end
  end
  
  if gcd(C.snf[end], n) == 1 && order(G) == 1
    return empty_ray_class(m)
  end
  
  valclass, nonnclass = ppio(exponent(C), fmpz(n))
  C, mC, vect = _class_group_mod_n(C, mC, Int(valclass))
  
  if check_expo && exponent(C)*exponent(G)<n
    return empty_ray_class(m)
  end
  
  U, mU = unit_group_fac_elem(O)
  exp_class, Kel = Hecke._elements_to_coprime_ideal(C, mC, m)
  for i=1:ngens(C)
    @hassert :RayFacElem 1 iscoprime(numerator(evaluate(exp_class(C[i]))), m)
  end
  
  if isone(order(G))
    return class_as_ray_class(C,mC,exp_class,m,n)    
  end
  
#
# We start to construct the relation matrix
#

  expo = exponent(G)
  
  R = zero_matrix(FlintZZ, 2*ngens(C)+ngens(U)+2*ngens(G), ngens(C)+ngens(G))
  for i=1:cols(R)
    R[ngens(C)+ngens(U)+ngens(G)+i,i] = n
  end
  for i=1:ngens(C)
    R[i,i]=C.snf[i]
  end
  if issnf(G)
    for i=1:ngens(G)
      R[i+ngens(C),i+ngens(C)]=G.snf[i]
    end
  else
    for i=1:ngens(G)
      R[i+ngens(C),i+ngens(C)]=G.rels[i,i]
    end
  end
  
  
#
# We compute the relation matrix given by the image of the map U -> (O/m)^*
#

  @hassert :RayFacElem 1 issnf(U)
  @vprint :RayFacElem 1 "Collecting elements to be evaluated; first, units \n"
  evals = NfOrdQuoRingElem[]
  tobeeval = FacElem{nf_elem, AnticNumberField}[]
  if gcd(U.snf[1],n) != 1
    if U.snf[1] == 2
      push!(evals, Q(-1))
    else
      push!(tobeeval, mU(U[1]))
    end
  else 
    push!(evals,Q(1))
  end
  append!(tobeeval,[mU(U[i]) for i=2:ngens(U)])
  
  @vprint :RayFacElem 1 "then principal ideal generators \n"
  for i=1:ngens(C)
    push!(tobeeval, mC.princ_gens[i][2]*(Kel[i]^(C.snf[i]*vect[i])))
  end
  
  @vprint :RayFacElem 1 "Time for elements evaluation: "
  #@vtime :RayFacElem 1 ev, quots, idemps = fac_elems_eval(O, Q, tobeeval, lp, fmpz(gcd(expo,n)))
  @vtime :RayFacElem 1 ev, quots, idemps = _units_andprincgens_eval(O, Q, tobeeval, lp, fmpz(gcd(expo,n)))
  append!(evals, ev)
  @vprint :RayFacElem 1 "\n"
    
  for i=1:ngens(U)
    @vprint :RayFacElem 1 "Disclog of unit $i \n"
    a=(mG\(evals[i])).coeff
    if iszero(mod(n,2)) && !isempty(pr)
      if i==1
        a=hcat(a, matrix(FlintZZ,1,length(pr), [1 for i in pr]))
      else
        b = lH(mU(U[i]))
        a = hcat(a, b.coeff)
      end
    end
    for j=1:ngens(G)
      R[i+ngens(G)+ngens(C),ngens(C)+j]=a[1,j]
    end
  end 

  # 
  # We compute the relation between generators of Cl and (O/m)^* in Cl^m
  #

  for i=1:ngens(C)
    @vprint :RayFacElem 1 "Disclog of class group element $i \n"
    invn=invmod(vect[i],fmpz(expo))
    a=((mG\(evals[i+ngens(U)]))*invn).coeff
    if mod(n,2)==0 && !isempty(pr)
      b=lH(mC.princ_gens[i][2]*(Kel[i]^(C.snf[i]*vect[i])))
      a=hcat(a, b.coeff)
    end
    for j=1: ngens(G)
      R[i,ngens(C)+j]=-a[1,j]
    end 
  end
  X = AbelianGroup(R)
   
  #
  # Discrete logarithm
  #
  inverse_d=invmod(fmpz(nonnclass),fmpz(expo))
  @assert gcd(fmpz(nonnclass),fmpz(expo))==1

  function disclog(J::FacElem{NfOrdIdl, NfOrdIdlSet})
  
    a= C([0 for i=1:ngens(C)])
    for (ff,k) in J.fac
      a+=k*(mC\ff)
    end
    Id=J* inv(exp_class(a))
    Id=Id^Int(nonnclass)
    z=principal_gen_fac_elem(Id)
    el=Hecke._fac_elem_evaluation(O, Q, quots, idemps, z, gcd(expo,n))
    y=((mG\(pi(el)))*inverse_d).coeff
    if mod(n,2)==0 && !isempty(pr)
      b=lH(z)
      y=hcat(y, b.coeff)
    end
    return X(hcat(a.coeff,y))
  end
  
  function disclog(J::NfOrdIdl)
    
    @hassert :RayFacElem 1 iscoprime(J, I)
    res = zero_matrix(FlintZZ, 1, ngens(X))
    if J.is_principal==1
      if isdefined(J,:princ_gen)
        el = J.princ_gen
        y = (mG\(pi(el))).coeff
        for i = 1:cols(y)
          res[1, ngens(C) + i] = y[1, i]
        end
        if iszero(mod(n,2)) && !isempty(inf_plc)
          b = lH(K(el))
          for i = 1:length(inf_plc)
            res[1, ngens(C)+cols(y)+i] = b[i]
          end
        end
        return X(res)
      elseif isdefined(J,:princ_gen_special)
        el=O(J.princ_gen_special[2])+O(J.princ_gen_special[3])
        y=(mG\(pi(el))).coeff
        for i = 1:cols(y)
          res[1, ngens(C) + i] = y[1, i]
        end
        if mod(n,2)==0 && !isempty(pr)
          b=lH(K(el))
          for i = 1:length(inf_plc)
            res[1, ngens(C)+cols(y)+i] = b[i]
          end
        end
        return X(res)
      else
        z=principal_gen_fac_elem(J)
        el = _fac_elem_evaluation(O, Q, quots, idemps, z, gcd(expo,n))
        y=(mG\(pi(el))).coeff
        for i = 1:cols(y)
          res[1, ngens(C) + i] = y[1, i]
        end
        if mod(n,2)==0 && !isempty(pr)
          b=lH(z)
          for i = 1:length(inf_plc)
            res[1, ngens(C)+cols(y)+i] = b[i]
          end
        end
        return X(res)
      end 
    else      
      W = mC\J
      for i = 1:ngens(C)
        res[1, i] = W[i]
      end
      s=exp_class(W)
      for (el,v) in s.fac
        s.fac[el] = -nonnclass*v
      end
      if haskey(s.fac, J)
        s.fac[J] += nonnclass
      else
        s.fac[J] = nonnclass
      end
      z = principal_gen_fac_elem(s)
      el = _fac_elem_evaluation(O, Q, quots, idemps, z, gcd(expo,n))
      y=(mG\(pi(el))).coeff
      for i = 1:cols(y)
        res[1, ngens(C) + i] = y[1, i]*inverse_d
      end
      if mod(n,2)==0 && !isempty(pr)
        b = lH(z)
        for i = 1:length(inf_plc)
          res[1, ngens(C)+cols(y)+i] = b[i]
        end
      end
      return X(res)
    end    
    
  end 

  #
  # Exponential map
  #

  function expon(a::GrpAbFinGenElem)
    b=C([a.coeff[1,i] for i=1:ngens(C)])
    if mod(n,2)!=0  || isempty(pr)
      c=G([a.coeff[1,i] for i=ngens(C)+1:ngens(X)])
      return exp_class(b)*ideal(O,mG(c).elem)
    else 
      c=T([a.coeff[1,i] for i=ngens(C)+1:ngens(T)+ngens(C)])
      d=H([a.coeff[1,i] for i=ngens(T)+ngens(C)+1: ngens(X)])
      el=mG(c).elem
      # I need to modify $el$ so that it has the correct sign at the embeddings contained in primes
      vect=(lH(K(el))).coeff
      if vect==d.coeff
        return exp_class(b)*ideal(O,el)
      else 
        correction=eH(d)
        while vect!=d.coeff
          el=el+correction
          vect=(lH(K(el))).coeff
        end
        return exp_class(b)*ideal(O,el)
      end 
    end
  end 
  
  for (prim, mprim) in tame
    dis = zero_matrix(FlintZZ, 1, ngens(X))
    to_be_c = mprim.disc_log.coeff
    for i = 1:length(to_be_c)
      dis[1, i+ngens(C)] = to_be_c[1, i]
    end
    mprim.disc_log = X(dis)
  end

  mp = Hecke.MapRayClassGrp{typeof(X)}()
  mp.header = Hecke.MapHeader(X, FacElemMon(parent(m)) , expon, disclog)
  mp.modulus_fin = I
  mp.quots_nquo = quots
  mp.idemps = idemps
  mp.coprime_elems = Kel
  mp.fact_mod = lp
  mp.tame_mult_grp = tame
  mp.wild_mult_grp = wild
  mp.defining_modulus = (m, inf_plc)

  if mod(n,2)==0
    mp.modulus_inf=pr
  else
    mp.modulus_inf=inf_plc
  end
  return X, mp
  
end

##################################################################################
#
#  Ray Class Group over QQ
#
##################################################################################

function ray_class_groupQQ(O::NfOrd, modulus::Int, inf_plc::Bool, n_quo::Int)

  R=ResidueRing(FlintZZ, modulus, cached=false)
  U,mU=unit_group_mod(R, n_quo)
  if inf_plc 
    function disc_log1(I::NfOrdIdl)
      @assert gcd(minimum(I),modulus)==1
      i=Int(mod(I.minimum, modulus))
      return mU\(R(i))
    end
    
    function expon1(a::GrpAbFinGenElem)
      x=mU(a)
      return FacElem(Dict{NfOrdIdl, fmpz}(ideal(O,lift(x)) => 1))
    end
    
    mp=Hecke.MapRayClassGrp{typeof(U)}()
    mp.header = Hecke.MapHeader(U, FacElemMon(parent(ideal(O,1))) , expon1, disc_log1)
    mp.modulus_fin = ideal(O,modulus)
    mp.modulus_inf = real_places(nf(O))
    mp.defining_modulus = (ideal(O, modulus), real_places(nf(O)))
    return U, mp
    
    
  elseif isodd(n_quo)
    
    function disc_log2(I::NfOrdIdl)
      @assert gcd(minimum(I),modulus)==1
      i=Int(mod(I.minimum, modulus))
      return mU\(R(i))
    end
    
    function expon2(a::GrpAbFinGenElem)
      x=mU(a)
      return FacElem(Dict{NfOrdIdl, fmpz}(ideal(O,lift(x)) => 1))
    end
    
    mp = Hecke.MapRayClassGrp{typeof(U)}()
    mp.header = Hecke.MapHeader(U, FacElemMon(parent(ideal(O,1))) , expon2, disc_log2)
    mp.modulus_fin = ideal(O, modulus)
    mp.modulus_inf = InfPlc[]
    mp.defining_modulus = (ideal(O, modulus), InfPlc[])

    return U,mp
  
  else
      
    Q,mQ=quo(U, [mU\(R(-1))])
    
    function disc_log(I::NfOrdIdl)
      i=Int(mod(minimum(I), modulus))
      return mQ(mU\(R(i)))
    end
    
    function expon(a::GrpAbFinGenElem)
      x=mU(mQ\a)
      return FacElem(Dict{NfOrdIdl, fmpz}(ideal(O,x) => 1))
    end
    
    mp=Hecke.MapRayClassGrp{typeof(Q)}()
    mp.header = Hecke.MapHeader(Q, FacElemMon(parent(ideal(O,1))) , expon, disc_log)
    mp.modulus_fin=ideal(O,modulus)
    mp.modulus_inf=[]
    mp.defining_modulus = (ideal(O, modulus), InfPlc[])
    return Q,mp

  end

end

##################################################################################
#
#  Action of the Galois Group on the Ray Class Group
#
##################################################################################

function change_into_coprime(mR::MapRayClassGrp, a::fmpz)

  m = minimum(mR.modulus_fin)
  com, uncom = ppio(a, m)
  if uncom == 1
    return nothing
  end
  _, s, t = gcdx(uncom, m)
  tmg = mR.tame_mult_grp
  wld = mR.wild_mult_grp
  for (p, v) in tmg
    new_p = GrpAbFinGenToNfAbsOrdMap(domain(v), codomain(v), [ m*t*v.generators[1] + s*uncom ], v.discrete_logarithm)
    if isdefined(v, :disc_log)
      new_p.disc_log = v.disc_log
    end
    tmg[p] = new_p
  end
  for (p, v) in wld
    wld[p] = GrpAbFinGenToNfAbsOrdMap(domain(v), codomain(v), [ m*t*v.generators[i] + s*uncom for i=1:length(v.generators)], v.discrete_logarithm)
  end
  return nothing
  
end


#
#  Find small primes that generate the ray class group (or a quotient)
#  It needs a map GrpAbFinGen -> NfOrdIdlSet
#
function find_gens(mR::MapRayClassGrp; coprime_to::fmpz = fmpz(-1))

  O = order(codomain(mR))
  R = domain(mR) 
  m = mR.defining_modulus[1]
  mm = minimum(m)
  if coprime_to != -1
    mm = lcm(mm, coprime_to)
  end

  sR = GrpAbFinGenElem[]
  lp = NfOrdIdl[]
  q, mq = quo(R, sR, false)
  
  #
  #  First, generators of the multiplicative group. 
  #  If the class group is trivial, they are enough 
  #
  if isdefined(mR, :fact_mod) && !isempty(mR.fact_mod) 
    if coprime_to != -1
      # First, I change them in order to be coprime to coprime_to
      change_into_coprime(mR, coprime_to)
    end
    if !isempty(mR.modulus_inf)
      @vtime :NfOrd 1 totally_positive_generators(mR, true)
    end
    tmg = mR.tame_mult_grp
    wld = mR.wild_mult_grp
    for (p, v) in tmg
      if isdefined(v, :disc_log)
        if iszero(mq(v.disc_log))
          continue
        end
        I = ideal(O, v.generators[1])
        push!(sR, v.disc_log)
        push!(lp, I)
      else
        I = ideal(O, v.generators[1])
        f = mR\I
        if iszero(mq(f))
          continue
        end
        push!(sR, f)
        push!(lp, I)
      end
      q, mq = quo(R, sR, false)
      if order(q) == 1 
        return lp,sR
      end
    end

    for (p,v) in wld
      for i=1:length(v.generators)
        I=ideal(O,v.generators[i])
        f=mR\I
        if iszero(mq(f))
          continue
        end
        push!(sR, f)
        push!(lp, I)
        q, mq = quo(R, sR, false)
        if order(q) == 1 
          return lp, sR
        end
      end
    end
  end
  
  
  if !isempty(mR.modulus_inf)
    S, ex, lo=carlos_units(O)
    for i=1:length(mR.modulus_inf)      
      pl=mR.modulus_inf[i]
      @assert isreal(pl)
      delta=mm*ex(S[i])
      el=1+delta
      con=abs_upper_bound(1/real(conjugates_arb(delta))[i], fmpz)
      el+=con*delta
      I=ideal(O,el)
      f=mR\I
      if iszero(mq(f))
        continue
      end
      push!(sR, f)
      push!(lp, I)
      q, mq = quo(R, sR, false)
      if order(q)==1
        return lp, sR
      end
    end
  
  end
  
  if isdefined(mR, :prime_ideal_cache)
    S = mR.prime_ideal_cache
  else
    S = prime_ideals_up_to(O, max(1000,4*clog(discriminant(O),10)^2), degree_limit = 1, index_divisors = false)
    mR.prime_ideal_cache = S
  end
  q, mq = quo(R, sR, false)
  for P in S
    if gcd(minimum(P), mm) != 1
      continue
    end
    if coprime_to != -1 &&  gcd(minimum(P), coprime_to) != 1
      continue
    end
    if haskey(mR.prime_ideal_preimage_cache, P)
      f = mR.prime_ideal_preimage_cache[P]
    else
      f = mR\P
      mR.prime_ideal_preimage_cache[P] = f
    end
    if iszero(mq(f))
      continue
    end
    push!(sR, f)
    push!(lp, P)
    q, mq = quo(R, sR, false)
    if order(q) == 1 
      break
    end
  end
  @assert order(q) == 1
  return lp, sR
end

function induce_action(mR::MapRayClassGrp, Aut::Array{Hecke.NfToNfMor, 1} = Hecke.NfToNfMor[], mp = false)

  R=mR.header.domain
  O=mR.header.codomain.base_ring.order
  K=nf(O)
   
  if isempty(Aut)
    Aut = automorphisms(K)
    Aut = small_generating_set(Aut, *)
  end
  if ngens(R)==0
    return GrpAbFinGenMap[]
  end
  
  G = Array{GrpAbFinGenMap,1}(undef, length(Aut))
  #
  #  Instead of applying the automorphisms to the elements given by mR, I choose small primes 
  #  generating the group and study the action on them. In this way, I take advantage of the cache of the 
  #  class group map
  #

  lgens, subs = find_gens(mR) 
  if isempty(lgens)
    push!(G, GrpAbFinGenMap(R))
    return G
  end

  for k=1:length(Aut)
    images = Array{GrpAbFinGenElem,1}(undef, length(lgens))
    for i=1:length(lgens) 
      #println("Elem: $(subs[i].coeff)")
      @vtime :RayFacElem 3 J = induce_image(lgens[i], Aut[k])
      @vtime :RayFacElem 3 images[i] = mR\J
      #println("Image: $(images[i].coeff)")
    end
    if mp == false
      G[k] = hom(subs, images, check = true)
    else
      G[k] = hom([mp(x) for x = subs], [mp(x) for x = images], check = true)
    end
    @hassert :RayFacElem 1 isbijective(G[k])
  end
  return G
  
end

################################################################################
#
#  Generator 1 mod m
# 
################################################################################

@doc Markdown.doc"""
    has_principal_gen_1_mod_m(I::NfOrdIdl, m::NfOrdIdl, inf_plc::Array{InfPlc, 1} = InfPlc[]) -> Bool, NfOrdElem
    
> Given an ideal I, this function checks if the ideal is trivial in the ray class group mod ($m$, inf_plc).
  If this is the case, we also return a generator which is 1 mod $m$. If not, the second return value is wrong.

"""
function principal_gen_1_mod_m(I::NfOrdIdl, m::NfOrdIdl, inf_plc::Array{InfPlc, 1} = InfPlc[])

  # This function could be optimized if I cache some stuff from the construction
  # of the ray class group, but only in the case of the full ray_class_group
  # and not in the quotient.

  @assert iscoprime(I, m)
  O = order(I)
  C, mC = class_group(O)
  fl, gen = isprincipal_fac_elem(I)
  if !fl
    return false, O(0)
  end
  U, mU = unit_group_fac_elem(O)
  
  Q, mQ = quo(O, m)
  G, mG = multiplicative_group(Q)
  lp = Q.factor
  expo = exponent(G)
  tobeeval = FacElem{nf_elem, AnticNumberField}[mU(x) for x in gens(U)]
  push!(tobeeval, gen)
  evals = fac_elems_eval(O, Q, tobeeval, lp, expo)[1]
  els = GrpAbFinGenElem[mG\(Q(evals[i])) for i in 1:length(evals)-1]
  elgen = mG\(Q(evals[end]))
  if isempty(inf_plc)
    S, mS = sub(G, els)
    fl1, coord = haspreimage(mS, elgen)
  else
    #I have to take into account the signs!
    H, eH, lH = Hecke._infinite_primes(O, inf_plc, m)
    GH, iG, iH = direct_product(G, H)
    els_inf = GrpAbFinGenElem[lH(mU(U[i])) for i = 1:ngens(U)]
    els_tot = [iG(els[i]) + iH(els_inf[i]) for i = 1:ngens(U)]
    S, mS = sub(GH, els_tot)
    elgen = iG(elgen) + iH(lH(gen))
    fl1, coord = haspreimage(mS, elgen)
  end
  if !fl1
    return false, O(0)
  end
  @assert ngens(S) == ngens(U)
  for i = 1:ngens(U)
    if coord[i] != 0
      gen *= mU(U[i])^-Int(coord[i])
    end
  end
  return true, gen

end

function principal_gen_1_mod_m(I::FacElem{NfOrdIdl, NfOrdIdlSet}, m::NfOrdIdl, inf_plc::Array{InfPlc, 1} = InfPlc[])

  # This function could be optimized if I cache some stuff from the construction
  # of the ray class group, but only in the case of the full ray_class_group
  # and not in the quotient.

  O = order(m)
  C, mC = class_group(O)
  fl, gen = isprincipal_fac_elem(I)
  if !fl
    return fl, gen
  end
  U, mU = unit_group_fac_elem(O)
  
  Q, mQ = quo(O, m)
  G, mG = multiplicative_group(Q)
  lp = Q.factor
  expo = exponent(G)
  tobeeval = FacElem{nf_elem, AnticNumberField}[mU(x) for x in gens(U)]
  push!(tobeeval, gen)
  evals = fac_elems_eval(O, Q, tobeeval, lp, expo)[1]
  els = GrpAbFinGenElem[mG\(Q(evals[i])) for i in 1:length(evals)-1]
  elgen = mG\(Q(evals[end]))
  if isempty(inf_plc)
    S, mS = sub(G, els)
    fl1, coord = haspreimage(mS, elgen)
  else
    #I have to take into account the signs!
    H, eH, lH = Hecke._infinite_primes(O, inf_plc, m)
    GH, iG, iH = direct_product(G, H)
    els_inf = GrpAbFinGenElem[lH(mU(U[i])) for i = 1:ngens(U)]
    els_tot = [iG(els[i]) + iH(els_inf[i]) for i = 1:ngens(U)]
    S, mS = sub(GH, els_tot)
    elgen = iG(elgen) + iH(lH(gen))
    fl1, coord = haspreimage(mS, elgen)
  end
  if !fl1
    return false, gen
  end
  @assert ngens(S) == ngens(U)
  for i = 1:ngens(U)
    if coord[i] != 0
      gen *= mU(U[i])^-Int(coord[i])
    end
  end
  return true, gen

end

function disc_log_generalized_ray_class_grp(I::NfOrdIdl, mr::MapRayClassGrp)
  
  R = domain(mr)
  el = mr\I
  lI = Array{Tuple{FacElem{NfOrdIdl, NfOrdIdlSet}, Int}, 1}(undef, ngens(R))
  J = codomain(mr)()
  for i = 1:ngens(R)
    lI[i] = (mr(R[i]), Int(el[i]))
    J *= lI[i][1]^lI[i][2]
  end
  I1 = I * inv(J)
  fl1 , gen1 = principal_gen_1_mod_m(I1, mr.modulus_fin, mr.modulus_inf)
  @assert fl1
  return gen1, lI
  
end


###############################################################################
#
#  Ray Class Group: Field function
#
###############################################################################

function ray_class_group_quo(O::NfOrd, n_quo::Int, m::Int, wprimes::Dict{NfOrdIdl,Int}, inf_plc::Array{InfPlc,1}, units::Vector{NfOrdElem}, mC::MapClassGrp, princ_gens::Vector{NfOrdElem}, vect::Vector{fmpz})
  
  K=nf(O)
  d1=Dict{NfOrdIdl, Int}()
  lp=factor(m)
  for q in keys(lp.fac)
    lq=prime_decomposition(O,q) 
    for (P,e) in lq
      d1[P]=1
    end   
  end
  I = ideal(O, m)
  for (p, v) in wprimes
    I *= p^v
  end
  return ray_class_group_quo(n_quo, I, d1, wprimes, inf_plc, units, mC, princ_gens, vect)
  
end

function log_infinite_primes(O::NfOrd, p::Array{InfPlc,1})
    
    S = DiagonalGroup([2 for i=1:length(p)])

    function log(B::nf_elem)
      emb=Hecke.signs(B, p)
      ar = [0 for i = 1:length(p)]
      for i=1:length(p)
        if emb[p[i]] == -1
          ar[i] = 1
        end
      end
      return S(ar)
    end 
    
    function log(B::FacElem{nf_elem})
      emb=Hecke.signs(B,p)
      ar = [0 for i = 1:length(p)]
      for i=1:length(p)
        if emb[p[i]] == -1
          ar[i] = 1
        end
      end
      return S(ar)
    end 
  return S, log
  
end

function ray_class_group_quo(n::Integer, I::NfOrdIdl, y1::Dict{NfOrdIdl,Int}, y2::Dict{NfOrdIdl,Int}, inf_plc::Vector{InfPlc}, units::Vector{NfOrdElem}, mC::MapClassGrp, princ_gens::Vector{NfOrdElem}, vect::Vector{fmpz})

  O=order(I)
  K=nf(O)
  @assert length(y1) + length(y2) == 0 || !isone(I)
  
  lp=merge(max, y1, y2)
  
  Q,pi = quo(O, I)
  Q.factor = lp
  C = domain(mC)
  
  @vtime :RayFacElem 1 G, mG, tame, wild= _mult_grp_mod_n(Q, y1, y2, n)
  if mod(n,2)==0 && !isempty(inf_plc)
    @vtime :RayFacElem 1 H, lH = Hecke.log_infinite_primes(O, inf_plc)
    T = G
    G = Hecke.direct_product(G, H)[1]
  end
  expo = exponent(G)
  
  if exponent(C)*expo < n
    return empty_ray_class(I)
  end
  
  C1, mC1 = class_group(O) 
  valclass, nonnclass = ppio(exponent(C1), fmpz(n))
  U, mU = unit_group_fac_elem(O)

  exp_class, Kel = Hecke._elements_to_coprime_ideal(C, mC, I)
  
  if order(G)==1
    return class_as_ray_class(C, mC, exp_class, I, n)    
  end
  
#
# We start to construct the relation matrix
#

  
  R = zero_matrix(FlintZZ, 2*ngens(C)+ngens(U)+2*ngens(G), ngens(C)+ngens(G))
  for i=1:cols(R)
    R[ngens(C)+ngens(U)+ngens(G)+i,i] = n
  end
  for i=1:ngens(C)
    R[i,i]=C.snf[i]
  end
  if issnf(G)
    for i=1:ngens(G)
      R[i+ngens(C),i+ngens(C)]=G.snf[i]
    end
  else
    for i=1:ngens(G)
      R[i+ngens(C),i+ngens(C)]=G.rels[i,i]
    end
  end
  
  
#
# We compute the relation matrix given by the image of the map U -> (O/m)^*
#

  @hassert :RayFacElem 1 issnf(U)
  @vprint :RayFacElem 1 "Collecting elements to be evaluated; first, units \n"
  to_be_eval = Vector{NfOrdElem}(undef, ngens(C) + ngens(U))
  for i = 1:length(units)
    to_be_eval[i] = units[i]
  end
  for i = 1:ngens(C)
    expokel = mod(C.snf[i]*vect[i], fmpz(n))
    numkel = numerator(Kel[i])
    denkel = denominator(Kel[i])
    mul!(numkel, princ_gens[i].elem_in_nf, numkel^expokel)
    if denkel != 1
      numkel *= denkel^(mod(-expokel, fmpz(n)))
    end
    to_be_eval[i+length(units)] = O(numkel)
  end
  @vprint :RayFacElem 1 "Time for elements evaluation: "
  @vtime :RayFacElem 1 evals, quots, idemps = _crt_normalization(O, Q, to_be_eval, lp)
  @vprint :RayFacElem 1 "\n"
  
  for i=1:ngens(U)
    @vprint :RayFacElem 1 "Disclog of unit $i \n"
    a=(mG\(evals[i])).coeff
    for j = 1:cols(a)
      R[i+ngens(G)+ngens(C), ngens(C)+j] = a[1, j]
    end
    if mod(n, 2)==0 && !isempty(inf_plc)
      if i==1
        for j = 1:length(inf_plc)
          R[i+ngens(G)+ngens(C), ngens(C)+cols(a)+j] = 1
        end
      else
        b = lH(mU(U[i]))
        for j = 1:length(inf_plc)
          R[i+ngens(G)+ngens(C), ngens(C)+cols(a)+j] = b[j]
        end
      end
    end

  end 

  # 
  # We compute the relation between generators of Cl and (O/m)^* in Cl^m
  #

  for i=1:ngens(C)
    @vprint :RayFacElem 1 "Disclog of class group element $i \n"
    invn=invmod(vect[i],fmpz(expo))
    a=((mG\(evals[i+ngens(U)]))*invn).coeff
    for j = 1:length(a)
      R[i,ngens(C)+j]=-a[1,j]
    end
    if mod(n,2)==0 && !isempty(inf_plc)
      b = lH(mC.princ_gens[i][2]*(Kel[i]^(C.snf[i]*vect[i]))).coeff
      for j = 1:cols(b)
        R[i, ngens(C)+cols(a)+j] = -b[1, j]
      end
    end
  end
  
  X = AbelianGroup(R)
  
  disc_log_inf = Dict{InfPlc, GrpAbFinGenElem}()
  for i = 1:length(inf_plc)
    eldi = zeros(FlintZZ, cols(R))
    eldi[cols(R) - length(inf_plc) + i] = 1
    disc_log_inf[inf_plc[i]] = X(eldi)
  end
   
  #
  # Discrete logarithm
  #
  inverse_d = invmod(nonnclass, expo)
  
  function disclog(J::NfOrdIdl)
    
    res = zero_matrix(FlintZZ, 1, ngens(X))
    @hassert :RayFacElem 1 iscoprime(J,I)
    if J.is_principal==1
      if isdefined(J,:princ_gen)
        el = J.princ_gen
        y = (mG\(pi(el))).coeff
        for i = 1:cols(y)
          res[1, ngens(C) + i] = y[1, i]
        end
        if iszero(mod(n,2)) && !isempty(inf_plc)
          b = lH(K(el))
          for i = 1:length(inf_plc)
            res[1, ngens(C)+cols(y)+i] = b[i]
          end
        end
        return X(res)
      elseif isdefined(J,:princ_gen_special)
        el=O(J.princ_gen_special[2])+O(J.princ_gen_special[3])
        y=(mG\(pi(el))).coeff
        for i = 1:cols(y)
          res[1, i+ngens(C)] = y[1, i]
        end
        if iszero(mod(n,2)) && !isempty(pr)
          b = lH(K(el)).coeff
          for i = 1:cols(b)
            res[1, i+ngens(C)+cols(y)] = b[1, i]
          end
        end
        return X(res)
      else
        z = principal_gen_fac_elem(J)
        el = _fac_elem_evaluation(O, Q, quots, idemps, z, gcd(expo,n))
        y = (mG\(pi(el))).coeff
        for i = 1:cols(y)
          res[1, i+ngens(C)] = y[1, i]
        end
        if mod(n,2)==0 && !isempty(inf_plc)
          b=lH(z).coeff
          for i = 1:cols(b)
            res[1, i+ngens(C)+cols(y)] = b[1, i]
          end
        end
        return X(res)
      end 
    else      
      W = mC\J
      for i = 1:ngens(C)
        res[1, i] = W[i]
      end
      s = exp_class(W)
      pow!(s, -nonnclass)
      if haskey(s.fac, J)
        s.fac[J] += nonnclass
      else
        s.fac[J] = nonnclass
      end
      z = principal_gen_fac_elem(s)
      el = _fac_elem_evaluation(O, Q, quots, idemps, z, gcd(expo,n))
      y=(mG\(pi(el))).coeff
      for i = 1:cols(y)
        res[1, i+ngens(C)] = y[1, i]*inverse_d
      end
      if mod(n,2)==0 && !isempty(inf_plc)
        b=lH(z).coeff
        for i = 1:cols(b)
          res[1, i+ngens(C)+cols(y)] = b[1, i]
        end
      end
      return X(res)
    end    
    
  end 
  
  for (prim, mprim) in tame
    dis = zero_matrix(FlintZZ, 1, ngens(X))
    to_be_c = mprim.disc_log.coeff
    for i = 1:length(to_be_c)
      dis[1, i+ngens(C)] = to_be_c[1, i]
    end
    mprim.disc_log = X(dis)
  end

  mp = Hecke.MapRayClassGrp{typeof(X)}()
  mp.header = Hecke.MapHeader(X, FacElemMon(parent(I)))
  mp.header.preimage = disclog
  mp.modulus_fin = I
  mp.modulus_inf = inf_plc
  mp.quots_nquo = quots
  mp.idemps = idemps
  mp.coprime_elems = Kel
  mp.fact_mod = lp
  mp.tame_mult_grp = tame
  mp.wild_mult_grp = wild
  mp.defining_modulus = (I, inf_plc)
  mp.disc_log_inf_plc = disc_log_inf
  return X, mp
  
end
#
#  Find small primes that generate the ray class group (or a quotient)
#  It needs a map GrpAbFinGen -> NfOrdIdlSet
#
function find_gens_for_action(mR::MapRayClassGrp)

  O = order(codomain(mR))
  R = domain(mR) 
  m = mR.defining_modulus[1]
  mm = minimum(m)
  lp = NfOrdIdl[]
  sR = GrpAbFinGenElem[]
  ip = InfPlc[]
  sR1 = GrpAbFinGenElem[]
  q, mq = quo(R, sR, false)
  
  #
  #  First, generators of the multiplicative group. 
  #  If the class group is trivial, they are enough 
  #
  if isdefined(mR, :fact_mod) && !isempty(mR.fact_mod) 
    if !isempty(mR.modulus_inf)
      @vtime :NfOrd 1 totally_positive_generators(mR, true)
    end
    tmg = mR.tame_mult_grp
    wld = mR.wild_mult_grp
    for (p, v) in tmg
      if isdefined(v, :disc_log)
        if iszero(mq(v.disc_log))
          continue
        end
        I = ideal(O, v.generators[1])
        push!(sR, v.disc_log)
        push!(lp, I)
      else
        I = ideal(O, v.generators[1])
        f = mR\I
        if iszero(mq(f))
          continue
        end
        push!(sR, f)
        push!(lp, I)
      end
      q, mq = quo(R, sR, false)
      if order(q) == 1 
        return lp, ip, sR, sR1
      end
    end

    for (p,v) in wld
      for i=1:length(v.generators)
        I=ideal(O,v.generators[i])
        f=mR\I
        if iszero(mq(f))
          continue
        end
        push!(sR, f)
        push!(lp, I)
        q, mq = quo(R, sR, false)
        if order(q) == 1 
          return lp, ip, sR, sR1
        end
      end
    end
  end
  
  
  if !isempty(mR.modulus_inf)
    dlog_dict = mR.disc_log_inf_plc
    for (p, v) in dlog_dict
      if iszero(mq(v))
        continue
      end
      push!(ip, p)
      push!(sR1, v)
      q, mq = quo(R, vcat(sR, sR1), false)
      if order(q) == 1 
        return lp, ip, sR, sR1
      end
    end
  end
  
  if isdefined(mR, :prime_ideal_cache)
    S = mR.prime_ideal_cache
  else
    S = prime_ideals_up_to(O, max(1000,4*clog(discriminant(O),10)^2), degree_limit = 1, index_divisors = false)
    mR.prime_ideal_cache = S
  end

  for P in S
    if gcd(minimum(P), mm) != 1
      continue
    end
    if haskey(mR.prime_ideal_preimage_cache, P)
      f = mR.prime_ideal_preimage_cache[P]
    else
      f = mR\P
      mR.prime_ideal_preimage_cache[P] = f
    end
    if iszero(mq(f))
      continue
    end
    push!(sR, f)
    push!(lp, P)
    q, mq = quo(R, vcat(sR, sR1), false)
    if order(q) == 1 
      break
    end
  end
  @assert order(q) == 1
  return lp, ip, sR, sR1
end

function induce_action_new(mR::MapRayClassGrp, Aut::Array{Hecke.NfToNfMor, 1})

  G = Array{GrpAbFinGenMap,1}(undef, length(Aut))
  #  Instead of applying the automorphisms to the elements given by mR, I choose small primes 
  #  generating the group and study the action on them. In this way, I take advantage of the cache of the 
  #  class group map
  Igens, IPgens, subs, IPsubs = find_gens_for_action(mR) 
  genstot = vcat(subs, IPsubs)
  for k=1:length(Aut)
    images = Array{GrpAbFinGenElem,1}(undef, length(Igens)+length(IPgens))
    for i=1:length(Igens) 
      #println("Elem: $(subs[i].coeff)")
      @vtime :RayFacElem 3 J = induce_image(Igens[i], Aut[k])
      @vtime :RayFacElem 3 images[i] = mR\J
      #println("Image: $(images[i].coeff)")
    end
    for i = 1:length(IPgens)
      #println("Elem: $(IPsubs[i].coeff)")
      Pn = induce_image(IPgens[i], Aut[k])
      images[i+length(Igens)] = mR.disc_log_inf_plc[Pn]
      #println("Image: $(images[i+length(Igens)].coeff)")
    end
    G[k] = hom(genstot, images, check = true)
    @hassert :RayFacElem 1 isbijective(G[k])
  end
  return G
  
end

