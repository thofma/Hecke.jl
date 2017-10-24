
export ray_class_group, stable_subgroups

add_verbose_scope(:RayFacElem)

###############################################################################
#  
#  Map Type
#
###############################################################################


mutable struct MapRayClassGrp{T} <: Map{T, FacElemMon{Hecke.NfOrdIdlSet}}
  header::Hecke.MapHeader
  modulus_fin::NfOrdIdl
  modulus_inf::Array{InfPlc,1}
  fact_mod::Dict{NfOrdIdl, Int}
  
  function MapRayClassGrp{T}() where {T}
    return new{T}()
  end
end


###############################################################################
#
#  Ray Class Group interface
#
###############################################################################


doc"""
***
    ray_class_group(m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[]; p_part,n_quo)
    
> Given a modulus with finite part $m$ and infinite part inf_plc, it returns the Ray Class Group Cl_m. If p_part is given, the function will return the largest quotient of the Ray Class Group of p-power order. If n_quo is given, it will return the quotient of the Ray Class Group by n

"""

function ray_class_group(m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[]; p_part=0, n_quo=0)

  if p_part!=0
    @assert isprime(fmpz(p_part))
    return ray_class_group_p_part(p_part, m, inf_plc)
  elseif n_quo!=0
    return ray_class_group(n_quo,m,inf_plc)
  else 
    return ray_class_group_fac_elem(m,inf_plc)
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


function fac_elems_eval(O::NfOrd, Q::NfOrdQuoRing, elems::Array{FacElem{nf_elem, AnticNumberField},1}, lp::Dict{NfOrdIdl, Int}, exponent::Int)

  newelems=_preproc(O,elems,exponent)
  quots=[]
  idemps=[]
  el=[Q(1) for i=1:length(newelems)]
  I=ideal(O,1)
  for (p,vp) in lp
    q=p^vp
    y, Qn=_eval_quo(O, newelems, p, q, anti_uniformizer(p), vp, exponent)
    push!(quots,Qn)
    a,b=idempotents(I,q)
    push!(idemps,(a,b))
    for i=1:length(el)
      el[i]=Q(y[i])*Q(a)+el[i]*Q(b)
    end
    I=I*q
  end
  return el, quots, idemps

end

#
#  Reduces the elements modulo the exponents and computes a representation as a product of elements in O
#

function _preproc(O::NfOrd, elems::Array{FacElem{nf_elem, AnticNumberField},1}, exponent::Int)
  
  assure_has_basis_mat_inv(O)
  M = O.tcontain
  newelems=FacElem{NfOrdElem, NfOrd}[]
  for el in elems
    x=Dict{NfOrdElem, fmpz}()
    for (f,k) in el.fac
      l=mod(k,exponent)
      if !iszero(l)
        elem_to_mat_row!(M.num, 1, M.den, f)
        M = mul!(M, M, O.basis_mat_inv)
        if M.den==1
          el=O(vec(Array(M.num)))
          if haskey(x,el)
            x[el]+=l
          else
            x[el]=l
          end
        else
          d=O(M.den)
          n=O(vec(Array(M.num)))
          if haskey(x,n)
            x[n]=mod(x[n]+l,exponent)
          else
            x[n]=l
          end
          if haskey(x,d)
            x[d]=mod(x[d]+exponent-l,exponent)
          else
            x[d]=exponent-l
          end
        end
      end
    end
    if !isempty(x)
      push!(newelems, FacElem(x))
    else 
      K=parent(first(keys(elems.fac)))
      push!(newelems,FacElem(Dict(K(1)=> 1)))
    end
  end
  return newelems

end


function _eval_quo(O::NfOrd, elems::Array{FacElem{NfOrdElem, NfOrd},1}, p::NfOrdIdl, q::NfOrdIdl, anti_uni::nf_elem, mult::Int, exp::Int)
  
  if mult==1
    @vtime :RayFacElem 2 Q,mQ=ResidueField(O,p)
    el=[Q(1) for i=1:length(elems)]
    for i=1:length(elems)
      J=elems[i]
      neg_el=Q(1)
      for (f,k) in J.fac
        act_el=f
        if mQ(act_el)!=0
          el[i]*=mQ(act_el)^k
          continue
        end
        val=valuation(act_el,p)
        act_el=O(act_el*(anti_uni^val),false)
        el[i]*= mQ(O(act_el))^k
      end
    end
    return [mQ\el[i] for i=1:length(el)], (Q,mQ)
  else
    @vtime :RayFacElem 2 Q,mQ=quo(O,q)
    el=[Q(1) for i=1:length(elems)]
    for i=1:length(elems)
      J=elems[i]
      for (f,k) in J.fac
        act_el=f
        if mod(act_el, p)!=0
          el[i]*=mQ(act_el)^k
          continue
        end
        val=valuation(act_el,p)
        act_el=O(act_el*(anti_uni^val),false)
        el[i]*=Q(act_el)^k
      end
    end
    return [mQ\el[i] for i=1:length(el)], Q
  end
 
end


#
#  Single element evaluation (for the disclog)
#


function _fac_elem_evaluation(O::NfOrd, Q::NfOrdQuoRing, quots::Array, idemps::Array, J::FacElem{nf_elem,AnticNumberField}, primes::Dict{NfOrdIdl, Int}, exponent::Int)
  
  assure_has_basis_mat_inv(O)
  M=O.tcontain
  element=Q(1)
  i=0
  #Reduce the exponents and reduce to elements in O
  x=Dict{NfOrdElem, fmpz}()
  for (f,k) in J.fac
    l=mod(k,exponent)
    if !iszero(l)
      elem_to_mat_row!(M.num, 1, M.den, f)
      M = mul!(M, M, O.basis_mat_inv)
      if M.den==1
        el=O(vec(Array(M.num)))
        if haskey(x,el)
          x[el]=mod(x[el]+l,exponent)
        else
          x[el]=l
        end
      else
        d=O(M.den)
        n=O(vec(Array(M.num)))
        if haskey(x,n)
          x[n]=mod(x[n]+l,exponent)
        else
          x[n]=l
        end
        if haskey(x,d)
          x[d]=mod(x[d]+exponent-l,exponent)
        else
          x[d]=exponent-l
        end
      end
    end
  end
  if isempty(x)
    return el
  end
  tobeeval=FacElem(x)
  for (p,vp) in primes
    i+=1
    y=_eval_quo(O, quots[i], tobeeval, p, anti_uniformizer(p), vp)
    a,b=idemps[i]
    element=Q(Q(y)*Q(a)+element*Q(b))
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
#  Ray Class Group - Auxiliary functions
#
###############################################################################

#
# Function that finds the generators of the infinite part
#

function _infinite_primes(O::NfOrd, p::Array{InfPlc,1}, m::NfOrdIdl)

  K=O.nf
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
    emb=signs(K(a),p)
    t=S([emb[x]==1 ? 0 : 1 for x in collect(keys(emb))])
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
  hS = Hecke.GrpAbFinGenMap(S, S, vcat([x.coeff for x in s]))   # Change of coordinates so that the canonical basis elements are mapped to the elements found above
  r = elem_type(O)[]
  for i=1:length(p)
    y = haspreimage(hS,S[i])[2]
    push!(r, prod([g[i]^Int(y[i]) for i=1:length(p)]))
  end

  function exp(A::GrpAbFinGenElem)
    
    s=O(abs(m.gen_one))
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
    return S([emb[x]==1 ? 0 : 1 for x in collect(keys(emb))])
  end 
  
  function log(B::FacElem{nf_elem})
    emb=Hecke.signs(B,p)
    return S([emb[x]==1 ? 0 : 1 for x in collect(keys(emb))])
  end 
  
  return S,log,exp

end


#
#  Changes the exponential map of the class group so that the chosen representatives are coprime to the modulus
#

function _coprime_ideal(C::GrpAbFinGen, mC::Map, m::NfOrdIdl)
 
  O=parent(m).order
  K=nf(O)
  L=NfOrdIdl[]
  
  for i=1:ngens(C)
    a=mC(C[i])
    if iscoprime(a,m)
      push!(L,a)
    else  
      J=inv(a)
      s=K(rand(J.num,5))//J.den  # Is the bound acceptable?
      I=s*a
      simplify(I)
      I = num(I)
      while !iscoprime(I,m)
        s=K(rand(J.num,5))//J.den  
        I=s*a
        simplify(I)
        I = num(I)
      end
      push!(L,I)
    end
  end
  
  function exp(a::GrpAbFinGenElem)  
    e=FacElem(Dict{NfOrdIdl,fmpz}(ideal(O,1) => fmpz(1)))
    for i=1:ngens(C)
      if Int(a.coeff[1,i])!= 0
        e*=FacElem(Dict(L[i] => a.coeff[1,i]))
      end
    end
    return e
  end
  
  return exp

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
  mp.modulus_inf=InfPlc[]
    
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
    mp.modulus_inf=InfPlc[]
    
    return X,mp

end


###################################################################################
#
#  Ray Class Group
#
###################################################################################


function ray_class_group_fac_elem(m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[])

#
# We compute the group using the sequence U -> (O/m)^* _> Cl^m -> Cl -> 1
# First of all, we compute all these groups with their own maps
#  

  O=parent(m).order
  K=nf(O)
  

  C, mC = class_group(O)

  exp_class=Hecke._coprime_ideal(C,mC,m)
  U, mU = unit_group_fac_elem(O)
  Q, pi= quo(O,m)
  G, mG=unit_group(Q)
  
  lp=Q.factor
  
  p = [ x for x in inf_plc if isreal(x) ]
  if !isempty(p)
    H,lH,eH=Hecke._infinite_primes(O,p,m)
    T=G
    G=direct_product(G,H)
  end
  
  @vprint :RayFacElem 1 "The multiplicative group is $G \n"
  @vprint :RayFacElem 1 "The class group is $C \n"
  @vprint :RayFacElem 1 "The units are $U \n"
    
  expon=Int(exponent(G))

#
# We construct the relation matrix and evaluate units and relations with the class group in the quotient by m
# Then we compute the discrete logarithms
#

  R=zero_matrix(FlintZZ,ngens(C)+ngens(U)+ngens(G), ngens(C)+ngens(G))
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
 

  @vprint :RayFacElem 1 "Collecting elements to be evaluated; first, units \n"
  evals=[]
  tobeeval=FacElem{nf_elem, AnticNumberField}[]
  if U.snf[1]==2
    push!(evals,O(-1))
  else
    push!(tobeeval, mU(U[1]))
  end
  append!(tobeeval,[mU(U[i]) for i=2:ngens(U)])
  
  @vprint :RayFacElem 1 "then principal ideal generators \n"
  princ_gens=[]
  for i=1:ngens(C)
    @vtime :RayFacElem 1 push!(princ_gens, Hecke.principal_gen_fac_elem((exp_class(C[i]))^(Int(order(C[i])))))
  end
  append!(tobeeval,princ_gens)
  
  @vprint :RayFacElem 1 "Time for elements evaluation: "
  @vtime :RayFacElem 1 ev,quots,idemps=fac_elems_eval(O,Q,tobeeval,lp,expon)
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

  for i=1: ngens(C)
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

  mp=MapRayClassGrp{typeof(X)}()
  mp.header = Hecke.MapHeader(X, FacElemMon(parent(m)), expo, disclog)
  mp.modulus_fin=m
  mp.modulus_inf=p
  mp.fact_mod=Q.factor
  return X, mp
  
end


########################################################
#
#  Ray Class Group - p-part
#
########################################################


function prime_part_multgrp_mod_p(p::NfOrdIdl, prime::Int)
  @hassert :NfOrdQuoRing 2 isprime(p)
  O = order(p)
  Q , mQ = ResidueField(O,p)
  
  n = norm(p) - 1
  s=valuation(n,prime)
  powerp=prime^s
  m=div(n,powerp)
  
  powm=div(powerp,prime)
  found=false
  g=Q(1)
  while found==false
    g = rand(Q)
    if g != Q(0) 
      g=g^m
      if g^powm != Q(1) 
        found=true
      end
    end
  end
  inv=gcdx(m,fmpz(powerp))[2]
  
  function disclog(x::NfOrdElem)
    t=mQ(x)^m
    if powerp<10
      w=1
      el=g
      while el!=t
        w+=1
        el*=g
      end
      return [w*inv]
    else
      return [Hecke._pohlig_hellman_prime_power(g,prime,s,t)*inv]
    end
  end
  
  return mQ\g , [powerp], disclog
end


function _mult_grp(Q::NfOrdQuoRing, p::Integer)

  O=Q.base_ring
  K=nf(O)

  
  gens = Vector{NfOrdQuoRingElem}()
  structt = Vector{fmpz}()
  disc_logs = Vector{Function}()
  
  
  fac=factor(Q.ideal)
  Q.factor=fac
  y1=Dict{NfOrdIdl,Int}()
  y2=Dict{NfOrdIdl,Int}()
  for (q,e) in fac
    if divisible(norm(q)-1,p)
      y1[q]=Int(1)
    else 
      if divisible(norm(q),p) && e>=2
        y2[q]=Int(e)
      end
    end
  end
  
  prime_power=Dict{NfOrdIdl, NfOrdIdl}()
  for (q,vq) in fac
    prime_power[q]=q^vq
  end
  
  for (q,vq) in y1
    gens_q , struct_q , dlog_q = prime_part_multgrp_mod_p(q,p)
  
    # Make generators coprime to other primes
    if length(fac) > 1
      i_without_q = 1
      for (q2,vq2) in fac
        (q != q2) && (i_without_q *= prime_power[q2])
      end
      alpha, beta = idempotents(prime_power[q] ,i_without_q)
      gens_q = beta*gens_q + alpha
    end
 
    append!(gens,[Q(gens_q)])
    append!(structt,struct_q)
    push!(disc_logs,dlog_q)
  
  end
  for (q,vq) in y2
    gens_q, snf_q, disclog_q = Hecke._1_plus_p_mod_1_plus_pv(q,vq)

    # Make generators coprime to other primes
    nq=norm(q)-1
    
    if length(fac) > 1
      i_without_q = 1
      for (p2,vp2) in fac
        (q != p2) && (i_without_q *= prime_power[p2])
      end

      alpha, beta = idempotents(prime_power[q],i_without_q)
      for i in 1:length(gens_q)
        gens_q[i] = beta*gens_q[i] + alpha
      end
    end
    
    ciclmax=prod(Set(snf_q))
    inv=gcdx(nq,ciclmax)[2]
    
    function dlog_q_norm(x::NfOrdElem)
      y=Q(x)^Int(nq)
      y=disclog_q(y.elem)
      for i=1:length(y)
        y[i]*=inv
      end
      return y
    end
        
    gens_q = map(Q,gens_q)
    append!(gens,gens_q)
    append!(structt,snf_q)
    push!(disc_logs,dlog_q_norm)
  end 
  
  G=DiagonalGroup(structt)
  
  function exp(a::GrpAbFinGenElem)
    
    x=Q(1)
    for i=1:ngens(G)
      if Int(a.coeff[1,i])!= 0
        x=x*(gens[i]^(Int(a.coeff[1,i])))
      end
    end
    return x
  
  end
  
  function dlog(x::NfOrdElem)
    result = Vector{fmpz}()
    for disclog in disc_logs
      append!(result,disclog(x))
    end
    return G(result)
  end
  
  mG=Hecke.AbToResRingMultGrp(G,Q,exp,dlog)
  
  return G, mG, merge(y1, y2)
end




function ray_class_group_p_part(p::Integer, m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[])

  O=parent(m).order
  K=nf(O)
  Q,pi=quo(O,m)
  G, mG, lp = _mult_grp(Q,p)
  C, mC = class_group(O)
  
  if p==2 
    pr = [ x for x in inf_plc if isreal(x) ]
    if !isempty(pr)
      H,lH,eH=Hecke._infinite_primes(O,pr,m)
      T=G
      G =Hecke.direct_product(G,H)
    end
  end
  
  valclassp=Int(p^(valuation(order(C[ngens(C)]),p)))
  nonppartclass=Int(div(order(C[ngens(C)]),valclassp))
  
  if valclassp==1 && order(G)==1
    return empty_ray_class(m)
  end
  
  C, mC = _class_group_mod_n(C,mC,valclassp)
  U, mU = unit_group_fac_elem(O)
  exp_class = Hecke._coprime_ideal(C,mC,m)
    
  if order(G)==1
    return class_as_ray_class(C,mC,exp_class,m)    
  end

  n=ideal(O,1)
  for (q,vq) in lp
    n*=q^vq
  end
  
#
# We start to construct the relation matrix
#

  expo=Int(exponent(G))
  inverse_d=gcdx(nonppartclass,expo)[2]
  
  R=zero_matrix(FlintZZ, ngens(C)+ngens(U)+ngens(G), ngens(C)+ngens(G))
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

  @assert issnf(U)
  @vprint :RayFacElem 1 "Collecting elements to be evaluated; first, units \n"
  evals=NfOrdQuoRingElem[]
  tobeeval=FacElem{nf_elem, AnticNumberField}[]
  if gcd(U.snf[1],p)!=1
    if U.snf[1]==2
      push!(evals,Q(-1))
    else
      push!(tobeeval, mU(U[1]))
    end
  else 
    push!(evals, Q(1))
  end
  append!(tobeeval,[mU(U[i]) for i=2:ngens(U)])
  
  @vprint :RayFacElem 1 "then principal ideal generators \n"
  for i=1:ngens(C)
    @vtime :RayFacElem 1 push!(tobeeval, Hecke.principal_gen_fac_elem((exp_class(C[i]))^(Int(order(C[i]))*nonppartclass)))
  end
  
  @vprint :RayFacElem 1 "Time for elements evaluation: "
  ev,quots,idemps=fac_elems_eval(O,Q,tobeeval,lp,expo)
  @vtime :RayFacElem 1 append!(evals, ev)
  @vprint :RayFacElem 1 "\n"
  
  for i=1:ngens(U)
    @vprint :RayFacElem 1 "Disclog of unit $i \n"
    a=(mG\(evals[i].elem)).coeff
    if p==2 && !isempty(pr)
      if i==1
        a=hcat(a, matrix(FlintZZ,1,length(pr), [1 for i in pr]))
      else
        b=lH(tobeeval[length(tobeeval)-ngens(C)-ngens(U)+i])
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

  for i=1: ngens(C)
    @vprint :RayFacElem 1 "Disclog of class group element $i \n"
    a=((mG\(evals[i+ngens(U)].elem))*inverse_d).coeff
    if p==2 && !isempty(pr)
      b=lH(tobeeval[length(tobeeval)-ngens(C)+i])
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
    a= X([0 for i=1:ngens(X)])
    for (f,k) in J.fac
      a+=k*disclog(f)
    end
    return a
  end
 
  function disclog(J::NfOrdIdl)
    if isone(J)
      return X([0 for i=1:ngens(X)])
    else
      L=mC\J
      s=exp_class(L)
      I=J* inv(s)
      I=I^Int(nonppartclass)
      z=principal_gen_fac_elem(I)
      el=Hecke._fac_elem_evaluation(O, Q, quots, idemps, z, lp, expo)
      y=((mG\el)*inverse_d).coeff
      if p==2 && !isempty(pr)
        b=lH(z)
        y=hcat(y, b.coeff)
      end
      return X(hcat(L.coeff,y))
    end
  end 

#
# Exp map
#

  function expon(a::GrpAbFinGenElem)
    b=C([a.coeff[1,i] for i=1:ngens(C)])
    if p!=2 || isempty(pr)
      c=G([a.coeff[1,i] for i=ngens(C)+1:ngens(X)])
      return exp_class(b)*ideal(O,pi\(mG(c)))
    else 
      c=T([a.coeff[1,i] for i=ngens(C)+1:ngens(T)+ngens(C)])
      d=H([a.coeff[1,i] for i=ngens(T)+ngens(C)+1: ngens(X)])
      el=pi\(mG(c))
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

  mp=Hecke.MapRayClassGrp{typeof(X)}()
  mp.header = Hecke.MapHeader(X, FacElemMon(parent(m)) , expon, disclog)
  mp.modulus_fin=n
  mp.modulus_inf=inf_plc

  return X,mp
end 


#####################################################################################################
#
#  Quotient by n of the Ray Class Group
#
#####################################################################################################


function _class_group_mod_n(C::GrpAbFinGen, mC::Hecke.MapClassGrp, n::Integer)
  
  @assert issnf(C)
  O=parent(mC(C[1])).order
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
   return G,mp
  
  else
    
    ind=1
    while gcd(order(C[ind]),n)==1
      ind+=1
    end
    
    vect=[gcd(C.snf[ind+j],n) for j=0:ngens(C)-ind]
    G=DiagonalGroup(vect)
    G.issnf=true
    G.snf=vect
    
    function exp2(a::GrpAbFinGenElem)
      x=C([0 for i=1:ngens(C)])
      for i=ind:ngens(C)
        x.coeff[1,i]=a.coeff[1,i-ind+1]  
      end
      return mC(x)
    end 
    
    function disclog2(I::NfOrdIdl)
      x=mC\I
      y=G([0 for j=1:ngens(G)])
      for i=ind:ngens(C)
          y.coeff[1,i-ind+1]=x.coeff[1,i]
      end 
      return y
    end
  
    mp=Hecke.MapClassGrp{typeof(G)}()
    mp.header=Hecke.MapHeader(G, mC.header.codomain, exp2, disclog2)
    
    return G,mp
  end
end 


function _n_part_multgrp_mod_p(p::NfOrdIdl, n::Int)
  @hassert :NfOrdQuoRing 2 isprime(p)
  O = order(p)
  Q , mQ = ResidueField(O,p)
  
  f=collect(keys(factor(fmpz(n)).fac))
  np = norm(p) - 1
  val=Array{Int,1}(length(f))
  for i=1:length(f)
    val[i]=valuation(np,f[i])
  end
  npart=prod([f[i]^(val[i]) for i=1:length(f) if val[i]!=0])
  m=div(np,npart)
  powm=[divexact(npart,f[i]) for i=1:length(f) if val[i]!=0]
  #
  #  We search for a random element with the right order
  #
  
  found=false
  g=Q(1)
  while found==false
    g = rand(Q)
    if g != Q(0) 
      g=g^m
      found=true
      for i=1:length(powm)
        if g^powm[i] == Q(1) 
          found=false
          continue
        end
      end     
    end
  end
  k=gcd(npart,n)
  inv=gcdx(m,fmpz(npart))[2]
  quot=divexact(npart, k)
  
  function disclog(x::NfOrdElem)
    t=mQ(x)^(m*quot)
    if t==Q(1)
      return [Int(0)]
    end
    if k<10
      s=1
      w=g^quot
      el=w
      while el!=t
        s+=1
        el*=w
      end
      return [s*inv]
    else 
      return [pohlig_hellman(g^quot,k,t)*inv] 
    end
  end
  
  return mQ\g , k, disclog
end

function _mult_grp_mod_n(Q::NfOrdQuoRing, y1::Dict{NfOrdIdl,Int}, y2::Dict{NfOrdIdl,Int},n::Integer)

  O=Q.base_ring
  K=nf(O)
 
  gens = Vector{NfOrdQuoRingElem}()
  structt = Vector{fmpz}()
  disc_logs = Vector{Function}()
  
  prime_power=Dict{NfOrdIdl, NfOrdIdl}()
  for (q,vq) in Q.factor
    prime_power[q]=q^vq
  end
 
  
  for (q,vq) in y1
    gens_q , struct_q , dlog_q = _n_part_multgrp_mod_p(q,n)
  
    # Make generators coprime to other primes
    if length(Q.factor) > 1
      i_without_q = 1
      for (q2,vq2) in Q.factor
        (q != q2) && (i_without_q *= prime_power[q2])
      end
      alpha, beta = idempotents(prime_power[q] ,i_without_q)
      gens_q = beta*gens_q + alpha
    end
 
    push!(gens,Q(gens_q))
    push!(structt,struct_q)
    push!(disc_logs,dlog_q)
  
  end
  for (q,vq) in y2
    gens_q, snf_q, disclog_q = Hecke._1_plus_p_mod_1_plus_pv(q,vq)

    # Make generators coprime to other primes
    nq=norm(q)-1  
    if length(Q.factor) > 1
      i_without_q = 1
      for (p2,vp2) in Q.factor
        (q != p2) && (i_without_q *= prime_power[p2])
      end

      alpha, beta = idempotents(prime_power[q],i_without_q)
      for i in 1:length(gens_q)
        gens_q[i] = beta*gens_q[i] + alpha
      end
    end
    
    inv=gcdx(nq,snf_q[end])[2]
       
    function dlog_q_norm(x::NfOrdElem)
      y=Q(x)^Int(nq)
      y=disclog_q(y.elem)
      for i=1:length(y)
        y[i]*=inv
      end
      return y
    end
        
    gens_q = map(Q,gens_q)
    append!(gens,gens_q)
    append!(structt,snf_q)
    push!(disc_logs,dlog_q_norm)
  end 
  
  G=DiagonalGroup(structt)
  
  function exp(a::GrpAbFinGenElem)   
    x=Q(1)
    for i=1:ngens(G)
      if Int(a.coeff[1,i])!= 0
        x=x*(gens[i]^(Int(a.coeff[1,i])))
      end
    end
    return x
  end
  
  function dlog(x::NfOrdElem)
    result = Vector{fmpz}()
    for disclog in disc_logs
      append!(result,disclog(x))
    end
    return G(result)
  end
  
  mG=Hecke.AbToResRingMultGrp(G,Q,exp,dlog)
  
  return G, mG 
end


function ray_class_group(n::Integer, m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[])

  O=parent(m).order
  K=nf(O)
  
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
    else 
      if gcd(norm(q),n)!=1 && e>=2
        y2[q]=Int(e)
      end
    end
  end
  return ray_class_group(n, m, y1, y2, inf_plc)
  
end


function ray_class_group(n::Integer, m::NfOrdIdl, y1::Dict{NfOrdIdl,Int}, y2::Dict{NfOrdIdl,Int}, inf_plc::Array{InfPlc,1}=InfPlc[])

  O=parent(m).order
  K=nf(O)
  
  # Compute the modulus of the quotient
  I=ideal(O,1)
  for (q,vq) in y1
    I*=q^vq
  end
  for (q,vq) in y2
    I*=q^vq
  end
  lp=merge(max,y1,y2)
  
  Q,pi=quo(O,I)
  Q.factor=lp
  @vtime :RayFacElem G, mG= _mult_grp_mod_n(Q,y1,y2,n)
  C, mC = class_group(O)
  
  if mod(n,2)==0 
    pr = [ x for x in inf_plc if isreal(x) ]
    if !isempty(pr)
      H,lH,eH=Hecke._infinite_primes(O,pr,m)
      T=G
      G =Hecke.direct_product(G,H)
    end
  end
  
  if gcd(C.snf[end],n)==1 && order(G)==1
    return empty_ray_class(m)
  end
  
  f=collect(keys(factor(fmpz(n)).fac))
  val=Array{Int,1}(length(f))
  for i=1:length(f)
    val[i]=valuation(C.snf[end],f[i])
  end
  valclass=1
  for i=1:length(f)
    if val[i]!=0
      valclass*=f[i]^(val[i])
    end
  end
  nonnclass=divexact(C.snf[end], valclass)

  C, mC = _class_group_mod_n(C,mC,Int(valclass))
  U, mU = unit_group_fac_elem(O)
  exp_class = Hecke._coprime_ideal(C,mC,m)
  
  if order(G)==1
    return class_as_ray_class(C,mC,exp_class,m,n)    
  end


  
#
# We start to construct the relation matrix
#

  expo=Int(exponent(G))
  inverse_d=gcdx(fmpz(nonnclass),fmpz(expo))[2]
  
  R=zero_matrix(FlintZZ, 2*ngens(C)+ngens(U)+2*ngens(G), ngens(C)+ngens(G))
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
  for i=1:cols(R)
    R[ngens(C)+ngens(U)+ngens(G)+i,i]=n
  end
  
#
# We compute the relation matrix given by the image of the map U -> (O/m)^*
#

  @assert issnf(U)
  @vprint :RayFacElem 1 "Collecting elements to be evaluated; first, units \n"
  evals=NfOrdQuoRingElem[]
  tobeeval=FacElem{nf_elem, AnticNumberField}[]
  if gcd(U.snf[1],n)!=1
    if U.snf[1]==2
      push!(evals,Q(-1))
    else
      push!(tobeeval, mU(U[1]))
    end
  else 
    push!(evals,Q(1))
  end
  append!(tobeeval,[mU(U[i]) for i=2:ngens(U)])
  
  @vprint :RayFacElem 1 "then principal ideal generators \n"
  for i=1:ngens(C)
    @vtime :RayFacElem 1 push!(tobeeval, Hecke.principal_gen_fac_elem((exp_class(C[i]))^(Int(order(C[i]))*nonnclass)))
  end
  
  @vprint :RayFacElem 1 "Time for elements evaluation: "
  @vtime :RayFacElem 1 ev,quots,idemps=fac_elems_eval(O,Q,tobeeval,lp,gcd(expo,n))
  append!(evals, ev)
  @vprint :RayFacElem 1 "\n"
  
  for i=1:ngens(U)
    @vprint :RayFacElem 1 "Disclog of unit $i \n"
    a=(mG\(evals[i].elem)).coeff
    if mod(n,2)==0 && !isempty(pr)
      if i==1
        a=hcat(a, matrix(FlintZZ,1,length(pr), [1 for i in pr]))
      else
        b=lH(tobeeval[length(tobeeval)-ngens(C)-ngens(U)+i])
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

  for i=1: ngens(C)
    @vprint :RayFacElem 1 "Disclog of class group element $i \n"
    a=((mG\(evals[i+ngens(U)].elem))*inverse_d).coeff
    if mod(n,2)==0 && !isempty(pr)
      b=lH(tobeeval[length(tobeeval)-ngens(C)+i])
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
    a= X([0 for i=1:ngens(X)])
    for (f,k) in J.fac
      a+=k*disclog(f)
    end
    return a
  end

  function disclog(J::NfOrdIdl)

    if isone(J)
      return X([0 for i=1:ngens(X)])
    else
      L=mC\J
      s=exp_class(L)
      I=J* inv(s)
      I=I^Int(nonnclass)
      z=principal_gen_fac_elem(I)
      el=Hecke._fac_elem_evaluation(O, Q, quots, idemps, z, lp, gcd(expo,n))
      y=((mG\(el))*inverse_d).coeff
      if mod(n,2)==0 && !isempty(pr)
        b=lH(z)
        y=hcat(y, b.coeff)
      end
      return X(hcat(L.coeff,y))
    end
  end 

#
# Exp map
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

  mp=Hecke.MapRayClassGrp{typeof(X)}()
  mp.header = Hecke.MapHeader(X, FacElemMon(parent(m)) , expon, disclog)
  mp.modulus_fin=I
  if mod(n,2)==0
    mp.modulus_inf=pr
  else
    mp.modulus_inf=inf_plc
  end
  return X,mp
  
end

##################################################################################
#
#  Stable Subgroups of Ray Class Group
#
##################################################################################


function _act_on_ray_class(mR::Map, p::Int, Aut::Array{Hecke.NfToNfMor,1})

  R=mR.header.domain
  O=mR.header.codomain.base_ring.order
  K=nf(O)
  F, _=Nemo.FiniteField(p,1, "_")  
  G=MatElem[]
  
  for phi in Aut
    M=zero_matrix(F,ngens(R), ngens(R))
    for i=1:ngens(R) 
      J=mR(R[i])
      I=FacElem(Dict(ideal(O,1)=> 1))
      for (f,k) in J.fac
        I.fac[_aut_on_id(O, phi, f)]=k
      end
      elem=mR\I
      for j=1:ngens(R)
        M[i,j]=F(elem.coeff[1,j])
      end
    end
    push!(G,M)
  end 
  return FqGModule(G)
  
end

function _aut_on_id(O::NfOrd, phi::Hecke.NfToNfMor, I::NfOrdIdl) 
  
  K=nf(O)
  y=K(I.gen_two)
  y=O(phi(y))
  return ideal(O,I.gen_one,y)
  
end

function stable_index_p_subgroups(R::GrpAbFinGen, index::Int, act::Array{T, 1}, op=sub) where T <: Map{GrpAbFinGen, GrpAbFinGen} 
  
  S,mS=snf(R)

  @assert length(act)>0
  p = S.snf[1]
  @assert isprime(p)
  @assert all(x -> x==p, S.snf)

  F, _ = Nemo.FiniteField(Int(p), 1, "_")
  FM = MatrixSpace(F, ngens(S), ngens(S))
  G = Generic.Mat{fq_nmod}[ FM(vcat([mS(X(preimage(mS, S[i]))).coeff for i=1:ngens(S)])) for X = act]
  M = FqGModule(G)

  ls=submodules(M,index)
  subgroups=[]
  for s in ls
    subs=GrpAbFinGenElem[]
    for i=1:rows(s)
      x=zero_matrix(FlintZZ,1,cols(s))()
      for j=1:cols(s)
        x[1,j]=FlintZZ(coeff(s[i,j],0))
      end
      push!(subs, mS(S(x)))
    end
    push!(subgroups, op(R, subs))
  end
  return subgroups
end

#
#  Find small primes that generate the ray class group (or a quotient)
#  It needs a map GrpAbFinGen -> NfOrdIdlSet
#
function find_gens(mR::Map)

  O = order(codomain(mR))
  R = domain(mR) 
  m=Hecke._modulus(mR)
  
  sR = elem_type(R)[]
  lp = []

  S=Hecke.PrimesSet(2,-1)
  st = start(S)
  
  q, mq = quo(R, sR,false)
  while true
    p, st = next(S, st)
    if m.gen_one % p == 0
      continue
    end

    lP = prime_decomposition(O, p)

    f=R[1]
    for (P,e) in lP
      f= mR\P
      if iszero(mq(f))
        continue
      end
      push!(sR, f)
      push!(lp, P)
      q, mq = quo(R, sR, false)
    end
    if order(q) == 1   
      break
    end
  end

  return lp, sR
end


function _act_on_ray_class(mR::Map , Aut::Array{Hecke.NfToNfMor,1}=Array{Hecke.NfToNfMor,1}())

  R=mR.header.domain
  O=mR.header.codomain.base_ring.order
  K=nf(O)
  if isempty(Aut)
    Aut=automorphisms(K)
  end
  G=Hecke.GrpAbFinGenMap[]
  if ngens(R)==0
    return G
  end
  #
  #  Instead of applying the automorphisms to the elements given by mR, I choose small primes 
  #  generating the group and study the action on them. In this way, I take advantage of the cache of the 
  #  class group map
  #

  lgens,subs=find_gens(mR)
  
  if isempty(lgens)
    push!(G, GrpAbFinGenMap(R))
    return G
  end
  #
  #  Write the matrices for the change of basis
  #
  auxmat=zero_matrix(FlintZZ, ngens(R), length(lgens)+nrels(R))
  for i=1:length(lgens)
    for j=1:ngens(R)
      auxmat[j,i]=subs[i][j]
    end
  end
  if issnf(R)
    for i=1:ngens(R)
      auxmat[i,length(lgens)+i]=R.snf[i]
    end
  else
    for i=1:ngens(R)
      for j=1:nrels(R)
        auxmat[i,length(lgens)+j]=R.rels[j,i]
      end
    end
  end

  Ml=solve(auxmat,eye(auxmat,ngens(R)))'
  
  #
  #  Now, we compute the action on the group
  #
  
  for phi in Aut
    M=zero_matrix(FlintZZ,length(lgens), ngens(R))
    for i=1:length(lgens) 
      J=_aut_on_id(O,phi,lgens[i])
      elem=mR\J
      for j=1:ngens(R)
        M[i,j]=elem[j]
      end
    end
    push!(G,GrpAbFinGenMap(R,R,view(Ml,1:rows(Ml),1:length(lgens))*M))
  end
  
  return G
  
end

doc"""
***
    stable_subgroups(R::GrpAbFinGen, quotype::Array{Int,1}, act::Array{T, 1}; op=sub)
    
> Given a group R, an array of endomorphisms of the group and the type of the quotient, it returns all the stable 
> subgroups of R such that the corresponding quotient has the required type.
"""


function stable_subgroups(R::GrpAbFinGen, quotype::Array{Int,1}, act::Array{T, 1}; op=sub) where T <: Map{GrpAbFinGen, GrpAbFinGen} 
  
  c=lcm(quotype)
  Q,mQ=quo(R,c, false)
  lf=factor(order(Q)).fac
  list=[]
  for p in keys(lf)
    
    x=valuation(c,p)
    if x==0
      continue
    end
    G,mG=psylow_subgroup(Q, p)
    S,mS=snf(G)
    #
    #  Action on the group: we need to distinguish between FqGModule and ZpnGModule (in the first case the algorithm is more efficient)
    #
    
    if x==1
    
      F, _ = Nemo.FiniteField(Int(p), 1, "_")
      act_mat=Array{Generic.Mat{fq_nmod},1}(length(act))
      for z=1:length(act)
        y=transpose(solve(hcat(mG.map', rels(Q)'), (mS.map*mG.map*act[z].map)'))
        y=view(y,1:ngens(S), 1:ngens(G))*mS.imap
        act_mat[z]=MatrixSpace(F,ngens(S), ngens(S))(y)
      end
      M=FqGModule(act_mat)
      
      #
      #  Searching for submodules
      #
      
      ind=0
      for i=1:length(quotype)
        if divisible(fmpz(quotype[i]),p)
          ind+=1
        end
      end
      plist=submodules(M,ind)
      push!(list, (_lift_and_construct(x, mQ,mG,mS,c) for x in plist))

    else    
    
      RR=ResidueRing(FlintZZ, Int(p^x))
      act_mat=Array{nmod_mat,1}(length(act))
      auxmat1=hcat(mG.map', rels(Q)')
      auxmat2=mS.map*mG.map
      for z=1:length(act)
        y=transpose(solve(auxmat1, (auxmat2*act[z].map)'))
        y=view(y,1:ngens(S), 1:ngens(G))*mS.imap
        act_mat[z]=MatrixSpace(RR,ngens(S), ngens(S))(y)
      end
      
      #
      #  Searching for submodules
      #
      
      M=Hecke.ZpnGModule(S,act_mat)
    
      quotype_p=Int[]
      for i=1:length(quotype)
        v=valuation(quotype[i],p)
        if v>0
          push!(quotype_p,v)
        end
      end
      plist=submodules(M,typequo=quotype_p)
      push!(list, (_lift_and_construct(x, mQ,mG,mS,c) for x in plist))
      
    end
  end
  if isempty(list)
    return ([])
  end

  final_it = ( op(R,vcat(c...)) for c in Iterators.product(list...))
  return final_it

end

function _lift_and_construct(A::nmod_mat, mQ::GrpAbFinGenMap, mG::GrpAbFinGenMap, mS::GrpAbFinGenMap, c::Int)
  
  R=mQ.header.domain
  newsub=GrpAbFinGenElem[c*R[i] for i=1:ngens(R)]
  for i=1:rows(A)
    y=view(A,i:i,1:cols(A))
    if !iszero(y)
      push!(newsub,mQ\(mG(mS(mS.header.domain(lift(y))))))
    end       
  end
  return newsub

end

function _lift_and_construct(A::Generic.Mat{fq_nmod}, mQ::GrpAbFinGenMap, mG::GrpAbFinGenMap, mS::GrpAbFinGenMap, c ::Int)
  
  R=mQ.header.domain
  newsub=GrpAbFinGenElem[c*R[i] for i=1:ngens(R)]
  for i=1:rows(A)
    z=zero_matrix(FlintZZ,1,cols(A))
    for j=1:cols(z)
      z[1,j]=FlintZZ(coeff(A[i,j],0))
    end
    push!(newsub,mQ\(mG(mS(mS.header.domain(z)))))
  end
  return newsub

end


function stable_index_p_subgroups(mR::Hecke.MapRayClassGrp, p::Int, index::Int=1, Aut::Array{NfToNfMor, 1}=NfToNfMor[])
  
  O=mR.header.codomain.base_ring.order
  K=nf(O)
  
  if isempty(Aut)
    Aut=automorphisms(K)
  end
  
  for phi in Aut
    @assert mR.modulus_fin==_aut_on_id(O,phi, mR.modulus_fin)
  end 
  
  R=mR.header.domain
  Q,mQ=quo(R,p, false)
  S,mS=snf(Q)

  M=_act_on_ray_class(mR*inv(mQ)*mS, p, Aut)

  ls=submodules(M,index)
  subgroups=Map[]
  for s in ls
    subs=[p*R[i] for i=1:ngens(R)]
    for i=1:rows(s)
      x=zero_matrix(FlintZZ,1,cols(s))
      for j=1:cols(s)
        x[1,j]=FlintZZ(coeff(s[i,j],0))
      end
      push!(subs, mQ\(mS(S(x))))
    end
    W,mW=quo(R, subs, false) 
    push!(subgroups, mR*inv(mW))
  end
  return subgroups

end
