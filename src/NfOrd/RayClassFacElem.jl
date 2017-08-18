
export ray_class_group_fac_elem, ray_class_group_p_part


add_verbose_scope(:RayFacElem)

###############################################################################
#  
#  Types
#
###############################################################################


mutable struct MapRayClassGrpFacElem{T} <: Map{T, FacElemMon{Hecke.NfOrdIdlSet}}
  header::Hecke.MapHeader
  modulus_fin::NfOrdIdl
  modulus_inf::Array{InfPlc,1}
  fact_mod::Dict{NfOrdIdl, Int}
  
  function MapRayClassGrpFacElem{T}() where {T}
    return new{T}()
  end
end


mutable struct MapMultGrp <: Map{GrpAbFinGen, NfOrdQuoRing}
  header::Hecke.MapHeader

  function MapMultGrp()
    return new()
  end
end



###############################################################################
#
#  Ray Class Group - Factored Form
#
###############################################################################


function _fac_elem_evaluation(O::NfOrd, J::FacElem{nf_elem}, primes::Dict{NfOrdIdl, Int}, exponent::Int)
  
  el=O(1)
  I=ideal(O,1)
  for (p,vp) in primes
    q=p^vp
    y=_eval_quo(O, J, p, q, anti_uniformizer(p),exponent)
    a,b=idempotents(I,q)
    el=y*a+el*b
    I=I*q
  end
  return el

end

function _eval_quo(O::NfOrd, J::FacElem{nf_elem}, p::NfOrdIdl, q::NfOrdIdl, anti_uni::nf_elem, exponent::Int)
  
  Q,mQ=quo(O,q)
  el=Q(1)
  for (f,k) in J.fac
    act_el=f
    val=valuation(act_el,p)
    if val!=0
      act_el=act_el*(anti_uni^val)
    end
    if act_el in O
      el=el*Q(O(act_el))^mod(k,exponent)
    else 
      d=den(act_el,O)
      n=act_el*d
      val=valuation(d,p)
      if val!=0
        d=d*anti_uni^(val)
        n=n*anti_uni^(val)
      end
      el=el* Q(O(n))^mod(k,exponent) * Q(O(d))^mod(-k,exponent)
    end
  end
  return el.elem
  
end

#
#  Given prime ideals $p_1,\dots, p_k$, the function returns uniformizers $f_1,\dots , f_k$ such that $v_{p_i}(f_j)=\delta_{ij}$
#


function uniformizers(K::AnticNumberField, d::Dict{NfOrdIdl, Int})

  
  unif=Dict{NfOrdIdl,nf_elem}()
  for (q,e) in d
    t=Set{Int}()
    for (p,e1) in d
      if p.gen_one!=q.gen_one
        push!(t,p.gen_one)
      end
    end
    unif[q]=(K(prod(t))*K(q.gen_two)+K(q.gen_one^2))
  end
  return unif
  
end


function _coprime_ideal_fac_elem(C::GrpAbFinGen, mC::Map, m::NfOrdIdl)
 
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


doc"""
***
    ray_class_group_fac_elem (m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[])
    
> Given a modulus with finite part $m$ and infinite part inf_plc, it returns the ray class group Cl_m with the factored element representation

"""


function ray_class_group_fac_elem(m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[])

#
# We compute the group using the sequence U -> (O/m)^* _> Cl^m -> Cl -> 1
# First of all, we compute all these groups with their own maps
#  

  O=parent(m).order
  K=nf(O)
  

  C, mC = class_group(O)

  exp_class=Hecke._coprime_ideal_fac_elem(C,mC,m)
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
  
  @vprint :RayFacElem 1 "The multiplicative group is $G\n"
  @vprint :RayFacElem 1 "The order of the class group is $C\n"
  @vprint :RayFacElem 1 "The units are $U\n"
    
  exponent=Int(order(G[ngens(G)]))

#
# We start to construct the relation matrix
#
  RG=rels(G)
  RC=rels(C)

  A=vcat(RC, MatrixSpace(FlintZZ, ngens(G)+ngens(U), cols(RC))())
  B=vcat(MatrixSpace(FlintZZ, ngens(C), cols(RG))(), RG)
  B=vcat(B, MatrixSpace(FlintZZ, ngens(U) , cols(RG))())
 
#
# We compute the relation matrix given by the image of the map U -> (O/m)^*
#
  for i=1:ngens(U)
    u=mU(U[1])
    @vprint :RayFacElem 1 "Processing unit number $i \n"
    el=Hecke._fac_elem_evaluation(O,u,lp,exponent)
    @vprint :RayFacElem 1 "Product computed, now discrete logarithm\n"
    a=(mG\Q(el)).coeff
    if !isempty(p)
      b=sum([lH(f) for f in keys(u.fac)])
      a=hcat(a, b.coeff)
    end 
    for j=1:ngens(G)
      B[i+rows(RC)+rows(RG),j]=a[1,j]
    end
  end 
  
  @vprint :RayFacElem 1 "Relation with the unit group computed\n"

#
# We compute the relation between generators of Cl and (O/m)^* in Cl^m
#

  for i=1: ngens(C)
    @vprint :RayFacElem 1 "Processing class group generator number i \n"
    if order(C[i])!=1
      y=Hecke.principal_gen_fac_elem((exp_class(C[i]))^(Int(order(C[i]))))
      el=Hecke._fac_elem_evaluation(O,y,lp,exponent)
      a=(mG\Q(el)).coeff
      if !isempty(p)
        b=sum([lH(f) for f in keys(y.fac)])
        a=hcat(a, b.coeff)
      end 
      for j=1: ngens(G)
        B[i,j]=-a[1,j]
      end 
    end
  end

  R=hcat(A,B)
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
      z=Hecke.principal_gen_fac_elem(I)
      el=_fac_elem_evaluation(O,z,lp,exponent)
      y=(mG\Q(el)).coeff
      if !isempty(p)
        b=sum([lH(f) for f in keys(z.fac)])
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
      # I need to modify $el$ so that it has the correct sign at the embeddings contained in primes
      vect=(lH(K(el))).coeff
      if vect==d.coeff
        return exp_class(b)*ideal(O,el)
      else 
        correction=O(1)
        for i=1:ngens(H)
          if d.coeff[1,i]==1
            correction=correction*eH(H[i])
          end
        end
        while vect!=d.coeff
          el=el+correction
          vect=(lH(K(el))).coeff
        end
        return exp_class(b)*ideal(O,el)
      end 
    end
  end 

  mp=MapRayClassGrpFacElem{typeof(X)}()
  mp.header = Hecke.MapHeader(X, FacElemMon(parent(m)) , expo, disclog)
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


function _ptorsion_class_group(C::GrpAbFinGen, mC::Hecke.MapClassGrp, p::Integer)
  
  O=parent(mC(C[1])).order
  if !divisible(order(C[ngens(C)]),p)
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
 
    powerp=valuation(order(C[ngens(C)]),p)
    ind=1
    while !divisible(order(C[ind]),p)
      ind+=1
    end
    
    G=DiagonalGroup([gcd(order(C[ind+j]),fmpz(p^powerp)) for j=0:ngens(C)-ind])

    function exp2(a::GrpAbFinGenElem)
      x=C([0 for i=1:ngens(C)])
      for i=ind:ngens(C)
        x.coeff[1,i]=a.coeff[1,i-ind+1]  # careful!!! this ideal will not
                                         # have a p-power order!
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

function prime_part_multgrp_mod_p(p::NfOrdIdl, prime::Int)
  @hassert :NfOrdQuoRing 2 isprime(p)
  O = order(p)
  Q , mQ = quo(O,p)
  
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

  function disclog(x::NfOrdElem)
    t=mQ(x)^m
    res=Hecke._pohlig_hellman_prime_power(g,prime,s,t)
    inv=gcdx(m,fmpz(powerp))[2]
    return [res*inv]
  end
  return mQ\g , [powerp], disclog
end



function _mult_grp(Q::NfOrdQuoRing, p::Integer, inf_plc::Array{InfPlc,1}=InfPlc[])

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
  
  mG=Hecke.MapMultGrp()
  mG.header=Hecke.MapHeader(G,Q,exp,dlog)
  
  return G, mG, merge(y1, y2)
end





doc"""
***
    ray_class_group_p_part (p::Integer, m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[])
    
> Given a modulus with finite part m and infinite part inf_plc, it returns the quotient of the ray class group Cl_m by the subgroup generated by elements of order coprime to $p$

"""

function ray_class_group_p_part(p::Integer, m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[])

  O=parent(m).order
  K=nf(O)
  

  C, mC = class_group(O)
  valclassp=Int(p^(valuation(order(C[ngens(C)]),p)))
  nonppartclass=Int(div(order(C[ngens(C)]),valclassp))
  
  
  C, mC = _ptorsion_class_group(C,mC,p)
  Q,pi=quo(O,m)
  G, mG, lp = _mult_grp(Q,p, inf_plc)

  if p==2 
    pr = [ x for x in inf_plc if isreal(x) ]
    if !isempty(pr)
      H,lH,eH=Hecke._infinite_primes(O,pr,m)
      T=G
      G =Hecke.direct_product(G,H)
    end
  end
  
  if order(C)==1 && order(G)==1
    X=DiagonalGroup([1])
    function exp2(a::GrpAbFinGenElem)
      return FacElem(Dict(ideal(O,1) => fmpz(1)))
    end
    
    function disclog2(J::Union{NfOrdIdl, FacElem{NfOrdIdl}})
      return X([0])
    end
    
    mp=Hecke.MapRayClassGrpFacElem{typeof(X)}()
    mp.header = Hecke.MapHeader(X, FacElemMon(parent(m)) , exp2, disclog2)
    mp.modulus_fin=ideal(O,1)
    mp.modulus_inf=InfPlc[]
    
    return X,mp
  end

  U, mU = unit_group_fac_elem(O)
  exp_class = Hecke._coprime_ideal_fac_elem(C,mC,m)

  if order(G)==1
    X=deepcopy(C)
    function exp3(a::GrpAbFinGenElem)
      return exp_class(a)
    end
    
    function disclog3(J::NfOrdIdl)
      return X((mC\J).coeff)
    end
    
    function disclog3(J::FacElem)
      a= X([0 for i=1:ngens(X)])
      for (f,k) in J.fac
        a+=k*disclog3(f)
      end
      return a
    end
    
    mp=Hecke.MapRayClassGrpFacElem{typeof(X)}()
    mp.header = Hecke.MapHeader(X, FacElemMon(parent(m)) , exp3, disclog3)
    mp.modulus_fin=ideal(O,1)
    mp.modulus_inf=InfPlc[]
    
    return X,mp
    
  end

  n=ideal(O,1)
  for (q,vq) in lp
    n*=q^vq
  end
#
# We start to construct the relation matrix
#

  expo=Int(1)  # exponent of the unit group of the residue ring
  for ind=1:ngens(G)
    if rels(G)[ind,ind]>expo
      expo=Int(rels(G)[ind,ind])
    end
  end
  
  inverse_d=gcdx(nonppartclass,expo)[2]
  
  RG=rels(G)
  RC=rels(C)

  A=vcat(RC, MatrixSpace(FlintZZ,rows(RG)+ngens(U), cols(RC))())
  B=vcat(RG, MatrixSpace(FlintZZ, ngens(U) , ngens(G))())
  
#
# We compute the relation matrix given by the image of the map U -> (O/m)^*
#
  @assert issnf(U)
  if gcd(order(U[1]),p)!=1
    u=mU(U[1])
    el=Hecke._fac_elem_evaluation(O,u,lp,expo)
    a=(mG\el).coeff
    if p==2 && !isempty(pr)
      b=sum([lH(x) for x in keys(u.fac)])
      a=hcat(a, b.coeff)
    end
    for j=1:ngens(G)
      B[1+ngens(G),j]=a[1,j]
    end
  end
  
  
  for i=2:ngens(U)
    u=mU(U[i])
    el=Hecke._fac_elem_evaluation(O,u,lp,expo)
    a=(mG\el).coeff
    if p==2 && !isempty(pr)
      b=sum([lH(x) for x in keys(u.fac)])
      a=hcat(a, b.coeff)
    end
    for j=1:ngens(G)
      B[i+ngens(G),j]=a[1,j]
    end
  end 
  B=vcat(MatrixSpace(FlintZZ, ngens(C), cols(RG))(), B)

  
#
# We compute the relation between generators of Cl and (O/m)^* in Cl^m
#

  for i=1: ngens(C)
    if order(C[i])!=1
      y=Hecke.principal_gen_fac_elem((exp_class(C[i]))^(Int(order(C[i]))*nonppartclass))
      el=Hecke._fac_elem_evaluation(O,y,lp,expo)
      a=((mG\el)*inverse_d).coeff
      if p==2 && !isempty(pr)
        b=sum([lH(x) for x in keys(y.fac)])
        a=hcat(a, b.coeff)
      end
      for j=1: ngens(G)
        B[i,j]=-a[1,j]
      end 
    end
    
  end
  
  R=hcat(A,B)
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
      z=Hecke.principal_gen_fac_elem(I)
      el=Hecke._fac_elem_evaluation(O,z,lp,expo)
      y=((mG\el)*inverse_d).coeff
      if p==2 && !isempty(pr)
        b=sum([lH(x) for x in keys(z.fac)])
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
        correction=O(1)
        for i=1:ngens(H)
          if d.coeff[1,i]==1
            correction=correction*eH(H[i])
          end
        end
        while vect!=d.coeff
          el=el+correction
          vect=(lH(K(el))).coeff
        end
        return exp_class(b)*ideal(O,el)
      end 
    end
  end 

  mp=Hecke.MapRayClassGrpFacElem{typeof(X)}()
  mp.header = Hecke.MapHeader(X, FacElemMon(parent(m)) , expon, disclog)
  mp.modulus_fin=n
  mp.modulus_inf=inf_plc

  return X,mp
end 



##################################################################################
#
#  Stable Subgroups of Ray Class Group
#
##################################################################################

function automorphisms(K::AnticNumberField)

  f=K.pol
  lr=roots(f,K)
  Aut=Hecke.NfToNfMor[]
  for r in lr
    push!(Aut, Hecke.NfToNfMor(K, K, r))
  end
  return Aut
  
end


function _act_on_ray_class(mR::Map, p::Int, Aut::Array{Hecke.NfToNfMor,1})

  R=mR.header.domain
  O=mR.header.codomain.base_ring.order
  K=nf(O)
  F, _=FiniteField(p,1, "_")  
  G=MatElem[]
  
  for phi in Aut
    M=MatrixSpace(F,ngens(R), ngens(R))()
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

  println("instable: S=$S\n")
  F, _ = FiniteField(Int(p), 1, "_")
  FM = MatrixSpace(F, ngens(S), ngens(S))
  G = MatElem[ FM(vcat([mS(X(preimage(mS, S[i]))).coeff for i=1:ngens(S)])) for X = act]
  println(G)
  M = FqGModule(G)

  ls=submodules(M,index)
  subgroups=[]
  for s in ls
    subs=GrpAbFinGenElem[]
    for i=1:rows(s)
      x=MatrixSpace(ZZ,1,cols(s))()
      for j=1:cols(s)
        x[1,j]=ZZ(coeff(s[i,j],0))
      end
      push!(subs, mS\(S(x)))
    end
    push!(subgroups, op(R, subs))
  end
  println("after all: found", length(subgroups))
  return subgroups
end

function stable_index_p_subgroups(mR::Hecke.MapRayClassGrpFacElem, p::Int, index::Int=1, Aut::Array{NfToNfMor, 1}=NfToNfMor[])
  
  O=mR.header.codomain.base_ring.order
  K=nf(O)
  
  if isempty(Aut)
    Aut=automorphisms(K)
  end
  
  for phi in Aut
    @assert mR.modulus_fin==_aut_on_id(O,phi, mR.modulus_fin)
  end 
  
  R=mR.header.domain
  Q,mQ=quo(R,p)
  S,mS=snf(Q)

  M=_act_on_ray_class(mR*inv(mQ)*inv(mS), p, Aut)

  ls=submodules(M,index)
  subgroups=Map[]
  for s in ls
    subs=GrpAbFinGenElem[]
    for i=1:rows(s)
      x=MatrixSpace(ZZ,1,cols(s))()
      for j=1:cols(s)
        x[1,j]=ZZ(coeff(s[i,j],0))
      end
      push!(subs, mQ\(mS\(S(x))))
    end
    W,mW=quo(R, subs) #TODO: probably wrong if R has exponent > p as the p*R
                      # need not be contained in subs
    push!(subgroups, mR*inv(mW))
  end
  println("after all: found", length(subgroups))
  return subgroups

end
