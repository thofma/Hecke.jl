export conductor, isconductor

########################################################################################
#
#  Tools for conductor
#
########################################################################################


function _modulus_with_inf(mR::Map)
  global bad = mR
  while issubtype(typeof(mR), Hecke.CompositeMap)
    mR = mR.f
  end
  if issubtype(typeof(mR), Hecke.MapClassGrp)
    return ideal(order(codomain(mR)), 1),InfPlc[]
  end
  @assert issubtype(typeof(mR), Hecke.MapRayClassGrp)
  return mR.modulus_fin, mR.modulus_inf
end

#
#  Find small primes generating a subgroup of the ray class group
#

function find_gens_sub(mR::Map, mT::GrpAbFinGenMap)

  O = order(codomain(mR))
  R = domain(mR) 
  T = domain(mT)
  m = Hecke._modulus(mR)
  l = minimum(m)
  lp = NfOrdIdl[]
  sR = GrpAbFinGenElem[]
  if isdefined(mR, :prime_ideal_cache)
    S = mR.prime_ideal_cache
  else
    S = prime_ideals_up_to(O, 1000)
    mR.prime_ideal_cache = S
  end
  q, mq = quo(T, sR, false)
  for (i,P) in enumerate(S)
    if divisible(l,minimum(P))
      continue
    end
    if haskey(mR.prime_ideal_preimage_cache, P)
      f = mR.prime_ideal_preimage_cache[P]
    else
      f = mR\P
      mR.prime_ideal_preimage_cache[P] = f
    end
    bool, pre = haspreimage(mT, f)
    if !bool
      continue
    end
    if iszero(mq(pre))
      continue
    end
    push!(sR, pre)
    push!(lp, P)
    q, mq = quo(T, sR, false)
    if order(q) == 1 
      break
    end
  end
  if order(q) == 1
    return lp
  else
    error("Not enough primes")
  end
end

#######################################################################################
#
#  Conductor functions
#
#######################################################################################

doc"""
***
  conductor(C::Hecke.ClassField) -> NfOrdIdl, Array{InfPlc,1}

> Return the conductor of the abelian extension corresponding to C
***
"""
function conductor(C::Hecke.ClassField)

  mp=C.mq
  
  #
  #  First, we need to find the subgroup
  #
  
  mR=mp.f
  mS=mp.g
  while issubtype(typeof(mR), Hecke.CompositeMap)
    mS = mR.g*mS
    mR = mR.f
  end
  
  R=domain(mR)
  cond=mR.modulus_fin
  inf_plc=mR.modulus_inf
  O=parent(cond).order
  E=order(domain(mp))
  expo=Int(exponent(domain(mp)))
  K=O.nf
  
  mS=inv(mS)
  dom=domain(mS)
  M=zero_matrix(FlintZZ,ngens(dom), ngens(codomain(mS)))
  for i=1:ngens(dom)
    elem=mS(dom[i]).coeff
    for j=1:ngens(codomain(mS))
      M[i,j]=elem[1,j]
    end
  end
  S1=Hecke.GrpAbFinGenMap(domain(mS),codomain(mS),M)
  T,mT=Hecke.kernel(S1)


  Sgens=find_gens_sub(mR,mT)

  #
  #  Some of the factors of the modulus are unnecessary for order reasons:
  #
    
  L=factor(cond)
  for (p,vp) in L
    if gcd(E,minimum(p))==1
      if gcd(E, norm(p)-1)==1
        Base.delete!(L,p)
      else
        L[p]=1
      end  
    else
      if L[p]==1
        Base.delete!(L,p)
      end
    end
  end
  divisors=collect(keys(L))
  

  candidate=1
  
  #
  # Test the finite primes dividing the modulus
  #
  iscandcond=true
  while !isempty(divisors)
    p=divisors[length(divisors)]
    if L[p]==1
      candidate=ideal(O,1)
      for (q,vq) in L
        if q !=p
          candidate*=q^Int(vq)
        end
      end
      r,mr=ray_class_group(candidate,inf_plc,n_quo=expo)
      quot=GrpAbFinGenElem[mr\s for s in Sgens]
      s,ms=quo(r,quot, false)
      if order(s)==E
        Base.delete!(L,p)
      end
      pop!(divisors)
    else 
      j=1
      cand=ideal(O,1)
      for (q,vq) in L
        if q !=p
          cand*=q^Int(vq)
        end
      end
      for j=1:L[p]-1
        candidate=cand*p^(L[p]-j)
        iscandcond=true
        r, mr=ray_class_group(candidate,inf_plc, n_quo=expo)
        quot=GrpAbFinGenElem[mr\s for s in Sgens]
        s,ms=quo(r,quot, false) 
        if order(s) < E
          iscandcond=false
          break
        end
      end
      if !iscandcond
        L[p]=L[p]-j+1
        pop!(divisors)
      else 
        L[p]=1
      end
    end
  end
  cond=ideal(O,1)
  for (p,vp) in L
    cond*=p^vp
  end
  
  #
  #  Test the infinite primes dividing the modulus
  #
  
  if !isempty(inf_plc)
    l=valuation(E,2)
    cond_inf=[x for x in inf_plc]
    for i=1:length(inf_plc)
      candidate_inf=[x for x in cond_inf if x !=inf_plc[i]]
      r,mr=ray_class_group(cond,candidate_inf, n_quo=2^l)
      quot=GrpAbFinGenElem[mr\s for s in Sgens]
      s,ms=quo(r,quot, false)
      if valuation(order(s),2)==l
        cond_inf=candidate_inf
      end
    end
    inf_plc=cond_inf
  end
  
  return cond, inf_plc
  
end 



doc"""
***
  isconductor(C::Hecke.ClassField, m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[]) -> NfOrdIdl, Array{InfPlc,1}

> Checks if m, inf_plc is the conductor of the abelian extension corresponding to C

***
"""
function isconductor(C::Hecke.ClassField, m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[])

  mp=C.mq
  
  #
  #  First, we need to find the subgroup
  #
  
  mR=mp.f
  mS=mp.g
  while issubtype(typeof(mR), Hecke.CompositeMap)
    mS = mR.g*mS
    mR = mR.f
  end
  
  R=domain(mR)
  cond=mR.modulus_fin
  inf_plc1=mR.modulus_inf
  O=parent(cond).order
  E=order(domain(mp))
  expo=Int(exponent(domain(mp)))
  K=O.nf
  
  mS=inv(mS)
  dom=domain(mS)
  M=zero_matrix(FlintZZ,ngens(dom), ngens(codomain(mS)))
  for i=1:ngens(dom)
    elem=mS(dom[i]).coeff
    for j=1:ngens(codomain(mS))
      M[i,j]=elem[1,j]
    end
  end
  S1=Hecke.GrpAbFinGenMap(domain(mS),codomain(mS),M)
  T,mT=Hecke.kernel(S1)

  Sgens=find_gens_sub(mR,mT)

  
  
  L=factor(cond)
  for (p,vp) in L
    if gcd(E,minimum(p))==1
      if gcd(E, norm(p)-1)==1
        Base.delete!(L,p)
      else
        L[p]=1
      end  
    else
      if L[p]==1
        Base.delete!(L,p)
      end
    end
  end
  
  
  L1=factor(m)
  for (p,vp) in L1
    if !haskey(L,p) &&
      return false
    elseif L1[p]>L[p]
      return false
    end
  end
  

  found=true
  for x in inf_plc
    found=false
    for i=1:length(inf_plc1)
      if x==inf_plc1[i]
        found=true
        break
      end
      if found==false
        return false
      end
    end
  end
  #
  #  We check that m, inf_plc is a possible conductor
  #
  r,mr=ray_class_group(m,inf_plc, n_quo= expo)
  quot=GrpAbFinGenElem[mr\s for s in Sgens]
  s,ms=quo(r,quot, false)
  if order(s)<E
    return false
  end
  
  #
  #  Now, we check that every divisor of m,inf_plc is not in the same congruence subgroup
  #

  divisors=collect(keys(L1))
  candidate=1
  
  # Test the finite primes.
  
  while !isempty(divisors)
    p=divisors[length(divisors)]
    if L1[p]==1
      candidate=ideal(O,1)
      for (q,vq) in L1
        if q !=p
          candidate*=q^Int(vq)
        end
      end
      r,mr=ray_class_group(candidate,inf_plc, n_quo=expo)
      quot=GrpAbFinGenElem[mr\s for s in Sgens]
      s,ms=quo(r,quot, false)
      if order(s)==E
        return false
      end
      pop!(divisors)
    else 
      candidate=ideal(O,1)
      for (q,vq) in L1
        if q !=p
          candidate*=q^Int(vq)
        end
      end
      candidate=candidate*p^(L1[p]-1)
      r, mr=ray_class_group(candidate,inf_plc, n_quo=expo)
      quot=GrpAbFinGenElem[mr\s for s in Sgens]
      s,ms=quo(r,quot, false) 
      if order(s) == E
        return false
      end
      pop!(divisors)
    end
  end
    
  # Test the infinite primes.
  
  if !isempty(inf_plc)
    l=valuation(E,2)
    if iszero(l)
      return false
    end
    cond_inf=[x for x in inf_plc]
    for i=1:length(inf_plc)
      candidate_inf=[x for x in cond_inf if x !=inf_plc[i]]
      r,mr=ray_class_group(m,candidate_inf, n_quo = 2^l)
      quot=GrpAbFinGenElem[mr\s for s in Sgens]
      s,ms=quo(r,quot, false)
      if valuation(order(s),2)==l
        return false
      end
    end
  end
  
  return true

end


doc"""
***
  function norm_group(f::Nemo.PolyElem, mR::Hecke.MapRayClassGrp) -> Hecke.FinGenGrpAb, Hecke.FinGenGrpAbMap

 > Computes the subgroup of the Ray Class Group $R$ given by the norm of the extension generated by the roots of $f$ 
   
***
"""

function norm_group(f::Nemo.PolyElem, mR::Hecke.MapRayClassGrp)
  
  R=mR.header.domain
  O=mR.modulus_fin.parent.order
  K=O.nf
  d=discriminant(f)
  N=num(norm(K(d)))
  N1=fmpz(norm(mR.modulus_fin))
  n=degree(f)
  
  Q,mQ=quo(R,n, false)
  
  S,mS=snf(Q)
  M=rels(S)
  
  p=1
  Ox,x=O["y"]
  f=Ox([O(coeff(f,i)) for i=0:n])
  
  determinant=abs(det(M))
  listprimes=typeof(R[1])[]  
  new_mat=M
  
  #
  # Adding small primes until they generate the norm group
  #
  
  while determinant!= n
    p=next_prime(p)
    if !divisible(N,p) && !divisible(N1,p) 
      L=prime_decomposition(O,p)
      for i=1:length(L)
        F,mF=ResidueField(O,L[i][1])
        Fz,z= F["z"]
        g=mF(f)
        D=factor_shape(g)
        E=collect(keys(D))[1]
        candidate=mR\(((L[i][1]))^E)
        new_mat=vcat(new_mat,((mS*mQ)(candidate)).coeff)
        new_mat=hnf(new_mat)
        new_mat=submat(new_mat,1,1,ngens(S), ngens(S))  
        new_det=abs(det(new_mat))
        if determinant!=new_det
          push!(listprimes, candidate)
          determinant=new_det
        end
      end
    end
  end
  
  #
  # Computing the Hermite normal form of the subgroup
  #
  subgrp=[el for el in listprimes]
  for i=1:ngens(R)
    push!(subgrp, n*R[i])
  end
  return sub(R, subgrp, false)

end


doc"""
***
  function isabelian(f::Nemo.Generic.Poly, K::Nemo.AnticNumberField) -> Bool

 > Check if the extension generated by a root of the irreducible polynomial $f$ over a number field $K$ is abelian
 > The function is probabilistic.

***
"""

function isabelian(f::Nemo.PolyElem, K::Nemo.AnticNumberField)
  
  O=maximal_order(K)
  d=discriminant(f)
  N=num(norm(K(d)))
  n=degree(f)
  
  inf_plc=real_places(K)
  m=ideal(O,O(d))
  lp=collect(keys(factor(n)))
  M=zero_matrix(FlintZZ,0,0)
  Grps=Any[]
  R=AbelianGroup(fmpz[])
  for i=1:length(lp)
    T,mT=ray_class_group_p_part(Int(lp[i]),m,inf_plc)
    if valuation(order(T),lp[i])<valuation(n,lp[i])
      return false
    end
    push!(Grps, [T,mT])
  end
  for i=1:length(lp)
    R=direct_product(R,Grps[i][1])
  end
  function mR(J::NfOrdIdl)
    x=(Grps[1][2]\J).coeff
    for i=2:length(lp)
      hcat!(x,((Grps[i][2])\J).coeff)
    end
    return R(x)
  end
 
  
  S,mS=snf(R)
  M=rels(S)
  
  p=1
  Ox,x=O["y"]
  f1=Ox([O(coeff(f,i)) for i=0:n])
  
  determinant=order(S)
  new_mat=M

  B=log(abs(discriminant(O)))*degree(f)+log(N)
  B=4*B+2.5*degree(f)*degree(O)+5
  B=B^2
  
  #
  # Adding small primes until they generate the norm group
  #
  
  while determinant > n 
    p=next_prime(p)
    if p>B
      return false #Bach bound says that the norm group must be generated by primes $\leq B$
    end
    if !divisible(N,p)
      L=prime_decomposition(O,p)
      for i=1:length(L)
        F,mF=ResidueField(O,L[i][1])
        Fz,z= F["z"]
        g=mF(f1)
        D=factor_shape(g)
        if length(D)>1
          return false
        end
        candidate=mR(((L[i][1])^first(keys(D))))
        new_mat=vcat(new_mat,(mS(candidate)).coeff)
        new_mat=hnf(new_mat)
        new_mat=submat(new_mat,1,1,ngens(S), ngens(S))  
        determinant=abs(det(new_mat))
      end
    end
  end
  if determinant==n
    return true
  else 
    return false
  end

end



doc"""
***
  conductor_min(C::Hecke.ClassField) -> NfOrdIdl

> Return the minimum integer in the conductor of the abelian extension corresponding to C
***
"""
function conductor_min(C::Hecke.ClassField)

  mp=C.mq
  
  #
  #  First, we need to find the subgroup
  #
  
  mR=mp.f
  mS=mp.g
  while issubtype(typeof(mR), Hecke.CompositeMap)
    mS = mR.g*mS
    mR = mR.f
  end
  
  R=domain(mR)
  cond=mR.modulus_fin
  inf_plc=mR.modulus_inf
  O=parent(cond).order
  E=order(domain(mp))
  K=O.nf
  expo=Int(exponent(domain(mp)))
  
  mS=inv(mS)
  dom=domain(mS)
  M=zero_matrix(FlintZZ,ngens(dom), ngens(codomain(mS)))
  for i=1:ngens(dom)
    elem=mS(dom[i]).coeff
    for j=1:ngens(codomain(mS))
      M[i,j]=elem[1,j]
    end
  end
  S1=Hecke.GrpAbFinGenMap(domain(mS),codomain(mS),M)
  T,mT=Hecke.kernel(S1)

  Sgens=find_gens_sub(mR,mT)

  #
  #  Some of the factors of the modulus are unnecessary for order reasons:
  #
   
  L=factor(cond)
  for (p,vp) in L
    if gcd(E,minimum(p))==1
      if gcd(E, norm(p)-1)==1
        Base.delete!(L,p)
      else
        L[p]=1
      end  
    else
      if L[p]==1
        Base.delete!(L,p)
      end
    end
  end
  divisors=collect(keys(L))
  
  cond=1
  candidate=1
  
  #
  # Test the finite primes dividing the modulus
  #
  
  while !isempty(divisors)
    p=divisors[length(divisors)]
    if L[p]==1
      candidate=ideal(O,1)
      for (q,vq) in L
        if q !=p
          candidate*=q^Int(vq)
        end
      end
      r,mr=ray_class_group(candidate,inf_plc, n_quo=expo)
      quot=GrpAbFinGenElem[mr\s for s in Sgens]
      s,ms=quo(r,quot, false)
      if order(s)==E
        Base.delete!(L,p)
      else 
        i=1
        if !divisible(fmpz(cond),minimum(p))
          cond*=minimum(p)
        end
        pd=prime_decomposition(O,Int(minimum(p)))
        while i<= length(divisors)-1
          if divisors[i].gen_one== minimum(p)  
            j=1
            while divisors[i] != pd[j][1]
              j+=1
            end
            if L[divisors[i]]<= pd[j][2]
              Base.delete!(L,p)
              deleteat!(divisors,i)
              continue
            end
          end
          i+=1
        end
      end
      pop!(divisors)
    else 
      j=1
      l=valuation(E,minimum(p))
      cand=ideal(O,1)
      for (q,vq) in L
        if q !=p
          cand*=q^Int(vq)
        end
      end
      for j=1:L[p]-1
        candidate=cand*p^(L[p]-j)
        iscandcond=true
        r, mr=ray_class_group(candidate,inf_plc, Int(minimum(p))^l)
        quot=GrpAbFinGenElem[mr\s for s in Sgens]
        s,ms=quo(r,quot, false) 
        if valuation(order(s),minimum(p)) < l
          iscandcond=false
          break
        end
      end
      if !iscandcond
        L[p]=L[p]-j+1
        i=1
        pd=prime_decomposition(O,Int(minimum(p)))
        j=1
        while pd[j][1]!=p
          j+=1
        end
        k=Int(ceil(L[p]/pd[j][2]))
        v=valuation(cond,minimum(p))
        if v<k
          cond*=minimum(p)^(k-v)
        end
        while i<= length(divisors)-1
          if divisors[i].gen_one== minimum(p)  
            j=1
            while divisors[i] != pd[j][1]
              j+=1
            end
            if L[divisors[i]]<= k*pd[j][2]
              Base.delete!(L,p)
              deleteat!(divisors,i)
              continue
            end
          end
          i+=1
        end
        pop!(divisors)
      else 
        L[p]=1
      end
    end
  end 
  return cond
  
end 

#
#  For this function, we assume the base field to be normal over Q and the conductor of the extension we are considering to be invariant
#  The input must be a multiple of the minimum of the conductor, we don't check for consistancy. 
#



function _is_conductor_min_tame_normal(C::Hecke.ClassField, a::Int)
  return _is_conductor_min_normal(C, a, Dict{NfOrdIdl,Int}())
end

function _is_conductor_min_normal(C::Hecke.ClassField, a::Int, wprimes::Dict{NfOrdIdl, Int})

  mp=C.mq
  mR=mp.f
  mS=mp.g
  while issubtype(typeof(mR), Hecke.CompositeMap)
    mS = mR.g*mS
    mR = mR.f
  end
  
  R=domain(mR)
  cond=mR.modulus_fin
  inf_plc=mR.modulus_inf
  O=parent(cond).order
  E=Int(order(domain(mp)))
  expo=Int(exponent(domain(mp)))
  K=O.nf
  
  #
  #  First, we need to find the subgroup
  #
  if isdefined(C, :norm_group)
    mT=C.norm_group
  else
    mS=inv(mS)
    dom=domain(mS)
    M=zero_matrix(FlintZZ,ngens(dom), ngens(codomain(mS)))
    for i=1:ngens(dom)
      elem=mS(dom[i]).coeff
      for j=1:ngens(codomain(mS))
        M[i,j]=elem[1,j]
      end
    end
    S1=Hecke.GrpAbFinGenMap(domain(mS),codomain(mS),M)
    _,mT=Hecke.kernel(S1)
    C.norm_group=mT
  end
  if isdefined(C, :small_gens)
    Sgens=C.small_gens
  else
    Sgens=find_gens_sub(mR,mT)
    C.small_gens=Sgens
  end
  
  # We try to remove the integers from the factorization
  lp=collect(keys(factor(a).fac))
  lq=[prime_decomposition(O,p) for p in lp]
  for i=1:length(lp)
    P=lq[i][1][1]
    g=gcd(E, norm(P)-1)
    if g==1
      return false
    end
    d1=Dict{NfOrdIdl,Int}()
    for j=1:length(lq)
      if j!=i
        for k=1:length(lq[j])
          d1[lq[j][k][1]]=1
        end
      end
    end
    r,mr=ray_class_group(O, expo, mR, d1, wprimes, inf_plc)
    quot=GrpAbFinGenElem[mr(s) for s in Sgens]
    s,ms=quo(r,quot)
    if order(s)==E
      return false
    end
  end
  if !isempty(wprimes)
    d=Dict{NfOrdIdl, Int}()
    for j=1:length(lq)
      for k=1:length(lq[j])
        d[lq[j][k][1]]=1
      end
    end
    lpw=Set([minimum(p) for p in keys(wprimes)])
    for q in lpw
      newwp=Dict{NfOrdIdl,Int}()
      for (P,e) in wprimes
        if minimum(P)==q 
          if e > 2
            newwp[P]=e-1
          end
        else
          newwp[P]=e
        end
      end 
      r,mr=ray_class_group(O, expo, mR, d, newwp, inf_plc)
      quot=GrpAbFinGenElem[mr(s) for s in Sgens]
      s,ms=quo(r,quot)
      if order(s)==E
        return false
      end
    end
  end
  return true

  
end 


function _conductor_min_tame_normal(C::Hecke.ClassField, a::Int)
  return _conductor_min_normal(C::Hecke.ClassField, a::Int, Dict{NfOrdIdl, Int}())
end


function _conductor_min_normal(C::Hecke.ClassField, a::Int, wprimes::Dict{NfOrdIdl, Int})

  mp=C.mq
  
  #
  #  First, we need to find the subgroup
  #
  
  mR=mp.f
  mS=mp.g
  while issubtype(typeof(mR), Hecke.CompositeMap)
    mS = mR.g*mS
    mR = mR.f
  end
  
  R=domain(mR)
  cond=mR.modulus_fin
  inf_plc=mR.modulus_inf
  O=parent(cond).order
  E=Int(order(domain(mp)))
  expo=Int(exponent(domain(mp)))
  K=O.nf
  
  if isdefined(C, :norm_group)
    mT=C.norm_group
  else
    mS=inv(mS)
    dom=domain(mS)
    M=zero_matrix(FlintZZ,ngens(dom), ngens(codomain(mS)))
    for i=1:ngens(dom)
      elem=mS(dom[i]).coeff
      for j=1:ngens(codomain(mS))
        M[i,j]=elem[1,j]
      end
    end
    S1=Hecke.GrpAbFinGenMap(domain(mS),codomain(mS),M)
    _,mT=Hecke.kernel(S1)
    C.norm_group=mT
  end
  if isdefined(C, :small_gens)
    Sgens=C.small_gens
  else
    Sgens=find_gens_sub(mR,mT)
    C.small_gens=Sgens
  end
  cond=1
  lp=collect(keys(factor(a).fac))
  lq=[prime_decomposition(O,p) for p in lp]
  for i=1:length(lp)
    P=lq[i][1][1]
    g=gcd(E, norm(P)-1)
    if g==1
      continue
    end
    d1=Dict{NfOrdIdl,Int}()
    for j=1:length(lq)
      if j!=i
        for k=1:length(lq[j])
          d1[lq[j][k][1]]=1
        end
      end
    end
    r,mr=ray_class_group(O, expo, mR, d1, wprimes, inf_plc)
    quot=GrpAbFinGenElem[mr(s) for s in Sgens]
    s,ms=quo(r,quot)
    if order(s)==E
      continue
    else 
      cond*=lp[i]
    end
  end
  return cond

  
end 
