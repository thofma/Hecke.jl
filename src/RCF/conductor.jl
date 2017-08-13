export conductor, isconductor

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
  K=O.nf
  
  mS=inv(mS)
  dom=domain(mS)
  M=MatrixSpace(ZZ,0, ngens(codomain(mS)))()
  for i=1:ngens(dom)
    M=vcat(M,(mS(dom[i])).coeff)
  end
  S1=Hecke.GrpAbFinGenMap(domain(mS),codomain(mS),M)
  T,mT=Hecke.kernel(S1)
  W,mW=snf(T)
  
  Sgens=[mR(mT(mW\w)) for w in gens(W)]
  
  #
  #  Some of the factors of the modulus are unnecessary for order reasons:
  #
  
  
  L=factor(cond)
  for (p,vp) in L
    if gcd(E,p.gen_one)==1
      if gcd(E, norm(p)-1)==1
        delete!(L,p)
      else
        L[p]=1
      end  
    else
      if L[p]==1
        delete!(L,p)
      end
    end
  end
  divisors=collect(keys(L))
  

  candidate=1
  
  #
  # Test the finite primes dividing the modulus
  #
  
  while !isempty(divisors)
    p=divisors[length(divisors)]
    if L[p]==1
      lp=factor(gcd(E, norm(p)-1))
      candidate=ideal(O,1)
      for (q,vq) in L
        if q !=p
          candidate*=q^Int(vq)
        end
      end
      iscandcond=true
      for (q,vq) in lp
        r,mr=ray_class_group_p_part(Int(q),candidate,inf_plc)
        quot=GrpAbFinGenElem[mr\s for s in Sgens]
        s,ms=quo(r,quot)
        if valuation(order(s),q)<valuation(E,q)
          iscandcond=false
          break
        end
      end
      if iscandcond
        delete!(L,p)
      end
      pop!(divisors)
    else 
      j=1
      l=valuation(E,p.gen_one)
      cand=ideal(O,1)
      for (q,vq) in L
        if q !=p
          cand*=q^Int(vq)
        end
      end
      for j=1:L[p]-1
        candidate=cand*p^(L[p]-j)
        iscandcond=true
        r, mr=ray_class_group_p_part(Int(p.gen_one),candidate,inf_plc)
        quot=GrpAbFinGenElem[mr\s for s in Sgens]
        s,ms=quo(r,quot) 
        if valuation(order(s),p.gen_one) < l
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
      r,mr=ray_class_group_p_part(2,cond,candidate_inf)
      quot=GrpAbFinGenElem[mr\s for s in Sgens]
      s,ms=quo(r,quot)
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
  K=O.nf
  
  mS=inv(mS)
  dom=domain(mS)
  M=MatrixSpace(ZZ,0, ngens(codomain(mS)))()
  for i=1:ngens(dom)
    M=vcat(M,(mS(dom[i])).coeff)
  end
  S1=Hecke.GrpAbFinGenMap(domain(mS),codomain(mS),M)
  T,mT=Hecke.kernel(S1)
  W,mW=snf(T)
  
  Sgens=[mR(mT(mW\w)) for w in gens(W)]
  
  L=factor(cond)
  for (p,vp) in L
    if gcd(E,p.gen_one)==1
      if gcd(E, norm(p)-1)==1
        delete!(L,p)
      else
        L[p]=1
      end  
    else
      if L[p]==1
        delete!(L,p)
      end
    end
  end
  
  
  L1=factor(m)
  for (p,vp) in L1
    if haskey(L,p) && L1[p]>L[p]
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
  lp=factor(E)
  for (p,vp) in lp
    r,mr=ray_class_group_p_part(Int(p),m,inf_plc)
    quot=GrpAbFinGenElem[mr\s for s in Sgens]
    s,ms=quo(r,quot)
    if valuation(order(s),p)<vp
      println("m is not in the congruence subgroup\n")
      return false
    end
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
      lp=factor(gcd(E, norm(p)-1))
      candidate=ideal(O,1)
      for (q,vq) in L1
        if q !=p
          candidate*=q^Int(vq)
        end
      end
      iscandcond=true
      for (q,vq) in lp
        r,mr=ray_class_group_p_part(Int(q),candidate,inf_plc)
        quot=GrpAbFinGenElem[mr\s for s in Sgens]
        s,ms=quo(r,quot)
        if valuation(order(s),q)<valuation(E,q)
          iscandcond=false
          break
        end
      end
      if iscandcond
        return false
      end
      pop!(divisors)
    else 
      l=valuation(E,p.gen_one)
      candidate=ideal(O,1)
      for (q,vq) in L1
        if q !=p
          cand*=q^Int(vq)
        end
      end
      candidate=candidate*p^(L1[p]-1)
      iscandcond=true
      r, mr=ray_class_group(Int(p.gen_one),candidate,inf_plc)
      quot=GrpAbFinGenElem[mr\s for s in Sgens]
      s,ms=quo(r,quot) 
      if valuation(order(s),p.gen_one) < l
        iscandcond=false
        break
      end
      if iscandcond
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
      r,mr=ray_class_group_p_part(2,m,candidate_inf)
      quot=GrpAbFinGenElem[mr\s for s in Sgens]
      s,ms=quo(r,quot)
      if valuation(order(s),2)==l
        return false
      end
    end
  end
  
  return true

end


function _modulus_with_inf(mR::Map)
  global bad = mR
  while issubtype(typeof(mR), Hecke.CompositeMap)
    mR = mR.f
  end
  if issubtype(typeof(mR), Hecke.MapClassGrp)
    return ideal(order(codomain(mR)), 1),InfPlc[]
  elseif issubtype(typeof(mR), Hecke.MapRayClassGrpFacElem)
    return mR.modulus_fin, mR.modulus_inf
  end
  @assert issubtype(typeof(mR), Hecke.MapRayClassGrp)
  return mR.modulus_fin, mR.modulus_inf
end
