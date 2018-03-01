export conductor, isconductor

########################################################################################
#
#  Tools for conductor
#
########################################################################################


function _modulus_with_inf(mR::Map)
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

function find_gens_sub(mR::MapRayClassGrp, mT::GrpAbFinGenMap)

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

function _1pluspk_1pluspk1(K::AnticNumberField, p::NfOrdIdl, pk::NfOrdIdl, pv::NfOrdIdl, lp::Dict{NfOrdIdl, Int}, prime_power::Dict{NfOrdIdl, NfOrdIdl}, a::Int, n::Int)
  
  O=maximal_order(K)
  b=basis(pk)
  N = basis_mat(pv)*basis_mat_inv(pk)
  G=AbelianGroup(numerator(N))
  S,mS=snf(G)
  #Generators
  gens=Array{NfOrdElem,1}(ngens(S))
  for i=1:ngens(S)
    x=mS(S[i])
    gens[i]=O(0)
    for j=1:ngens(G)
      gens[i]+=mod(x[j], S.snf[end])*b[j]
    end
  end
  for i=1:ngens(S)
    gens[i]+=1
  end
  if length(lp) > 1
    i_without_p = ideal(O,1)
    for (p2,vp2) in lp
      (p != p2) && (i_without_p *= prime_power[p2])
    end

    alpha, beta = idempotents(prime_power[p],i_without_p)
    for i in 1:length(gens)
      gens[i] = beta*gens[i] + alpha
    end   
  end
  if mod(n,2)==0
    for i=1:length(gens)
      gens[i]=make_positive(gens[i],a)
    end
  end
  return gens
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

  if isdefined(C,:conductor)
    return C.conductor
  end
  mp=C.mq
  G=domain(mp)
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
  if minimum(cond)==1 && isempty(inf_plc)
    return ideal(O,1), InfPlc[]
  end

  E=order(domain(mp))
  expo=Int(exponent(domain(mp)))
  K=O.nf
  
  
  
  #
  #  Some of the factors of the modulus are unnecessary for order reasons:
  #
    
  L=deepcopy(mR.fact_mod)
  for (p,vp) in L
    if !divisible(E,minimum(p))
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
  
  prime_power=Dict{NfOrdIdl, NfOrdIdl}()
  for (p,v) in mR.fact_mod
    prime_power[p]=p^v
  end
  
  if !isempty(inf_plc)
    totally_positive_generators(mR,Int(cond.gen_one))
  end

  #Finite part of the modulus
  if !isempty(L)
    tmg=mR.tame_mult_grp
    wild=mR.wild_mult_grp
  end
  for (p,v) in L
    if v==1
      Q,mQ=quo(G,[mp\ideal(O,tmg[p][1])],false)
      if order(Q)==E
        Base.delete!(L,p)
      end  
    else
      k1=v-1
      k2=v
      gens=GrpAbFinGenElem[]
      Q=DiagonalGroup(Int[])
      while k1>=1
        multg=_1pluspk_1pluspk1(K, p, p^k1, p^k2, mR.fact_mod, prime_power, Int(cond.gen_one),Int(E))
        for i=1:length(multg)
          push!(gens, mp\ideal(O,multg[i]))
        end
        Q,mQ=quo(G,gens,false)
        if order(Q)!=E
          L[p]=k2
          break
        end
        k1-=1
        k2-=1
      end
      if order(Q)==E
        if haskey(tmg, p)
          push!(gens, mp\ideal(O,tmg[p][1]))
          Q,mQ=quo(G,gens,false)
          if order(Q)==E
            delete!(L,p)
          end
        else
          delete!(L,p)
        end
      end
    end
  end
  cond=ideal(O,1)
  for (p,vp) in L
    cond*=p^vp
  end
  #Infinite part of the modulus
  cond_inf=InfPlc[]
  if !isempty(inf_plc)
    S, ex, lo=carlos_units(O)
    for i=1:length(inf_plc)
      pl=inf_plc[i]
      j=1
      while true
        if !ispositive(ex(S[j]),pl)
          break
        end
        i+=1
      end
      delta=minimum(cond)*ex(S[j])
      el=1+delta
      con=abs_upper_bound(1/real(conjugates_arb(delta))[j], fmpz)
      el+=con*delta
      Q,mQ=quo(G,mp\ideal(O,el),false)
      if order(Q)!=e
        push!(cond_inf, pl)
      end
    end
  end

  return cond, cond_inf
  
end 


doc"""
***
  isconductor(C::Hecke.ClassField, m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[]; check) -> NfOrdIdl, Array{InfPlc,1}

> Checks if m, inf_plc is the conductor of the abelian extension corresponding to C. If check is false, it assumes that the 
> given modulus is a multiple of the conductor.

***
"""
function isconductor(C::Hecke.ClassField, m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[]; check::Bool=true)

  mp=C.mq
  G=domain(mp)
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
  inf_plc2=mR.modulus_inf
  O=parent(cond).order
  E=order(domain(mp))
  expo=Int(exponent(domain(mp)))
  K=O.nf
  tmg=mR.tame_mult_grp
  wild=mR.wild_mult_grp
  
  if check 
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
    
    r,mr=ray_class_group(m,inf_plc, n_quo= expo)
    quot=GrpAbFinGenElem[mr\s for s in Sgens]
    s,ms=quo(r,quot, false)
    if order(s)!=E
      return false
    end
  end

  #
  #  Some of the factors of the modulus are unnecessary for order reasons:
  #
  
  
  L=factor(m)
  for (p,vp) in L
    if !haskey(mR.fact_mod, p) || vp>mR.fact_mod[p]
      return false
    end
    if !divisible(E,minimum(p))
      if gcd(E, norm(p)-1)==1
        return false
      elseif vp>1
        return false
      end 
    elseif vp==1
      return false
    end
  end
  
  if isodd(E) && !isempty(inf_plc)
    return false
  end
  for pl in inf_plc
    if !(pl in inf_plc2)
      return false
    end
  end
  
  prime_power=Dict{NfOrdIdl, NfOrdIdl}()
  for (p,v) in L
    prime_power[p]=p^v
  end
  
  if !isempty(inf_plc2)
    totally_positive_generators(mR,Int(cond.gen_one))
  end
  
  #Finite part of the modulus
  for (p,v) in L
    if v==1
      Q,mQ=quo(G,[mp\ideal(O,tmg[p][1])])
      if order(Q)==E
        return false
      end  
    else     
      multg=_1pluspk_1pluspk1(K, p, p^(v-1), p^v, mR.fact_mod, prime_power, Int(cond.gen_one),Int(E))
      gens=Array{GrpAbFinGenElem,1}(length(multg))
      for i=1:length(multg)
        gens[i]= mp\ideal(O,multg[i])
      end
      Q,mQ=quo(G,gens, false)
      if order(Q)==E
        return false
      end
    end
  end

  #Infinite part of the modulus
  if !isempty(inf_plc2)
    S, ex, lo=carlos_units(O)
    for i=1:length(inf_plc)
      i=1
      while true
        if !ispositive(ex(S[i]),pl)
          break
        end
        i+=1
      end
      el=1+minimum(cond)*ex(S[i])
      while !ispositive(el, pl)
        el+=minimum(cond)*ex(S[i])
      end
      Q,mQ=quo(G,mp\ideal(O,el), false)
      if order(Q)==e
        return false
      end
    end
  end
  
  return true
  
end


#
#  For this function, we assume the base field to be normal over Q and the conductor of the extension we are considering to be invariant
#  The input must be a multiple of the minimum of the conductor, we don't check for consistancy. 
#

function _is_conductor_min_normal(C::Hecke.ClassField, a::Int)
# a is a positive integer in the modulus

  mp=C.mq
  R=domain(mp)
  mr=mp.f
  while issubtype(typeof(mr), Hecke.CompositeMap)
    mr = mr.f
  end
  lp=mr.fact_mod
  if isempty(lp)
    return true
  end
  O=order(first(keys(lp)))
  K=nf(O)
  tmg=mr.tame_mult_grp
  #first, tame part
  primes_done=fmpz[]
  for p in keys(tmg)
    if minimum(p) in primes_done 
      continue
    end
    push!(primes_done, minimum(p))
    el=mp\ideal(O,tmg[p][1])
    if iszero(el)
      return false
    end
  end
  
  #wild part
  if !isempty(mr.wild_mult_grp)
    prime_power=Dict{NfOrdIdl, NfOrdIdl}()
    for (p,v) in lp
      prime_power[p]=p^v
    end
    wldg=mr.wild_mult_grp
    primes_done=fmpz[]
    for p in keys(wldg)
      if minimum(p) in primes_done
        continue
      end
      push!(primes_done, minimum(p))
      @assert lp[p]>=2
      k=lp[p]-1
      pk=p^k
      pv=prime_power[p]
      gens=_1pluspk_1pluspk1(K, p, pk, pv, lp, prime_power, a, Int(order(R)))
      iscond=false
      for i in 1:length(gens)
        if !iszero(mp\ideal(O,gens[i]))
          iscond=true
          break
        end
      end
      if !iscond
        return false
      end
    end
  end
  return true

end 

####################################################################################
#
#  Discriminant function
#
####################################################################################

function discriminant(C::ClassField)
  
  if isdefined(C,:conductor)
    m=C.conductor[1]
    inf_plc=C.conductor[2]
  else
    C.conductor=conductor(C)
    m=C.conductor[1]
    inf_plc=C.conductor[2]  
  end
  @assert typeof(m)==NfOrdIdl
  
  mp=C.mq
  G=domain(mp)
  n=order(G)
  
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
  
  relative_disc=Dict{NfOrdIdl,Int}()
  abs_disc=Dict{fmpz,fmpz}()
  lp=mR.fact_mod
  if isempty(lp)
    C.relative_discriminant=relative_disc
  end
  tmg=mR.tame_mult_grp
  wldg=mr.wild_mult_grp
  prime_power=Dict{NfOrdIdl, NfOrdIdl}()
  for (p,v) in lp
    prime_power[p]=p^v
  end
  fact=factor(m)

  for (p,v) in fac
    if v==1
      ap=n
      if isprime(n)
        ap-=1
      else
        el=mp\ideal(O,tmg[p][1]) #The generator is totally positive, we modified it before
        q,mq=quo(R,[el])
        ap-= order(q)
      end
      qw=divexact(degree(O),prime_decomposition_type(O,Int(minimum(p)))[1][2])*ap
      abs_disc[minimum(p)]=qw
      relative_disc[p]=ap
    else
      ap=n*s
      if isprime(n)
        ap-=lp[p]
      else
        if length(lp) > 1
          i_without_p = ideal(O,1)
          for (p2,vp2) in lp
            (p != p2) && (i_without_p *= prime_power[p2])
          end
          alpha, beta = idempotents(prime_power[p],i_without_p)
        end
        s=lp[p]
        @hassert :QuadraticExt 1 s>=2
        els=GrpAbFinGenElem[]
        for k=2:lp[p]      
          s=s-1
          pk=p^s
          pv=pk*p
          gens=_1pluspk_1pluspk1(K, p, pk, pv, lp, prime_power, a,n)
          for i=1:length(gens)
            push!(els,mp\ideal(O,gens[i]))
          end
          ap-=order(quo(R,els)[1])
          @hassert :QuadraticExt 1 ap>0
        end
        if haskey(tmg, p)
          push!(els, mp\ideal(O,tmg[p][1]))
        end
        ap-=order(quo(R,els)[1])
        @hassert :QuadraticExt 1 ap>0
      end
      td=prime_decomposition_type(O,Int(minimum(p)))
      np=fmpz(minimum(p))^(td[1][1]*length(td)*ap)
      discr*=np
      abs_disc[minimum(p)]=td[1][1]*length(td)*ap
      relative_disc[p]=ap
    end
  end
  C.relative_discriminant=relative_disc
  C.absolute_discriminant=abs_disc
  return true
  
end


#######################################################################################
#
#  Functions to compute the relative discriminant of a class field
#
#######################################################################################

function discriminant_conductor(O::NfOrd, C::ClassField, a::Int, mr::MapRayClassGrp, bound::fmpz, n::Int)
  
 
  lp=mr.fact_mod
  abs_disc=factor(discriminant(O)^n).fac
  if isempty(lp)
    C.absolute_discriminant=abs_disc
    return true
  end
  K=nf(O)
  
  discr=fmpz(1)
  mp=C.mq
  R=domain(mp)
  
  cyc_prime= isprime(n)==true
  
  #first, tamely ramified part
  tmg=mr.tame_mult_grp
  primes_done=fmpz[]
  for p in keys(tmg) 
    if minimum(p) in primes_done || haskey(mr.wild_mult_grp, p)
      continue
    end
    ap=n
    push!(primes_done, minimum(p))
    if cyc_prime
      ap-=1
    else
      el=mp\ideal(O,tmg[p][1]) #The generator is totally positive, we modified it before
      q,mq=quo(R,[el])
      ap-= order(q)
    end
    qw=divexact(degree(O),prime_decomposition_type(O,Int(minimum(p)))[1][2])*ap
    discr*=fmpz(minimum(p))^qw
    if discr>bound
      @vprint :QuadraticExt 2 "too large\n"
      return false
    else
      if haskey(abs_disc, minimum(p))
        abs_disc[minimum(p)]+=qw
      else 
        abs_disc[minimum(p)]=qw
      end
      #for q in keys(tmg)
      #  if minimum(q)==minimum(p) 
      #    relative_disc[q]=ap
      #  end
      #end
    end
  end
  
  #now, wild ramification
  if !isempty(mr.wild_mult_grp)
    prime_power=Dict{NfOrdIdl, NfOrdIdl}()
    for (p,v) in lp
      prime_power[p]=p^v
    end
    wldg=mr.wild_mult_grp
    primes_done=fmpz[]
    for p in keys(wldg)
      if minimum(p) in primes_done
        continue
      end 
      push!(primes_done, minimum(p)) 
      ap=n*lp[p]
      if cyc_prime
        ap-=lp[p]
      else
        if length(lp) > 1
          i_without_p = ideal(O,1)
          for (p2,vp2) in lp
            (p != p2) && (i_without_p *= prime_power[p2])
          end

          alpha, beta = idempotents(prime_power[p],i_without_p)
        end
        s=lp[p]
        @hassert :QuadraticExt 1 s>=2
        els=GrpAbFinGenElem[]
        for k=2:lp[p]      
          s=s-1
          pk=p^s
          pv=pk*p
          gens=_1pluspk_1pluspk1(K, p, pk, pv, lp, prime_power, a,n)
          for i=1:length(gens)
            push!(els,mp\ideal(O,gens[i]))
          end
          ap-=order(quo(R,els)[1])
          @hassert :QuadraticExt 1 ap>0
        end
        if haskey(tmg, p)
          push!(els, mp\ideal(O,tmg[p][1]))
        end
        ap-=order(quo(R,els)[1])
        @hassert :QuadraticExt 1 ap>0
      end
      td=divexact(degree(O),prime_decomposition_type(O,Int(minimum(p)))[1][2])*ap
      np=fmpz(minimum(p))^td
      discr*=np
      if discr>bound
        @vprint :QuadraticExt 2 "too large\n"
        return false
      else
        if haskey(abs_disc, minimum(p))
          abs_disc[minimum(p)]+=td
        else 
          abs_disc[minimum(p)]=td
        end
      #  for q in keys(tmg)
      #    if minimum(q)==minimum(p) 
      #      relative_disc[q]=ap
      #    end
      #  end
      end
    end
  end
  #C.relative_discriminant=relative_disc
  C.absolute_discriminant=abs_disc
  return true

end

##############################################################################
#
#  Is Abelian function
#
##############################################################################

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
  Ox,x=PolynomialRing(O,"y", cached=false)
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
        Fz,z= PolynomialRing(F,"z", cached=false)
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

################################################################################
#
#  Norm group function
#
################################################################################

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
  Ox,x=PolynomialRing(O,"y", cached=false)
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
        Fz,z= PolynomialRing(F, "z", cached=false)
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


function _norm_group_gens_small(C::ClassField)

  mp=C.mq
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
  
  return Sgens
  
end

