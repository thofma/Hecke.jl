export conductor, isconductor, norm_group, maximal_abelian_subfield, genus_field, content_ideal

########################################################################################
#
#  Tools for conductor
#
########################################################################################

function _norm_group_gens_small(C::ClassField)

  mp=C.mq

  mR = C.rayclassgroupmap
  mS = C.quotientmap
  
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
    if divisible(l,P.minimum)
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

#
#  This functions constructs generators for 1+p^u/1+p^u+1
#

function _1pluspk_1pluspk1(K::AnticNumberField, p::NfOrdIdl, pk::NfOrdIdl, pv::NfOrdIdl, lp::Dict{NfOrdIdl, Int}, prime_power::Dict{NfOrdIdl, NfOrdIdl}, a::Int, n::Int)
  
  O=maximal_order(K)
  b=basis(pk)
  N = basis_mat(pv, Val{false})*basis_mat_inv(pk, Val{false})
  G=AbelianGroup(N.num)
  S,mS=snf(G)
  #Generators
  gens=Array{NfOrdElem,1}(ngens(S))
  for i=1:ngens(S)
    gens[i]=O(0)
    for j=1:ngens(G)
      gens[i]+=mod(mS.map[i,j], S.snf[end])*b[j]
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
  mR = C.rayclassgroupmap
  mS = C.quotientmap
  mp = inv(mS)* mR
  G = domain(mp)
  #
  #  First, we need to find the subgroup
  #
  
  cond = mR.modulus_fin
  inf_plc = mR.modulus_inf
  O = parent(cond).order
  if isone(cond) && isempty(inf_plc)
    return ideal(O,1), InfPlc[]
  end
  E=order(G)
  expo=Int(exponent(G))
  K=O.nf
 
  #
  #  Some of the factors of the modulus are unnecessary for order reasons:
  #   
  L=deepcopy(mR.fact_mod)
  for (p,vp) in L
    if !divisible(E,p.minimum)
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
      Q,mQ = quo(G,[preimage(mp, ideal(O,tmg[p][1]))],false)
      if order(Q) == E
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
          push!(gens, preimage(mp, ideal(O,multg[i])))
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
    S, ex, lo = carlos_units(O)
    for i=1:length(inf_plc)
      pl=inf_plc[i]
      j=1
      while true
        if !ispositive(ex(S[j]),pl)
          break
        end
        j+=1
      end
      delta=minimum(mR.modulus_fin)*ex(S[j])
      el=1+delta
      con=abs_upper_bound(1/real(conjugates_arb(delta))[j], fmpz)
      el+=con*delta
      Q,mQ=quo(G, [mp\ideal(O,el)], false)
      if order(Q)!=E
        push!(cond_inf, pl)
      end
    end
  end

  return cond, cond_inf
  
end 

###############################################################################
#
#  isconductor function
#
###############################################################################

doc"""
***
  isconductor(C::Hecke.ClassField, m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[]; check) -> NfOrdIdl, Array{InfPlc,1}

> Checks if m, inf_plc is the conductor of the abelian extension corresponding to C. If check is false, it assumes that the 
> given modulus is a multiple of the conductor.

***
"""
function isconductor(C::Hecke.ClassField, m::NfOrdIdl, inf_plc::Array{InfPlc,1}=InfPlc[]; check::Bool=true)
  #
  #  First, we need to find the subgroup
  #
  
  mR = C.rayclassgroupmap
  mS = C.quotientmap
  G = codomain(mS)
  mp = inv(mS) * mR
  
  R = domain(mR)
  cond = mR.modulus_fin
  inf_plc2 = mR.modulus_inf
  O=parent(cond).order
  E=order(G)
  expo=Int(exponent(G))
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
    s,ms=quo(r, quot, false)
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
      Q,mQ=quo(G,[preimage(mp, ideal(O,tmg[p][1]))])
      if order(Q)==E
        return false
      end  
    else     
      multg=_1pluspk_1pluspk1(K, p, p^(v-1), p^v, mR.fact_mod, prime_power, Int(cond.gen_one),Int(E))
      gens=Array{GrpAbFinGenElem,1}(length(multg))
      for i=1:length(multg)
        gens[i]= preimage(mp, ideal(O,multg[i]))
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
      Q,mQ=quo(G,preimage(mp, ideal(O,el)), false)
      if order(Q)==E
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

doc"""
    discriminant(C::ClassField) -> NfOrdIdl
> Using the conductor-discriminant formula, compute the (relative) discriminant of $C$.
> This does not use the defining equations.
"""
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
  
  mp = inv(C.quotientmap) * C.rayclassgroupmap
  R = domain(mp)
  n = order(R)
  
  mR = C.rayclassgroupmap

  cond=mR.modulus_fin
  inf_plc=mR.modulus_inf
  O=parent(cond).order
  E=order(R)
  expo=Int(exponent(R))
  K=O.nf
  a=Int(minimum(m))
  relative_disc=Dict{NfOrdIdl,Int}()
  abs_disc=Dict{fmpz,fmpz}()
  lp=mR.fact_mod
  if isempty(lp)
    C.relative_discriminant=relative_disc
  end
  tmg=mR.tame_mult_grp
  wldg=mR.wild_mult_grp
  prime_power=Dict{NfOrdIdl, NfOrdIdl}()
  for (p,v) in lp
    prime_power[p]=p^v
  end
  fact=factor(m)

  for (p,v) in fact
    if v==1
      ap=n
      if isprime(n)
        ap-=1
      else
        el=mp\ideal(O,tmg[p][1]) #The generator is totally positive, we modified it before
        q,mq=quo(R,[el])
        ap-= order(q)
      end
      qw=divexact(degree(O), prime_decomposition_type(O,Int(p.minimum))[1][2])*ap
      abs_disc[p.minimum] = qw
      relative_disc[p] = ap
    else
      ap=n*v
      if isprime(n)
        ap-=v
      else
        if length(lp) > 1
          i_without_p = ideal(O,1)
          for (p2,vp2) in lp
            (p != p2) && (i_without_p *= prime_power[p2])
          end
          alpha, beta = idempotents(prime_power[p],i_without_p)
        end
        s=v
        @hassert :QuadraticExt 1 s>=2
        els=GrpAbFinGenElem[]
        for k=2:v      
          s=s-1
          pk=p^s
          pv=pk*p
          gens=_1pluspk_1pluspk1(K, p, pk, pv, lp, prime_power, a,Int(n))
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
      td=prime_decomposition_type(O,Int(p.minimum))
      np=fmpz(p.minimum)^(td[1][1]*length(td)*ap)
      abs_disc[p.minimum]=td[1][1]*length(td)*ap
      relative_disc[p]=ap
    end
  end
  C.relative_discriminant=relative_disc
  C.absolute_discriminant=abs_disc
  return C.relative_discriminant
  
end


###############################################################################
#
#  conductor function for abelian extension function
#
###############################################################################
#
#  For this function, we assume the base field to be normal over Q and the conductor of the extension we are considering to be invariant
#  The input must be a multiple of the minimum of the conductor, we don't check for consistency. 
#

function _is_conductor_min_normal(C::Hecke.ClassField, a::Int)
# a is a positive integer in the modulus

  mr = C.rayclassgroupmap

  mp = inv(C.quotientmap) * mr 
  R = domain(mp)

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
    if p.minimum in primes_done 
      continue
    end
    push!(primes_done, p.minimum)
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
      if p.minimum in primes_done
        continue
      end
      push!(primes_done, p.minimum)
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

#
#  Same function as above, but in the assumption that the map comes from a ray class group over QQ
#

function _is_conductor_minQQ(C::Hecke.ClassField, n::Int)

  mr = C.rayclassgroupmap
  mp = inv(C.quotientmap) * mr
  m = mr.modulus_fin
  mm = Int(minimum(m))
  lp = factor(m.minimum)
  
  O=order(m)
  K=nf(O)
  
  R=ResidueRing(FlintZZ, mm, cached=false)
  for (p,v) in lp.fac
    if isodd(p)
      if v==1
        x=_unit_grp_residue_field_mod_n(Int(p), n)[1]
        s=divexact(mm,Int(p))
        d,a,b=gcdx(s,Int(p))
        l=a*s*R(x)+p*b  
        if iszero(mp\(ideal(O,Int(l.data))))
          return false
        end
      else      
        s=divexact(mm,p^v)
        d,a,b=gcdx(s,p^v)
        x=a*s*R(1+p)^((p-1)*p^(v-2))+p^v*b
        if iszero(mp\(ideal(O,Int(x.data))))
          return false
        end
      end
    else
      if v==1
        return false
      end
      if v==2
        s=divexact(mm,4)
        d,a,b=gcdx(s,4)
        l=a*s*R(-1)+4*b
        if iszero(mp\(ideal(O,Int(l.data))))
          return false
        end
      else
        s=divexact(mm,2^v)
        d,a,b=gcdx(s, 2^v)
        l=a*s*R(5)^(2^(v-3))+2^v*b
        if iszero(mp\(ideal(O,Int(l.data))))
          return false
        end
      end
    end
  end
  return true

end 


#######################################################################################
#
#  relative discriminant for abelian extension function
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
  mp=inv(C.quotientmap) * C.rayclassgroupmap 
  R=domain(mp)
  
  cyc_prime= isprime(n)==true
  
  #first, tamely ramified part
  tmg=mr.tame_mult_grp
  primes_done=fmpz[]
  for p in keys(tmg) 
    if p.minimum in primes_done || haskey(mr.wild_mult_grp, p)
      continue
    end
    ap=n
    push!(primes_done, p.minimum)
    if cyc_prime
      ap-=1
    else
      el=mp\ideal(O,tmg[p][1]) #The generator is totally positive, we modified it before
      q,mq=quo(R,[el])
      ap-= order(q)
    end
    qw=divexact(degree(O),prime_decomposition_type(O,Int(p.minimum))[1][2])*ap
    discr*=fmpz(p.minimum)^qw
    if discr>bound
      @vprint :QuadraticExt 2 "too large\n"
      return false
    else
      if haskey(abs_disc, p.minimum)
        abs_disc[p.minimum]+=qw
      else 
        abs_disc[p.minimum]=qw
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
      if p.minimum in primes_done
        continue
      end 
      push!(primes_done, p.minimum) 
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
      td=divexact(degree(O),prime_decomposition_type(O,Int(p.minimum))[1][2])*ap
      np=p.minimum^td
      discr*=np
      if discr>bound
        @vprint :QuadraticExt 2 "too large\n"
        return false
      else
        if haskey(abs_disc, p.minimum)
          abs_disc[p.minimum]+=td
        else 
          abs_disc[p.minimum]=td
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

#same function but for ray class groups over QQ

function discriminant_conductorQQ(O::NfOrd, C::ClassField, m::Int, bound::fmpz, n::Int)
  
  discr=fmpz(1)
  mp = inv(C.quotientmap) * C.rayclassgroupmap
  G=domain(mp)
  
  cyc_prime= isprime(n)==true
  
  lp=factor(m).fac
  abs_disc=Dict{fmpz,Int}()

  R=ResidueRing(FlintZZ, m, cached=false)

  for (p,v) in lp 
    if v==1
      ap=n
      if cyc_prime
        ap-=1
      else
        x=_unit_grp_residue_field_mod_n(Int(p),n)[1]
        s=divexact(m,Int(p))
        d,a,b=gcdx(s, Int(p))
        l=Int((R(x)*a*s+b*Int(p)).data)
        el=mp\ideal(O,l)
        q,mq=quo(G,[el])
        ap-= order(q)
      end
      discr*=p^ap
      if discr>bound
        @vprint :QuadraticExt 2 "too large\n"
        return false
      else
        abs_disc[p]=ap
      end
    else
      ap=n*v
      pow=Int(p)^Int(v)
      el=R(1)
      if cyc_prime
        ap-=v
      else
        if isodd(p)
          s=divexact(m,pow)
          d,a,b=gcdx(pow,s)  
          s1=R(1+p)^(p-1)
          el=G[1]
          if v==2
            el=mp\ideal(O,Int((b*s*R(s1)+a*pow).data))
            ap-=order(quo(G,[el])[1])
          else
            for k=0:v-2      
              el=mp\ideal(O,Int((b*s*R(s1)^(p^k)+a*pow).data))
              ap-=order(quo(G,[el])[1])
              @hassert :QuadraticExt 1 ap>0
            end
          end
          if gcd(n,p-1)==1
            ap-=order(quo(G,[mp\(ideal(O,fmpz((b*s*R(s1)+a*pow).data)))])[1])
          else
            x=_unit_grp_residue_field_mod_n(Int(p),n)[1]
            el1=mp\ideal(O,Int((R(x)*b*s+a*pow).data))
            ap-=order(quo(G,[mp\(ideal(O,Int((b*s*R(s1)+a*pow).data))), el1])[1])
          end
        else
          s=divexact(m,2^v)
          d,a,b=gcdx(2^v,s)  
          el=0*G[1]
          for k=v-3:-1:0
            el=mp\ideal(O,Int((R(5)^(2^k)*b*s+a*2^v).data))
            ap-=order(quo(G,[el])[1])
          end
          el1=mp\ideal(O,Int((R(-1)*b*s+a*p^v).data))
          ap-=2*order(quo(G,[el, el1])[1])
        end
      end
      discr*=p^ap
      if discr>bound
        @vprint :QuadraticExt 2 "too large\n"
        return false
      else
        abs_disc[p]=ap
      end
    end
  end
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
  isabelian(K::NfRel) -> Bool

> Check if the extension is abelian over the coefficient ring.
> The function is probabilistic.
***
"""
function isabelian(K::NfRel)
  return isabelian(K.pol, base_ring(K))
end

doc"""
***
  isabelian(f::Nemo.Generic.Poly, K::Nemo.AnticNumberField) -> Bool

 > Check if the extension generated by a root of the irreducible polynomial $f$ over a number field $K$ is abelian
 > The function is probabilistic.

***
"""
#TODO: consolidate with norm_group!!!!
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
        new_mat=sub(new_mat,1:ngens(S), 1:ngens(S))  
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
  norm_group(K::NfRel{nf_elem}, mR::Hecke.MapRayClassGrp) -> Hecke.FinGenGrpAb, Hecke.FinGenGrpAbMap
  norm_group(K::NfRel_ns{nf_elem}, mR::Hecke.MapRayClassGrp) -> Hecke.FinGenGrpAb, Hecke.FinGenGrpAbMap

> Computes the subgroup of the Ray Class Group $R$ given by the norm of the extension.
***
"""
function norm_group(K::NfRel{nf_elem}, mR::Hecke.MapRayClassGrp, isabelian::Bool = true)
  base_ring(K) == nf(mR.modulus_fin.order) || error("field has to be over the same field as the ray class group")
  return norm_group(K.pol, mR, isabelian)
end
function norm_group(K::NfRel_ns{nf_elem}, mR::Hecke.MapRayClassGrp, isabelian::Bool = true)
  base_ring(K) == nf(mR.modulus_fin.order) || error("field has to be over the same field as the ray class group")
  return norm_group([is_univariate(x)[2] for x = K.pol], mR, isabelian)
end
 
doc"""
***
  norm_group(f::Nemo.PolyElem, mR::Hecke.MapRayClassGrp, isabelian::Bool = true; of_closure::Bool = false) -> Hecke.FinGenGrpAb, Hecke.FinGenGrpAbMap
  norm_group(f::Array{PolyElem{nf_elem}, mR::Hecke.MapRayClassGrp, isabelian::Bool = true; of_closure::Bool = false) -> Hecke.FinGenGrpAb, Hecke.FinGenGrpAbMap

> Computes the subgroup of the Ray Class Group $R$ given by the norm of the extension generated by a/the roots of $f$. If {{{isabelian}}} is set to true, then the code assumes the field to be
> abelian, hence the algorithm stops when the quotient by the norm group has the correct order.
> Even though the algorithm is probabilistic by nature, in this case the result is guaranteed.
> If {{{of_closure}}} is given, then the norm group of the splitting field of the polynomial(s)
> is computed.
> It is the callers responsibility to ensure that the ray class group passed in is large enough.
   
***
"""
function norm_group(f::Nemo.PolyElem, mR::Hecke.MapRayClassGrp, isabelian::Bool = true)
  return norm_group([f], mR, isabelian)
end

function norm_group(f::Array{T, 1}, mR::Hecke.MapRayClassGrp, isabelian::Bool = true; of_closure::Bool = false) where T <: PolyElem{nf_elem}
  
  R=mR.header.domain
  O=mR.modulus_fin.order
  K=O.nf
  N=lcm([numerator(norm(K(discriminant(x)))) for x = f])
  N1=fmpz(norm(mR.modulus_fin))

  @assert all(x->base_ring(x) == K, f)

  n=prod(degree(x) for x = f)
 
  if of_closure  
    #we cannot work in the quotient, it "could" be lcm(factorial(degree(x)) for x = f)
    Q,mQ=quo(R, elem_type(R)[])
  else
    Q,mQ=quo(R,n, false)
  end
  
  p=maximum(degree(x)+1 for x = f)
  
  listprimes=typeof(R[1])[]  
  
  #
  # Adding small primes until it stabilizes
  #
  
  max_stable = 2*n
  stable = max_stable

  while true
    if isabelian && order(Q) == n
      break
    end
    if !isabelian && order(Q) <= n && stable <= 0
      break
    end
    p=next_prime(p)
    if !divisible(N,p) && !divisible(N1,p) 
      L=prime_decomposition(O,p,1)
      for i=1:length(L)
        candidate = mR\L[i][1]
        if iszero(mQ(candidate))
          stable -= 1
          continue
        end
        F,mF=ResidueFieldSmall(O,L[i][1])
        mFp = extend_easy(mF, K)  
        Fz,z= PolynomialRing(ResidueRing(FlintZZ, Int(p)), "z", cached=false)
        all_deg = []
        #= the idea, taking 2 polys:
          f splits in d_i
          g splits in e_i
        Then, over an extensions of degree d_i an irresducible of degree e_i
        splits into factors of degree e_i/gcd(d_i, e_i) so there are gcd() many
        (but this is not used). The total degree over base field is then 
        d_i * e_i/gcd() = lcm(d_i, e_i)
        This can be iterated...
        =#
        for x = f
          g=Fz([coeff(mFp(coeff(x, i)), 0) for i = 0:degree(x)]) 
          D=factor_shape(g)
          push!(all_deg, [x[1] for x = D])
        end
        all_f = Set{Int}()
        for d = Iterators.product(all_deg...)
          push!(all_f, lcm(collect(d)))
        end
        if of_closure
          all_f = Set(lcm([x for x = all_f]))
        end
        for E = all_f
          candidate=E*candidate
          if !iszero(mQ(candidate) )
            Q, nQ = quo(Q, [mQ(candidate)])
            mQ = mQ*nQ
            push!(listprimes, candidate)
            stable = max_stable
          else
            stable -= 1
          end
        end  
      end
    end
  end
  
  #
  # Computing the Hermite normal form of the subgroup
  #
  subgrp=[el for el in listprimes]
  if !of_closure
    for i=1:ngens(R)
      push!(subgrp, n*R[i])
    end
  end
  return sub(R, subgrp, true)
end

doc"""
    maximal_abelian_subfield(K::NfRel{nf_elem}; of_closure::Bool = false) -> ClassField
> Using a probabilistic algorithm for the norm group computation, determine tha maximal
> abelian subfield in $K$ over its base field. If {{{of_closure}}} is set to true, then
> the algorithm is applied to the normal closure if $K$ (without computing it).
"""
function maximal_abelian_subfield(K::NfRel{nf_elem}; of_closure::Bool = false)
  zk = maximal_order(base_ring(K))
  d = ideal(zk, discriminant(K))
  try
    ZK = _get_maximal_order_of_nf_rel(K)
    d = ideal(zk, discriminant(ZK))
  catch e
    if !isa(e, AccessorNotSetError)
      rethrow(e)
    end
  end

  r1, r2 = signature(base_ring(K))
  C, mC = ray_class_group(d.num, infinite_places(base_ring(K))[1:r1], n_quo = degree(K))
  N, iN = norm_group(K, mC, of_closure = of_closure)
  return ray_class_field(mC, quo(C, N)[2])
end

doc"""
    maximal_abelian_subfield(A::ClassField, k::AnticNumberField) -> ClassField
> The maximal abelian extension of $k$ contained in $A$. $k$ must be a subfield of
> the base field of $A$.
"""
function maximal_abelian_subfield(A::ClassField, k::AnticNumberField)
  K = base_field(A)
  fl, mp = issubfield(k, K)
  @assert fl
  ZK = maximal_order(K)
  zk = maximal_order(k)
  # disc(ZK/Q) = N(disc(ZK/zk)) * disc(zk)^deg
  # we need the disc ZK/k, well a conductor.
  # I think for now, I cheat
  d = div(discriminant(ZK), discriminant(zk)^div(degree(K), degree(k)))

  M0 = defining_modulus(A)[1]
  f_M0 = factor(M0)
  # want m0 meet zk:
  f_m0 = typeof(f_M0)()
  for (P,e) = f_M0
    lp = prime_decomposition(zk, P.gen_one)
    p = first([x[1] for x = lp if valuation(mp(k(x[1].gen_two)), P) > 0])
    if haskey(f_m0, p)
      f_m0[p] += e
    else
      f_m0[p] = e
    end
  end
  if length(f_m0) == 0
    m0 = ideal(zk, 1)
    m0 = lcm(m0, ideal(zk, d))
  else
    m0 = evaluate(FacElem(f_m0), coprime = true)
    @assert denominator(m0) == 1
    m0 = lcm(numerator(m0), ideal(zk, d))
  end

  r, mr = ray_class_group(m0, real_places(k), n_quo = degree(A) * div(degree(K), degree(k)))
  Q, mQ = quo(r, elem_type(r)[], false)

  p = 100
  max_stable = ngens(domain(A.rayclassgroupmap)) * degree(K) * 4 #need s.th. better here!!
  stable = max_stable
  #= Think: 
   should be enough to generate r
   and the Bach-bound from above for K/k
  =#
  while true
    p = next_prime(p)
    if minimum(m0) % p == 0
      continue
    end
    lp = prime_decomposition(zk, p, 1)
    for (P, e) = lp
      @assert e == 1
      c = mr\P
      lP = prime_decomposition_nonindex(mp, P)
      for (PP, ee) = lP
        (e, f, g) = prime_decomposition_type(A, PP)
        cq = mQ(div(degree(PP), degree(P))*f*c)
        if iszero(cq)
          stable -= 1
          continue
        end
        Q, nQ = quo(Q, [cq], false)
        mQ = mQ*nQ
        stable = max_stable
      end
    end
    if stable <= 0 || order(Q) == 1
      break
    end
  end
  return ray_class_field(mr, GrpAbFinGenMap(mQ))
end

doc"""
    genus_field(A::ClassField, k::AnticNumberField) -> ClassField
> The maximal extension contained in $A$ that is the compositum of $K$
> with an abelian extension of $k$.
"""
function genus_field(A::ClassField, k::AnticNumberField)
  B = maximal_abelian_subfield(A, k)
  K = base_field(A)
  fl, mp = issubfield(k, K)
  @assert fl
  h = norm_group_map(A, B, x -> norm(mp, x))
  return ray_class_field(A.rayclassgroupmap, GrpAbFinGenMap(A.quotientmap * quo(domain(h), kernel(h)[1])[2]))
end
 
doc"""
    is_univariate(f::Generic.MPoly{nf_elem}) -> Bool, PolyElem{nf_elem}
> Tests if $f$ involves only one variable. If so, return a corresponding univariate polynomial.
"""
function is_univariate(f::Generic.MPoly{nf_elem})
  kx, x = PolynomialRing(base_ring(f))
  if ngens(parent(f)) == 1
    return true, sum(f.coeffs[i]*x^f.exps[1, i] for i=1:f.length)
  end
  if f.length == 0
    @assert iszero(f)
    return true, kx(0)
  end
  n = ngens(parent(f))
  i = 1
  while i <= n && iszero(f.exps[i, :])
    i += 1
  end
  j = n
  while j >= 1 && iszero(f.exps[j, :])
    j -= 1
  end
  if i != j
    return false, x
  end
  return true, sum(f.coeffs[j]*x^f.exps[i, j] for j=1:f.length)
end
#TODO: should be done in Nemo/AbstractAlgebra s.w.
#      needed by ^ (the generic power in Base using square and multiply)
Base.copy(f::Generic.MPoly) = deepcopy(f)
Base.copy(f::Generic.Poly) = deepcopy(f)


doc"""
    lorenz_module(k::AnticNumberField, n::Int) -> NfOrdIdl
> Finds an ideal $A$ s.th. for all positive units $e = 1 \bmod A$ we have that 
> $e$ is an $n$-th power. Uses Lorenz, number theory, 9.3.1.
> If {{{containing}}} is set, it has to be an integral ideal. The resulting ideal will be
> a multiple of this.
"""
function lorenz_module(k::AnticNumberField, n::Int; containing=false)
  lf = factor(n)
  return Base.reduce(lcm, [lorenz_module_pp(k, Int(p), l, containing = containing) for (p,l) = lf.fac])
end

#TODO: is this the right interface???
doc"""
    (::NfAbsOrdIdlSet)(m::Map, I::NfOrdIdl) -> NfOrdIdl
> Given an embedding $m:k\to K$ of number fields and an ideal $I$ in $k$,
> find the ideal above $I$ in $K$.
"""
function (I::NfAbsOrdIdlSet{Nemo.AnticNumberField,Nemo.nf_elem})(mp::Map, i::NfOrdIdl)
  assure_2_normal(i)
  return ideal(order(I), i.gen_one, order(I)(mp(i.gen_two.elem_in_nf)))
end

#TODO: write code (map?) to change polynomial rings other than evaluate

doc"""
    norm(m::T, a::nf_elem) where T <: Map{AnticNumberField, AnticNumberField} -> nf_elem
> Given an embedding $m:k\to K$ of number fields and an element in $K$, find the norm
> $N_{K/k}(a)$.
"""
function norm(m::T, a::nf_elem) where T <: Map{AnticNumberField, AnticNumberField}
  K = codomain(m)
  #= shamelessly from Trager:
           K  Then: K = Q(c) = k(c) = Q(b)(c)
           |        f(c) = 0 in Q[t]
      k    |        h(c) = 0 in k[t]. Trager: N(h) = f. eta in Q[t] s.th. m(b) = eta(c) 
      |    |        h = gcd(b - eta, f)
      Q    Q  so N_K/k(a) = res(h, a)
  =#    
  @assert K == parent(a)
  k = domain(m)
  kt, t = PolynomialRing(k, cached = false)
  Qt = parent(K.pol)
  h = gcd(gen(k) - evaluate(Qt(m(gen(k))), t), evaluate(K.pol, t))
  return resultant(h, mod(evaluate(Qt(a), t), h))
end

function norm(m::T, a::FacElem{nf_elem, AnticNumberField}) where T <: Map{AnticNumberField, AnticNumberField}
  K = codomain(m)
  @assert K == base_ring(a)
  k = domain(m)
  kt, t = PolynomialRing(k, cached = false)
  Qt = parent(K.pol)
  h = gcd(gen(k) - evaluate(Qt(m(gen(k))), t), evaluate(K.pol, t))
  d = Dict{nf_elem, fmpz}()
  for (e,v) = a.fac
    n = resultant(h, mod(evaluate(Qt(e), t), h))
    if haskey(d, n)
      d[n] += v
    else
      d[n] = v
    end
  end
  return FacElem(d)
end


doc"""
    norm(m::T, I::NfOrdIdl) where T <: Map{AnticNumberField, AnticNumberField} -> NfOrdIdl
> Given an embedding $m:k\to K$ of number fields and an integral ideal in $K$, find the norm
> $N_{K/k}(I)$.
"""
function norm(m::T, I::NfOrdIdl) where T <: Map{AnticNumberField, AnticNumberField}
  K = codomain(m)
  @assert K == nf(order(I))
  k = domain(m)
  zk = maximal_order(k)
  if I.is_principal == 1
    if isdefined(I, :princ_gen)
      return ideal(zk, zk(norm(m, (I.princ_gen).elem_in_nf)))
    elseif isdefined(J,:princ_gen_special)
      el = J.princ_gen_special[2] + J.princ_gen_special[3]
      return ideal(zk, zk(norm(m, el)))
    end
  end
  assure_2_normal(I)
  return ideal(zk, I.gen_one^div(degree(K), degree(k)), zk(norm(m, I.gen_two.elem_in_nf)))
end

function norm(m::T, I::NfOrdFracIdl) where T <: Map{AnticNumberField, AnticNumberField}
  return norm(m, numerator(I))//denominator(I)^div(degree(codomain(m)), degree(domain(m)))
end

#TODO: intersect_nonindex uses a worse algo in a more special case. Combine.
#  for prime ideals, the gcd's can be done in F_p/ F_q hence might be faster
doc"""
    minimum(m::T, I::NfOrdIdl) where T <: Map{AnticNumberField, AnticNumberField} -> NfOrdIdl
> Given an embedding $m:k\to K$ of number fields and an integral ideal in $K$, find the 
> intersection $I \cap \Z_k$.
"""
function minimum(m::T, I::NfOrdIdl) where T <: Map{AnticNumberField, AnticNumberField}
  K = codomain(m)
  @assert K == nf(order(I))
  k = domain(m)
  assure_2_normal(I)
  zk = maximal_order(k)

  @assert K == nf(order(I))
  k = domain(m)
  kt, t = PolynomialRing(k, cached = false)
  Qt = parent(K.pol)
  h = gcd(gen(k) - evaluate(Qt(m(gen(k))), t), evaluate(K.pol, t))
  g, ai, _ = gcdx(evaluate(Qt(I.gen_two.elem_in_nf), t), h)
  @assert g == 1
  #so ai * a = 1 in K/k
  c = content_ideal(ai, zk)
  n,d = integral_split(c)
  return ideal(zk, I.gen_one) + d
end

function minimum(m::T, I::NfOrdFracIdl) where T <: Map{AnticNumberField, AnticNumberField}
  return minimum(m, numerator(I))//denominator(I)
end

function Base.intersect(I::NfAbsOrdIdl, R::NfAbsOrd)
  if number_field(R) == number_field(order(I))
    return I
  end
  fl, m = issubfield(number_field(R), number_field(order(I)))
  @assert fl
  return minimum(m, I)
end
Base.intersect(R::NfAbsOrd, I::NfAbsOrdIdl) = intersect(I, R)

function Base.intersect(I::NfOrdFracIdl, R::NfAbsOrd)
  n, d = integral_split(I)
  return intersect(n, R)
end

Base.intersect(R::NfAbsOrd, I::NfOrdFracIdl) = intersect(I, R)

doc"""
    content_ideal(f::PolyElem{nf_elem}, R::NfAbsOrd) -> NfAbsOrdIdl
> The fractional $R$-ideal generated by the coefficients of $f$.    
"""
function content_ideal(f::PolyElem{nf_elem}, R::NfAbsOrd)
  @assert number_field(R) == base_ring(f)
  i = sum(coeff(f, i)*R for i=0:degree(f) if !iszero(coeff(f, i)))
  return i    
end

doc"""
    content_ideal(f::PolyElem{NfAbsOrdElem}) -> NfAbsOrdIdl
> The ideal generated by the coefficients of $f$.    
"""
function content_ideal(f::PolyElem{NfAbsOrdElem})
  R = base_ring(f)
  return sum(coeff(f, i)*R for i=0:degree(f) if !iszero(coeff(f, i)))
end

#TODO: check the math
# - I think in the p==2 l is too large in general
# - I probably only the p-part of c is needed
# - possibly even only the p-th cyclo field, although I really don't know
function lorenz_module_pp(k::AnticNumberField, p::Int, l::Int; containing=false)
  if p == 2
    l = max(l, lorenz_eta_level(k))
    l += 1
  end
  n = p^l
  C = cyclotomic_extension(k, n)
  Ka = C.Ka
  ZK = maximal_order(Ka)
  c, mc = class_group(Ka)
  lp = prime_decomposition(ZK, p)
  S = [P[1] for P = lp]
  s = [P[1] for P = prime_decomposition(maximal_order(k), p)]

  fc = false
  if containing != false
    @assert typeof(containing) == NfOrdIdl
    fc = factor(containing)
    s = union(s, collect(keys(fc)))
    fc = factor(parent(S[1])(C.mp[2], containing))
    S = union(S, collect(keys(fc)))
  end
  Q, mQ = quo(c, [mc\P for P = S])

  a, _ = find_gens(inv(mc)*mQ, PrimesSet(degree(k), -1), p*numerator(discriminant(Ka)))
  S = Set(intersect_nonindex(C.mp[2], P) for P = a)
  union!(S, s)

  d = Dict{typeof(first(S)), Int}()
  for P = S
    # need x = 1 mod P^l -> x = y^n in k_P
    # Newton: x^n-1 has derivative nx^(n-1) and need l > 2*val(n, P)
    v = 2*valuation(p, P) + 1
    if containing != false
      v = max(v, valuation(containing, P))
    end
    d[P] = v
  end
  return numerator(evaluate(FacElem(d), coprime = true))  
end

function lorenz_eta_level(k::AnticNumberField)
  # find max r s.th. eta_r in k, eta_(r+1) not in k
  # where eta_r = (zeta_(2^r) + 1/zeta_(2^r))
  r = 3
  x = PolynomialRing(FlintZZ, cached = false)[2]
  while true
    f = cos_minpoly(2^r, x)
    if hasroot(f, k)[1]
      return r-1
    end
    r += 1
  end
end
