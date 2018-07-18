add_verbose_scope(:QuadraticExt)
add_assert_scope(:QuadraticExt)

##############################################################################
#
#  Sieves for primes and squarefree numbers
#
##############################################################################

function squarefree_up_to(n::Int; coprime_to::Array{fmpz,1}=fmpz[])

  list= trues(n)
  for x in coprime_to
    t=x
    while t<= n
      @inbounds list[Int(t)]=false
      t+=x
    end
  end
  i=2
  b=Base.sqrt(n)
  while i<=b
    @inbounds if list[i]
      j=i^2
      @inbounds if !list[j]
        i+=1
        continue
      else 
        @inbounds list[j]=false
        t=2*j
        while t<= n
          @inbounds list[t]=false
          t+=j
        end
      end
    end
    i+=1
  end
  @inbounds return Int[i for i=1:n if list[i]]

end

function SqfSet(n::fmpz; coprime_to::Int=-1)
  return (i for i=-n:n if i!= -1 && i!=0 && issquarefree(i))
end

function primes_up_to(n::Int)
  
  list= trues(n)
  list[1]=false
  i=2
  s=4
  while s<=n
    list[s]=false
    s+=2
  end
  i=3
  b=sqrt(n)
  while i<=b
    if list[i]
      j=3*i
      s=2*i
      while j<= n
        list[j]=false
        j+=s
      end
    end
    i+=1
  end
  return Int[i for i=1:n if list[i]]
  
end

                                                                
                                                                               
###########################################################################
#
#  Some useful functions
#
###########################################################################

#This function gets a quotient of the ray class group and the action on
# the ray class group
# In output, we get the quotient group as a ZpnGModule

function _action_on_quo(mq::GrpAbFinGenMap, act::Array{GrpAbFinGenMap,1})
  
  q=mq.header.codomain
  S,mS=snf(q)
  n=Int(S.snf[end])
  R=ResidueField(FlintZZ, n, cached=false)
  W=MatrixSpace(R, ngens(S), ngens(S), false)
  quo_action=Array{nmod_mat,1}(length(act))
  for s=1:length(act)
    quo_action[s]=W(mS.map*act[i].map*mS.imap)
  end
  return ZpnGModule(S, quo_action)

end



function _min_wild(D::Dict{NfOrdIdl, Int})

  res=1
  primes_done=fmpz[]
  for (p,v) in D
    s=minimum(p)
    if s in primes_done
      continue
    end
    push!(primes_done, s)
    res*=Int(s)^v
  end  
  return res  

end

function totally_positive_generators(mr::MapRayClassGrp, a::Int, wild::Bool=false)

  if isdefined(mr, :tame_mult_grp)
    tmg=mr.tame_mult_grp
    for (p,v) in tmg
      mr.tame_mult_grp[p]=(make_positive(v[1],a),v[2],v[3])
      @hassert :RayFacElem 1 istotally_positive(mr.tame_mult_grp[p][1])
    end
  end
  if wild && isdefined(mr, :wild_mult_grp)
    wld=mr.wild_mult_grp
    for (p,v) in wld
      x=v[1]
      for i=1:length(x)
        x[i]=make_positive(x[i],a)
        @hassert :RayFacElem 1 iscoprime(ideal(parent(x[i]), x[i]), ideal(parent(x[i]), a))
      end
      mr.wild_mult_grp[p]=(x,v[2],v[3])
    end 
  end

end

function make_positive(x::NfOrdElem, a::Int)
 
  els=conjugates_arb(x)
  m=1
  for i=1:length(els)
    if isreal(els[i])
      y=BigFloat(midpoint(real(els[i]/a)))
      if y>0
        continue
      else
        m=max(m,1-ceil(Int,y))
      end
    end
  end
  @hassert :RayFacElem 1 iscoprime(ideal(parent(x),x+m*a), ideal(parent(x), a))
  @hassert :RayFacElem 1 istotally_positive(x+m*a)
  return x+m*a
  
end


function small_generating_set(Aut::Array{NfToNfMor, 1})
  K=Aut[1].header.domain
  a=gen(K)
  Identity = Aut[1]
  for i in 1:length(Aut)
    Au = Aut[i]
    if Au.prim_img == a
      Identity = Aut[i]
      break
    end
  end
  return  Hecke.small_generating_set(Aut, *, Identity)
end

function _are_there_subs(G::GrpAbFinGen,gtype::Array{Int,1})

  H=DiagonalGroup(gtype)
  H, _=snf(H)
  G1, _=snf(G)
  if length(G1.snf)<length(H.snf)
    return false
  end
  for i=0:length(H.snf)-1
    if !divisible(G1.snf[end-i],H.snf[end-i])
      return false
    end
  end
  return true
end

function issquarefree(n::Union{Int,fmpz})
  if iszero(n)
    throw(error("Argument must be non-zero"))
  end
  return isone(abs(n)) || maximum(values(factor(n).fac)) == 1
end

function absolute_automorphism_group(C::ClassField)
  L = number_field(C)
  K = base_field(C)
  autK = automorphisms(K)
  id = find_identity(autK, *)
  autK_gen = small_generating_set(autK, *, id)
  return absolute_automorphism_group(C, autK_gen)
end

function absolute_automorphism_group(C::ClassField, aut_gen_of_base_field::Array{NfToNfMor, 1})
  L = number_field(C)
  aut_L_rel = rel_auto(C)::Vector{NfRel_nsToNfRel_nsMor}
  rel_extend = NfRel_nsToNfRel_nsMor[ Hecke.extend_aut(C, a) for a in aut_gen_of_base_field ]
  rel_gens = vcat(aut_L_rel, rel_extend)
  return rel_gens::Array{NfRel_nsToNfRel_nsMor, 1}
end

function automorphism_groupQQ(C::ClassField)
  return rel_auto(C)
end

##########################################################################################################
#
#  Functions for conductors
#
##########################################################################################################

function tame_conductors_degree_2(O::NfOrd, bound::fmpz)
 
  K=nf(O)
  d=degree(O)
  b1=Int(root(bound,d))
  ram_primes=collect(keys(factor(O.disc).fac))
  sort!(ram_primes)
  filter!(x -> x!=2 ,ram_primes)
  list=squarefree_up_to(b1, coprime_to=vcat(ram_primes,2))

  extra_list=Tuple{Int, fmpz}[(1,fmpz(1))]
  for q in ram_primes
    tr=prime_decomposition_type(O,Int(q))
    e=tr[1][2]
    nq=fmpz(q)^(divexact(d,e))
    if nq> bound
      break
    end
    l=length(extra_list)
    for i=1:l
      n=extra_list[i][2]*nq
      if n> bound
        continue
      end
      push!(extra_list, (extra_list[i][1]*q, n))
    end
  end
  
  final_list=Tuple{Int,fmpz}[]
  l=length(list)
  for (el,norm) in extra_list
    for i=1:l
      if fmpz(list[i])^d*norm>bound
        continue
      end
      push!(final_list, (list[i]*el, fmpz(list[i])^d*norm))
    end
  end
  return final_list
  
end

function squarefree_for_conductors(O::NfOrd, n::Int, deg::Int ; coprime_to::Array{fmpz,1}=fmpz[])
  
  sqf= trues(n)
  primes= trues(n)
  
  #remove primes that can be wildly ramified or
  #that are ramified in the base field
  for x in coprime_to
    el=Int(x)
    t=el
    while t<= n
      @inbounds sqf[t]=false
      @inbounds primes[t]=false
      t+=el
    end
  end
  
  #sieving procedure
  
  if !(2 in coprime_to)
    dt=prime_decomposition_type(O,2)
    if gcd(2^dt[1][1]-1, deg)==1
      j=2
      while j<=n
        @inbounds sqf[j]=false
        @inbounds primes[j]=false
        j+=2
      end
    else 
      i=2
      s=4
      while s<=n
        @inbounds primes[s]=false
        s+=2
      end
      s=4
      while s<=n
        @inbounds sqf[s]=false
        s+=4
      end
    end
  end
  i=3
  b=Base.sqrt(n)
  while i<=b
    if primes[i]
      dt=prime_decomposition_type(O,i)
      if gcd(deg,i^dt[1][1]-1)==1
        @inbounds primes[i]=false
        @inbounds sqf[i]=false
        j=i
        while j<= n
         @inbounds primes[j]=false
         @inbounds sqf[j]=false
         j+=i
        end
      else 
        j=i
        while j<= n
          @inbounds primes[j]=false
          j+=i
        end
        j=i^2
        t=2*j
        while j<= n
          @inbounds sqf[j]=false
          j+=t
        end
      end
    end
    i+=2
  end
  while i<=n
    if primes[i]
      dt=prime_decomposition_type(O,i)
      if gcd(deg,i^dt[1][1]-1)==1
        @inbounds sqf[i]=false
        j=i
        while j<= n
         @inbounds sqf[j]=false
         j+=i
        end
      end
    end
    i+=2
  end
  
  if degree(O)==1
    i=2
    while i<=length(sqf)
      @inbounds sqf[i]=false
      i+=4
    end
    
  end
   
  return Int[i for i=1:length(sqf) if sqf[i]]
  
end

function conductors_tame(O::NfOrd, n::Int, bound::fmpz)

  if n==2
    return tame_conductors_degree_2(O,bound)
  end
  #
  #  First, conductors coprime to the ramified primes and to the 
  #  degree of the extension we are searching for.
  # 
  d=degree(O)
  K=nf(O)
  wild_ram=collect(keys(factor(fmpz(n)).fac))
  ram_primes=collect(keys(factor(O.disc).fac))
  filter!(x -> !divisible(fmpz(n),x), ram_primes)
  coprime_to=cat(1,ram_primes, wild_ram)
  sort!(ram_primes)
  m=minimum(wild_ram)
  k=divexact(n,m)
  b1=Int(root(fmpz(bound),Int(degree(O)*(m-1)*k))) 
  
  list= squarefree_for_conductors(O, b1, n, coprime_to=coprime_to)

  extra_list=Tuple{Int, Int}[(1,1)]
  for q in ram_primes
    tr=prime_decomposition_type(O,Int(q))
    f=tr[1][1]
    nq=Int(q)^f 
    if gcd(nq-1,n)==1
      continue
    end
    if nq> bound
      break
    end
    l=length(extra_list)
    for i=1:l
      no=extra_list[i][2]*nq
      if no> bound
        continue
      end
      push!(extra_list, (extra_list[i][1]*q, no))
    end
  end
  
  final_list=Tuple{Int,fmpz}[]
  l=length(list)
  for (el,norm) in extra_list
    for i=1:l
      if (list[i]^d)*norm>bound
        continue
      end
      push!(final_list, (list[i]*el, (list[i]^(Int((m-1)*k)*d))*norm))
    end
  end
  
  return final_list
end

function conductors(O::NfOrd, n::Int, bound::fmpz, tame::Bool=false)
  
  K=nf(O)
  d=degree(O)
  wild_ram=collect(keys(factor(fmpz(n)).fac))

  #
  # First, conductors for tamely ramified extensions
  #

  list=conductors_tame(O,n,bound)

  if tame
    return Tuple{Int, Dict{NfOrdIdl, Int}}[(x[1], Dict{NfOrdIdl, Int}()) for x in list]  
  end
  #
  # now, we have to multiply the obtained conductors by proper powers of wildly ramified ideals. 
  #
  wild_list=Tuple{Int, Dict{NfOrdIdl, Int}, fmpz}[(1, Dict{NfOrdIdl, Int}(),1)]
  for q in wild_ram
    lp=prime_decomposition(O,Int(q))
    fq=divexact(d,lp[1][2]*length(lp))
    l=length(wild_list)
    sq=fmpz(q)^(divexact(d,lp[1][2])) #norm of the squarefree part of the integer q
    #=
      we have to use the conductor discriminant formula to understand the maximal possible exponent of q.
      Let ap be the exponent of p in the relative discriminant, let m be the conductor and h_(m,C) the cardinality of the 
      quotient of ray class group by its subgroup C.
      Then 
          ap= v_p(m)h_(m,C)- sum_{i=1:v_p(m)} h_(m/p^i, C)
      Since m is the conductor, h_(m/p^i, C)<= h_(m,C)/q.
      Consequently, we get
        v_p(m)<= (q*ap)/(h_(m,C)*(q-1))
      To find ap, it is enough to compute a logarithm.
    =#
    nisc= gcd(q^(fq)-1,n)
    if nisc!=1
      nbound=n+n*lp[1][2]*valuation(n,q)-1
    else
      nbound=n+n*lp[1][2]*valuation(n,q)-div(fmpz(n), q^(valuation(n,q)))
    end
    obound=flog(bound,sq)
    bound_max_ap= min(nbound, obound)  #bound on ap
    bound_max_exp=div(q*bound_max_ap, n*(q-1)) #bound on the exponent in the conductor
    
    if nisc != 1
      fnisc=minimum(keys(factor(nisc).fac))
      nq=sq^((fnisc-1)*(divexact(n, fnisc)))
      for s=1:l
        nn=nq*wild_list[s][3]
        if nn>bound
          continue
        end
        push!(wild_list, (q*wild_list[s][1], wild_list[s][2], nn))
      end
    end
    for i=2:bound_max_exp
      d1=Dict{NfOrdIdl, Int}()
      for j=1:length(lp)
        d1[lp[j][1]]=i
      end
      nq= sq^(i*(q-1)*divexact(n,q))
      for s=1:l
        nn=nq*wild_list[s][3]
        if nn>bound
          continue
        end
        d2=merge(max, d1, wild_list[s][2]) 
        if nisc!=1
          push!(wild_list, (q*wild_list[s][1], d2, nn))
        else
          push!(wild_list, (wild_list[s][1], d2, nn))
        end
      end
    end
  end
  
  #the final list
  final_list=Tuple{Int, Dict{NfOrdIdl, Int}}[]
  for (el, nm) in list
    for (q,d,nm2) in wild_list
      if nm*nm2 > bound
        continue
      end
      push!(final_list, (el*q,d))
    end
  end

  return final_list
  
end


function conductors_tameQQ(O::NfOrd, n::Int, bound::fmpz)

  #
  #  First, conductors coprime to the ramified primes and to the 
  #  degree of the extension we are searching for.
  # 
  
  wild_ram=collect(keys(factor(fmpz(n)).fac))
  m=minimum(wild_ram)
  k=divexact(n,m)
  b1=Int(root(fmpz(bound),Int((m-1)*k))) 
  
  return squarefree_for_conductors(O, b1, n, coprime_to=wild_ram)

end

function conductorsQQ(O::NfOrd, n::Int, bound::fmpz, tame::Bool=false)
  
  K=nf(O)
  d=degree(O)
  wild_ram=collect(keys(factor(fmpz(n)).fac))

  #
  # First, conductors for tamely ramified extensions
  #

  list=conductors_tameQQ(O,n,bound)

  if tame
    return list  
  end
  #
  # now, we have to multiply the obtained conductors by proper powers of wildly ramified ideals. 
  #
  wild_list=Tuple{Int, Int, fmpz}[(1, 1,1)]
  for q in wild_ram
    l=length(wild_list)
    #=
      we have to use the conductor discriminant formula to understand the maximal possible exponent of q.
      Let ap be the exponent of p in the relative discriminant, let m be the conductor and h_(m,C) the cardinality of the 
      quotient of ray class group by its subgroup C.
      Then 
          ap= v_p(m)h_(m,C)- sum_{i=1:v_p(m)} h_(m/p^i, C)
      Since m is the conductor, h_(m/p^i, C)<= h_(m,C)/q.
      Consequently, we get
        v_p(m)<= (q*ap)/(h_(m,C)*(q-1))
      To find ap, it is enough to compute a logarithm.
    =#
    nisc= gcd(q-1,n)
    if nisc!=1
      nbound=n+n*valuation(n,q)-1
    else
      nbound=n+n*valuation(n,q)-div(fmpz(n), q^(valuation(n,q)))
    end
    obound=flog(bound,q)
    nnbound=valuation_bound_discriminant(n,q)
    bound_max_ap= min(nbound, obound, nnbound)  #bound on ap
    bound_max_exp=div(q*bound_max_ap, n*(q-1)) #bound on the exponent in the conductor
    
    if nisc != 1
      fnisc=minimum(keys(factor(nisc).fac))
      nq=fmpz(q)^((fnisc-1)*(divexact(n, fnisc)))
      for s=1:l
        nn=nq*wild_list[s][3]
        if nn>bound
          continue
        end
        push!(wild_list, (q*wild_list[s][1], wild_list[s][2], nn))
      end
    end
    t=(q-1)*divexact(n,q)
    for i=2:bound_max_exp
      nq= q^(i*t)
      for s=1:l
        nn=nq*wild_list[s][3]
        if nn>bound
          continue
        end
        push!(wild_list, (wild_list[s][1], wild_list[s][2]*q^i, nn))
      end
    end
  end
  
  #the final list
  final_list=Int[]
  exps=Int((minimum(wild_ram)-1)*divexact(n,minimum(wild_ram)))
  for el in list
    for (q,d,nm2) in wild_list
      if (fmpz(el)^exps)*nm2 > bound
        continue
      end
      push!(final_list, (el*q*d))
    end
  end

  return final_list
  
end


###############################################################################
#
#  Abelian extensions
#
###############################################################################

function abelian_extensions(O::Union{FlintIntegerRing, FlintRationalField},
                            gtype::Vector{Int}, discriminant_bound::fmpz;
                            real::Bool = false,
                            tame::Bool = false)

  Qx, x = PolynomialRing(FlintQQ, "x")
  K, _ = NumberField(x - 1, "a")
  OK = maximal_order(K)
  l = abelian_extensions(OK, gtype, discriminant_bound,
                         real = real,
                         tame = tame)


  newlist = Vector{NfAbsNS}(length(l))
  for j in 1:length(l)
    newlist[j], _ = number_field([Qx([coeff(coeff(f, i), 0) for i in 0:length(f)]) for f in l[j].abs_pol])
  end
  return newlist
end

function abelian_extensions(O::NfOrd, gtype::Array{Int,1}, absolute_discriminant_bound::fmpz; real::Bool=false, tame::Bool=false, with_autos::Type{Val{T}} = Val{false}) where T 
  
  K=nf(O) 
  @assert degree(K)==1
  n=prod(gtype)
    
  expo=lcm(gtype)
    
  #Getting conductors
  l_conductors=conductorsQQ(O,n,absolute_discriminant_bound, tame)
  @vprint :QuadraticExt 1 "Number of conductors: $(length(l_conductors)) \n"
  if with_autos==Val{true}
    fields = Tuple{NfRel_ns, Array{NfRel_nsToNfRel_nsMor,1}}[]
  else
    fields = NfRel_ns[]
  end

  #Now, the big loop
  for (i, k) in enumerate(l_conductors)
    @vprint :QuadraticExt 1 "Conductor: $k \n"
    @vprint :QuadraticExt 1 "Left: $(length(l_conductors) - i)\n"
    r,mr=Hecke.ray_class_groupQQ(O,k,!real,expo)
    if !Hecke._are_there_subs(r,gtype)
      continue
    end
    ls=subgroups(r,quotype=gtype, fun= (x, y) -> quo(x, y, false)[2])
    for s in ls
      C=ray_class_field(mr, s)
      if Hecke._is_conductor_minQQ(C,n) && Hecke.discriminant_conductorQQ(O,C,k,absolute_discriminant_bound,n)
        @vprint :QuadraticExt 1 "New Field \n"
        L=number_field(C)
        if with_autos==Val{true}
          push!(fields,(L, automorphism_groupQQ(C)))
        else
          push!(fields, L)
        end
      end
    end
  end

  return fields

end


function abelian_normal_extensions(O::NfOrd, gtype::Array{Int,1}, absolute_discriminant_bound::fmpz; ramified_at_infplc::Bool=true, tame::Bool=false, absolute_galois_group::Symbol = :all,  with_autos::Type{Val{T}} = Val{false}, autos::Array{NfToNfMor,1}=NfToNfMor[]) where T 

  d=degree(O)
  if d==1
    return abelian_extensions(O, gtype, absolute_discriminant_bound, real=!ramified_at_infplc, tame=tame, with_autos=with_autos) 
  end

  K=nf(O) 
  n=prod(gtype)
  inf_plc=InfPlc[]
  
  if with_autos==Val{true}
    fields=Tuple{NfRel_ns,Vector{NfRel_nsToNfRel_nsMor{nf_elem}}}[]
  else
    fields=NfRel_ns[]
  end
  
  bound = abs(div(absolute_discriminant_bound,discriminant(O)^n))
  if bound==0
    return fields
  end

  if mod(n,2)==0 && ramified_at_infplc
    inf_plc=real_places(K)
  end

  expo=lcm(gtype)
  C,mC=class_group(O)
  cgrp= gcd(n,order(C))!=1
  if cgrp
    S = prime_ideals_up_to(O, max(100,12*clog(abs(discriminant(O)),10)^2))
  end
  allow_cache!(mC)
  
  #
  # Getting a small set of generators
  # for the automorphisms group
  #
  if isempty(autos)
    Aut=Hecke.automorphisms(K)
    @assert length(Aut)==degree(O) #The field is normal over Q
    gens = Hecke.small_generating_set(Aut)
  else
    gens = autos
  end

  #Getting conductors
  l_conductors=conductors(O,n,bound, tame)
  @vprint :QuadraticExt 1 "Number of conductors: $(length(l_conductors)) \n"
  

  #Now, the big loop
  for (i, k) in enumerate(l_conductors)
    @vprint :QuadraticExt 1 "Conductor: $k \n"
    @vprint :QuadraticExt 1 "Left: $(length(l_conductors) - i)\n"
    r,mr=ray_class_group_quo(O,expo,k[1], k[2],inf_plc)
    if !_are_there_subs(r,gtype)
      continue
    end
    if cgrp
        mr.prime_ideal_cache = S
    end
    act=_act_on_ray_class(mr,gens)
    ls=stable_subgroups(r,gtype,act, op=(x, y) -> quo(x, y, false)[2])
    a=_min_wild(k[2])*k[1]
    totally_positive_generators(mr,a)
    for s in ls
      @hassert :QuadraticExt 1 order(codomain(s))==n
      C=ray_class_field(mr, s)
      if Hecke._is_conductor_min_normal(C,a) && Hecke.discriminant_conductor(O,C,a,mr,bound,n)
        @vprint :QuadraticExt 1 "New Field \n"
        L = number_field(C)
        if absolute_galois_group != :all
          autabs = absolute_automorphism_group(C, gens)
          G = generic_group(autabs, *)
          if absolute_galois_group == :_16T7
            if isisomorphic_to_16T7(G)
              @vprint :QuadraticExt 1 "I found a field with Galois group 16T7 (C_2 x Q_8)\n"
              @vtime :QuadraticExt 1 push!(fields, L)
            end
          elseif absolute_galois_group == :_8T5
            if isisomorphic_to_8T5(G)
              @vprint :QuadraticExt 1 "I found a field with Galois group 8T5 (Q_8)\n"
              @vtime :QuadraticExt 1 push!(fields, L)
            end
          else
            error("Group not supported (yet)")
          end
        else
          if with_autos==Val{true}
            push!(fields, (L,absolute_automorphism_group(C,gens))) 
          else
            push!(fields, L)
          end
        end
      end
    end
  end

  return fields

end

###############################################################################
#
#  Quadratic Extensions of Q
#
###############################################################################

function quadratic_extensions(bound::Int; tame::Bool=false, real::Bool=false, complex::Bool=false, u::UnitRange{Int}=-1:0)

  @assert !(real && complex)
  Qx,x=PolynomialRing(FlintQQ, "x")
  sqf=squarefree_up_to(bound);
  if real
    deleteat!(sqf,1)
  elseif complex
    sqf=Int[-i for i in sqf]
  else
    sqf= vcat(sqf[2:end], Int[-i for i in sqf])
  end
  if tame
    filter!( x -> mod(x,4)==1, sqf)
    return ( number_field(x^2-x+divexact(1-i,4), cached=false)[1] for i in sqf)
  end
  final_list=Int[]
  for i=1:length(sqf)
    if abs(sqf[i]*4)< bound
      @views push!(final_list,sqf[i])
      continue
    end
    if mod(sqf[i],4)==1
      @views push!(final_list,sqf[i])
    end
  end
  if u==-1:0
    return ( mod(i,4)!=1 ? number_field(x^2-i, cached=false)[1] : number_field(x^2-x+divexact(1-i,4), cached=false)[1] for i in final_list)
  else
    return ( mod(final_list[i],4)!=1 ? number_field(x^2-final_list[i], cached=false)[1] : number_field(x^2-x+divexact(1-final_list[i],4), cached=false)[1] for i in u)
  end

end

function quadratic_extensions(bound::Int; tame::Bool=false, real::Bool=false, complex::Bool=false, with_autos::Type{Val{T}}=Val{false}) where T

  @assert !(real && complex)
  Qx,x=PolynomialRing(FlintQQ, "x")
  sqf=squarefree_up_to(bound)
  if real
    deleteat!(sqf,1)
  elseif complex
    sqf=Int[-i for i in sqf]
  else
    sqf= vcat(sqf[2:end], Int[-i for i in sqf])
  end
  if tame
    filter!( x -> mod(x,4)==1, sqf)
    return ( number_field(x^2-x+divexact(1-i,4), cached=false)[1] for i in sqf)
  end
  final_list=Int[]
  for i=1:length(sqf)
    if abs(sqf[i]*4)< bound
      @views push!(final_list,sqf[i])
      continue
    end
    if mod(sqf[i],4)==1
      @views push!(final_list,sqf[i])
    end
  end
  return ( mod(i,4)!=1 ? number_field(x^2-i, cached=false)[1] : number_field(x^2-x+divexact(1-i,4), cached=false)[1] for i in final_list)

end

function _quad_exts_as_ab_exts(bound::Int)

  Qy,y=PolynomialRing(FlintQQ, "y")
  K,a=NumberField(y-1)
  Kx,x=PolynomialRing(K,"x")
  sqf=squarefree_up_to(bound)
  sqf= vcat(sqf[2:end], Int[-i for i in sqf])
  final_list=Int[]
  for i=1:length(sqf)
    if abs(sqf[i]*4)< bound
      @views push!(final_list,sqf[i])
      continue
    end
    if mod(sqf[i],4)==1
      @views push!(final_list,sqf[i])
    end
  end
  return ( _quad_ext_with_auto(Kx,i) for i in final_list)

end

function _quad_ext_with_auto(Kx,a::Int)
  x=gen(Kx)
  if a % 4 == 1
    L, lg = number_field([x^2-x+divexact(1-a,4)])
    b=lg[1]
    mL=NfRel_nsToNfRel_nsMor(L,L, [1-b])::NfRel_nsToNfRel_nsMor{nf_elem}
  else
    L, lg = number_field([x^2-a])
    b = lg[1]
    mL=NfRel_nsToNfRel_nsMor(L,L, [-b])::NfRel_nsToNfRel_nsMor{nf_elem}
  end
  return (L, NfRel_nsToNfRel_nsMor{nf_elem}[mL])::Tuple{NfRel_ns{nf_elem}, Array{NfRel_nsToNfRel_nsMor{nf_elem},1}}

end

###############################################################################
#
#  C2 x C2 extensions of Q
#
###############################################################################

function C22_extensions(bound::Int)
  
  
  Qx,x=PolynomialRing(FlintZZ, "x")
  K,_=NumberField(x-1)
  Kx,x=PolynomialRing(K,"x", cached=false)
  b1=ceil(Int,Base.sqrt(bound))
  n=2*b1+1
  pairs=_find_pairs(bound)
  poszero=b1+1
  return (_ext(Kx,x,i-poszero,j-poszero) for i=1:n for j=i+1:n if pairs[i,j])
  
end

function _C22_exts_abexts(bound::Int)
  Qx,x=PolynomialRing(FlintZZ, "x")
  K,_=NumberField(x-1)
  Kx,x=PolynomialRing(K,"x", cached=false)
  pairs=_find_pairs(bound)
  b1=ceil(Int,Base.sqrt(bound))
  n=2*b1+1
  poszero=b1+1
  return (_ext_with_autos(Kx,x,i-poszero,j-poszero) for i=1:n for j=i+1:n if pairs[i,j])

end

function _ext_with_autos(Ox,x,i,j)
 
  y1=mod(i,4)
  pol1=Ox(1)
  if y1!=1
    pol1=x^2-i
  else
    pol1=x^2-x+divexact(1-i,4)
  end
  y2=mod(j,4)
  pol2=Ox(1)
  if y2!=1
    pol2=x^2-j
  else
    pol2=x^2-x+divexact(1-j,4)
  end
  L, lg= number_field([pol1,pol2])
  if y1!=1
    a1=-lg[1]
  else
    a1=1-lg[1]
  end
  if y2!=1
    a2=-lg[2]
  else
    a2=1-lg[2]
  end
  mL1=NfRel_nsToNfRel_nsMor(L,L, [a1,lg[2]])
  mL2=NfRel_nsToNfRel_nsMor(L,L, [lg[1],a2])
  return (L, [mL1,mL2])

end

function _find_pairs(bound::Int)
  
  b1=ceil(Int,Base.sqrt(bound))
  n=2*b1+1
  pairs=trues(n,n)
  poszero=b1+1
  
  for i=1:n
    pairs[i,poszero]=false
    pairs[i,b1+2]=false
    pairs[poszero,i]=false
    pairs[b1+2,i]=false
  end
  
  #sieve for squarefree  
  list= trues(b1)
  i=2
  b=Base.sqrt(b1)
  while i<=b
    if list[i]
      j=i^2
      if !list[j]
        i+=1
        continue
      else 
        list[j]=false
        t=2*j
        while t <= b1
          list[t]=false
          t+=j
        end
      end
    end
    i+=1
  end
  #now translate it into the matrix
  for i=1:b1
    if !list[i]
      pairs[poszero+i,1:n]=false
      pairs[1:n,poszero+i]=false
      pairs[poszero-i,1:n]=false
      pairs[1:n,poszero-i]=false
    end
  end
  #check
#=  
  for i=1:n
    for j=1:n
      if pairs[i,j]
        @assert issquarefree(i-poszero)
        @assert issquarefree(j-poszero)
      end
    end
  end
=#
  #removing diagonal
  for i=1:n
    pairs[i,i]=false
  end
  
  #counting extensions  
  for i=1:n
    for j=i+1:n
      if pairs[i,j]
        pairs[j,i]=false
        third=divexact((i-poszero)*(j-poszero), gcd(i-poszero, j-poszero)^2)
        if abs(third)>b1
          pairs[i,j]=false
        else
          y=third+poszero
          pairs[y,i]=false
          pairs[y,j]=false
          pairs[i,y]=false
          pairs[j,y]=false
          first=i-poszero
          second=j-poszero
          d1=_discn(first)
          d2=_discn(second)
          g1=d1*d2
          if abs(g1)<b1
            continue
          else 
            d3=_discn(third)
            g2=d1*d3
            if abs(g2)<b1
              continue
            else
              g3=d2*d3
              if abs(g3)<b1
                continue
              else
                g=gcd(g1,g2,g3)
                if abs(g)<b1
                  continue
                elseif check_disc(first, second, third, bound)
                  pairs[i,j]=false
                end
              end
            end
          end
        end
      end
    end
  end
  return pairs
  
end

function check_disc(a::Int,b::Int,c::Int,bound::Int)
  
  if mod(a,4)!=2 && mod(b,4)!=2
    return true
  end 
  if mod(a,4)==1 || mod(b,4)==1 || mod(c,4)==1
    return true
  end
  if 64*a*b*c>=bound
    return true
  else
    return false
  end
  
end

#given integers i,j, this function returns the extension Q(sqrt(i))Q(sqrt(j))
function _ext(Ox,x,i,j)
 
  y=mod(i,4)
  pol1=Ox(1)
  if y!=1
    pol1=x^2-i
  else
    pol1=x^2-x+divexact(1-i,4)
  end
  y=mod(j,4)
  pol2=Ox(1)
  if y!=1
    pol2=x^2-j
  else
    pol2=x^2-x+divexact(1-j,4)
  end
  return number_field([pol1,pol2])

end

# Given a squarefree integer n, this function computes the absolute value
# of the discriminant of the extension Q(sqrt(n))
function _discn(n::Int)
  
  x=mod(n,4)
  if x!=1
    return 4*n
  else
    return n
  end
  
end

function C22_extensions_tame_real(bound::Int)
  
  
  Qx,x=PolynomialRing(FlintZZ, "x")
  K,_=NumberField(x-1)
  Kx,x=PolynomialRing(K,"x", cached=false)

  b1=floor(Int,Base.sqrt(bound))
  n=b1
  pairs=trues(b1,b1)
  
  #sieve for squarefree number congruent to 1 mod 4
  i=2
  k=4
  while k<=b1
    pairs[1:i,i]=false
    pairs[1:k,k]=false
    pairs[i,i+1:n]=false
    pairs[k,k+1:n]=false
    i+=4
    k+=4
  end
  i=3
  b=Base.sqrt(b1)
  while i<=b
    if pairs[1,i]
      j=i^2
      if !pairs[1,j]
        i+=2
        continue
      else 
        pairs[1:j,j]=false
        pairs[j,1:j]=false
        t=2*j
        while t <= b1
          pairs[t,t:n]=false
          pairs[1:t,t]=false
          t+=j
        end
      end
    end
    i+=2
  end
  k=3
  while k<=b1
    pairs[1:k,k]=false
    pairs[k,k:n]=false
    k+=4
  end
  pairs[1,1:n]=false
  
  #counting extensions  
  for i=5:b1
    for j=i+1:b1
      if pairs[i,j]
        k=divexact(i*j, gcd(i, j)^2)
        if k>b1
          pairs[i,j]=false
        else
          if k>i
            pairs[i,k]=false
          else
            pairs[k,i]=false
          end
          if k>j
            pairs[j,k]=false
          else
            pairs[k,j]=false
          end
          if i*j*k<bound
            continue
          else 
            pairs[i,j]=false
          end
        end
      end
    end
  end
  
  return (_ext(Kx,x,i,j) for i=5:b1 for j=i+1:b1 if pairs[i,j])
  
end


###############################################################################
#
#  Dycyclic Dic3
#
###############################################################################

#K is a C4 field
function Dic3_extensions(absolute_bound::fmpz, K::AnticNumberField)

  O=maximal_order(K)
  D=abs(discriminant(O))
  
  C,mC=class_group(O)
  allow_cache!(mC)
  cgrp=false
  if gcd(C.snf[end],3)!=1
    cgrp=true
    S = prime_ideals_up_to(O, max(100,100*clog(D,10)^2))
  end
  gens=Hecke.automorphisms(K)
  gens=small_generating_set(gens)
  
  #Getting conductors
  bound = div(absolute_bound, D^3)
  l_conductors=conductors(O,3, bound)
  @vprint :QuadraticExt "Number of conductors: $(length(l_conductors)) \n"

  res = []
  
  #Now, the big loop
  for k in l_conductors
    r,mr=ray_class_group_quo(O,3,k[1], k[2])
    if cgrp
      mr.prime_ideal_cache = S
    end
    act=_act_on_ray_class(mr,gens)
    ls=stable_subgroups(r,[3],act, op=(x, y) -> quo(x, y, false)[2])
    a=_min_wild(k[2])*k[1]
    totally_positive_generators(mr,a)
    for s in ls
      if _trivial_action(s,act,3)
        continue
      end
      C=ray_class_field(mr, s)
      if Hecke._is_conductor_min_normal(C,a) && Hecke.discriminant_conductor(O,C,a,mr,bound,3)
        @vprint :QuadraticExt 1 "New Field"
        L=number_field(C)
        SS=Hecke.simple_extension(L)[1]
        F=absolute_field(SS)[1]
        push!(res, (F.pol, prod([ fmpz(p)^e for (p, e) in C.absolute_discriminant])))
      end
    end
  end
  return res
end

###############################################################################
#
#  Dihedral group D5 with equation of degree 5
#
###############################################################################


function conductorsD5(O::NfOrd, bound_non_normal::fmpz)

  D=abs(discriminant(O))
  ram_primes=collect(keys(factor(O.disc).fac))
  coprime_to=cat(1,ram_primes, fmpz(5))
  sort!(ram_primes)
  b=root(bound_non_normal,2)
  b1=root(div(b,D),2)
  #
  # First, conductors for tamely ramified extensions
  #
  
  sqf_list= squarefree_for_conductors(O, Int(b1), 5, coprime_to=coprime_to)
  l=length(sqf_list)
  #
  # now, we have to multiply the obtained conductors by proper powers of wildly ramified ideals. 
  #
  lp=prime_decomposition(O,5)
  final_list=Tuple{Int, Dict{NfOrdIdl, Int}}[]
  if 5 in ram_primes
    bound_max_exp=flog(b1,5)
    final_list=[(x, Dict{NfOrdIdl, Int}()) for x in sqf_list]
    for i=2:bound_max_exp
      isodd(i) && continue
      d1=Dict{NfOrdIdl, Int}()
      for j=1:length(lp)
        d1[lp[j][1]]=i
      end
      min_id=div(i,2)
      for s=1:l 
        if sqf_list[s]*5^min_id<b1
          push!(final_list,(sqf_list[s],d1))
        end
      end
    end
  else
    bound_max_exp=flog(b1,5)
    final_list=[(x, Dict{NfOrdIdl, Int}()) for x in sqf_list]
    for i=2:bound_max_exp
      d1=Dict{NfOrdIdl, Int}()
      for j=1:length(lp)
        d1[lp[j][1]]=i
      end
      for s=1:l 
        if sqf_list[s]*5^i<b1
          push!(final_list,(sqf_list[s],d1))
        end
      end
    end
  end
  return final_list

end

#The input are the absolute bound for the non-normal extension of degree 5 and the list of the quadratic fields
function D5_extensions(absolute_bound::fmpz, quad_fields)
  
  len=length(quad_fields)
  z = []
  for K in quad_fields
    len-=1
    
     @vprint :QuadraticExt 1 "Field: $K\n"   
     @vprint :QuadraticExt 1 "Remaining Fields: $(len)\n"
    append!(z, single_D5_extensions(absolute_bound, K))
  end
  return z
end

function D5_extensions(absolute_bound::fmpz, quad_fields, f::IOStream)
  
  len=length(quad_fields)
  for K in quad_fields
    len-=1
    
    @vprint :QuadraticExt 1  "Field: $K\n"
    @vprint :QuadraticExt 1 "Remaining Fields: $(len)\n"
    for g in single_D5_extensions(absolute_bound, K)
      Base.write(f, "($g)\n" )
    end
  end
  return len
end


function single_D5_extensions(absolute_bound::fmpz, K::AnticNumberField)

  O=maximal_order(K)
  D=abs(discriminant(O))
  
  C,mC=class_group(O)
  allow_cache!(mC)
  cgrp=false
  if gcd(C.snf[end],5)!=1
    cgrp=true
    S = prime_ideals_up_to(O, max(100,100*clog(D,10)^2))
  end
  gens=Hecke.automorphisms(K)
  a=gen(K)
  if gens[1](a)==a
    deleteat!(gens,1)
  else
    deleteat!(gens,2)
  end

  z = []
  
  #Getting conductors
  l_conductors=conductorsD5(O,absolute_bound)
#  @vprint :QuadraticExt "Number of conductors: $(length(l_conductors)) \n"
  
  #Now, the big loop
  for k in l_conductors
    r,mr=ray_class_group_quo(O,5,k[1], k[2])
    if cgrp
      mr.prime_ideal_cache = S
    end
    act=_act_on_ray_class(mr,gens)
    ls=stable_subgroups(r,[5],act, op=(x, y) -> quo(x, y, false)[2])
    a=_min_wild(k[2])*k[1]
    for s in ls
      if _trivial_action(s,act,5)
        continue
      end
      C=ray_class_field(mr, s)
      if Hecke._is_conductor_min_normal(C,a)
        @vprint :QuadraticExt 1 "New Field"
        L=number_field(C)
        auto=Hecke.extend_aut(C, gens[1])
        pol=_quintic_ext(auto)
        push!(z, (pol,D^2*minimum(mr.modulus_fin)^4))
      end
    end
  end
  return z
end

function _quintic_ext(auto)#::NfRel_nsToNfRel_nsMor)

  #first, find a generator of the simple extension
  L=domain(auto)
  S,mS=simple_extension(L)
  x=mS(gen(S))
  
  #Find primitive element 
  pr_el=x+auto(x)
  
  #Take minimal polynomial; I need to embed the element in the absolute extension
  pol=absolute_minpoly(pr_el)
  if degree(pol)==15
    return pol
  else
    pr_el=x*(auto(x))
    return absolute_minpoly(pr_el)
  end
  
end


###############################################################################
#
#  Dihedral group Dn with n odd
#
###############################################################################

function conductorsDn(O::NfOrd, n::Int, bound::fmpz, tame::Bool=false)
  
  K=nf(O)
  d=degree(O)
  wild_ram=collect(keys(factor(fmpz(n)).fac))
  ram_primes=collect(keys(factor(O.disc).fac))
  coprime_to=cat(1,ram_primes, wild_ram)
  sort!(ram_primes)
  m=minimum(wild_ram)
  k=divexact(n,m)
  b1=Int(root(fmpz(bound),Int(2*(minimum(wild_ram)-1)*k))) 

  #
  # First, conductors for tamely ramified extensions
  #

  list= squarefree_for_conductors(O, b1, n, coprime_to=coprime_to)
  
  if tame
    error("Not yet implemented") 
  end
  
  #
  # now, we have to multiply the obtained conductors by proper powers of wildly ramified ideals. 
  #
  wild_list=Tuple{Int, Dict{NfOrdIdl, Int}, Int}[(1, Dict{NfOrdIdl, Int}(),1)]
  for q in wild_ram
    lp=prime_decomposition(O,q)
    l=length(wild_list)
    #=
      we have to use the conductor discriminant formula to understand the maximal possible exponent of q.
      Let ap be the exponent of p in the relative discriminant, let m be the conductor and h_(m,C) the cardinality of the 
      quotient of ray class group by its subgroup C.
      Then 
          ap= v_p(m)h_(m,C)- sum_{i=1:v_p(m)} h_(m/p^i, C)
      Since m is the conductor, h_(m/p^i, C)<= h_(m,C)/q.
      Consequently, we get
        v_p(m)<= (q*ap)/(h_(m,C)*(q-1))
      To find ap, it is enough to compute a logarithm.
    =#
    sq=fmpz(q)^(divexact(2,lp[1][2]))
    fq=divexact(2,length(lp)*lp[1][2])
    bound_max_ap=clog(bound,sq) #bound on ap
    bound_max_exp=divexact(q*bound_max_ap, n*(q-1)) #bound on the exponent in the conductor
    nisc= gcd(q^fq-1,n)!=1
    if !(q in ram_primes) && nisc
      for s=1:l
        nn=sq*wild_list[s][3]
        if nn>bound
          continue
        end
        push!(wild_list, (q*wild_list[s][1], wild_list[s][2], nn))
      end
    end
    for i=2:bound_max_exp
      if q in ram_primes && i % 2 ==1
        continue
      end
      d1=Dict{NfOrdIdl, Int}()
      for j=1:length(lp)
        d1[lp[j][1]]=i
      end
      nq= sq^i
      for s=1:l
        nn=nq*wild_list[s][3]
        if nn>bound
          continue
        end
        d2=merge(max, d1, wild_list[s][2]) 
        if nisc
          push!(wild_list, (q*wild_list[s][1], d2, nn))
        else 
          push!(wild_list, (wild_list[s][1], d2, nn))
        end
      end
    end
  end
  
  #the final list
  final_list=Set(Tuple{Int, Dict{NfOrdIdl, Int}}[])
  for el in list
    for (q,d1,nm2) in wild_list
      if el^2*nm2 > bound
        continue
      end
      push!(final_list, (el*q,d1))
    end
  end

  return final_list
  
end

function Dn_extensions(n::Int, absolute_bound::fmpz; totally_real::Bool=false, complex::Bool=false, tame::Bool=false)

  if mod(n,2)==0
    error("Not yet implemented")
  end
  @assert !(totally_real && complex)
  
  bound_quadratic= Int(root(absolute_bound, n))
  list_quad=quadratic_extensions(bound_quadratic, tame=tame, real=totally_real, complex=complex)
  return Dn_extensions(n,absolute_bound, list_quad, tame=tame)
  
end

function Dn_extensions(n::Int, absolute_bound::fmpz, list_quad ; tame::Bool=false)
  @assert absolute_bound>0
  len=length(list_quad)
  fieldslist=Tuple{NfRel_ns,  Array{NfRel_nsToNfRel_nsMor{nf_elem},1},fmpz, Array{fmpz,1}}[]
  
  for K in list_quad
    len-=1
    
    @vprint :QuadraticExt 1 "Field: $K\n"
    @vprint :QuadraticExt 1 "Fields left: $len\n"
    O=maximal_order(K)
    D=abs(discriminant(O))
    if D^n>absolute_bound
      continue
    end
    bound = div(absolute_bound, abs(D)^n)
   
    C,mC=class_group(O)
    allow_cache!(mC)
    cgrp=false
    if gcd(C.snf[end],n)!=1
      cgrp=true
      S = prime_ideals_up_to(O, max(30,12*clog(D,10)^2))
    end

    gens=Hecke.automorphisms(K)
    a=gen(K)
    if gens[1](a)==a
      deleteat!(gens,1)
    else
      deleteat!(gens,2)
    end
    
    #Getting conductors
    l_conductors=conductorsDn(O,n,bound, tame)

    @vprint :QuadraticExt "Number of conductors: $(length(l_conductors)) \n"
  
    #Now, the big loop
    for k in l_conductors
      r,mr=ray_class_group_quo(O,n,k[1], k[2])
      if !_are_there_subs(r,[n])
        continue
      end
      if cgrp
        mr.prime_ideal_cache = S
      end
      act=_act_on_ray_class(mr,gens)
      ls=stable_subgroups(r,[n],act, op=(x, y) -> quo(x, y, false)[2])
      a=_min_wild(k[2])*k[1]
      for s in ls
        if _trivial_action(s,act,n)
          continue
        end
        C=ray_class_field(mr, s)
        if Hecke._is_conductor_min_normal(C,a) && Hecke.discriminant_conductor(O,C,a,mr,bound,n)
          @vprint :QuadraticExt 1 "\n New Field!\n"
          L=number_field(C)
          ram_primes=Set(collect(keys(factor(a).fac)))
          for p in keys(factor(O.disc).fac)
            push!(ram_primes, p)
          end
          aut=absolute_automorphism_group(C,gens)
          push!(fieldslist,(L,aut, evaluate(FacElem(C.absolute_discriminant)), collect(ram_primes)))
        end
      end
    end
    
  end
  
  return fieldslist

end

function _trivial_action(s::GrpAbFinGenMap, act::Array{GrpAbFinGenMap,1}, n::Int)

  @assert length(act)==1
  S=codomain(s)
  T,mT=snf(S)
  @assert T.snf[1]==n
  @assert ngens(T)==1
  new_el=mT\(s(act[1](s\mT(T[1]))))
  if new_el==(n-1)*T[1]
    return false
  else
    return true
  end
  
end

###############################################################################
#
#  C3 x D5 extensions
#
###############################################################################

function C3xD5_extensions(non_normal_bound::fmpz)

  
  bound_quadratic= Int(root(non_normal_bound, 6))
  list_quad=quadratic_extensions(bound_quadratic, complex=true)
  fieldslist=Tuple{AnticNumberField, Array{fmpz,1}}[]
  
  for K in list_quad
    
    @vprint :QuadraticExt 1 "Field: $K\n"
    O=maximal_order(K)
    D=abs(discriminant(O))

    bound5=root(non_normal_bound,3)
    bound = non_normal_bound^2
   
    C,mC=class_group(O)
    allow_cache!(mC)
    cgrp=false
    if gcd(C.snf[end],15)!=1
      cgrp=true
      S = prime_ideals_up_to(O, max(100,12*clog(D,10)^2))
    end
    gens=Hecke.automorphisms(K)
    a=gen(K)
    if gens[1](a)==a
      deleteat!(gens,1)
    else
      deleteat!(gens,2)
    end
    
    #Getting conductors
    l_conductors=conductors(O,15,bound)
    @vprint :QuadraticExt "Number of conductors: $(length(l_conductors)) \n"
  
    #Now, the big loop
    for (i, k) in enumerate(l_conductors)
      r,mr=ray_class_group_quo(O,15,k[1], k[2])
      if !_are_there_subs(r,[15])
        continue
      end
      if cgrp
        mr.prime_ideal_cache = S
      end
      act=_act_on_ray_class(mr,gens)
      ls=stable_subgroups(r,[15],act, op=(x, y) -> quo(x, y, false)[2])
      a=_min_wild(k[2])*k[1]
      for s in ls
        if !_right_actionD5C3(s,act)
          continue
        end
        C=ray_class_field(mr, s)
        if Hecke._is_conductor_min_normal(C,a) && Hecke.discriminant_conductor(O,C,a,mr,bound,15)
          @vprint :QuadraticExt "New Field \n"
          #Before computing the field, I check if the discriminant of the $D_5$ extension is compatible
          s1=codomain(s)
          q1,mq1=quo(s1,5, false)
          C1=ray_class_field(mr, Hecke._compose(s, mq1))
          cond=conductor(C1)[1]
          condint=minimum(cond)
          if condint^4*D^2>bound5
            @vprint :QuadraticExt "Too large (without computing it) :( \n"
            continue
          end
          L=number_field(C)
          ram_primes=Set(collect(keys(factor(a).fac)))
          for p in keys(factor(O.disc).fac)
            push!(ram_primes, p)
          end
          auto=extend_aut(C,gens[1])
          T,mT=simple_extension(L)
          x=mT(gen(T))
          if (auto*auto)(x)!=x
            auto=auto^3
          end
          pol=absolute_minpoly(x+auto(x))
          if degree(pol)!=15
            pol=absolute_minpoly(x*(auto(x)))
          end
          K,_=NumberField(pol, cached= false)
          if _is_discriminant_lower(K, collect(ram_primes), non_normal_bound)
            @vprint :QuadraticExt "The field is: $pol \n"
            push!(fieldslist, (number_field(pol)[1], collect(ram_primes)))
          end
        end
      end
    end
    
  end
  
  return fieldslist
  
end


function _right_actionD5C3(s::GrpAbFinGenMap, act::Array{GrpAbFinGenMap,1})

  @assert length(act)==1
  S=codomain(s)
  T,mT=snf(S)
  @assert T.snf[1]==15
  @assert ngens(T)==1
  new_el=mT\(s(act[1](s\mT(T[1]))))
  if 3*new_el==12*T[1] && 5*new_el==5*T[1]
    return true
  else
    return false
  end
end

###############################################################################
#
#  S3 x C5 extensions
#
###############################################################################
function S3xC5_extensions(non_normal_bound::fmpz)

  bound_quadratic= Int(root(non_normal_bound,5))
  list_quad=quadratic_extensions(bound_quadratic, complex=true)
  return S3xC5_extensions(non_normal_bound,collect(list_quad))
end


function S3xC5_extensions(non_normal_bound::fmpz, list_quad)


  fieldslist=Tuple{AnticNumberField, Array{fmpz,1}}[]

  for K in list_quad
    
    @vprint :QuadraticExt 1 "Field: $K\n"
    O=maximal_order(K)
    D=abs(discriminant(O))
    bound = non_normal_bound^2
   
    bound3=root(non_normal_bound, 5)
    C,mC=class_group(O)
    allow_cache!(mC)
    cgrp=false
    if gcd(C.snf[end],15)!=1
      cgrp=true
      S = prime_ideals_up_to(O, max(100,12*clog(D,10)^2))
    end
    gens=Hecke.automorphisms(K)
    a=gen(K)
    if gens[1](a)==a
      deleteat!(gens,1)
    else
      deleteat!(gens,2)
    end
    
    #Getting conductors
    l_conductors=conductors(O,15,bound)
    @vprint :QuadraticExt "Number of conductors: $(length(l_conductors)) \n"
  
    #Now, the big loop
    for (i, k) in enumerate(l_conductors)
      r,mr=ray_class_group_quo(O,15,k[1], k[2])
      if !_are_there_subs(r,[15])
        continue
      end
      if cgrp
        mr.prime_ideal_cache = S
      end
      act=_act_on_ray_class(mr,gens)
      ls=stable_subgroups(r,[15],act, op=(x, y) -> quo(x, y, false)[2])
      a=_min_wild(k[2])*k[1]
      for s in ls
        if !_right_actionC5S3(s,act)
          continue
        end
        C=ray_class_field(mr, s)
        if Hecke._is_conductor_min_normal(C,a) && Hecke.discriminant_conductor(O,C,a,mr,bound,15)
          @vprint :QuadraticExt 1  "\n New Field!\n"
          #Before computing the field, I check if the discriminant of the $S_3$ extension is compatible
          s1=codomain(s)
          q1,mq1=quo(s1,3, false)
          C1=ray_class_field(mr, _compose(s, mq1))
          cond=conductor(C1)[1]
          condint=minimum(cond)
          if condint^2*D>bound3
            @vprint :QuadraticExt "Too large :( \n"
            continue
          end
          L=number_field(C)
          ram_primes=Set(collect(keys(factor(a).fac)))
          for p in keys(factor(O.disc).fac)
            push!(ram_primes, p)
          end
          auto=extend_aut(C,gens[1])
          T,mT=simple_extension(L)
          x=mT(gen(T))
          if (auto*auto)(x)!=x
            auto=auto*auto*auto*auto*auto
          end
          pol=absolute_minpoly(x+auto(x))
          if degree(pol)!=15
            pol=absolute_minpoly(x*(auto(x)))
          end
          K=number_field(pol, cached=false)[1]
          if _is_discriminant_lower(K, collect(ram_primes), non_normal_bound)
            push!(fieldslist, (K, collect(ram_primes)))
            @vprint :QuadraticExt "New candidate! \n"
            @vprint :QuadraticExt "$(pol) \n"
          else
            @vprint :QuadraticExt "Too large :( \n"
          end
        end
      end
    end
  end
  
  return fieldslist
  
end

function _right_actionC5S3(s::GrpAbFinGenMap, act::Array{GrpAbFinGenMap,1})

  @assert length(act)==1
  S=codomain(s)
  T,mT=snf(S)
  @assert T.snf[1]==15
  @assert ngens(T)==1
  new_el=mT\(s(act[1](s\mT(T[1]))))
  if 3*new_el==3*T[1] && 5*new_el==10*T[1]
    return true
  else
    return false
  end
end

###############################################################################
#
#  Semidirect product of C9 and C4
#
###############################################################################

function C9semiC4(absolute_bound::fmpz; real::Bool=false)

  Qx,x=PolynomialRing(FlintQQ, "x")
  K,a=NumberField(x-1,"a")
  O=maximal_order(K)

  l=Hecke.abelian_normal_extensions(O,[4], root(absolute_bound, 9), ramified_at_infplc=!real)
  return C9semiC4(absolute_bound, l)
  
end

function C9semiC4(absolute_bound::fmpz, l)  
  
  field=1
  for L in l
    S=Hecke.simple_extension(L)[1]
    K=Hecke.absolute_field(S)[1]
    K=simplify(K, canonical=true)[1]
    O=maximal_order(K)
    D=abs(discriminant(O))
    if D^9>absolute_bound
      continue
    end
    bo = ceil(Rational{BigInt}(absolute_bound//D^9))
    bound = FlintZZ(fmpq(bo))
   
    C,mC=class_group(O)
    allow_cache!(mC)
    cgrp=false
    if gcd(C.snf[end],3)!=1
      cgrp=true
      S = prime_ideals_up_to(O, max(100,12*clog(D,10)^2))
    end
    Aut=Hecke.automorphisms(K)
    @assert length(Aut)==degree(O) #The field is normal over Q
    gens = Hecke.small_generating_set(Aut)
  
    #Getting conductors
    l_conductors=conductors(O,9,bound, false)
    @vprint :QuadraticExt 1 "Conductors: $(length(l_conductors))\n"
    #Now, the big loop
    for (i, k) in enumerate(l_conductors)
      @vprint :QuadraticExt 1 "Doing $i\n"
      r,mr=ray_class_group_quo(O,9,k[1], k[2])
      if !_are_there_subs(r,[9])
        continue
      end
      if cgrp
        mr.prime_ideal_cache = S
      end
      @vprint :QuadraticExt 1 "Computing the action\n"
      act=_act_on_ray_class(mr,gens)
      @vprint :QuadraticExt 1 "Computing subgroups\n"
      ls=stable_subgroups(r,[9],act, op=(x, y) -> quo(x, y, false)[2])
      a=_min_wild(k[2])*k[1]
      for s in ls
        if _trivial_action(s,act,9)
          continue
        end
        C=ray_class_field(mr, s)
        if Hecke._is_conductor_min_normal(C,a) && Hecke.discriminant_conductor(O,C,a,mr,bound,9) && evaluate(FacElem(C.absolute_discriminant)) <= absolute_bound
          absolute_bound=evaluate(FacElem(C.absolute_discriminant))
          @vprint :QuadraticExt 1 "New Field with discriminant $absolute_bound"
          field=C
        end
      end
    end
  end
  #if typeof(field)==ClassField
  #  field=number_field(C)
  #end
  
  return field
  
end


###############################################################################
#
#  Sieving discriminants  
#
###############################################################################

function _discriminant_bound(autos, ram_primes::Array{fmpz,1}, bound::fmpz)

  K=_to_non_normal(autos)
  @vprint :QuadraticExt 1 "Doing $(K)"
  #now, compute the discriminant of K. Since we know the ramified primes, 
  #we know the primes dividing the discriminant and this is easier than computing the maximal order.
  return _is_discriminant_lower(K,ram_primes,bound)
  
end

function _is_discriminant_lower(K::AnticNumberField, ram_primes::Array{fmpz,1}, bound::fmpz)

  disc=fmpz(1)
  O=EquationOrder(K)
  for p in ram_primes
    OO=pmaximal_overorder(O,p)
    disc*=p^(valuation(discriminant(OO),p))
    if disc>bound
      return false
    end
  end
  return true

end

###############################################################################
#
#  From normal extension to the non-normal one using the trace/norm function
#
###############################################################################

function _to_non_normal(autos)#::Vector{NfRel_nsToNfRel_nsMor})

  #first, find a generator of the simple extension
  L=domain(autos[1])
  S,mS=simple_extension(L)
  x=mS(gen(S))
  
  #find an element of order 2 in the automorphisms
  Id=find_identity(autos,*)
  i=1
  while autos[i]==Id || autos[i]*autos[i]!=Id
    i+=1
  end
  
  #Find primitive element 
  pr_el=x+autos[i](x)
  
  #Take minimal polynomial; I need to embed the element in the absolute extension
  pol=absolute_minpoly(pr_el)
  if degree(pol)==15
    return number_field(pol)[1]
  else
    pr_el=x*(autos[i](x))
    return number_field(absolute_minpoly(pr_el))[1]
  end
  
end



################################################################################
#
#  Valuation bounds for discriminants
#
################################################################################

function valuation_bound_discriminant(n::Int, p::Union{Integer, fmpz})
  # First compute the p-adic expansion of n
  S = Vector{typeof(p)}()
	q = typeof(p)(n)
  q, r = divrem(q, p)
  push!(S, r)
  while q >= p
    q, r = divrem(q, p)
    push!(S, r)
  end

	if !iszero(q)
		push!(S, q)
	end

	@assert sum(S[i + 1] * p^i for i in 0:length(S)-1) == n

	b = zero(typeof(p))

	for i in 0:length(S) - 1
		b = b + S[i + 1] * (i + 1) * p^i
		if !iszero(S[i + 1])
			b = b - 1
		end
	end

  return b
end

###############################################################################
#
#  From relative to absolute
#
###############################################################################

function _from_relative_to_abs(L::Tuple{NfRel_ns{T}, Array{NfRel_nsToNfRel_nsMor{T},1}}) where T
  
  S,mS=simple_extension(L[1])
  K,mK=absolute_field(S, false)
  
  #First, we compute the maximal order of the absolute field.
  #We start from the maximal orders of the relative extension and of the base field.
  #FALSE: Since the computation of the relative maximal order is slow, I prefer to bring to the absolute field the elements
  # generating the equation order.
  O=maximal_order(L[1].base_ring)
  OL=EquationOrder(L[1])
  B=pseudo_basis(OL)
  
  @vprint :QuadraticExt 2 "Maximal Orders computed\n"
  #Then we consider the product basis
  basisL=Array{NfRel_nsElem, 1}(2*degree(L[1]))
  for i=1:degree(L[1])
    _assure_weakly_normal_presentation(B[i][2].num)
    basisL[2*i-1]=divexact(B[i][2].num.gen_one* B[i][1], B[i][2].den)
    basisL[2*i]=divexact(L[1].base_ring(B[i][2].num.gen_two)* B[i][1], B[i][2].den)
  end
  basisO=[L[1](O.basis_nf[i]) for i=1:degree(O)]
  
  nbasisL=[mK(mS\(el)) for el in basisL]
  nbasisO=[mK(mS\(el)) for el in basisO]

  cbasis=[x*y for x in nbasisL for y in nbasisO]
  append!(cbasis, [gen(K)^i for i=0:degree(K)-1])
  @vprint :QuadraticExt 2 "Product basis computed\n"
  #Now, we compute the maximal order. Then we simplify.
  O1=MaximalOrder(_order(K, cbasis))
  O1.ismaximal=1
  _set_maximal_order_of_nf(K,O1)
  Ks, mKs= simplify(K)
  
  #Now, we have to construct the maximal order of this field.
  #I am computing the preimages of mKs by hand, by inverting the matrix.
  M = zero_matrix(FlintZZ, degree(Ks), degree(Ks))
  prim_img=mKs(gen(Ks))
  M1=inv(basis_mat([prim_img^i for i=0:degree(Ks)-1]))
  basisO2=Array{nf_elem, 1}(degree(Ks))
  M=zero_matrix(FlintZZ, 1, degree(Ks))
  for i=1:length(basisO2)
    elem_to_mat_row!(M, 1, denominator(O1.basis_nf[i]), O1.basis_nf[i])
    mul!(M, M, M1.num)
    basisO2[i]=elem_from_mat_row(Ks, M, 1, M1.den*denominator(O1.basis_nf[i]))
  end
  O2=Order(Ks, basisO2, false)
  O2.ismaximal=1
  _set_maximal_order_of_nf(Ks,O2)
  @vprint :QuadraticExt 2 "MaximalOrder Computed. Now Automorphisms\n"

  #Now, the automorphisms.
  autos=Array{NfToNfMor, 1}(length(L[2]))
  el=mS(mK\(mKs(gen(Ks))))
  for i=1:length(L[2])
    x=mK(mS\(L[2][i](el)))
    elem_to_mat_row!(M, 1, denominator(x), x)
    mul!(M, M, M1.num)
    y=elem_from_mat_row(Ks, M, 1, M1.den*denominator(x))
    @assert Ks.pol(y)==0
    autos[i]=NfToNfMor(Ks,Ks,y)
  end
  
  @vprint :QuadraticExt 2 "Finished\n"
  return Ks, autos

end 

###############################################################################
#
#  Read-Write
#
###############################################################################

function _write_fields(list::Array{Tuple{AnticNumberField, fmpz},1}, filename::String)
  f=open(filename, "a")
  for L in list
    x=([coeff(L[1].pol, i) for i=0:degree(L[1].pol)], L[2])
    Base.write(f, "$x\n")
  end
  close(f)
end

function _read_fields(filename::String)
  f=open(filename, "r")
  Qx,x=PolynomialRing(FlintQQ,"x")
  pols=Tuple{fmpq_poly, fmpz}[]
  for s in eachline(f)
    a=eval(parse(s))
	  push!(pols,(Qx(a[1]), a[2]))
	end
	close(f)
	return pols
end
