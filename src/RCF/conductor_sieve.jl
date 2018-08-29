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
  quo_action=Array{nmod_mat,1}(undef, length(act))
  for s=1:length(act)
    quo_action[s]=W(mS.map*act[i].map*mS.imap)
  end
  return ZpnGModule(S, quo_action)

end


# Function that finds an integer in the ideal 
function _min_wild(D::Dict{NfOrdIdl, Int})

  res = fmpz(1)
  primes_done=fmpz[]
  for (p,v) in D
    s=minimum(p)
    if s in primes_done
      continue
    end
    push!(primes_done, s)
    res*=s^v
  end  
  return res  

end

function totally_positive_generators(mr::MapRayClassGrp, a::fmpz, wild::Bool=false)

  if isdefined(mr, :tame_mult_grp)
    tmg=mr.tame_mult_grp
    for (p,v) in tmg
      mr.tame_mult_grp[p] = GrpAbFinGenToNfAbsOrdMap(domain(v), codomain(v), [ make_positive(v.generators[1], a) ], v.discrete_logarithm)
      @hassert :RayFacElem 1 istotally_positive(mr.tame_mult_grp[p].generators[1])
    end
  end
  if wild && isdefined(mr, :wild_mult_grp)
    wld=mr.wild_mult_grp
    for (p,v) in wld
      x=v.generators
      for i=1:length(x)
        x[i]=make_positive(x[i],a)
        @hassert :RayFacElem 1 iscoprime(ideal(parent(x[i]), x[i]), ideal(parent(x[i]), a))
      end
      mr.wild_mult_grp[p] = GrpAbFinGenToNfAbsOrdMap(domain(v), codomain(v), x, v.discrete_logarithm)
    end 
  end

end

function make_positive(x::NfOrdElem, a::fmpz)
 
  els=conjugates_arb(x)
  m=fmpz(0)
  for i=1:length(els)
    if isreal(els[i])
      y=BigFloat(midpoint(real(els[i]/a)))
      if y>0
        continue
      else
        m = max(m,1-ceil(fmpz,y))
      end
    end
  end
  @hassert :RayFacElem 1 iscoprime(ideal(parent(x),x), ideal(parent(x), a))
  @hassert :RayFacElem 1 iscoprime(ideal(parent(x),x+fmpz(m)*a), ideal(parent(x), a))
  @hassert :RayFacElem 1 istotally_positive(x+m*a)
  return x+fmpz(m)*a
    
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

function squarefree_for_conductors(O::NfOrd, n::Int, deg::Int; coprime_to::Array{fmpz,1}=fmpz[])
  
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
  coprime_to=cat(ram_primes, wild_ram, dims = 1)
  sort!(ram_primes)
  m=minimum(wild_ram)
  k=divexact(n,m)
  b1=Int(root(fmpz(bound),Int(degree(O)*(m-1)*k))) 
  list = squarefree_for_conductors(O, b1, n, coprime_to=coprime_to)

  extra_list = Tuple{Int, Int}[(1,1)]
  for q in ram_primes
    tr = prime_decomposition_type(O,Int(q))
    f = tr[1][1]
    nq = Int(q)^f 
    if gcd(nq-1,n) == 1
      continue
    end
    if nq > bound
      continue
    end
    l=length(extra_list)
    for i=1:l
      no = extra_list[i][2]*nq
      if no > bound
        continue
      end
      push!(extra_list, (extra_list[i][1]*q, no))
    end
  end
  
  final_list=Tuple{Int,fmpz}[]
  l=length(list)
  e = Int((m-1)*k)
  for (el,norm) in extra_list
    for i=1:l
      if (list[i]^d) * norm > bound
        continue
      end
      push!(final_list, (list[i]*el, (list[i]^(e*d))*norm))
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

###############################################################################
#
#  Conductors over QQ
#
###############################################################################


function squarefree_for_conductorsQQ(O::NfOrd, n::Int, a::Array{Int, 1}; coprime_to::Array{fmpz,1}=fmpz[])
  
  G = map(Int, snf(DiagonalGroup(a))[1].snf)
  sqf= trues(n)
  primes= trues(n)
  deg = G[end]
  #remove primes that can be wildly ramified
  for x in coprime_to
    el=Int(x)
    t=el
    while t<= n
      @inbounds sqf[t]=false
      @inbounds primes[t]=false
      t+=el
    end
  end
  
  single = Array{Int, 1}()
  push!(single, 1)
  multiple = Array{Int, 1}()
  
  #sieving procedure
  #First, I can remove all the multiples of 2
  if !(2 in coprime_to)
    i=2
    while i<=length(sqf)
      @inbounds sqf[i]=false
      i+=2
    end
  end  

  i=3
  b=Base.sqrt(n)
  while i<=b
    if primes[i]
      if gcd(deg,i-1)==1
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
      if gcd(deg,i-1) == 1
        @inbounds primes[i] = false
        @inbounds sqf[i]=false
        j = i
        while j <= n
         @inbounds sqf[j]=false
         j += i
        end
      end
    end
    i+=2
  end
  if length(G) > 1
    i = 3
    while i < n
      if primes[i]
        push!(single, i)
      elseif sqf[i]
        push!(multiple, i)
      end
      i += 2
    end
  elseif !isprime(deg)
    i = 3
    while i < n
      if primes[i] 
        if i-1 % deg == 0
          push!(multiple, i)
        else
          push!(single, i)
        end
      elseif sqf[i]
        push!(multiple, i)
      end
      i += 2
    end
  else
    multiple = Int[i for i = 1:length(sqf) if sqf[i]]
  end
  #@assert length(single) + length(multiple) == length(Int[i for i = 1:length(sqf) if sqf[i]])
   
  return single, multiple 
  
end



function conductors_tameQQ(O::NfOrd, a::Array{Int, 1}, bound::fmpz)

  #
  #  First, conductors coprime to the ramified primes and to the 
  #  degree of the extension we are searching for.
  # 
  n = prod(a)
  wild_ram = collect(keys(factor(fmpz(n)).fac))
  m = minimum(wild_ram)
  k = divexact(n, m)
  b1 = Int(root(fmpz(bound),Int((m-1)*k))) 
  
  return squarefree_for_conductorsQQ(O, b1, a, coprime_to=wild_ram)

end

function conductorsQQ(O::NfOrd, a::Array{Int, 1}, bound::fmpz, tame::Bool=false)
  
  K = nf(O)
  d = degree(O)
  n = prod(a)
  wild_ram = collect(keys(factor(fmpz(n)).fac))

  #
  # First, conductors for tamely ramified extensions
  #

  single, multiple = conductors_tameQQ(O,a,bound)

  if tame
    return multiple  
  end
  #
  # now, we have to multiply the obtained conductors by proper powers of wildly ramified ideals. 
  #
  wild_list=Tuple{Int, Int, fmpz}[(1, 1, 1)]
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
  final_list = Int[]
  exps = Int((minimum(wild_ram)-1)*divexact(n, minimum(wild_ram)))
  for el in multiple
    for (q,d,nm2) in wild_list
      if (fmpz(el)^exps)*nm2 > bound
        continue
      end
      push!(final_list, (el*q*d))
    end
  end
  
  for el in single
    for (q,d,nm2) in wild_list
      if (fmpz(el)^exps)*nm2 > bound
        continue
      end
      push!(final_list, (el*q*d))
    end
    #=
    for j = 2:length(wild_list)
      q,d,nm2 = wild_list[j]
      if (fmpz(el)^exps)*nm2 > bound
        continue
      end
      push!(final_list, (el*q*d))
    end
    =#
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


  newlist = Vector{NfAbsNS}(undef, length(l))
  for j in 1:length(l)
    newlist[j], _ = number_field([Qx([coeff(coeff(f, i), 0) for i in 0:length(f)]) for f in l[j].abs_pol])
  end
  return newlist
end

function abelian_extensions(O::NfOrd, gtype::Array{Int,1}, absolute_discriminant_bound::fmpz; real::Bool=false, tame::Bool=false, with_autos::Type{Val{T}} = Val{false}) where T 
  
  K=nf(O) 
  @assert degree(K)==1
  gtype = map(Int, snf(DiagonalGroup(gtype))[1].snf)
  n = prod(gtype)
    
  expo = lcm(gtype)
    
  #Getting conductors
  l_conductors=conductorsQQ(O, gtype, absolute_discriminant_bound, tame)
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
    ls=stable_subgroups(r, act, op=(x, y) -> quo(x, y, false)[2], quotype=gtype)
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
      pairs[poszero+i,1:n] .=false
      pairs[1:n,poszero+i] .=false
      pairs[poszero-i,1:n] .=false
      pairs[1:n,poszero-i] .=false
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
  @vprint :QuadraticExt 2 "Computing the maximal order\n"
  O=maximal_order(L[1].base_ring)
  OL=EquationOrder(L[1])
  B=pseudo_basis(OL)
  
  
  #Then we consider the product basis
  basisL=Array{NfRel_nsElem, 1}(undef, 2*degree(L[1]))
  for i=1:degree(L[1])
    _assure_weakly_normal_presentation(B[i][2].num)
    basisL[2*i-1]=divexact(B[i][2].num.gen_one* B[i][1], B[i][2].den)
    basisL[2*i]=divexact(L[1].base_ring(B[i][2].num.gen_two)* B[i][1], B[i][2].den)
  end
  basisO=[L[1](O.basis_nf[i]) for i=1:degree(O)]
  
  nbasisL=[mK(mS\(el)) for el in basisL]
  nbasisO=[mK(mS\(el)) for el in basisO]

  cbasis=[x*y for x in nbasisL for y in nbasisO]
  powgen = Array{nf_elem, 1}(undef, degree(K))
  powgen[1] = K(1)
  for i = 2:degree(K)
    powgen[i] = powgen[i-1]*gen(K)
  end
  append!(cbasis, powgen)
  #Now, we compute the maximal order. Then we simplify.
  O1 = MaximalOrder(_order(K, cbasis))
  O1.ismaximal = 1
  _set_maximal_order_of_nf(K, O1)
  @vprint :QuadraticExt 2 "Done. Now simplify and translate information\n"
  Ks, mKs = simplify(K)
  
  #Now, we have to construct the maximal order of this field.
  #I am computing the preimages of mKs by hand, by inverting the matrix.
  M = zero_matrix(FlintZZ, degree(Ks), degree(Ks))
  arr_prim_img = Array{nf_elem, 1}(undef, degree(Ks))
  arr_prim_img[1] = K(1)
  prim_img=mKs(gen(Ks))
  for i = 2:degree(Ks)
    arr_prim_img[i] = arr_prim_img[i-1]*prim_img
  end
  M1=inv(basis_mat(arr_prim_img))
  basisO2 = Array{nf_elem, 1}(undef, degree(Ks))
  M = zero_matrix(FlintZZ, 1, degree(Ks))
  for i=1:length(basisO2)
    elem_to_mat_row!(M, 1, denominator(O1.basis_nf[i]), O1.basis_nf[i])
    mul!(M, M, M1.num)
    basisO2[i]=elem_from_mat_row(Ks, M, 1, M1.den*denominator(O1.basis_nf[i]))
  end
  O2 = Order(Ks, basisO2, false)
  O2.ismaximal = 1
  _set_maximal_order_of_nf(Ks,O2)

  #Now, the automorphisms.
  autos=Array{NfToNfMor, 1}(undef, length(L[2]))
  el=mS(mK\(mKs(gen(Ks))))
  for i=1:length(L[2])
    x=mK(mS\(L[2][i](el)))
    elem_to_mat_row!(M, 1, denominator(x), x)
    mul!(M, M, M1.num)
    y=elem_from_mat_row(Ks, M, 1, M1.den*denominator(x))
    @assert Ks.pol(y)==0
    autos[i]=NfToNfMor(Ks,Ks,y)
  end
  _set_automorphisms_nf(Ks, closure(autos, *))
  
  @vprint :QuadraticExt 2 "Finished\n"
  return Ks, autos

end 

