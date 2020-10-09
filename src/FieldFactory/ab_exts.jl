add_verbose_scope(:AbExt)
add_assert_scope(:AbExt)

add_verbose_scope(:MaxAbExt)

##########################################################################################################
#
#  Functions for conductors
#
##########################################################################################################

function tame_conductors_degree_2(O::NfOrd, bound::fmpz)
 
  K = nf(O)
  d = degree(O)
  b1 = Int(root(bound,d))
  ram_primes = ramified_primes(O)
  sort!(ram_primes)
  filter!(x -> x!=2, ram_primes)
  list = squarefree_up_to(b1, coprime_to = vcat(ram_primes,2))

  extra_list = Tuple{Int, fmpz}[(1,fmpz(1))]
  for q in ram_primes
    tr = prime_decomposition_type(O, Int(q))
    e = tr[1][2]
    nq = fmpz(q)^(divexact(d,e))
    if nq > bound
      break
    end
    l=length(extra_list)
    for i = 1:l
      n = extra_list[i][2]*nq
      if n > bound
        continue
      end
      push!(extra_list, (extra_list[i][1]*q, n))
    end
  end
  
  final_list=Tuple{Int,fmpz}[]
  l = length(list)
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
  
  sqf = trues(n)
  primes = trues(n)
  
  #remove primes that can be wildly ramified or
  #that are ramified in the base field
  for x in coprime_to
    el = Int(x)
    t = el
    while t <= n
      @inbounds sqf[t]=false
      @inbounds primes[t]=false
      t += el
    end
  end
  
  #sieving procedure
  
  if !(2 in coprime_to)
    dt = prime_decomposition_type(O,2)
    if isone(gcd(2^dt[1][1]-1, deg))
      j=2
      while j<=n
        @inbounds sqf[j]=false
        @inbounds primes[j]=false
        j += 2
      end
    else 
      i=2
      s=4
      while s <= n
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
  i = 3
  b = root(n, 2)
  while i <= b
    if primes[i]
      if gcd(i-1, deg) != 1
        j = i
        while j <= n
          @inbounds primes[j]=false
          j += i
        end
        j = i^2
        t = j
        while j <= n
          @inbounds sqf[j]=false
          j += t
        end
      else
        dt = prime_decomposition_type(O, i)
        if gcd(deg, i^dt[1][1]-1) == 1
          @inbounds primes[i] = false
          @inbounds sqf[i] = false
          j = i
          while j <= n
           @inbounds primes[j] = false
           @inbounds sqf[j] = false
           j+=i
          end
        else 
          j=i
          while j <= n
            @inbounds primes[j]=false
            j+=i
          end
          j=i^2
          t=j
          while j<= n
            @inbounds sqf[j]=false
            j+=t
          end
        end
      end
    end
    i+=2
  end
  while i<=n
    if primes[i] && gcd(i-1, deg) == 1
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

  if n == 2
    return tame_conductors_degree_2(O,bound)
  end
  #
  #  First, conductors coprime to the ramified primes and to the 
  #  degree of the extension we are searching for.
  # 
  d = degree(O)
  K = nf(O)
  wild_ram = collect(keys(factor(fmpz(n)).fac))
  ram_primes = ramified_primes(O)
  filter!(x -> !divisible(fmpz(n),x), ram_primes)
  coprime_to = vcat(ram_primes, wild_ram)
  sort!(ram_primes)
  m = minimum(wild_ram)
  k = divexact(n, m)
  e = Int((m-1)*k)
  b1 = Int(root(bound, degree(O)*e))
  list = squarefree_for_conductors(O, b1, n, coprime_to = coprime_to)
  
  extra_list = Tuple{Int, fmpz}[(1, fmpz(1))]
  for q in ram_primes
    tr = prime_decomposition_type(O, Int(q))
    f = tr[1][1]
    nq = q^f 
    if iscoprime(nq - 1, fmpz(n))
      continue
    end
    nq = nq^(length(tr)*e)
    if nq > bound
      continue
    end
    l = length(extra_list)
    for i=1:l
      no = extra_list[i][2]*nq
      if no > bound
        continue
      end
      push!(extra_list, (extra_list[i][1]*q, no))
    end
  end
  
  final_list = Tuple{Int, fmpz}[]
  l = length(list)
  e = Int((m-1)*k)
  for (el,norm) in extra_list
    for i=1:l
      if (list[i]^(e*d)) * norm > bound
        continue
      end
      push!(final_list, (list[i]*el, (fmpz(list[i])^(e*d))*norm))
    end
  end
  
  return final_list
end


function conductors(O::NfOrd, a::Array{Int, 1}, bound::fmpz, tame::Bool=false)
  
  #Careful: I am assuming that a is in snf!
  K=nf(O)
  d=degree(O)
  n = prod(a)
  expo = a[end]
  wild_ram = collect(keys(factor(fmpz(n)).fac))

  #
  # First, conductors for tamely ramified extensions
  #
  bound_tame = root(bound, divexact(n, expo))
  list = conductors_tame(O, expo, bound_tame)

  if tame
    reverse!(list)
    return Tuple{Int, Dict{NfOrdIdl, Int}}[(x[1], Dict{NfOrdIdl, Int}()) for x in list]  
  end
  #
  # now, we have to multiply the obtained conductors by proper powers of wildly ramified ideals. 
  #
  wild_list = Tuple{Int, Dict{NfOrdIdl, Int}, fmpz}[(1, Dict{NfOrdIdl, Int}(), fmpz(1))]
  for q in wild_ram
    lp = prime_decomposition(O, Int(q))
    fq = divexact(d, lp[1][2]*length(lp))
    l = length(wild_list)
    sq = fmpz(q)^(divexact(d,lp[1][2])) #norm of the squarefree part of the integer q
    #=
      we have to use the conductor discriminant formula to understand the maximal possible exponent of q.
      Let ap be the exponent of p in the relative discriminant, let m be the conductor and h_(m,C) the cardinality of the 
      quotient of ray class group by its subgroup C.
      Then 
          ap= v_p(m)h_(m,C)- sum_{i=1:v_p(m)} h_(m/p^i, C)
      Since m is the conductor, h_(m/p^i, C)<= h_(m,C)/q.
      Consequently, we get
        v_p(m)<= (q*ap)/(h_(m,C)*(q-1))
    =#
    v = valuation(expo, q)
    # First, we compute the bound coming from the bound on the discriminant
    boundsubext = root(bound, Int(divexact(n, q^v))) #The bound on the norm of the discriminant on the subextension 
                                                     # of order q^v
    #Bound coming from the bound on the discriminant
    obound = flog(boundsubext, sq)                                                
    
    #Bound coming from the analysis on the different in a local extension
    nbound = q^v + lp[1][2] * v * q^v - 1

    bound_max_ap = min(nbound, obound)  #bound on ap
    bound_max_exp = div(bound_max_ap, (q-1)*q^(v-1)) #bound on the exponent in the conductor
    
    #Ramification groups bound
    max_nontrivial_ramification_group = div(lp[1][2]*(q^v), q-1)
    if v > 1
      ram_groups_bound = max_nontrivial_ramification_group - sum(q^i for i = 1:v-1) + v 
    else
      ram_groups_bound = max_nontrivial_ramification_group + 1 
    end
    bound_max_exp = min(ram_groups_bound, bound_max_exp)
    
    #The prime may be also tamely ramified!
    nisc = gcd(q^(fq)-1, fmpz(expo))
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
      exp1 = i*(q-1)*divexact(n,q)
      nq= sq^(exp1)
      for s=1:l
        nn=nq*wild_list[s][3]
        if nn>bound
          continue
        end
        d2 = merge(max, d1, wild_list[s][2]) 
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
  reverse!(final_list)
  return final_list
  
end

###############################################################################
#
#  Conductors over QQ
#
###############################################################################

function squarefree_for_conductorsQQ(O::NfOrd, n::Int, a::Array{Int, 1}; coprime_to::Array{fmpz,1}=fmpz[])
  
  G = map(Int, snf(abelian_group(a))[1].snf)
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
        if rem(i-1, deg) == 0
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
    multiple = Int[i for i = 2:length(sqf) if sqf[i]]
  end
   
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
  expo = a[end]
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
    l = length(wild_list)
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
    v = valuation(expo, q)
    
    #I don't need to give a bound for a_p on the big extension but only on the maximum extension of q-power order
    #This is the only thing that matters for the exponent of the conductor
    nisc = gcd(q-1,n)
    nbound = q^v + v * q^v - 1
    boundsubext = root(bound, Int(divexact(n, q^v)))
    obound = flog(boundsubext, q)
    nnbound = valuation_bound_discriminant(n, q)
    bound_max_ap = min(nbound, obound, nnbound)  #bound on ap
    bound_max_exp = div(bound_max_ap, (q^(v-1))*(q-1)) #bound on the exponent in the conductor
    if q == 2
      bound_max_exp = min(bound_max_exp, valuation(expo, q)+2)
    else
      bound_max_exp = min(bound_max_exp, valuation(expo, q)+1)
    end
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
    for j = 2:length(wild_list)
      q,d,nm2 = wild_list[j]
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

  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  K, _ = NumberField(x - 1, "a", cached = false)
  OK = maximal_order(K)
  l = abelian_extensions(OK, gtype, discriminant_bound,
                         real = real,
                         tame = tame)


  newlist = Vector{NfAbsNS}(undef, length(l))
  for j in 1:length(l)
    newlist[j], _ = number_field([Qx([coeff(coeff(f, i), 0) for i in 0:length(f)]) for f in l[j].abs_pol], cached = false, check = false)
  end
  return newlist
end

function abelian_extensions(O::NfOrd, gtype::Array{Int,1}, absolute_discriminant_bound::fmpz; real::Bool=false, tame::Bool=false, with_autos::Type{Val{T}} = Val{false}) where T 
  
  K=nf(O) 
  @assert degree(K)==1
  gtype = map(Int, snf(abelian_group(gtype))[1].snf)
  n = prod(gtype)
    
  expo = lcm(gtype)
    
  #Getting conductors
  l_conductors=conductorsQQ(O, gtype, absolute_discriminant_bound, tame)
  @vprint :AbExt 1 "Number of conductors: $(length(l_conductors)) \n"
  if with_autos==Val{true}
    fields = Tuple{NfRelNS, Array{NfRelNSToNfRelNSMor,1}}[]
  else
    fields = NfRelNS[]
  end

  #Now, the big loop
  for (i, k) in enumerate(l_conductors)
    @vprint :AbExt 1 "Conductor: $k \n"
    @vprint :AbExt 1 "Left: $(length(l_conductors) - i)\n"
    r,mr=Hecke.ray_class_groupQQ(O, k, !real, expo)
    if !has_quotient(r, gtype)
      continue
    end
    ls=subgroups(r,quotype=gtype, fun= (x, y) -> quo(x, y, false)[2])
    for s in ls
      C=ray_class_field(mr, s)
      if Hecke._is_conductor_minQQ(C,n) && Hecke.discriminant_conductorQQ(O,C,k,absolute_discriminant_bound)
        @vprint :AbExt 1 "New Field \n"
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

#TODO: Allow more groups
function abelian_normal_extensions(O::NfOrd, gtype::Array{Int,1}, absolute_discriminant_bound::fmpz; ramified_at_infplc::Bool=true, tame::Bool=false, absolute_galois_group::Symbol = :all,  with_autos::Type{Val{T}} = Val{false}, autos::Array{NfToNfMor,1}=NfToNfMor[]) where T 

  d=degree(O)
  if d == 1
    return abelian_extensions(O, gtype, absolute_discriminant_bound, real=!ramified_at_infplc, tame=tame, with_autos=with_autos) 
  end

  K=nf(O) 
  n=prod(gtype)
  inf_plc=InfPlc[]
  
  if with_autos == Val{true}
    fields=Tuple{NfRelNS,Vector{NfRelNSToNfRelNSMor{nf_elem}}}[]
  else
    fields=NfRelNS[]
  end
  
  bound = div(absolute_discriminant_bound, abs(discriminant(O))^n)
  if bound == 0
    return fields
  end

  if mod(n,2)==0 && ramified_at_infplc
    inf_plc=real_places(K)
  end

  expo = lcm(gtype)
  C, mC = class_group(O)
  cgrp = !iscoprime(n, order(C))
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
  l_conductors=conductors(O, gtype, bound, tame)
  @vprint :AbExt 1 "Number of conductors: $(length(l_conductors)) \n"
  
  ctx = rayclassgrp_ctx(O, expo)
  #Now, the big loop
  for (i, k) in enumerate(l_conductors)
    @vprint :AbExt 1 "Conductor: $k \n"
    @vprint :AbExt 1 "Left: $(length(l_conductors) - i)\n"
    r,mr = ray_class_group_quo(O, k[1], k[2], inf_plc, ctx)
    if !has_quotient(r,gtype)
      continue
    end
    act = induce_action(mr,gens)
    ls = stable_subgroups(r, act, op=(x, y) -> quo(x, y, false)[2], quotype = gtype)
    for s in ls
      @hassert :AbExt 1 order(codomain(s))==n
      C = ray_class_field(mr, s)
      if Hecke._is_conductor_min_normal(C) && Hecke.discriminant_conductor(C, bound)
        @vprint :AbExt 1 "New Field \n"
        L = number_field(C)
        if absolute_galois_group != :all
          autabs = absolute_automorphism_group(C, gens)
          G = generic_group(autabs, *)
          if absolute_galois_group == :_16T7
            if isisomorphic_to_16T7(G)
              @vprint :AbExt 1 "I found a field with Galois group 16T7 (C_2 x Q_8)\n"
              @vtime :AbExt 1 push!(fields, L)
            end
          elseif absolute_galois_group == :_8T5
            if isisomorphic_to_8T5(G)
              @vprint :AbExt 1 "I found a field with Galois group 8T5 (Q_8)\n"
              @vtime :AbExt 1 push!(fields, L)
            end
          else
            error("Group not supported (yet)")
          end
        else
          if with_autos==Val{true}
            push!(fields, (L, absolute_automorphism_group(C,gens))) 
          else
            push!(fields, L)
          end
        end
      end
    end
  end

  return fields

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
  quo_action=Array{nmod_mat,1}(undef, length(act))
  for s=1:length(act)
    quo_action[s]= change_base_ring(mS.map*act[i].map*mS.imap, R)
  end
  return ZpnGModule(S, quo_action)

end

###############################################################################
#
#  Quadratic Extensions of Q
#
###############################################################################

function quadratic_fields(bound::Int; tame::Bool=false, real::Bool=false, complex::Bool=false, with_autos::Type{Val{T}}=Val{false}) where T

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
    return ( number_field(x^2-x+divexact(1-i,4), cached=false, check = false)[1] for i in sqf)
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
  return ( mod(i,4)!=1 ? number_field(x^2-i, cached=false, check = false)[1] : number_field(x^2-x+divexact(1-i,4), cached = false, check = false)[1] for i in final_list)

end

function _quad_ext(bound::Int, only_real::Bool = false)
  
  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  K = NumberField(x-1, cached = false, check = false)[1]
  sqf = squarefree_up_to(bound)
  final_list = Int[]
  for i=2:length(sqf)
    if abs(sqf[i]*4)< bound
      @views push!(final_list, sqf[i])
      continue
    end
    if mod(sqf[i], 4) == 1
      @views push!(final_list, sqf[i])
    end
  end
  if !only_real
    for i = 1:length(sqf)
      if abs(sqf[i]*4)< bound
        @views push!(final_list, -sqf[i])
        continue
      end
      if mod(sqf[i], 4) == 3
        @views push!(final_list, -sqf[i])
      end
    end
  end
  fields_list = Array{Tuple{AnticNumberField, Vector{NfToNfMor}, Vector{NfToNfMor}}, 1}(undef, length(final_list))
  for i = 1:length(final_list)
    if mod(final_list[i],4) != 1
      cp = Vector{fmpz}(undef, 3)
      cp[1] = -final_list[i]
      cp[2] = 0
      cp[3] = 1
      L, gL = number_field(Qx(cp), cached=false, check = false)
      auts = NfToNfMor[hom(L, L, -gL, check = false)]
      emb = NfToNfMor[hom(K, L, one(L), check = false)]
      fields_list[i] = (L, auts, emb)
    else
      cp = Vector{fmpz}(undef, 3)
      cp[1] = divexact(1-final_list[i], 4)
      cp[2] = -1
      cp[3] = 1
      L, gL = number_field(Qx(cp), cached=false, check = false)
      auts = NfToNfMor[hom(L, L, 1-gL, check = false)]
      emb = NfToNfMor[hom(K, L, one(L), check = false)]
      fields_list[i] = (L, auts, emb)
    end
  end
  return fields_list

end

###############################################################################
#
#  C2 x C2 extensions of Q
#
###############################################################################

function C22_extensions(bound::Int)
  
  
  Qx, x=PolynomialRing(FlintZZ, "x")
  K, _=NumberField(x-1, cached = false)
  Kx,x=PolynomialRing(K,"x", cached=false)
  b1=ceil(Int,Base.sqrt(bound))
  n=2*b1+1
  pairs = _find_pairs(bound)
  return (_ext(Kx,x,i,j) for (i, j) in pairs)
  
end

function _ext(Ox,x,i,j)
 
  y=mod(i,4)
  pol1 = x^2
  if y != 1
    pol1 = x^2-i
  else
    pol1 = x^2-x+divexact(1-i,4)
  end
  y=mod(j,4)
  pol2=Ox(1)
  if y!=1
    pol2=x^2-j
  else
    pol2=x^2-x+divexact(1-j,4)
  end
  return number_field([pol1,pol2], cached = false, check = false)

end


function _C22_exts_abexts(bound::Int, only_real::Bool = false)
  Qx, x = PolynomialRing(FlintZZ, "x")
  pairs = _find_pairs(bound, only_real)
  return (_ext_with_autos(Qx, x, i, j) for (i, j) in pairs)
end

function _ext_with_autos(Qx, x, i::Int, j::Int)
  first = i
  second = j
  g = gcd(i, j)
  if g != 1
    third = divexact(i*j, g^2)
    if gcd(first, third) == 1
      second = third
    elseif gcd(second, third) == 1
      first = third
    end
  end
  y1 = mod(first, 4)
  cp1 = Vector{fmpz}(undef, 3)
  cp1[3] = fmpz(1)
  if y1 != 1
    cp1[1] = fmpz(-first)
    cp1[2] = fmpz(0)
  else
    cp1[1] = fmpz(divexact(1-first,4))
    cp1[2] = fmpz(-1)
  end
  y2 = mod(second, 4)
  cp2 = Vector{fmpz}(undef, 3)
  cp2[3] = fmpz(1)
  if y2 != 1
    cp2[1] = fmpz(-second)
    cp2[2] = fmpz(0)
  else
    cp2[1] = fmpz(divexact(1-second, 4))
    cp2[2] = fmpz(-1)
  end
  return Qx(cp1), Qx(cp2)
end

function __get_term(a::fmpq_mpoly, exps::Vector{UInt})
   z = fmpq()
   ccall((:fmpq_mpoly_get_coeff_fmpq_ui, libflint), Nothing,
         (Ref{fmpq}, Ref{fmpq_mpoly}, Ptr{UInt}, Ref{FmpqMPolyRing}),
         z, a, exps, parent(a))
   return z
end

function _C22_with_max_ord(l)
  list = Vector{Tuple{AnticNumberField, Vector{NfToNfMor}, Vector{NfToNfMor}}}()
  Qx, x = PolynomialRing(FlintQQ, "x", cached = false)
  K = NumberField(x-1, cached = false)[1]
  for (p1, p2) in l
    Kns, g = number_field(fmpz_poly[p1, p2], check = false, cached = false)
    S, mS = simple_extension(Kns, check = false)
    d1 = discriminant(p1)
    d2 = discriminant(p2)
    cf = gcd(d1, d2)
    B = Vector{nf_elem}(undef, 4)
    B[1] = S(1)
    B[2] = mS\(g[1])
    B[3] = mS\(g[2])
    B[4] = B[2] * B[3]
    M = basis_matrix(B, FakeFmpqMat)
    hnf_modular_eldiv!(M.num, M.den, :lowerleft)
    O = NfAbsOrd(S, FakeFmpqMat(M.num, M.den))
    O.disc = d1^2*d2^2
    d3 = numerator(discriminant(S))
    if d3 < 0 
      O.disc = -O.disc
    end
    O.index = divexact(d3, O.disc)
    if cf != 1
      fac = factor(cf)
      for (p, v) in fac
        O = pmaximal_overorder(O, p)        
      end
    end
    O.ismaximal = 1
    Hecke._set_maximal_order_of_nf(S, O) 
    coord1 = __get_term(mS.prim_img.data, UInt[1, 0])
    coord2 = __get_term(mS.prim_img.data, UInt[0, 1])
    auts = Vector{NfToNfMor}(undef, 2)
    if iszero(coeff(p1, 1))
      auts[1] = hom(S, S, (-coord1)*B[2]+coord2*B[3], check = false)
    else
      auts[1] = hom(S, S, 1+(-coord1)*B[2]+coord2*B[3], check = false)
    end
    if iszero(coeff(p2, 1))
      auts[2] = hom(S, S, coord1*B[2]+(-coord2)*B[3], check = false)
    else      
      auts[2] = hom(S, S, coord1*B[2]+1+(-coord2)*B[3], check = false)
    end
    cl_auts = Vector{NfToNfMor}(undef, 4)
    cl_auts[1] = id_hom(S)
    cl_auts[2] = auts[1]
    cl_auts[3] = auts[2]
    cl_auts[4] = auts[1] * auts[2]
    Hecke._set_automorphisms_nf(S, cl_auts)
    push!(list, (S, auts, NfToNfMor[hom(K, S, S(1), check = false)]))
  end
  return list
end

function _disc(a::Int, b::Int, c::Int, bound::Int)
  a1 = mod(a, 4)
  b1 = mod(b, 4)
  if a1 == 1 && b1 == 1
    return a*b*c <= bound
  end
  c1 = mod(c, 4)
  if a1 == 1 || b1 == 1 || c1 == 1
    return 16*a*b*c <= bound
  else
    return 64*a*b*c <= bound
  end
end

function _pairs_totally_real(pairs, ls, bound)
  b1=floor(Int, Base.sqrt(bound))
  pairs[1, 1:length(ls)] .= false
  pairs[1:length(ls), 1] .= false
  for j = 2:length(ls)
    for i = j:length(ls)
      pairs[i, j] = false
    end
  end
  for j = 2:length(ls)
    second = ls[j]
    for i = 2:j-1
      if pairs[i, j]
        first = ls[i]
        g = gcd(first, second)
        if isone(g)
          third = first*second
        else
          third = divexact(first*second, g^2)
        end
        if abs(third) > b1
          pairs[i, j] = false
          continue
        end
        k = searchsortedfirst(ls, third)
        if i < k
          pairs[i, k] = false
        else
          pairs[k, i] = false
        end
        if j < k
          pairs[j, k] = false
        else
          pairs[k, j] = false
        end
        if !_disc(first, second, third, bound)
          pairs[i, j] = false
        end
      end
    end
  end
  it = findall(pairs)
  totally_real_exts = Vector{Tuple{Int, Int}}(undef, length(it))
  ind = 1
  for I in it
    totally_real_exts[ind] = (ls[I[1]], ls[I[2]])
    ind += 1
  end
  return totally_real_exts

end


function _find_pairs(bound::Int, only_real::Bool = false)

  #first, we need the squarefree numbers
  b1=ceil(Int, Base.sqrt(bound))
  ls = squarefree_up_to(b1)
  #The first step is to enumerate all the totally real extensions.
  pairs = trues(length(ls), length(ls))
  real_exts = _pairs_totally_real(pairs, ls, bound)
  if only_real
    return real_exts
  end
  ls1 = -ls
  #Now, all the others.
  pairs[1:length(ls), 2:length(ls)] .= true
  for j = 2:length(ls)
    second = ls[j]
    for i = 1:length(ls)
      if pairs[i, j]
        first = ls1[i]
        g = gcd(first, second)
        if isone(g)
          third = first*second
        else
          third = divexact(first*second, g^2)
        end
        abt = -third
        if abt > b1
          pairs[i, j] = false
          continue
        end
        k = searchsortedfirst(ls, abt)
        pairs[k, j] = false
        if !_disc(first, second, third, bound)
          pairs[i, j] = false
        end
      end
    end
  end
  it = findall(pairs)
  ind = 1
  res = Vector{Tuple{Int, Int}}(undef, length(it))
  for I in it
    res[ind] = (ls1[I[1]], ls[I[2]])
    ind += 1
  end 
  return vcat(res, real_exts)
end

###############################################################################
#
#  From relative to absolute
#
###############################################################################

function _from_relative_to_absQQ(L::NfRelNS{T}, auts::Array{NfRelNSToNfRelNSMor{T}, 1}) where T

  @vprint :AbExt 2 "Computing maximal orders of subfields\n"
  Qx, x = PolynomialRing(FlintQQ, "x")
  fields = Vector{AnticNumberField}(undef, length(L.pol))
  auts_abs = Vector{NfToNfMor}(undef, length(fields))
  for i = 1:length(L.pol)
    fK = isunivariate(L.pol[i])[2]
    f = Qx(fmpq[coeff(coeff(fK, j), 0) for j = 0:degree(fK)])
    K = number_field(f, cached = false, check = false)[1]
    #Since the field is abelian, setting the automorphisms helps the simplify
    fautK = isunivariate(auts[i].emb[i].data)[2]
    img = K(fmpq[coeff(coeff(fautK, j), 0) for j = 0:degree(K)-1])
    genautK = hom(K, K, img)
    Hecke._set_automorphisms_nf(K, closure(NfToNfMor[genautK], degree(K)))
    Ks, mKs = simplify(K, cached = false)
    fields[i] = Ks
    _compute_preimg(mKs)
    auts_abs[i] = hom(Ks, Ks, mKs\(genautK(mKs.prim_img)))
  end
  NS, embeddings = number_field(fields, check = false, cached = false)
  S, mS = simple_extension(NS, check = false)
  B = Vector{Vector{nf_elem}}(undef, length(fields))
  discs = Vector{fmpz}(undef, length(fields))
  discOS = fmpz(1)
  for i = 1:length(fields)
    B[i] = Vector{nf_elem}(undef, degree(fields[i]))
    OK = maximal_order(fields[i])
    BOK = basis(OK, fields[i])
    for j = 1:degree(fields[i])
      B[i][j] = mS\(embeddings[i](BOK[j]))
    end
    discs[i] = discriminant(OK)
    discOS *= discs[i]^(divexact(degree(S), degree(OK)))
  end
  prod_basis = product_basis(B)
  OS = NfOrd(S, basis_matrix(prod_basis, FakeFmpqMat))
  OS.disc = discOS
  to_test = fmpz[]
  for i = 1:length(discs)
    for j = i+1:length(discs)
      g = gcd(discs[i], discs[j])
      if !isone(g)
        push!(to_test, g)
      end
    end
  end
  if isempty(to_test)
    lp = to_test
  else
    lp = coprime_base(to_test)
  end
  Ofinal = OS
  for p in lp
    if isprime(p)
      Ofinal = sum_as_Z_modules(Ofinal, pmaximal_overorder(OS, p))
    else
      fac = factor(p)
      for (k, v) in fac
        Ofinal = sum_as_Z_modules(Ofinal, pmaximal_overorder(OS, k))
      end
    end
  end
  Ofinal.ismaximal = 1
  _set_maximal_order(S, Ofinal)
  #Now, we translate the automorphisms.
  autsNS = Vector{NfAbsNSToNfAbsNS}(undef, length(auts))
  gNS = gens(NS)
  for t = 1:length(auts)
    imgs = Vector{NfAbsNSElem}(undef, length(fields))
    for i = 1:length(imgs)
      if i == t
        imgs[i] = embeddings[i](auts_abs[i].prim_img)
      else
        imgs[i] = gNS[i]
      end
    end
    autsNS[t] = hom(NS, NS, imgs)
  end
  #Now, to the simple field
  auts_abs = Vector{NfToNfMor}(undef, length(autsNS))
  gK = mS(gen(S))
  for i = 1:length(auts_abs)
    auts_abs[i] = hom(S, S, mS\(autsNS[i](gK)))
  end
  @vprint :AbExt 2 "Done. Now simplify and translate information\n"
  @vtime :AbExt 2 Ks, mKs = simplify(S, cached = false, save_LLL_basis = true)
  #Now, we have to construct the maximal order of this field.
  #I am computing the preimages of mKs by hand, by inverting the matrix.
  #Now, the automorphisms.
  autos = Array{NfToNfMor, 1}(undef, length(auts_abs))
  el = mKs(gen(Ks))
  for i = 1:length(auts)
    autos[i] = hom(Ks, Ks, mKs\(auts_abs[i](el)), check = false)
  end

  @vprint :AbExt 2 "Finished\n"
  return Ks, autos

end 

function _from_relative_to_abs(L::NfRelNS{T}, auts::Array{NfRelNSToNfRelNSMor{T}, 1}) where T

  S, mS = simple_extension(L)
  K, mK, mK2 = absolute_field(S, false)
  #First, we compute the maximal order of the absolute field.
  #Since the computation of the relative maximal order is slow, I bring to the absolute field the elements
  # generating the equation order.
  @vprint :AbExt 2 "Computing the maximal order\n"
  #First, I construct the product basis of the relative extension
  pols = L.pol
  gL = gens(L)
  B = Array{nf_elem, 1}(undef, degree(K))
  B[1] = K(1)
  ind = total_degree(pols[1])
  genjj = mK\(mS\gL[1])
  for i = 2:ind
    B[i] = genjj*B[i-1]
  end
  for jj = 2:length(pols)
    genjj = mK\(mS\gL[jj])
    el = genjj
    new_deg = total_degree(pols[jj])
    for i = 2:new_deg
      for j = 1:ind
        B[(i-1)* ind + j] = B[j]* el 
      end
      mul!(el, el, genjj)
    end
    ind *= new_deg
  end

  #Now, I add the elements of the maximal order
  if degree(base_field(L)) > 1
    O = maximal_order(S.base_ring)
    for i = 1:degree(O)
      el = mK\(S(O.basis_nf[i]))
      for j = 1:ind
        B[(i-1)* ind + j] = B[j] * el 
      end
    end
  end
  #Now, we compute the maximal order. Then we simplify.
  PO = Order(K, B, check = false, cached = false, isbasis = true)
  @vtime :AbExt 2 O1 = MaximalOrder(PO)
  O1.ismaximal = 1
  _set_maximal_order_of_nf(K, O1)
  @vprint :AbExt 2 "Done. Now simplify and translate information\n"
  @vtime :AbExt 2 Ks, mKs = simplify(K, cached = false)
  #Now, we have to construct the maximal order of this field.
  #I am computing the preimages of mKs by hand, by inverting the matrix.


  #Now, the automorphisms.
  autos=Array{NfToNfMor, 1}(undef, length(auts))
  el=mS(mK((mKs(gen(Ks)))))
  for i=1:length(auts)
    y = mKs\(mK\(mS\(auts[i](el))))
    autos[i] = hom(Ks, Ks, y, check = false)
  end
  _set_automorphisms_nf(Ks, closure(autos, degree(Ks)))
  
  @vprint :AbExt 2 "Finished\n"
  return Ks, autos
end 


#######################################################################################
#
#  relative discriminant for abelian extension function
#
#######################################################################################

function discriminant_conductor(C::ClassField, bound::fmpz; lwp::Dict{Tuple{Int, Int}, Array{GrpAbFinGenElem, 1}} = Dict{Tuple{Int, Int}, Array{GrpAbFinGenElem, 1}}())
  
  mr = C.rayclassgroupmap 
  O = base_ring(C)
  n = degree(C)
  e = Int(exponent(C))
  lp = mr.fact_mod
  abs_disc = factor(discriminant(O)^n).fac
  if isempty(lp)
    C.absolute_discriminant=abs_disc
    return true
  end
  K = nf(O)
  d = degree(K)
  discr = fmpz(1)
  mp = pseudo_inv(C.quotientmap) * mr
  R = domain(mp)
  a = minimum(defining_modulus(mr)[1])
  primes_done = fmpz[]
  if isprime(n)
    for (p, v) in lp
      if minimum(p, copy = false) in primes_done
        continue
      end
      push!(primes_done, minimum(p, copy = false))
      ap = n*v-v
      qw = divexact(d, p.splitting_type[1])*ap
      mul!(discr, discr, fmpz(p.minimum)^qw)
      if discr > bound
        @vprint :AbExt 2 "too large\n"
        return false
      else
        if haskey(abs_disc, p.minimum)
          abs_disc[p.minimum] += qw
        else 
          abs_disc[p.minimum] = qw
        end
      end
    end
    return true
  end
  
  powers = mr.powers
  groups_and_maps = mr.groups_and_maps
  
  for i = 1:length(powers)
    p, q = powers[i]
    if p.minimum in primes_done
      continue
    end
    push!(primes_done, p.minimum)
    if p == q
      ap = n
      tmg = groups_and_maps[i][2].tame[p]
      el = C.quotientmap(tmg.disc_log)
      Q, mQ = quo(R, GrpAbFinGenElem[el], false)
      ap -= order(Q)
      qw = divexact(d, p.splitting_type[1])*ap
      mul!(discr, discr, fmpz(p.minimum)^qw)
      if discr > bound
        @vprint :AbExt 2 "too large\n"
        return false
      else
        if haskey(abs_disc, p.minimum)
          abs_disc[p.minimum] += qw
        else 
          abs_disc[p.minimum] = qw
        end
      end
      continue
    end
    np = p.minimum^divexact(d, p.splitting_type[1])
    ap = n*lp[p]
    s = lp[p]
    @hassert :AbExt 1 s>=2
    els=GrpAbFinGenElem[]
    for k=2:lp[p]      
      s = s-1
      pk = p^s
      pv = pk*p
      if haskey(lwp, (Int(p.minimum), s+1))
        gens = lwp[(Int(p.minimum), s+1)]
      else
        gens_els = _1pluspk_1pluspk1(K, p, pk, pv, powers, a, e)
        gens = Vector{GrpAbFinGenElem}(undef, length(gens_els))
        for i = 1:length(gens)
          gens[i] = mr\(ideal(O, gens_els[i]))
        end
        lwp[(Int(p.minimum), s+1)] = gens
      end
      for i = 1:length(gens)
        push!(els, C.quotientmap(gens[i]))
      end
      o = order(quo(R, els, false)[1])
      ap -= o
      tentative_ap = ap - (lp[p] - k + 1)*o
      tentative_discr = discr * (np^tentative_ap)
      if tentative_discr > bound
        return false
      end
      @hassert :AbExt 1 ap>0
    end
    if haskey(groups_and_maps[i][2].tame, p)
      v = groups_and_maps[i][2].tame[p]
      push!(els, C.quotientmap(v.disc_log))
    end
    ap -= order(quo(R, els, false)[1])
    @hassert :AbExt 1 ap>0
    np1 = np^ap
    mul!(discr, discr, np1)
    if discr > bound
      @vprint :AbExt 2 "too large\n"
      return false
    else
      if haskey(abs_disc, p.minimum)
        abs_disc[p.minimum] += ap*divexact(d, p.splitting_type[1])
      else 
        abs_disc[p.minimum] = ap*divexact(d, p.splitting_type[1])
      end
    end
  end
  C.absolute_discriminant = abs_disc
  return true

end

#same function but for ray class groups over QQ

function discriminant_conductorQQ(O::NfOrd, C::ClassField, m::Int, bound::fmpz)
  
  n = degree(C)
  discr=fmpz(1)
  mp = pseudo_inv(C.quotientmap) * C.rayclassgroupmap
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
        q,mq=quo(G, GrpAbFinGenElem[el], false)
        ap-= order(q)
      end
      discr*=p^ap
      if discr>bound
        @vprint :AbExt 2 "too large\n"
        return false
      else
        abs_disc[p]=ap
      end
    else
      ap=n*v
      pow=Int(p)^Int(v)
      el = R(1)
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
            ap-=order(quo(G,GrpAbFinGenElem[el], false)[1])
          else
            for k=0:v-2      
              el=mp\ideal(O,Int((b*s*R(s1)^(p^k)+a*pow).data))
              ap-=order(quo(G, GrpAbFinGenElem[el], false)[1])
              @hassert :AbExt 1 ap>0
            end
          end
          if gcd(n,p-1)==1
            ap-=order(quo(G, GrpAbFinGenElem[mp\(ideal(O,fmpz((b*s*R(s1)+a*pow).data)))], false)[1])
          else
            x=_unit_grp_residue_field_mod_n(Int(p),n)[1]
            el1=mp\ideal(O,Int((R(x)*b*s+a*pow).data))
            ap-=order(quo(G, GrpAbFinGenElem[mp\(ideal(O,Int((b*s*R(s1)+a*pow).data))), el1], false)[1])
          end
        else
          s=divexact(m,2^v)
          d,a,b=gcdx(2^v,s)  
          el=0*G[1]
          for k=v-3:-1:0
            el=mp\ideal(O,Int((R(5)^(2^k)*b*s+a*2^v).data))
            ap-=order(quo(G, GrpAbFinGenElem[el], false)[1])
          end
          el1=mp\ideal(O,Int((R(-1)*b*s+a*p^v).data))
          ap-=2*order(quo(G, GrpAbFinGenElem[el, el1], false)[1])
        end
      end
      discr*=p^ap
      if discr>bound
        @vprint :AbExt 2 "too large\n"
        return false
      else
        abs_disc[p]=ap
      end
    end
  end
  C.absolute_discriminant=abs_disc
  return true
end

function discriminantQQ(O::NfOrd, C::ClassField, m::Int)
  
  discr=fmpz(1)
  n = degree(C)
  mp = pseudo_inv(C.quotientmap) * C.rayclassgroupmap
  G = domain(mp)
  
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
        q,mq=quo(G, GrpAbFinGenElem[el], false)
        ap-= order(q)
      end
      discr*=p^ap
      abs_disc[p]=ap
    else
      ap=n*v
      pow=Int(p)^Int(v)
      el = R(1)
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
            ap-=order(quo(G,GrpAbFinGenElem[el], false)[1])
          else
            for k=0:v-2      
              el=mp\ideal(O,Int((b*s*R(s1)^(p^k)+a*pow).data))
              ap-=order(quo(G, GrpAbFinGenElem[el], false)[1])
              @hassert :AbExt 1 ap>0
            end
          end
          if gcd(n,p-1)==1
            ap-=order(quo(G, GrpAbFinGenElem[mp\(ideal(O,fmpz((b*s*R(s1)+a*pow).data)))], false)[1])
          else
            x=_unit_grp_residue_field_mod_n(Int(p),n)[1]
            el1=mp\ideal(O,Int((R(x)*b*s+a*pow).data))
            ap-=order(quo(G, GrpAbFinGenElem[mp\(ideal(O,Int((b*s*R(s1)+a*pow).data))), el1], false)[1])
          end
        else
          s=divexact(m,2^v)
          d,a,b=gcdx(2^v,s)  
          el=0*G[1]
          for k=v-3:-1:0
            el=mp\ideal(O,Int((R(5)^(2^k)*b*s+a*2^v).data))
            ap-=order(quo(G, GrpAbFinGenElem[el], false)[1])
          end
          el1=mp\ideal(O,Int((R(-1)*b*s+a*p^v).data))
          ap-=2*order(quo(G, GrpAbFinGenElem[el, el1], false)[1])
        end
      end
      discr*=p^ap
      abs_disc[p]=ap
    end
  end
  C.absolute_discriminant=abs_disc
  return discr
end

###############################################################################
#
#  conductor function for abelian extension function
#
###############################################################################

#  For this function, we assume the base field to be normal over Q and the conductor of the extension we are considering to be invariant
#  Checks if the defining modulus is the conductor of C

function _is_conductor_min_normal(C::Hecke.ClassField; lwp::Dict{Int, Array{GrpAbFinGenElem, 1}} = Dict{Int, Array{GrpAbFinGenElem, 1}}())
  mr = C.rayclassgroupmap
  lp = mr.fact_mod
  if isempty(lp)
    return true
  end
  
  a = minimum(defining_modulus(mr)[1])
  mp = pseudo_inv(C.quotientmap) * mr 
  R = domain(mp)
  e = Int(exponent(C))
  O = base_ring(C)
  K = nf(O)
  lp = mr.fact_mod
  powers = mr.powers
  groups_and_maps = mr.groups_and_maps
  #first, tame part
  primes_done = fmpz[]
  for i = 1:length(powers)
    p, q = powers[i]
    if p.minimum in primes_done 
      continue
    end
    push!(primes_done, p.minimum)
    if p == q
      #The prime is tamely ramified
      v = groups_and_maps[i][2].tame[p]
      el = C.quotientmap(v.disc_log)
      if iszero(el)
        return false
      end
      continue
    end
    if haskey(lwp, Int(p.minimum))
      gens = lwp[Int(p.minimum)]
    else
      k = lp[p]-1
      pk = p^k
      pv = q
      gens_els = _1pluspk_1pluspk1(K, p, pk, pv, powers, a, e)
      gens = Vector{GrpAbFinGenElem}(undef, length(gens_els))
      for i = 1:length(gens)
        gens[i] = mr\(ideal(O, gens_els[i]))
      end
      lwp[Int(p.minimum)] = gens
    end
    iscond = false
    for i in 1:length(gens)
      if !iszero(C.quotientmap(gens[i]))
        iscond = true
        break
      end
    end
    if !iscond
      return false
    end
  end
  return true
end 

#
#  Same function as above, but in the assumption that the map comes from a ray class group over QQ
#

function _is_conductor_minQQ(C::Hecke.ClassField, n::Int)

  mr = C.rayclassgroupmap
  mp = pseudo_inv(C.quotientmap) * mr
  m = defining_modulus(mr)[1]
  mm = Int(minimum(m))
  lp = factor(mm)
  
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
