##########################################################################################################
#
#  Conductors for normal extensions of normal fields
#
##########################################################################################################

function tame_conductors_degree_2(O::NfOrd, bound::fmpz; unramified_outside::Vector{fmpz} = fmpz[])
  K = nf(O)
  d = degree(O)
  b1 = Int(root(bound,d))
  ram_primes = ramified_primes(O)
  sort!(ram_primes)
  filter!(x -> x!=2, ram_primes)
  list = squarefree_up_to(b1, coprime_to = vcat(ram_primes,2), prime_base = unramified_outside)

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

function squarefree_for_conductors(O::NfOrd, n::Int, deg::Int; coprime_to::Vector{fmpz}=fmpz[], prime_base::Vector{fmpz} = fmpz[])

  sqf = trues(n)
  primes = trues(n)


  #remove primes that can be wildly ramified or
  #that are ramified in the base field
  for x in coprime_to
    if x > n
      continue
    end
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
      j = 2
      while j <= n
        @inbounds sqf[j] = false
        @inbounds primes[j] = false
        j += 2
      end
    else
      i=2
      s=4
      while s <= n
        @inbounds primes[s] = false
        s+=2
      end
      s=4
      while s <= n
        @inbounds sqf[s] = false
        s+=4
      end
    end
  end
  i = 3
  b = isqrt(n)
  while i <= b
    if primes[i]
      if gcd(i-1, deg) != 1 && (!isempty(prime_base) && (i in prime_base))
        j = i
        while j <= n
          @inbounds primes[j] = false
          j += i
        end
        j = i^2
        t = j
        while j <= n
          @inbounds sqf[j] = false
          j += t
        end
      else
        dt = prime_decomposition_type(O, i)
        if gcd(deg, i^dt[1][1]-1) == 1 || (!isempty(prime_base) && !(i in prime_base))
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
      if gcd(deg, i^dt[1][1]-1) == 1 || (!isempty(prime_base) && !(i in prime_base))
        @inbounds sqf[i]=false
        j=i
        while j <= n
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


function conductors_tame(O::NfOrd, n::Int, bound::fmpz; unramified_outside::Vector{fmpz} = fmpz[])

  if n == 2
    return tame_conductors_degree_2(O, bound, unramified_outside = unramified_outside)
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
  sort!(ram_primes)
  coprime_to = vcat(ram_primes, wild_ram)
  m = minimum(wild_ram)
  k = divexact(n, m)
  e = Int((m-1)*k)
  b1 = Int(root(bound, degree(O)*e))
  list = squarefree_for_conductors(O, b1, n, coprime_to = coprime_to, prime_base = unramified_outside)

  extra_list = Tuple{Int, fmpz}[(1, fmpz(1))]
  for q in ram_primes
    if !isempty(unramified_outside) && !(q in unramified_outside)
      continue
    end
    tr = prime_decomposition_type(O, Int(q))
    f = tr[1][1]
    nq = q^f
    if is_coprime(nq - 1, fmpz(n))
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

function conductors(O::NfOrd, a::Vector{Int}, bound::fmpz, tame::Bool=false; unramified_outside::Vector{fmpz} = fmpz[])

  #Careful: I am assuming that a is in snf!
  K = nf(O)
  d = degree(O)
  n = prod(a)
  expo = a[end]
  wild_ram = collect(keys(factor(n).fac))

  #
  # First, conductors for tamely ramified extensions
  #
  bound_tame = root(bound, divexact(n, expo))
  list = conductors_tame(O, expo, bound_tame, unramified_outside = unramified_outside)

  if tame
    reverse!(list)
    return Tuple{Int, Dict{NfOrdIdl, Int}}[(x[1], Dict{NfOrdIdl, Int}()) for x in list]
  end
  #
  # now, we have to multiply the obtained conductors by proper powers of wildly ramified ideals.
  #
  wild_list = Tuple{Int, Dict{NfOrdIdl, Int}, fmpz}[(1, Dict{NfOrdIdl, Int}(), fmpz(1))]
  for q in wild_ram
    if !isempty(unramified_outside) && !(q in unramified_outside)
      continue
    end
    lp = prime_decomposition(O, Int(q))
    fq = divexact(d, lp[1][2]*length(lp))
    l = length(wild_list)
    sq = q^(divexact(d,lp[1][2])) #norm of the squarefree part of the integer q
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
    obound = fmpz(flog(boundsubext, sq))

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

function squarefree_for_conductorsQQ(O::NfOrd, n::Int, a::Vector{Int}; coprime_to::Vector{fmpz}=fmpz[], unramified_outside::Vector{fmpz} = fmpz[])

  G = map(Int, snf(abelian_group(a))[1].snf)
  sqf= trues(n)
  primes= trues(n)
  deg = G[end]
  #remove primes that can be wildly ramified
  for x in coprime_to
    if x > n
      continue
    end
    el = Int(x)
    t=el
    while t <= n
      @inbounds sqf[t] = false
      @inbounds primes[t] = false
      t += el
    end
  end

  single = Vector{Int}()
  push!(single, 1)
  multiple = Vector{Int}()

  #sieving procedure
  #First, I can remove all the multiples of 2
  if !(2 in coprime_to)
    i=2
    while i<=length(sqf)
      @inbounds sqf[i] = false
      i+=2
    end
  end

  i=3
  b = isqrt(n)
  while i <= b
    if primes[i]
      if gcd(deg, i-1) == 1 || (!isempty(unramified_outside) && !(i in unramified_outside))
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
      if gcd(deg,i-1) == 1 || (!isempty(unramified_outside) && !(i in unramified_outside))
        @inbounds primes[i] = false
        @inbounds sqf[i]=false
        j = i
        while j <= n
         @inbounds sqf[j]=false
         j += i
        end
      end
    end
    i += 2
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
  elseif !is_prime(deg)
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



function conductors_tameQQ(O::NfOrd, a::Vector{Int}, bound::fmpz; unramified_outside::Vector{fmpz} = fmpz[])

  #
  #  First, conductors coprime to the ramified primes and to the
  #  degree of the extension we are searching for.
  #
  n = prod(a)
  wild_ram = collect(keys(factor(fmpz(n)).fac))
  m = minimum(wild_ram)
  k = divexact(n, m)
  b1 = Int(root(fmpz(bound),Int((m-1)*k)))

  return squarefree_for_conductorsQQ(O, b1, a, coprime_to = wild_ram, unramified_outside = unramified_outside)

end

function conductorsQQ(O::NfOrd, a::Vector{Int}, bound::fmpz, tame::Bool=false; unramified_outside::Vector{fmpz} = fmpz[])

  K = nf(O)
  d = degree(O)
  n = prod(a)
  expo = a[end]
  wild_ram = collect(keys(factor(fmpz(n)).fac))

  #
  # First, conductors for tamely ramified extensions
  #

  single, multiple = conductors_tameQQ(O, a, bound, unramified_outside = unramified_outside)

  if tame
    return multiple
  end
  #
  # now, we have to multiply the obtained conductors by proper powers of wildly ramified ideals.
  #
  wild_list=Tuple{Int, Int, fmpz}[(1, 1, 1)]
  for q in wild_ram
    if !isempty(unramified_outside) && !(q in unramified_outside)
      continue
    end
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

################################################################################
#
#  Conductors generic
#
################################################################################



function conductors_generic(K::AnticNumberField, gtype::Vector{Int}, absolute_bound::fmpz; only_tame::Bool = false)
  #I am assuming that gtype is in "SNF"
  conds_tame = conductors_generic_tame(K, gtype, absolute_bound)
  if only_tame
    return Dict{NfOrdIdl, Int}[(x[1], Dict{NfOrdIdl, Int}()) for x in conds_tame]
  end
  OK = maximal_order(K)
  wild = collect(keys(factor(gtype[end]).fac))
  n = prod(gtype)
  bound = div(absolute_bound, abs(discriminant(OK))^n)
  wild_primes = Vector{Tuple{NfOrdIdl, UnitRange{Int}}}()
  for p in wild
    lp = prime_decomposition(OK, p)
    for (P, v) in lp
      starting_power = 2
      ending_power = 2
      nP = norm(P)
      if nP > bound
        continue
      end
      gn = gcd(nP-1, gtype[end])
      if !isone(gn)
        starting_power = 1
      end
      vp = valuation(gtype[end], p)
      # First, we compute the bound coming from the bound on the discriminant
      boundsubext = root(bound, Int(divexact(n, p^vp))) #The bound on the norm of the discriminant on the subextension
                                                        # of order q^v
      #Bound coming from the bound on the discriminant
      obound = flog(boundsubext, nP)

      #Bound coming from the analysis on the different in a local extension
      nbound = p^vp + v * vp * p^vp - 1

      bound_max_ap = min(nbound, obound)  #bound on ap
      ending_power = Int(div(bound_max_ap, (p-1)*p^(vp-1)))
      if ending_power >= starting_power
        push!(wild_primes, (P, starting_power:ending_power))
      end
    end
  end
  #create now a sublist with just the wild ramified primes.
  conds_wild = Vector{Tuple{Dict{NfOrdIdl, Int}, fmpz}}()
  push!(conds_wild, (Dict{NfOrdIdl, Int}(), fmpz(1)))
  # For each p in wild_primes, p[2] describes the possible exponent
  # range. Of course, not every prime needs to appear, so we add
  # 0 to the list of possible exponents.
  it = cartesian_product_iterator(Array{Int}[push!(collect(x[2]), 0) for x in wild_primes], inplace = true)
  for I in it
    if all(x->x<2, I)
      # Exclude exponents (0, 0, ..., 0)
      # Note that all exponents are >= 2 by if they are nonzero
      continue
    end
    D = Dict{NfOrdIdl, Int}()
    nD = fmpz(1)
    for j = 1:length(I)
      if iszero(I[j])
        continue
      end
      P = wild_primes[j][1]
      nP = norm(P)
      p = minimum(P)
      vp = minimum([valuation(gtype[i], p) for i = 1:length(gtype)])
      nD *= nP^((p^vp-p^(vp-1))*I[j])
      if nD > bound
        break
      end
      D[P] = I[j]
    end
    if nD > bound
      continue
    end
    push!(conds_wild, (D, nD))
  end

  #Now, the final merge.
  conds = Vector{Dict{NfOrdIdl, Int}}()
  for i = 1:length(conds_wild)
    for j = 1:length(conds_tame)
      if conds_wild[i][2]*conds_tame[j][2] <= bound
        push!(conds, merge(conds_wild[i][1], conds_tame[j][1]))
      end
    end
  end
  return conds
end

function conductors_generic_tame(K::AnticNumberField, gtype::Vector{Int}, absolute_bound::fmpz)

  OK = maximal_order(K)
  n = prod(gtype)
  wild = collect(keys(factor(n).fac))
  pmin = Int(minimum(wild))
  bound = div(absolute_bound, abs(discriminant(OK))^n)
  lp = prime_ideals_up_to(OK, Int(root(bound, pmin-1)))
  filter!(x -> !(minimum(x, copy = false) in wild), lp)
  lf = Vector{Tuple{NfOrdIdl, fmpz}}()
  for P in lp
    nP = norm(P)
    gn = gcd(nP-1, gtype[end])
    if isone(gn)
      continue
    end
    fgn = factor(gn)
    k = minimum(keys(fgn.fac))
    kp, cpk = ppio(gtype[end], Int(k))
    dP = nP^(div(n, gtype[end])*(k-1)*cpk)
    if dP > bound
      continue
    end
    push!(lf, (P, dP))
  end
  #Now, I have to merge them.
  conds = Vector{Tuple{Dict{NfOrdIdl, Int}, fmpz}}()
  push!(conds, (Dict{NfOrdIdl, Int}(), fmpz(1)))
  if isempty(lf)
    return conds
  end
  for i = 1:length(lf)
    P = lf[i][1]
    dP = lf[i][2]
    indj = length(conds)
    new_conds = Vector{Tuple{Dict{NfOrdIdl, Int}, fmpz}}()
    for j = 1:indj
      Dd = dP*conds[j][2]
      if Dd > bound
        break
      end
      D = copy(conds[j][1])
      D[P] = 1
      push!(new_conds, (D, Dd))
    end
    for j = 1:length(new_conds)
      insert!(conds, searchsortedfirst(conds, new_conds[j], by = x -> x[2]), new_conds[j])
    end
  end
  return conds
end
