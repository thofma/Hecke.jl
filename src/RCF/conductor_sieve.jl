##############################################################################
#
#  Sieves for primes and squarefree numbers
#
##############################################################################

function squarefree_up_to(n::Int; coprime_to::Array{Int,1}=[])

  list= trues(n)
  for x in coprime_to
    t=x
    while t<= bound 
      list[t]=false
      t+=x
    end
  end
  i=2
  b=sqrt(n)
  while i<=b
    if list[i]
      j=i^2
      if !list[j]
        i+=1
        continue
      else 
        list[j]=false
        t=2*j
        while t<= n
          list[t]=false
          t+=j
        end
      end
    end
    i+=1
  end
  return Int[i for i=1:n if list[i]]

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
#  Conductors detection function
#
###########################################################################

function _squarefree_up_to_bitarray(n::Int; coprime_to::Array{fmpz,1}=[])

  list= trues(n)
  for x in coprime_to
    t=x
    while t<= n 
      list[Int(t)]=false
      t+=x
    end
  end
  i=2
  b=sqrt(n)
  while i<=b
    if list[i]
      j=i^2
      if !list[j]
        i+=1
        continue
      else 
        list[j]=false
        t=2*j
        while t<= n
          list[t]=false
          t+=j
        end
      end
    end
    i+=1
  end
  return list

end

function primes_for_conductors(O::NfOrd, n::Int, p::Int)
  
  list= trues(n)
  list[1]=false
  
  i=2
  b=sqrt(n)
  
  #case p=2 is easier
  if p==2
    s=2
    while s<=n
      list[s]=false
      s+=2
    end
    i=3
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
  
  #general case
  s=4
  while s<=n
    list[s]=false
    s+=2
  end
  i=3
  while i<=b
    if list[i]
      j=3*i
      s=2*i
      while j<= n
        list[j]=false
        j+=s
      end
      if divisible(fmpz(i-1),p)
        i+=1
        continue
      end
      lp=prime_decomposition_type(O,i)
      f=lp[1][1]
      if !divisible(fmpz(i)^f-1, p)
        list[i]=false
      end
    end
    i+=1
  end
  while i<=n && list[i] 
    if divisible(fmpz(i-1),p)
      i+=1
      continue
    end
    lp=prime_decomposition_type(O,i)
    f=lp[1][1]
    if !divisible(fmpz(i)^f-1, p)
      list[i]=false
    end
    i+=1
  end
  return Int[i for i=1:n if list[i]]
  
end

function conductors_cyclic(O::NfOrd, ram_primes::Array{Int,1}, p::Int, bound::Int)

  K=nf(O)
  n=degree(O)
  
  r=p-1
  b1=Int(root(fmpz(bound),Int(n*r)))
  
  prime_list=primes_for_conductors(O,b1,p)
  filter!(x -> !(x in ram_primes), prime_list)
  @show length(prime_list)

  candidates=Tuple{Array{Int, 1}, Int}[(Int[1], 1)]
  exp=n*r
  for q in prime_list
    nq=q^exp
    l=length(candidates)
    for i =1:l
      k=nq*candidates[i][2]
      if k>bound  
        continue
      end
      # If we insert the new element so that th array is sorted, 
      # we can break at this point if k>bound.
      push!(candidates, (vcat(candidates[i][1], q), k))
    end
  end
  return candidates
  #
  # now we take care of the possible wild ramification
  #
  
  lp=prime_decomposition(O,p)
  f=divexact(degree(O), length(lp)*lp[1][2])
  np=p^(f*(p-1))
  l=length(candidates)
  for i=1:l
    k=np^2*candidates[i][4]
    s=2
    while k<=bound
      x=Tuple{NfOrdIdl, Int}[]
      for i=1:length(lp)
        push!(x, (lp[i][1], s))
      end
      push!(candidates, [candidates[i][1], x, inf_plc, k])
      k*=np
      s+=1
    end
  end
  
  #
  #  infinite places
  #
  if p==2
    inf_plc=real_places(K)
    if !isempty(inf_plc)
      l=length(candidates)
      resize!(candidates, length(candidates)*2)
      for i=1:l
        x=copy(candidates[i])
        x[3]=inf_plc
        candidates[l+i]=x
      end
    end
  end
  return candidates
  
end

function conductors(O::NfOrd, ram_primes::Array{Int,1}, n::Int, bound::Int)

  if isprime(fmpz(n))
    return conductors_cyclic(O,ram_primes,n, bound)
  end
  
  #
  #  First, conductors coprime to the ramified primes and to the 
  #  degree of the extension we are searching for.
  # 

  wild_ram=collect(keys(factor(fmpz(n)).fac))
  K=nf(O)
  inf_plc=InfPlc[]
  if mod(n,2)==0
    inf_plc=real_places(K)
  end
  b1=Int(root(fmpz(bound),Int(degree(O)*(minimum(wild_ram)-1)))) #Maybe it is n-1 instead of minimun(wild_ram)-1. Check.
  coprime_to=cat(1,ram_primes, wild_ram)
  list= _squarefree_up_to_bitarray(b1, coprime_to=coprime_to)
  prime_list=primes_up_to(b1)

  for p in prime_list
    if (p in coprime_to) || gcd(fmpz(p-1),n)!=1
      continue
    end
    lp=prime_decomposition_type(O,p)
    f=lp[1][1]
    if gcd(n,p^f-1)==1
      s=p
      while s<=b1
        list[s]=false
        s+=p
      end 
    end
  end
  
  candidates=[]
  for i=1:b1
    if list[i]
      fac=keys(factor(fmpz(i)).fac)
      el=Dict{NfOrdIdl, Int}()
      for p in fac
        lp=prime_decomposition(O,p)
        for x in lp
          el[x[1]]=1
        end
      end
      D=Dict{NfOrdIdl,Int}
      push!(candidates, [el,D, i^degree(O)])    
    end
  end
  
  #
  #  We now need to take care of the ramified primes and of wild ramification
  #

  for p in ram_primes
    if !(p in wild_ram)
      lp=prime_decomposition_type(O,p)
      f=lp[1][1]
      if gcd(n,p^f-1)==1
        continue
      end
      lp=prime_decomposition(O,p)
      l1=length(candidates)
      for i=1:l1
        ex=p^(divexact(degree(O),lp[1][2]))
        if candidates[i][3]*ex>bound
          continue
        end
        x=copy(candidates[i][1])
        for j=1:length(lp)
          x[lp[j][1]]=1
        end
        push!(candidates, [x, Dict{NfOrdIdl, Int},candidates[i][3]*ex])
      end
    end  
  end

  for p in wild_ram
    if p in ram_primes
      lp=prime_decomposition(O,p)
      f=divexact(length(lp),lp[1][2])
      if gcd(n,p^f-1)==1
        l1=length(candidates)
        for i=1:l1
          ex=p^(divexact(degree(O),lp[1][2]))
          i=0
          while candidates[i][3]*ex^i<=bound
            x=copy(candidates[i][1])
          for j=1:length(lp)
            x[lp[j][1]]=1
          end
          push!(candidates, [x, Dict{NfOrdIdl, Int},candidates[i][3]*ex])
          end
          x=copy(candidates[i][1])
          for j=1:length(lp)
            x[lp[j][1]]=1
          end
          push!(candidates, [x, Dict{NfOrdIdl, Int},candidates[i][3]*ex])
        end
      else
        l1=length(candidates)
        for i=1:l1
          ex=p^(divexact(degree(O),lp[1][2]))
          if candidates[i][3]*ex>bound
            continue
          end
          x=copy(candidates[i][1])
          for j=1:length(lp)
            x[lp[j][1]]=1
          end
          push!(candidates, [x, Dict{NfOrdIdl, Int},candidates[i][3]*ex])
        end
      end
    else
      
    end
  end

end

################################################################################
#
#   First stupid iterator
#
################################################################################

function _it_single(x, A, B)
  return Iterators.flatten(( x for x in [((push!(copy(a), x), x*b) for (a, b) in A if x*b <= B), (a for a in A)]))
end

function squarefree_numbers_from_primes(P, B)
  sort!(P, rev=true)
  @assert P[1] <= B
  A = [ (Int[1], 1) ]
  p = pop!(P)
  it = _it_single(p, A, B)
  while length(P) > 0
    p = pop!(P)
    it = _it_single(p, it, B)
  end
  return it
end
