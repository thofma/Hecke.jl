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


function tame_conductors_degree_2(O::NfOrd, bound::fmpz)
 
  K=nf(O)
  n=degree(O)
  p=2
  b1=Int(root(bound,n))
  ram_primes=collect(keys(factor(abs(O.disc)).fac))
  sort!(ram_primes)
  filter!(x -> x!=p ,ram_primes)
  cond_list=squarefree_up_to(b1, coprime_to=vcat(ram_primes,p))
  extra_list=Tuple{Int, Int}[(1,1)]
  for q in ram_primes
    tr=prime_decomposition_type(O,Int(q))
    f=tr[1][1]
    nq=Int(q)^f
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
  deleteat!(extra_list,1)

  l=length(cond_list)
  for (el,norm) in extra_list
    for i=1:l
      if cond_list[i]^n*norm>bound
        continue
      end
      push!(cond_list, cond_list[i]*el)
    end
  end
  
  return cond_list
  
end

function tommy_ray_class_group(O::NfOrd, n_quo::Int, m::Int)
  
  K=nf(O)
  d1=Dict{NfOrdIdl, Int}()
  lp=factor(m)
  for q in keys(lp.fac)
    lq=prime_decomposition(O,q) 
    for (P,e) in lq
      d1[P]=1
    end   
  end
  return ray_class_group(n_quo, ideal(O,1), d1, Dict{NfOrdIdl,Int}(), real_places(K))
  
end


function quadratic_normal_extensions(O::NfOrd, bound::fmpz)
  
  K=nf(O)
  Aut=Hecke.automorphisms(K)
  conductors=tame_conductors_degree_2(O,bound)
  fields=[]
  for k in conductors
    r,mr=tommy_ray_class_group(O,2,k)
    act=_act_on_ray_class(mr,Aut)
    ls=stable_subgroups(r,[2],act, op=quo)
    for s in ls
      C=ray_class_field(mr*inv(s[2]))
      if conductor_min(C)==k
        push!(fields,number_field(C))
      end
    end
  end
  return fields

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
