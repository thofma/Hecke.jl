add_verbose_scope(:QuadraticExt)


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
#  Abelian Extensions Interface
#
###########################################################################

#function abelian__normal_extensions(O::NfOrd, gtype::Array{Int,1}, )

###########################################################################
#
#  Some useful functions
#
###########################################################################

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

function divisors(n::Int)
 return collect(keys(factor(n).fac))
end

function absolute_automorphism_group(C::ClassField)
  L = number_field(C)
  K = base_field(C)
  autK = automorphisms(K)
  id = find_identity(autK, *)
  autK_gen = small_generating_set(autK, *, id)
  return absolute_automorphism_group(C, autK_gen)
end

function absolute_automorphism_group(C::ClassField, aut_gen_of_base_field)
  L = number_field(C)
  aut_L_rel = rel_auto(C)
  rel_extend = [ Hecke.extend_aut(C, a) for a in aut_gen_of_base_field ]
  rel_gens = vcat(aut_L_rel, rel_extend)
  id = find_identity(rel_gens, *)
  return closure(rel_gens, *, id)
end


###########################################################################
#
#  Cyclic extensions of degree 2
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


function quadratic_normal_extensions(O::NfOrd, bound::fmpz;
                                     absolute_discriminant_bound::fmpz = -1,
                                     absolute_galois_group::Symbol = :all)
  
  if absolute_discriminant_bound != -1
    bo = ceil(Rational{BigInt}(absolute_discriminant_bound//discriminant(O)^2))
    bound = FlintZZ(fmpq(bo))
    @assert absolute_discriminant_bound <= discriminant(O)^2 * bound
    @assert absolute_discriminant_bound > discriminant(O)^2 * (bound - 1)
  end

  @show bound

  K=nf(O)
  C,mC=class_group(O)
  allow_cache!(mC)
  S = prime_ideals_up_to(O, 100*clog(discriminant(O),10)^2)
  
  Aut=Hecke.automorphisms(K)
  @assert length(Aut) == degree(K)
  gens = Hecke.small_generating_set(Aut)

  #Getting conductors
  conductors=tame_conductors_degree_2(O,bound)
  @vprint :QuadraticExt "Number of conductors: $(length(conductors)) \n"
  fields=[]
  
  #Now, the big loop
  for (i, k) in enumerate(conductors)
    println("Conductor: $k ")
    println("Left: $(length(conductors) - i)")
    @vtime :QuadraticExt 1 r,mr=ray_class_group(O,2,k)
    mr.prime_ideal_cache = S
    println("\n Computing action ")
    @vtime :QuadraticExt 1 act=_act_on_ray_class(mr,gens)
    println("\n Searching for subgroups ")
    @vtime :QuadraticExt 1 ls=stable_subgroups(r,[2],act, op=(x, y) -> (quo(x, y, false)[2], sub(x,y,false)[2]))
    for s in ls
      C=ray_class_field(mr*inv(s[1]))
      C.norm_group=s[2]
      println("\n Computing fields")
      if Hecke._is_conductor_min_tame_normal(C, k)
        L = number_field(C)
        if absolute_galois_group != :all
          autabs = absolute_automorphism_group(C, gens)
          M = multiplication_table(autabs, *)
          if defines_group_isomorphic_to_16T7(M)
            @vtime :QuadraticExt 1 push!(fields, L)
          end
        else
          @vtime :QuadraticExt 1 push!(fields, L)
        end
      end
    end
    println("\n")
  end
  return fields

end


###########################################################################################################
#
#  Tamely ramified abelian extensions
#
###########################################################################################################

function squarefree_for_conductors(O::NfOrd, n::Int, deg::Int ; coprime_to::Array{fmpz,1}=fmpz[])
  
  sqf= trues(n)
  primes= trues(n)
  
  #remove primes that can be wildly ramified or
  #that are ramified in the base field
  for x in coprime_to
    t=x
    while t<= n
      sqf[Int(t)]=false
      primes[Int(t)]=false
      t+=x
    end
  end
  
  #sieving procedure
  
  if !(2 in coprime_to)
    dt=prime_decomposition_type(O,2)
    if gcd(2^dt[1][1], deg)==1
      j=2
      while j<=n
        sqf[j]=false
        primes[j]=false
        j+=2
      end
    else 
      i=2
      s=4
      while s<=n
        primes[s]=false
        s+=2
      end
      s=4
      while s<=n
        sqf[s]=false
        s+=4
      end
    end
  end
  i=3
  b=sqrt(n)
  while i<=b
    if primes[i]
      dt=prime_decomposition_type(O,i)
      if gcd(deg,i^dt[1][1]-1)==1
        primes[i]=false
        sqf[i]=false
        j=3*i
        s=2*i
        while j<= n
         primes[j]=false
         sqf[j]=false
         j+=s
        end
      else 
        j=3*i
        s=2*i
        while j<= n
          primes[j]=false
          j+=s
        end
        j=i^2
        t=2*j
        while j<= n
          sqf[j]=false
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
        sqf[i]=false
        j=3*i
        s=2*i
        while j<= n
         sqf[j]=false
         j+=s
        end
      end
    end
    i+=2
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

  K=nf(O)
  wild_ram=collect(keys(factor(fmpz(n)).fac))
  ram_primes=collect(keys(factor(O.disc).fac))
  if length(wild_ram)==1
    filter!(x -> !divisible(fmpz(n),x), ram_primes)
    coprime_to=cat(1,ram_primes, wild_ram)
  else
    coprime_to=ram_primes
  end
  sort!(ram_primes)
  m=minimum(wild_ram)
  k=divexact(n,m)
  b1=Int(root(fmpz(bound),Int(degree(O)*(minimum(wild_ram)-1)*k))) 
  
  list= squarefree_for_conductors(O, b1, n, coprime_to=coprime_to)
  println("$(length(list))")
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
  
  l=length(list)
  for (el,norm) in extra_list
    for i=1:l
      if list[i]^n*norm>bound
        continue
      end
      push!(list, list[i]*el)
    end
  end
  
  if degree(O)==1
    i=1
    while i<=length(list)
      if mod(list[i],4)==2
        deleteat!(list,i)
      else 
        i+=1
      end
    end
  end  
  return list
end

function abelian_extensions_Q(O::NfOrd, gtype::Array{Int,1}, bound::fmpz)
  
  K=nf(O)
  inf_plc= real_places(K)
  n=prod(gtype)
  expo=lcm(gtype)
  println("Computing the conductors ... ")
  conductors=conductors_tame(O,n,bound) 
  println("Done")
  fields=[]
  
  #Now, the big loop
  for (i, k) in enumerate(conductors)
    println("Conductor: $k ")
    println("Left: $(length(conductors) - i)")
    @vtime :QuadraticExt 1 r,mr=ray_class_group(O,expo,k)
    println("\n Searching for subgroups ")
    if !_are_there_subs(r,gtype)
      continue
    end
    @vtime :QuadraticExt 1 ls=subgroups(r, quotype=gtype, fun= (x, y) -> (quo(x, y, false)[2], sub(x,y,false)[2]))
    for s in ls
      C=ray_class_field(mr*inv(s[1]))
      C.norm_group=s[2]
      println("\n Checking conductor")
      if Hecke._is_conductor_min_tame_normal(C, k) 
         println("Checking discriminant")
        if discriminant_conductor(O,C,k,Dict{NfOrdIdl,Int}(),mr,inf_plc,bound,expo,n)
          println("\n New Field!")
          @vtime :QuadraticExt 1 push!(fields,number_field(C))
        end
      end
    end
    println("\n")
  end
  return fields
end

function abelian_normal_extensions(O::FlintIntegerRing, gtype::Array{Int,1}, bound::fmpz)
  Qx, x = PolynomialRing(FlintQQ, "x")
  K, a = NumberField(x - 1, "a")
  OK = maximal_order(K)
  
  fields = abelian_extensions_Q(OK, gtype, bound)
  return fields
end
  
# Bound= Norm of the discriminant of the upper extension
function abelian_normal_tame_extensions(O::NfOrd, gtype::Array{Int,1}, bound::fmpz)
  
  K=nf(O)
  real_plc=real_places(K)
  n=prod(gtype)
  expo=lcm(gtype)
  C,mC=class_group(O)
  allow_cache!(mC)
  S = prime_ideals_up_to(O, 100*clog(discriminant(O),10)^2)
  
  #
  # Getting a small set of generators
  # for the automorphisms group
  #
  Aut=Hecke.automorphisms(K)
  @assert length(Aut)==degree(O)
  gens = Hecke.small_generating_set(Aut)
  
  #Getting conductors
  conductors=conductors_tame(O,n,bound)

  @vprint :QuadraticExt "Number of conductors: $(length(conductors)) \n"
  fields=[]
  
  #Now, the big loop
  for (i, k) in enumerate(conductors)
    println("Conductor: $k ")
    println("Left: $(length(conductors) - i)")
    @vtime :QuadraticExt 1 r,mr=ray_class_group(O,expo,k)
    mr.prime_ideal_cache = S
    println("\n Computing action ")
    @vtime :QuadraticExt 1 act=_act_on_ray_class(mr,gens)
    println("\n Searching for subgroups ")
    @vtime :QuadraticExt 1 ls=stable_subgroups(r,gtype,act, op=(x, y) -> (quo(x, y, false)[2], sub(x,y,false)[2]) )
    for s in ls
      C=ray_class_field(mr*inv(s[1]))
      C.norm_group=s[2]
      if Hecke._is_conductor_min_tame_normal(C, k) && discriminant_conductor(O,C,k,Dict{NfOrdIdl,Int}(),mr,real_plc,bound,expo,n)
        println("\n New Field!")
        @vtime :QuadraticExt 1 push!(fields,number_field(C))
      end
    end
    println("\n")
  end
  return fields

end

##################################################################################################
#
#  Abelian extensions: All 
#
##################################################################################################


function conductors(O::NfOrd, n::Int, bound::fmpz)
  
  K=nf(O)
  d=degree(O)
  wild_ram=collect(keys(factor(fmpz(n)).fac))
  ram_primes=collect(keys(factor(O.disc).fac))
  if length(wild_ram)==1
    filter!(x -> !divisible(fmpz(n),x), ram_primes)
    coprime_to=cat(1,ram_primes, wild_ram)
  else
    coprime_to=ram_primes
  end
  sort!(ram_primes)
  m=minimum(wild_ram)
  k=divexact(n,m)
  b1=Int(root(fmpz(bound),Int(degree(O)*(minimum(wild_ram)-1)*k))) 

  #
  # First, conductors for tamely ramified extensions
  #
  
  sqf_list= squarefree_for_conductors(O, b1, n, coprime_to=coprime_to)

  list=Tuple{Int, Int}[(1,1)]
  for q in ram_primes
    tr=prime_decomposition_type(O,Int(q))
    f=tr[1][1]
    nq=Int(q)^f
    if nq> bound
      break
    end
    l=length(list)
    for i=1:l
      nn=list[i][2]*nq
      if nn> bound
        continue
      end
      push!(list, (list[i][1]*q, nn))
    end
  end

  
  l=length(list)
  for el in sqf_list
    nel=el^d
    for i=1:l
      if list[i][2]*nel>bound
        continue
      end
      push!(list, (list[i][1]*el, list[i][2]*nel))
    end
  end
  deleteat!(list,1)

  #
  # now, we have to multiply the obtained conductors by proper powers of wildly ramified ideals. 
  #
  wild_list=Tuple{Dict{NfOrdIdl, Int}, Int}[(Dict{NfOrdIdl, Int}(),1)]
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
    sq=q^(divexact(degree(O),lp[1][2]))
    bound_max_ap=clog(bound,sq) #bound on ap
    bound_max_exp=divexact(q*bound_max_ap, n*(q-1)) #bound on the exponent in the conductor
    for i=2:bound_max_exp
      d1=Dict{NfOrdIdl, Int}()
      for j=1:length(lp)
        d1[lp[j][1]]=i
      end
      nq= sq^i
      for s=1:l
        nn=nq*wild_list[s][2]
        if nn>bound
          continue
        end
        d2=merge(max, d1, wild_list[s][1]) 
        push!(wild_list, (d2, nn))
      end
    end
  end
  
  #the final list
  final_list=Tuple{Int, Dict{NfOrdIdl, Int}}[]
  for (el, nm) in list
    for (d,nm2) in wild_list
      if nm*nm2 > bound
        continue
      end
      push!(final_list, (el,d))
    end
  end
  return final_list
  
end



function abelian_normal_extensions(O::NfOrd, gtype::Array{Int,1}, bound::fmpz)

  K=nf(O)
  inf_plc=real_places(K)
  n=prod(gtype)
  expo=lcm(gtype)
  _,mC=class_group(O)
  allow_cache!(mC)
  S = prime_ideals_up_to(O, max(1000,100*clog(discriminant(O),10)^2))
  #
  # Getting a small set of generators
  # for the automorphisms group
  #
  Aut=Hecke.automorphisms(K)
  @assert length(Aut)==degree(O) #The field is normal over Q
  gens = Hecke.small_generating_set(Aut)
  
  #Getting conductors
  l_conductors=conductors(O,n,bound)
  @vprint :QuadraticExt "Number of conductors: $(length(l_conductors)) \n"
  fields=[]
  
  #Now, the big loop
  for (i, k) in enumerate(l_conductors)
    println("Conductor: $k ")
    println("Left: $(length(l_conductors) - i)")
    @vtime :QuadraticExt 1 r,mr=ray_class_group(O,expo,k[1], k[2])
    mr.prime_ideal_cache = S
    println("\n Computing action ")
    @vtime :QuadraticExt 1 act=_act_on_ray_class(mr,gens)
    println("\n Searching for subgroups ")
    @vtime :QuadraticExt 1 ls=stable_subgroups(r,gtype,act, op=(x, y) -> (quo(x, y, false)[2], sub(x,y,false)[2]))
    for s in ls
      C=ray_class_field(mr*inv(s[1]))
      C.norm_group=s[2]
      println("\n Checking conductor")
      if Hecke._is_conductor_min_normal(C, k[1], k[2]) 
        println("Right conductor; now checking discriminant")
        if Hecke.discriminant_conductor(O,C,k[1],k[2],mr,inf_plc,bound,expo,n)
          println("\n New Field!")
          @vtime :QuadraticExt 1 push!(fields,number_field(C))
        end
      end
    end
    println("\n")
  end
  return fields

end

function discriminant_conductor(O::NfOrd, C::ClassField, k::Int, wprimes::Dict{NfOrdIdl, Int}, mr::MapRayClassGrp, inf_plc::Array{InfPlc,1}, bound::fmpz, expo::Int, n::Int)
  
  
  #first naive fast check
  s=fmpz(k)^n
  lw=Set{Int}([minimum(p) for p in keys(wprimes)])
  if !isempty(lw)
    maxs=maximum(values(wprimes))
    for w in lw
      s*=fmpz(w)^(n^2*maxs)  
    end
  end
  if s<=bound
    return true
  end
  #now, conductor discriminant formula
  fac=collect(keys(factor(k).fac))
  lp=[prime_decomposition(O,q) for q in fac]
  discr=fmpz(1)
  
  #first, tamely ramified part
  for j=1:length(lp)
    d1=Dict{NfOrdIdl, Int}()
    for l=1:length(lp)
      if l!=j
        for (P,e) in lp[l]
          d1[P]=1
        end   
      else
        for s=2:length(lp[j])
          d1[lp[j][s][1]]=1
        end
      end
    end
    R,mR=ray_class_group(O, expo, mr, d1, wprimes, inf_plc)
    dlogs=GrpAbFinGenElem[mR(s) for s in C.small_gens]
    q,mq=quo(R,dlogs)
    ap= n-order(q)
    qw=fmpz(divexact(degree(O),lp[j][1][2])*ap)
    discr*=fmpz(fac[j])^qw
    if discr>bound
      return false
    end
  end
  
  #now, wild ramification
  d=Dict{NfOrdIdl,Int}()
  for (Q, e) in mr.fact_mod
    if e==1
      d[Q]=1
    end
  end
  for w in lw
    i=0
    wprimes_new=Dict{NfOrdIdl, Int}()
    I=ideal(O,1)
    for (P,e) in wprimes
      if minimum(P)==w
        if i==0
          i+=1
          if e>2
            wprimes_new[P]=e-1
          end
          I=P
        else
          wprimes_new[P]=e
        end
      else
        wprimes_new[P]=e
      end
    end
    ap=n*wprimes[I]
    R,mR=ray_class_group(O, expo, mr, d, wprimes_new, inf_plc)
    dlogs=GrpAbFinGenElem[mR(s) for s in C.small_gens]
    q,mq=quo(R,dlogs)
    ap-=order(q)
    if haskey(wprimes_new,I) 
      wprimes_new[I]-=1
      while wprimes_new[I]!=1
        R,mR=ray_class_group(O, expo, mr, d, wprimes_new, inf_plc)
        dlogs=GrpAbFinGenElem[mR(s) for s in C.small_gens]
        q,mq=quo(R,dlogs)
        ap-=order(q)
        wprimes_new[I]-=1
      end
    end  
    d1=Dict{NfOrdIdl, Int}()
    for (J,e) in d
      d1[J]=1
    end
    if gcd(norm(I)-1, expo)!=1
      d1[I]=1
    end
    Base.delete!(wprimes_new,I)
    R,mR=ray_class_group(O, expo, mr, d, wprimes_new, inf_plc)
    dlogs=GrpAbFinGenElem[mR(s) for s in C.small_gens]
    q,mq=quo(R,dlogs)
    ap-=order(q)
    if !haskey(d1,I)
      ap-=order(q)
    else 
      Base.delete!(wprimes_new,I)
      R,mR=ray_class_group(O, expo, mr, d, wprimes_new, inf_plc)
      dlogs=GrpAbFinGenElem[mR(s) for s in C.small_gens]
      q,mq=quo(R,dlogs)
      ap-=order(q)
    end
    td=prime_decomposition_type(O,Int(minimum(I)))
    np=minimum(I)^(td[1][2])
    discr*=fmpz(np)^ap
    if discr>bound
      return false
    end
  end 
  return true

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
