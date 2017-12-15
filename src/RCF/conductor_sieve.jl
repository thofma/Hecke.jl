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
    end
  end
  if wild && isdefined(mr, :wild_mult_grp)
    wld=mr.wild_mult_grp
    for (p,v) in wld
      mr.wild_mult_grp[p]=(make_positive(v[1],a),v[2],v[3])
    end
  
  end
end

function make_positive(x::NfOrdElem, a::Int)
 
  els=conjugates_arb(x)
  m=1
  for i=1:length(els)
    if isreal(els[1])
      y=BigFloat(midpoint(real(els[i]/a)))
      if y>0
        continue
      else
        m=max(m,1-ceil(Int,y))
      end
    end
  end
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
  d=degree(O)
  p=2
  b1=Int(root(bound,d))
  ram_primes=collect(keys(factor(O.disc).fac))
  sort!(ram_primes)
  filter!(x -> x!=p ,ram_primes)
  cond_list=squarefree_up_to(b1, coprime_to=vcat(ram_primes,p))

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

  cond_listnew=Set(cond_list)
  l=length(cond_list)
  for (el,norm) in extra_list
    for i=1:l
      if fmpz(cond_list[i])^d*norm>bound
        continue
      end
      push!(cond_listnew, cond_list[i]*el)
    end
  end

  return cond_listnew
  
end


function quadratic_normal_real_extensions(O::NfOrd, bound::fmpz;
                                     absolute_discriminant_bound::fmpz = fmpz(-1),
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
  S = prime_ideals_up_to(O, max(1000,100*clog(discriminant(O),10)^2))
  
  Aut=Hecke.automorphisms(K)
  @assert length(Aut) == degree(K)
  gens = Hecke.small_generating_set(Aut)

  #Getting conductors
  conductors=tame_conductors_degree_2(O,bound)
  @vprint :QuadraticExt "Number of conductors: $(length(conductors)) \n"
  fields=[]
  
  #Now, the big loop
  for (i, k) in enumerate(conductors)
    println("Left: $(length(conductors) - i)")
    @vtime :QuadraticExt 2 r,mr=ray_class_group(O,2,k)
    mr.prime_ideal_cache = S
    @vtime :QuadraticExt 2 act=_act_on_ray_class(mr,gens)
    @vtime :QuadraticExt 2 ls=stable_subgroups(r,[2],act, op=(x, y) -> quo(x, y, false)[2])
    totally_positive_generators(mr,k)
    for s in ls
      C=ray_class_field(mr*inv(s))
      if Hecke._is_conductor_min_normal(C,k)
        L = number_field(C)
        if absolute_galois_group != :all
          autabs = absolute_automorphism_group(C, gens)
          G = generic_group(autabs, *)
          if absolute_galois_group == :_16T7
            if isisomorphic_to_16T7(G)
              @vprint :QuadraticExt 1 "I found a field with Galois group 16T7 (C_2 x Q_8)"
              @vtime :QuadraticExt 1 push!(fields, L)
            end
          elseif absolute_galois_group == :_8T5
            if isisomorphic_to_8T5(G)
              @vprint :QuadraticExt 1 "I found a field with Galois group 8T5 (Q_8)"
              @vtime :QuadraticExt 1 push!(fields, L)
            end
          else
            error("Group not supported (yet)")
          end
        else
          @vtime :QuadraticExt 1 push!(fields, L)
        end
      end
    end
  end
  return fields

end

##########################################################################################################
#
#  Functions for conductors
#
##########################################################################################################


function squarefree_for_conductors(O::NfOrd, n::Int, deg::Int ; coprime_to::Array{fmpz,1}=fmpz[])
  
  sqf= trues(n)
  primes= trues(n)
  
  #remove primes that can be wildly ramified or
  #that are ramified in the base field
  for x in coprime_to
    t=Int(x)
    while t<= n
      sqf[t]=false
      primes[t]=false
      t+=Int(x)
    end
  end
  
  #sieving procedure
  
  if !(2 in coprime_to)
    dt=prime_decomposition_type(O,2)
    if gcd(2^dt[1][1]-1, deg)==1
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
        j=i
        while j<= n
         primes[j]=false
         sqf[j]=false
         j+=i
        end
      else 
        j=i
        while j<= n
          primes[j]=false
          j+=i
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
        j=i
        while j<= n
         sqf[j]=false
         j+=i
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
    if gcd(nq-1,n)==1
      continue
    end
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

  list=Tuple{Int, fmpz}[(1,fmpz(1))]
  for q in ram_primes
    tr=prime_decomposition_type(O,Int(q))
    f=tr[1][1]
    nq=fmpz(q)^f
    if gcd(nq-1,n)==1
      continue
    end
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
    nel=fmpz(el)^d
    for i=1:l
      w=list[i][2]*nel
      if w>bound
        continue
      end
      push!(list, (list[i][1]*el, w))
    end
  end

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
    sq=fmpz(q)^(divexact(degree(O),lp[1][2]))
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
  final_list=Set(Tuple{Int, Dict{NfOrdIdl, Int}}[])
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


###########################################################################################################
#
#  Tamely ramified abelian extensions
#
###########################################################################################################

function abelian_tame_extensions_Q(O::NfOrd, gtype::Array{Int,1}, bound::fmpz)
  
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
    @vtime :QuadraticExt 1 r,mr=ray_class_group(O,expo,k,Dict{NfOrdIdl, Int}(),inf_plc)
    if !_are_there_subs(r,gtype)
      continue
    end
    @vtime :QuadraticExt 1 ls=subgroups(r, quotype=gtype, fun= (x, y) -> quo(x, y, false)[2])
    totally_positive_generators(mr,k)
    for s in ls
      C=ray_class_field(mr*inv(s))
      println("\n Checking conductor")
      if Hecke._is_conductor_min_normal(C,k) && discriminant_conductor(O,C,k,mr,bound,n)
        println("\n New Field!")
        @vtime :QuadraticExt 1 push!(fields,number_field(C))
      end
    end
    println("\n")
  end
  return fields
end

function abelian_tame_extensions(O::FlintIntegerRing, gtype::Array{Int,1}, bound::fmpz)
  Qx, x = PolynomialRing(FlintQQ, "x")
  K, a = NumberField(x - 1, "a")
  OK = maximal_order(K)
  
  fields = abelian_tame_extensions_Q(OK, gtype, bound)
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
  S = prime_ideals_up_to(O, max(1000,100*clog(discriminant(O),10)^2))
  
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
    @vtime :QuadraticExt 1 r,mr=ray_class_group(O,expo,k,Dict{NfOrdIdl, Int}(), real_plc)
    mr.prime_ideal_cache = S
    println("\n Computing action ")
    @vtime :QuadraticExt 1 act=_act_on_ray_class(mr,gens)
    println("\n Searching for subgroups ")
    @vtime :QuadraticExt 1 ls=stable_subgroups(r, gtype, act, op=(x, y) -> quo(x, y, false)[2])
    totally_positive_generators(mr,k)
    for s in ls
      C=ray_class_field(mr*inv(s))
      println("\n Checking conductor")
      if Hecke._is_conductor_min_normal(C,k) && discriminant_conductor(O,C,k,mr,bound,n)
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



function abelian_normal_extensions(O::NfOrd, gtype::Array{Int,1}, bound::fmpz)

  K=nf(O)
  inf_plc=real_places(K)
  n=prod(gtype)
  d=degree(O)
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
  fields=NfRel_ns[]
  
  #Now, the big loop
  for (i, k) in enumerate(l_conductors)
    println("Conductor: $k ")
    println("Left: $(length(l_conductors) - i)")
    @vtime :QuadraticExt 1 r,mr=ray_class_group(O,expo,k[1], k[2],inf_plc)
    mr.prime_ideal_cache = S
    println("\n Computing action ")
    @vtime :QuadraticExt 1 act=_act_on_ray_class(mr,gens)
    println("\n Searching for subgroups ")
    @vtime :QuadraticExt 1 ls=stable_subgroups(r,gtype,act, op=(x, y) -> quo(x, y, false)[2])
    a=_min_wild(k[2])*k[1]
    totally_positive_generators(mr,a)
    for s in ls
      C=ray_class_field(mr*inv(s))
      println("\n Checking conductor")
      if Hecke._is_conductor_min_normal(C,a) && Hecke.discriminant_conductor(O,C,a,mr,bound,n)
        println("\n New Field!")
        @vtime :QuadraticExt 1 push!(fields,number_field(C))
      end
    end
    println("\n")
  end
  return fields

end

function abelian_normal_extension_Q(gtype::Array{Int,1},bound::fmpz)

  Qx, x = PolynomialRing(FlintQQ, "x")
  K, a = NumberField(x - 1, "a")
  OK = maximal_order(K)
  
  inf_plc=real_places(K)
  n=prod(gtype)
  expo=lcm(gtype)
  
  l_conductors=conductorsQ(bound, n)
  fields=[]
  
  #Now, the big loop
  for (i, k) in enumerate(l_conductors)
    println("Conductor: $k ")
    println("Left: $(length(l_conductors) - i)")
    @vtime :QuadraticExt 1 r,mr=ray_class_group(O,expo,k[1], k[2], inf_plc)
    @vtime :QuadraticExt 1 ls=subgroups(r,quotype=gtype, fun=(x, y) -> quo(x, y, false)[2])
    a=_min_wild(k[2])*k[1]
    totally_positive_generators(mr,a)
    for s in ls
      C=ray_class_field(mr*inv(s))
      println("\n Checking conductor")
      if Hecke._is_conductor_min_normal(C,a) && Hecke.discriminant_conductor(O,C,a,mr,bound,n)
        println("\n New Field!")
        @vtime :QuadraticExt 1 push!(fields,number_field(C))
      end
    end
    println("\n")
  end
end

#######################################################################################
#
#  Functions to compute the relative discriminant of a class field
#
#######################################################################################

function discriminant_conductor(O::NfOrd, C::ClassField, a::Int, mr::MapRayClassGrp, bound::fmpz, n::Int)
  
 
  lp=mr.fact_mod
  if isempty(lp)
    return true
  end

  K=nf(O)
  relative_disc=Dict{NfOrdIdl,Int}()
  abs_disc=Dict{fmpz,fmpz}()
  discr=fmpz(1)
  mp=C.mq
  R=domain(mp)
  
  #first, tamely ramified part
  tmg=mr.tame_mult_grp
  primes_done=fmpz[]
  for p in keys(tmg) 
    if minimum(p) in primes_done || haskey(mr.wild_mult_grp, p)
      continue
    end
    ap=n
    push!(primes_done, minimum(p))
    if isprime(n)
      ap-=1
    else
      el=mp\ideal(O,tmg[p][1]) #The generator is totally positive, we modified it before
      q,mq=quo(R,[el])
      ap-= order(q)
    end
    qw=divexact(degree(O),prime_decomposition_type(O,Int(minimum(p)))[1][2])*ap
    discr*=fmpz(minimum(p))^qw
    if discr>bound
      return false
    else
      abs_disc[minimum(p)]=qw
      for q in keys(tmg)
        if minimum(q)==minimum(p) 
          relative_disc[q]=ap
        end
      end
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
          gens=_1pluspk_1pluspk1(K, p, pk, pv, lp, prime_power, a)
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
      if discr>bound
        return false
      else
        abs_disc[minimum(p)]=td[1][1]*length(td)*ap
        for q in keys(tmg)
          if minimum(q)==minimum(p) 
            relative_disc[q]=ap
          end
        end
      end
    end
  end
  C.relative_discriminant=relative_disc
  C.absolute_discriminant=abs_disc
  return true

end

################################################################################
#
#  Quadratic Extensions of Q
#
################################################################################

function quadratic_extensions(bound::Int; tame::Bool=false, real::Bool=false)

  
  Qx,x=PolynomialRing(FlintZZ, "x")
  sqf=squarefree_up_to(bound);
  if !real
    sqf= vcat(sqf[2:end], Int[-i for i in sqf])
  else 
    deleteat!(sqf,1)
  end
  if tame
    filter!( x -> mod(x,4)==1, sqf)
    return ( NumberField(x^2-x+divexact(1-i,4))[1] for i in sqf)
  end
  final_list=Int[]
  for i=1:length(sqf)
    if sqf[i]*4< bound
      push!(final_list,sqf[i])
      continue
    end
    if mod(sqf[i],4)==1
      push!(final_list,sqf[i])
    end
  end
  return ( mod(i,4)!=1 ? NumberField(x^2-i)[1] : NumberField(x^2-x+divexact(1-i,4))[1] for i in final_list)
end

################################################################################
#
#  C2 x C2 extensions of Q
#
################################################################################

function C22_extensions(bound::Int)
  
  
  Qx,x=PolynomialRing(FlintZZ, "x")
  K,_=NumberField(x-1)
  Kx,x=PolynomialRing(K,"x")

  b1=ceil(Int,sqrt(bound))
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
  b=sqrt(b1)
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
  
  return (_ext(Kx,x,i-poszero,j-poszero) for i=1:n for j=i+1:n if pairs[i,j])
  
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
  Kx,x=PolynomialRing(K,"x")

  b1=floor(Int,sqrt(bound))
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
  b=sqrt(b1)
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
#  Dihedral group Dn with n odd
#
################################################################################

function Dn_extensions(n::Int, absolute_bound::fmpz; totally_real::Bool=false, tame::Bool=false)

  if mod(n,2)==0
    error("Not yet implemented")
  end
  
  bound_quadratic= Int(root(absolute_bound, n))
  list_quad=quadratic_extensions(bound_quadratic, tame=tame, real=totally_real)
  fields=NfRel_ns[]
  autos=Vector{NfRel_nsToNfRel_nsMor}[]
  fac=factor(n).fac
  for K in list_quad
    
    println("Field: $K")
    O=maximal_order(K)
    D=abs(discriminant(O))
    if D^n>absolute_bound
      continue
    end
    bo = ceil(Rational{BigInt}(absolute_bound//D^n))
    bound = FlintZZ(fmpq(bo))
   
    _,mC=class_group(O)
    allow_cache!(mC)
    S = prime_ideals_up_to(O, max(1000,100*clog(D,10)^2))

    gens=Hecke.automorphisms(K)
    a=gen(K)
    if gens[1](a)==a
      deleteat!(gens,1)
    else
      deleteat!(gens,2)
    end
    
    inf_plc=InfPlc[]
    if !totally_real
      inf_plc=real_places(K)
    end
      
    #Getting conductors
    if tame
      l_conductor=[(k,Dict{NfOrdIdl,Int}()) for k in conductors_tame(O,n,bound)]
    else
      l_conductors=conductors(O,n,bound)
    end
    @vprint :QuadraticExt "Number of conductors: $(length(l_conductors)) \n"
  
    #Now, the big loop
    for (i, k) in enumerate(l_conductors)
      r,mr=ray_class_group(O,n,k[1], k[2], inf_plc)
      if !_are_there_subs(r,[n])
        continue
      end
      mr.prime_ideal_cache = S
      println(k)
      act=_act_on_ray_class(mr,gens)
      ls=stable_subgroups(r,[n],act, op=(x, y) -> quo(x, y, false)[2])
      a=_min_wild(k[2])*k[1]
      if !totally_real
        totally_positive_generators(mr,a)
      end
      for s in ls
        if _trivial_action(s,act,fac,n)
          continue
        end
        C=ray_class_field(mr*inv(s))
        if Hecke._is_conductor_min_normal(C,a) 
          if Hecke.discriminant_conductor(O,C,a,mr,bound,n)
            println("\n New Field!")
            @vtime :QuadraticExt 1 push!(fields,number_field(C))
            #push!(autos,absolute_automorphism_group(C,gens))
          end
        end
      end
    end
    
  end
  
  return fields, autos
  
end

function _trivial_action(s::GrpAbFinGenMap, act::Array{GrpAbFinGenMap,1}, fac::Dict{fmpz,Int}, n::Int)

  @assert length(act)==1
  S=codomain(s)
  T,mT=snf(S)
  @assert T.snf[1]==n
  @assert ngens(T)==1
  new_el=mT\(s(act[1](s\mT(T[1]))))
  for (k,s) in fac
    if mod(new_el[1],k^s)==1
      return true
    end
  end
  return false
  
end

###############################################################################
#
#  C3 x D5 extensions
#
###############################################################################


function C3xD5_extensions(absolute_bound::fmpz)

  n=15
  bound_quadratic= Int(root(absolute_bound, 15))
  list_quad=quadratic_extensions(bound_quadratic)
  fields=NfRel_ns[]
  autos=[]
  fac=factor(15).fac
  for K in list_quad
    
    println("Field: $K")
    O=maximal_order(K)
    D=abs(discriminant(O))
    if D^15>absolute_bound
      continue
    end
    bo = ceil(Rational{BigInt}(absolute_bound//D^n))
    bound = FlintZZ(fmpq(bo))
   
    _,mC=class_group(O)
    allow_cache!(mC)
    S = prime_ideals_up_to(O, max(1000,100*clog(D,10)^2))

    gens=Hecke.automorphisms(K)
    a=gen(K)
    if gens[1](a)==a
      deleteat!(gens,1)
    else
      deleteat!(gens,2)
    end
    
    inf_plc=real_places(K)
      
    #Getting conductors
    l_conductors=conductors(O,n,bound)
    @vprint :QuadraticExt "Number of conductors: $(length(l_conductors)) \n"
  
    #Now, the big loop
    for (i, k) in enumerate(l_conductors)
      r,mr=ray_class_group(O,n,k[1], k[2], inf_plc)
      if !_are_there_subs(r,[n])
        continue
      end
      mr.prime_ideal_cache = S
      act=_act_on_ray_class(mr,gens)
      ls=stable_subgroups(r,[n],act, op=(x, y) -> quo(x, y, false)[2])
      a=_min_wild(k[2])*k[1]
      totally_positive_generators(mr,a)
      for s in ls
        if !_right_action(s,act)
          continue
        end
        C=ray_class_field(mr*inv(s))
        if Hecke._is_conductor_min_normal(C,a) && Hecke.discriminant_conductor(O,C,a,mr,bound,n)
          println("\n New Field!")
          @vtime :QuadraticExt 1 push!(fields,number_field(C))
          push!(autos,absolute_automorphism_group(C,gens))
        end
      end
    end
    
  end
  
  return fields, autos
  
end

function _right_action(s::GrpAbFinGenMap, act::Array{GrpAbFinGenMap,1})

  @assert length(act)==1
  S=codomain(s)
  T,mT=snf(S)
  @assert T.snf[1]==15
  @assert ngens(T)==1
  new_el=mT\(s(act[1](s\mT(T[1]))))
  if mod(new_el[1],5)==1
    return false
  end
  @assert 3*new_el!=3*T[1]
  if mod(new_el[1],3)!=1
    return false
  end
  @assert 5*new_el==5*T[1]
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
