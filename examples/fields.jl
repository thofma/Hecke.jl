###############################################################################
#
#  Quadratic Extensions
#
###############################################################################

function quadratic_extensions(bound::Int; tame::Bool=false, real::Bool=false, complex::Bool=false, u::UnitRange{Int}=-1:0)

  @assert !(real && complex)
  Qx,x=PolynomialRing(FlintQQ, "x")
  sqf = Hecke.squarefree_up_to(bound);
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
  Hecke.allow_cache!(mC)
  cgrp=false
  if gcd(C.snf[end],3)!=1
    cgrp=true
    S = prime_ideals_up_to(O, max(100,100*clog(D,10)^2))
  end
  gens=Hecke.automorphisms(K)
  gens=small_generating_set(gens)
  
  #Getting conductors
  bound = div(absolute_bound, D^3)
  l_conductors=Hecke.conductors(O,[3], bound)
  @vprint :AbExt "Number of conductors: $(length(l_conductors)) \n"

  res = []
  
  #Now, the big loop
  for k in l_conductors
    r,mr=Hecke.ray_class_group_quo(O,3,k[1], k[2])
    if cgrp
      mr.prime_ideal_cache = S
    end
    act=Hecke.induce_action(mr,gens)
    ls=stable_subgroups(r,act, op=(x, y) -> quo(x, y, false)[2], quotype = [3])
    Hecke.totally_positive_generators(mr)
    for s in ls
      if _trivial_action(s,act,3)
        continue
      end
      C=ray_class_field(mr, s)
      if Hecke._is_conductor_min_normal(C) && Hecke.discriminant_conductor(C, bound)
        @vprint :AbExt 1 "New Field"
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

  D = abs(discriminant(O))
  ram_primes = collect(keys(factor(O.disc).fac))
  coprime_to = cat(ram_primes, fmpz(5), dims = 1)
  sort!(ram_primes)
  b=root(bound_non_normal, 2)
  b1=root(div(b,D), 2)
  #
  # First, conductors for tamely ramified extensions
  #
  
  sqf_list= Hecke.squarefree_for_conductors(O, Int(b1), 5, coprime_to=coprime_to)
  l=length(sqf_list)
  #
  # now, we have to multiply the obtained conductors by proper powers of wildly ramified ideals. 
  #
  lp=prime_decomposition(O, 5)
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

function D5_extensions(absolute_bound::fmpz, f::IOStream)
  
  l = Hecke.quadratic_extensions(Int(root(absolute_bound, 2)))
  return D5_extensions(absolute_bound, l)

end



#The input are the absolute bound for the non-normal extension of degree 5 and the list of the quadratic fields
function D5_extensions(absolute_bound::fmpz, quad_fields)
  
  len=length(quad_fields)
  z = []
  for K in quad_fields
    len-=1
    
     @vprint :AbExt 1 "\nDoing: $(K.pol)\n"   
     @vprint :AbExt 1 "Remaining Fields: $(len)\n"
    append!(z, single_D5_extensions(absolute_bound, K))
  end
  return z
end

function D5_extensions(absolute_bound::fmpz, quad_fields, f::IOStream)
  
  len=length(quad_fields)
  for K in quad_fields
    len-=1
    
    @vprint :AbExt 1 "Field: $K\n"
    @vprint :AbExt 1 "Remaining Fields: $(len)\n"
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
  Hecke.allow_cache!(mC)
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
  #@vprint :AbExt "Number of conductors: $(length(l_conductors)) \n"
  
  #Now, the big loop
  for k in l_conductors
    r,mr=Hecke.ray_class_group_quo(O,5,k[1], k[2])
    if cgrp
      mr.prime_ideal_cache = S
    end
    act=Hecke.induce_action(mr,gens)
    ls=stable_subgroups(r, act, op=(x, y) -> quo(x, y, false)[2], quotype = [5])
    for s in ls
      if _trivial_action(s,act,5)
        continue
      end
      C = ray_class_field(mr, s)
      if Hecke._is_conductor_min_normal(C)
        @vprint :AbExt 1 "New Field\n"
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
  pol = Hecke.absolute_minpoly(pr_el)
  if degree(pol)==15
    return pol
  else
    pr_el=x*(auto(x))
    return Hecke.absolute_minpoly(pr_el)
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
  coprime_to=cat(ram_primes, wild_ram, dims = 1)
  sort!(ram_primes)
  m=minimum(wild_ram)
  k=divexact(n,m)
  b1=Int(root(fmpz(bound),Int(2*(minimum(wild_ram)-1)*k))) 

  #
  # First, conductors for tamely ramified extensions
  #

  list= Hecke.squarefree_for_conductors(O, b1, n, coprime_to=coprime_to)
  
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
  fieldslist=Tuple{NfRel_ns,  Array{Hecke.NfRel_nsToNfRel_nsMor{nf_elem},1},fmpz, Array{fmpz,1}}[]
  
  for K in list_quad
    len-=1
    
    @vprint :AbExt 1 "Field: $K\n"
    @vprint :AbExt 1 "Fields left: $len\n"
    O=maximal_order(K)
    D=abs(discriminant(O))
    if D^n>absolute_bound
      continue
    end
    bound = div(absolute_bound, abs(D)^n)
   
    C,mC=class_group(O)
    Hecke.allow_cache!(mC)
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

    @vprint :AbExt "Number of conductors: $(length(l_conductors)) \n"
  
    #Now, the big loop
    for k in l_conductors
      r,mr=Hecke.ray_class_group_quo(O,n,k[1], k[2])
      if !Hecke._are_there_subs(r,[n])
        continue
      end
      if cgrp
        mr.prime_ideal_cache = S
      end
      act=Hecke.induce_action(mr,gens)
      ls=stable_subgroups(r, act, op=(x, y) -> quo(x, y, false)[2], quotype = [n])
      a=Hecke._min_wild(k[2])*k[1]
      for s in ls
        if _trivial_action(s,act,n)
          continue
        end
        C=ray_class_field(mr, s)
        if Hecke._is_conductor_min_normal(C) && Hecke.discriminant_conductor(C, bound)
          @vprint :AbExt 1 "\n New Field!\n"
          L=number_field(C)
          ram_primes=Set(collect(keys(factor(a).fac)))
          for p in keys(factor(O.disc).fac)
            push!(ram_primes, p)
          end
          aut=Hecke.absolute_automorphism_group(C,gens)
          push!(fieldslist,(L,aut, evaluate(FacElem(C.absolute_discriminant)), collect(ram_primes)))
        end
      end
    end
    
  end
  
  return fieldslist

end

function _trivial_action(s::Hecke.GrpAbFinGenMap, act::Array{Hecke.GrpAbFinGenMap,1}, n::Int)

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
    
    @vprint :AbExt 1 "Field: $K\n"
    O=maximal_order(K)
    D=abs(discriminant(O))

    bound5=root(non_normal_bound,3)
    bound = non_normal_bound^2
   
    C,mC=class_group(O)
    Hecke.allow_cache!(mC)
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
    l_conductors=Hecke.conductors(O, [15], bound)
    @vprint :AbExt "Number of conductors: $(length(l_conductors)) \n"
  
    #Now, the big loop
    for (i, k) in enumerate(l_conductors)
      r,mr=Hecke.ray_class_group_quo(O,15,k[1], k[2])
      if !Hecke._are_there_subs(r,[15])
        continue
      end
      if cgrp
        mr.prime_ideal_cache = S
      end
      act=Hecke.induce_action(mr,gens)
      ls=stable_subgroups(r,act, quotype = [15], op=(x, y) -> quo(x, y, false)[2])
      for s in ls
        if !_right_actionD5C3(s,act)
          continue
        end
        C=ray_class_field(mr, s)
        if Hecke._is_conductor_min_normal(C) && Hecke.discriminant_conductor(C, bound)
          @vprint :AbExt "New Field \n"
          #Before computing the field, I check if the discriminant of the $D_5$ extension is compatible
          s1=codomain(s)
          q1,mq1=quo(s1,5, false)
          C1=ray_class_field(mr, Hecke._compose(s, mq1))
          cond=conductor(C1)[1]
          condint=minimum(cond)
          if condint^4*D^2>bound5
            @vprint :AbExt "Too large (without computing it) :( \n"
            continue
          end
          L=number_field(C)
          ram_primes=Set(collect(keys(factor(a).fac)))
          for p in keys(factor(O.disc).fac)
            push!(ram_primes, p)
          end
          auto=Hecke.extend_aut(C,gens[1])
          T,mT=simple_extension(L)
          x=mT(gen(T))
          if (auto*auto)(x)!=x
            auto=auto^3
          end
          pol=Hecke.absolute_minpoly(x+auto(x))
          if degree(pol)!=15
            pol=Hecke.absolute_minpoly(x*(auto(x)))
          end
          K,_=NumberField(pol, cached= false)
          if _is_discriminant_lower(K, collect(ram_primes), non_normal_bound)
            @vprint :AbExt "The field is: $pol \n"
            push!(fieldslist, (number_field(pol)[1], collect(ram_primes)))
          end
        end
      end
    end
    
  end
  
  return fieldslist
  
end


function _right_actionD5C3(s::Hecke.GrpAbFinGenMap, act::Array{Hecke.GrpAbFinGenMap,1})

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
    
    @vprint :AbExt 1 "Field: $K\n"
    O=maximal_order(K)
    D=abs(discriminant(O))
    bound = non_normal_bound^2
   
    bound3=root(non_normal_bound, 5)
    C,mC=class_group(O)
    Hecke.allow_cache!(mC)
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
    l_conductors=Hecke.conductors(O,[15],bound)
    @vprint :AbExt "Number of conductors: $(length(l_conductors)) \n"
  
    #Now, the big loop
    for (i, k) in enumerate(l_conductors)
      r,mr=Hecke.ray_class_group_quo(O,15,k[1], k[2])
      if !Hecke._are_there_subs(r,[15])
        continue
      end
      if cgrp
        mr.prime_ideal_cache = S
      end
      act=Hecke.induce_action(mr,gens)
      ls=stable_subgroups(r,act, op=(x, y) -> quo(x, y, false)[2],quotype = [15])
      a=Hecke._min_wild(k[2])*k[1]
      for s in ls
        if !_right_actionC5S3(s,act)
          continue
        end
        C=ray_class_field(mr, s)
        if Hecke._is_conductor_min_normal(C) && Hecke.discriminant_conductor(C, bound)
          @vprint :AbExt 1  "\n New Field!\n"
          #Before computing the field, I check if the discriminant of the $S_3$ extension is compatible
          s1=codomain(s)
          q1,mq1=quo(s1,3, false)
          C1=ray_class_field(mr, _compose(s, mq1))
          cond=conductor(C1)[1]
          condint=minimum(cond)
          if condint^2*D>bound3
            @vprint :AbExt "Too large :( \n"
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
          pol=Hecke.absolute_minpoly(x+auto(x))
          if degree(pol)!=15
            pol=Hecke.absolute_minpoly(x*(auto(x)))
          end
          K=number_field(pol, cached=false)[1]
          if _is_discriminant_lower(K, collect(ram_primes), non_normal_bound)
            push!(fieldslist, (K, collect(ram_primes)))
            @vprint :AbExt "New candidate! \n"
            @vprint :AbExt "$(pol) \n"
          else
            @vprint :AbExt "Too large :( \n"
          end
        end
      end
    end
  end
  
  return fieldslist
  
end

function _right_actionC5S3(s::Hecke.GrpAbFinGenMap, act::Array{Hecke.GrpAbFinGenMap,1})

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
    Hecke.allow_cache!(mC)
    cgrp=false
    if gcd(C.snf[end],3)!=1
      cgrp=true
      S = prime_ideals_up_to(O, max(100,12*clog(D,10)^2))
    end
    Aut=Hecke.automorphisms(K)
    @assert length(Aut)==degree(O) #The field is normal over Q
    gens = Hecke.small_generating_set(Aut)
  
    #Getting conductors
    l_conductors=Hecke.conductors(O,[9],bound, false)
    @vprint :AbExt 1 "Conductors: $(length(l_conductors))\n"
    #Now, the big loop
    for (i, k) in enumerate(l_conductors)
      @vprint :AbExt 1 "Doing $i\n"
      r,mr=Hecke.ray_class_group_quo(O,9,k[1], k[2])
      if !Hecke._are_there_subs(r,[9])
        continue
      end
      if cgrp
        mr.prime_ideal_cache = S
      end
      @vprint :AbExt 1 "Computing the action\n"
      act=Hecke.induce_action(mr,gens)
      @vprint :AbExt 1 "Computing subgroups\n"
      ls=stable_subgroups(r, act, op=(x, y) -> quo(x, y, false)[2], quotype = [9])
      for s in ls
        if _trivial_action(s,act,9)
          continue
        end
        C=ray_class_field(mr, s)
        if Hecke._is_conductor_min_normal(C) && Hecke.discriminant_conductor(C, bound) && evaluate(FacElem(C.absolute_discriminant)) <= absolute_bound
          absolute_bound=evaluate(FacElem(C.absolute_discriminant))
          @vprint :AbExt 1 "New Field with discriminant $absolute_bound"
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
  @vprint :AbExt 1 "Doing $(K)"
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
  pol=Hecke.absolute_minpoly(pr_el)
  if degree(pol)==15
    return number_field(pol)[1]
  else
    pr_el=x*(autos[i](x))
    return number_field(Hecke.absolute_minpoly(pr_el))[1]
  end
  
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


