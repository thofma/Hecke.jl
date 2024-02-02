mutable struct MapRayClassGrpNew{T} #<: Hecke.Map{T, Hecke.AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}
  header::Hecke.MapHeader
  modulus_fin::Hecke.AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}
  modulus_inf::Vector{Hecke.InfPlc}

  function MapRayClassGrpNew{T}() where {T}
    return new{T}()
  end
end


#
# Modify the map of the class group so that the chosen representatives are coprime to m
#

function _coprime_ideal(C::FinGenAbGroup, mC::Map, m::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})

  O=parent(m).order
  K=nf(O)
  L=AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[]
  for i=1:ngens(C)
    a=mC(C[i])
    if is_coprime(a,m)
      push!(L,a)
    else
      J=inv(a)
      s=K(rand(J.num,5))//J.den  # Is the bound acceptable?
      I=s*a
      simplify(I)
      I = numerator(I)
      while !is_coprime(I,m)
        s=K(rand(J.num,5))//J.den
        I=s*a
        simplify(I)
        I = numerator(I)
      end
      push!(L,I)
    end
  end

  function exp(a::FinGenAbGroupElem)
    I=ideal(O,1)
    for i=1:ngens(C)
      if Int(a.coeff[1,i])!= 0
        I=I*(L[i]^(Int(a.coeff[1,i])))
      end
    end
    return I
  end

  mp=Hecke.MapClassGrp{typeof(C)}()
  mp.header=Hecke.MapHeader(C,Hecke.AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}(O),exp, mC.header.preimage)

  return mp

end


@doc raw"""
***
    ray_class_group(m::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, A::Vector{InfPlc}=[]) -> FinGenGrpAb, Map

> Compute the ray class group of the maximal order $L$ with respect to the modulus given by $m$ (the finite part) and the infinite primes of $A$
> and return an abstract group isomorphic to the ray class group with a map
> from the group to the ideals of $L$

"""
function ray_class_group_std(m::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, primes::Vector{InfPlc}=InfPlc[])

#
# We compute the group using the sequence U -> (O/m)^* _> Cl^m -> Cl -> 1
# First of all, we compute all these groups with their own maps
#
  O=parent(m).order
  K=nf(O)


  C, mC = class_group(O)
  mC=_coprime_ideal(C,mC,m)
  U, mU = unit_group(O)
  M, pi= quo(O,m)
  G, mG=unit_group(M)

  p = [ x for x in primes if isreal(x) ]
  if !isempty(p)
    H,lH,eH=_infinite_primes(O,p,m)
    T=G
    G=direct_product(G,H)
  end

#
# We start to construct the relation matrix
#
  RG=rels(G)
  RC=rels(C)

  A=vcat(RC, matrix_space(FlintZZ, ngens(G)+ngens(U), ncols(RC))())
  B=vcat(matrix_space(FlintZZ, ngens(C), ncols(RG))(), RG)
  B=vcat(B, matrix_space(FlintZZ, ngens(U) , ncols(RG))())

#
# We compute the relation matrix given by the image of the map U -> (O/m)^*
#
  for i=1:ngens(U)
    u=mU(U[i])
    a=(mG\(pi(u))).coeff
    if !isempty(primes)
      a=hcat(a, (lH(K(u))).coeff)
    end
    for j=1:ngens(G)
      B[i+nrows(RC)+nrows(RG),j]=a[1,j]
    end
  end

#
# We compute the relation between generators of Cl and (O/m)^* in Cl^m
#

  for i=1: ngens(C)
    if order(C[i])!=1
      y=Hecke.principal_generator((mC(C[i]))^(Int(order(C[i]))))
      b=(mG\(pi(y))).coeff
      if primes != []
        b=hcat(b, (lH(K(y))).coeff)
      end
      for j=1: ngens(G)
        B[i,j]=-b[1,j]
      end
    end
  end

  R=hcat(A,B)
  X=abelian_group(R)

#
# Discrete logarithm
#

  function disclog(J::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})

    !is_coprime(J,m) && error("The ideal is not coprime to the modulus")
    if isone(J)
      return X([0 for i=1:ngens(X)])
    else
      L=mC\J
      s=mC(L)
      I= J // s
      simplify(I)
      gamma=Hecke.principal_generator(I.num)
      y=((mG\(pi(gamma)))-(mG\(pi(O(I.den))))).coeff
      if primes!=[]
        z=lH(K(gamma))
        y=hcat(y, z.coeff)
      end
      return X(hcat(L.coeff,y))
    end
  end

#
# Exp map
#


  function expo(a::FinGenAbGroupElem)
    b=C([a.coeff[1,i] for i=1:ngens(C)])
    if isempty(primes)
      c=G([a.coeff[1,i] for i=ngens(C)+1:ngens(X)])
      return mC(b)*(pi\(mG(c)))
    else
      c=T([a.coeff[1,i] for i=ngens(C)+1:ngens(T)+ngens(C)])
      d=H([a.coeff[1,i] for i=ngens(T)+ngens(C)+1: ngens(X)])
      el=pi\(mG(c))
      # I need to modify $el$ so that it has the correct sign at the embeddings contained in primes
      vect=(lH(K(el))).coeff
      if vect==d.coeff
        return el*mC(b)
      else
        correction=O(1)
        for i=1:ngens(H)
          if d.coeff[1,i]==1
            correction=correction*eH(H[i])
          end
        end
        while vect!=d.coeff
          el=el+correction
          vect=(lH(K(el))).coeff
        end
        return el*mC(b)
      end
    end
  end

  mp=MapRayClassGrpNew{typeof(X)}()
  mp.header = Hecke.MapHeader(X, Hecke.AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}(O), expo, disclog)
  mp.modulus_fin=m
  mp.modulus_inf=p

  return X, mp

end


########################################################
#
#  Ray Class Group - p-part
#
########################################################
function ray_class_group_p_part(p::Integer, m::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, inf_plc::Vector{InfPlc}=InfPlc[])

  O=parent(m).order
  K=nf(O)
  Q,pi=quo(O,m)
  G, mG, lp = Hecke._mult_grp(Q,p)
  C, mC = class_group(O)
  Hecke._assure_princ_gen(mC)

  if p==2
    pr = [ x for x in inf_plc if isreal(x) ]
    if !isempty(pr)
      H,eH,lH=Hecke._infinite_primes(O,pr,m)
      T=G
      G =Hecke.direct_product(G,H)
    end
  end

  valclassp=Int(p^(valuation(order(C[ngens(C)]),p)))
  nonppartclass=div(order(C[ngens(C)]),valclassp)

  if valclassp==1 && order(G)==1
    return Hecke.empty_ray_class(m)
  end

  C, mC, vect = Hecke._class_group_mod_n(C,mC,valclassp)
  U, mU = unit_group_fac_elem(O)
  exp_class, Kel = Hecke._elements_to_coprime_ideal(C,mC,m)

  if order(G)==1
    return Hecke.class_as_ray_class(C,mC,exp_class,m)
  end

  n=ideal(O,1)
  for (q,vq) in lp
    n*=q^vq
  end

#
# We start to construct the relation matrix
#

  expo=exponent(G)
  inverse_d=gcdx(nonppartclass,expo)[2]

  R=zero_matrix(FlintZZ, ngens(C)+ngens(U)+ngens(G), ngens(C)+ngens(G))
  for i=1:ngens(C)
    R[i,i]=C.snf[i]
  end
  if is_snf(G)
    for i=1:ngens(G)
      R[i+ngens(C),i+ngens(C)]=G.snf[i]
    end
  else
    for i=1:ngens(G)
      R[i+ngens(C),i+ngens(C)]=G.rels[i,i]
    end
  end

#
# We compute the relation matrix given by the image of the map U -> (O/m)^*
#

  @assert is_snf(U)
  @vprintln :RayFacElem 1 "Collecting elements to be evaluated; first, units"
  evals = Hecke.AbsSimpleNumFieldOrderQuoRingElem[]
  tobeeval = FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}[]
  if gcd(U.snf[1],p)!=1
    if U.snf[1]==2
      push!(evals,Q(-1))
    else
      push!(tobeeval, mU(U[1]))
    end
  else
    push!(evals, Q(1))
  end
  append!(tobeeval,[mU(U[i]) for i=2:ngens(U)])

  @vprintln :RayFacElem 1 "then principal ideal generators"
  for i=1:ngens(C)
    @vtime :RayFacElem 1 push!(tobeeval, mC.princ_gens[i][2]*Kel[i])
  end

  @vprint :RayFacElem 1 "Time for elements evaluation: "
  ev,quots,idemps= Hecke.fac_elems_eval(O,Q,tobeeval,lp,expo)
  @vtime :RayFacElem 1 append!(evals, ev)
  @vprintln :RayFacElem 1 ""

  for i=1:ngens(U)
    @vprintln :RayFacElem 1 "Disclog of unit $i"
    a=(mG\(evals[i])).coeff
    if p==2 && !isempty(pr)
      if i==1
        a=hcat(a, matrix(FlintZZ,1,length(pr), [1 for i in pr]))
      else
        b=lH(tobeeval[length(tobeeval)-ngens(C)-ngens(U)+i])
        a=hcat(a, b.coeff)
      end
    end
    for j=1:ngens(G)
      R[i+ngens(G)+ngens(C),ngens(C)+j]=a[1,j]
    end
  end

#
# We compute the relation between generators of Cl and (O/m)^* in Cl^m
#

  for i=1: ngens(C)
    @vprintln :RayFacElem 1 "Disclog of class group element $i"
    invn=gcdx(vect[i], C.snf[i])[2]
    a=((mG\(evals[i+ngens(U)]))*invn).coeff
    if p==2 && !isempty(pr)
      b=lH(tobeeval[length(tobeeval)-ngens(C)+i])
      a=hcat(a, b.coeff)
    end
    for j=1: ngens(G)
      R[i,ngens(C)+j]=-a[1,j]
    end
  end

  X=abelian_group(R)


#
# Discrete logarithm
#

  function disclog(J::FacElem)
    a= X([0 for i=1:ngens(X)])
    for (f,k) in J.fac
      a+=k*disclog(f)
    end
    return a
  end

  function disclog(J::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
    if isone(J)
      return X([0 for i=1:ngens(X)])
    else
      L=mC\J
      s=exp_class(L)
      I=J* inv(s)
      I=I^Int(nonppartclass)
      z=Hecke.principal_generator_fac_elem(I)
      el=Hecke._fac_elem_evaluation(O, Q, quots, idemps, z, lp, expo)
      y=((mG\pi(el))*inverse_d).coeff
      if p==2 && !isempty(pr)
        b=lH(z)
        y=hcat(y, b.coeff)
      end
      return X(hcat(L.coeff,y))
    end
  end

#
# Exp map
#

  function expon(a::FinGenAbGroupElem)
    b=C([a.coeff[1,i] for i=1:ngens(C)])
    if p!=2 || isempty(pr)
      c=G([a.coeff[1,i] for i=ngens(C)+1:ngens(X)])
      return exp_class(b)*ideal(O,pi\(mG(c)))
    else
      c=T([a.coeff[1,i] for i=ngens(C)+1:ngens(T)+ngens(C)])
      d=H([a.coeff[1,i] for i=ngens(T)+ngens(C)+1: ngens(X)])
      el=pi\(mG(c))
      # I need to modify $el$ so that it has the correct sign at the embeddings contained in primes
      vect=(lH(K(el))).coeff
      if vect==d.coeff
        return exp_class(b)*ideal(O,el)
      else
        correction=eH(d)
        while vect!=d.coeff
          el=el+correction
          vect=(lH(K(el))).coeff
        end
        return exp_class(b)*ideal(O,el)
      end
    end
  end

  mp=Hecke.MapRayClassGrpNew{typeof(X)}()
  mp.header = Hecke.MapHeader(X, FacElemMon(parent(m)) , expon, disclog)
  mp.modulus_fin=n
  mp.modulus_inf=inf_plc
  mp.fact_mod=lp
  mp.tame_mult_grp=mG.tame
  mp.wild_mult_grp=mG.wild
  mp.defining_modulus = (m, inf_plc)

  return X,mp
end

