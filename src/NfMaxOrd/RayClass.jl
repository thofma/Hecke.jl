
export iscoprime, ray_class_group, conductor, isconductor, norm_group

#
# Test if two ideals $I,J$ in a maximal order are coprime.
#
doc"""
***
    iscoprime(I::NfMaxOrdIdl, J::NfMaxOrdIdl) -> Bool
> Test if ideals $I,J$ are coprime

"""

function iscoprime(I::NfMaxOrdIdl, J::NfMaxOrdIdl)

  if gcd(minimum(I), minimum(J))==1
    return true
  else 
    return isone(I+J)
  end

end 

#
# Modify the map of the class group so that the chosen representatives are coprime to m
# 

function _coprime_ideal(C::FinGenGrpAb, mC::Map, m::NfMaxOrdIdl)
 
  O=parent(m).order
  K=nf(O)
  L=NfMaxOrdIdl[]
  for i=1:ngens(C)
    a=mC(C[i])
    if iscoprime(a,m)
      push!(L,a)
    else  
      J=inv(a)
      s=K(rand(J.num,5))//J.den  # Is the bound acceptable?
      I=s*a
      simplify(I)
      I = num(I)
      while !iscoprime(I,m)
        s=K(rand(J.num,5))//J.den  
        I=s*a
        simplify(I)
        I = num(I)
      end
      push!(L,I)
    end
  end
  
  function exp(a::FinGenGrpAbElem)
    I=ideal(O,1)
    for i=1:ngens(C)
      if Int(a.coeff[1,i])!= 0
        I=I*(L[i]^(Int(a.coeff[1,i])))
      end
    end
    return I
  end
  
  mp=Hecke.MapClassGrp{typeof(C)}()
  mp.header=Hecke.MapHeader(C,Hecke.NfMaxOrdIdlSet(O),exp, mC.header.preimage)
  
  return mp
 
end 

#
# Function that finds the generators of the infinite part
#

function _infinite_primes(O::NfMaxOrd, p::Array{InfPlc,1}, m::NfMaxOrdIdl)

  K=O.nf
  S=DiagonalGroup([2 for i=1:length(p)])

  function logS(x::Array{Int, 1})
    return S([x[i] > 0 ? 0 : 1 for i=1:length(x)])
  end

  s = typeof(S[1])[]
  g = elem_type(O)[]
  u, mu = sub(S, s)
  b = 10
  cnt = 0
  while true
    a = rand(m, b)
    emb=signs(K(a),p)
    t=S([emb[x]==1 ? 0 : 1 for x in collect(keys(emb))])
    if !Hecke.haspreimage(mu, t)[1]
      push!(s, t)
      push!(g, a)
      u, mu = sub(S, s)
      if order(u) == order(S)
        break
      end
    else
      cnt += 1
      if cnt > 100
        b *= 2
        cnt = 0
      end
    end
  end
  hS = Hecke.FinGenGrpAbMap(S, S, vcat([x.coeff for x=s]))   # Change of coordinates so that the canonical basis elements are mapped to the elements found above
  r = elem_type(O)[]
  for i=1:length(p)
    y = haspreimage(hS,S[i])[2]
    push!(r, prod([g[i]^Int(y[i]) for i=1:length(p)]))
  end
  
  function exp(A::FinGenGrpAbElem)
    s=O(1)
    for i=1:length(p)
      if Int(A.coeff[1,i]) == 1
        s=s*r[i]
      end 
    end
    return s
  end 

  function log(B::nf_elem)
    emb=Hecke.signs(B,p)
    return S([emb[x]==1 ? 0 : 1 for x in collect(keys(emb))])
  end 
  
  return S,log,exp

end



doc"""
***
    direct_product(G::FinGenGrpAb, H::FinGenGrpAb) -> FinGenGrpAb
> Return the abelian group $G\times H$

"""

function direct_product(G::FinGenGrpAb, H::FinGenGrpAb) 

  A=vcat(rels(G), MatrixSpace(FlintZZ, rows(rels(H)), cols(rels(G)))())
  B=vcat(MatrixSpace(FlintZZ, rows(rels(G)), cols(rels(H)))(),rels(H))
 
  return AbelianGroup(hcat(A,B))
  
end 

type MapRayClassGrp{T} <: Map{T, Hecke.NfMaxOrdIdlSet}
  header::Hecke.MapHeader
  modulus_fin::NfMaxOrdIdl
  modulus_inf::Array{InfPlc,1}
  
  function MapRayClassGrp()
    return new()
  end
end

doc"""
***
    ray_class_group(m::NfMaxOrdIdl, A::Array{Int64,1} (optional)) -> FinGenGrpAb, Map
> Compute the ray class group of the maximal order $L$ with respect to the modulus given by $m$ (the finite part) and the infinite primes of $A$
  and return an abstract group isomorphic to the ray class group with a map 
  from the group to the ideals of $L$

"""
function ray_class_group(m::NfMaxOrdIdl, primes::Array{InfPlc,1}=InfPlc[])

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

  A=vcat(RC, MatrixSpace(FlintZZ, ngens(G)+ngens(U), cols(RC))())
  B=vcat(MatrixSpace(FlintZZ, ngens(C), cols(RG))(), RG)
  B=vcat(B, MatrixSpace(FlintZZ, ngens(U) , cols(RG))())
 
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
      B[i+rows(RC)+rows(RG),j]=a[1,j]
    end
  end 

#
# We compute the relation between generators of Cl and (O/m)^* in Cl^m
#

  for i=1: ngens(C)
    if order(C[i])!=1
      y=Hecke.principal_gen((mC(C[i]))^(Int(order(C[i]))))
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
  X=AbelianGroup(R)

#
# Discrete logarithm
#

  function disclog(J::NfMaxOrdIdl)

    if isone(J)
      return X([0 for i=1:ngens(X)])
    else
      L=mC\J
      s=mC(L)
      I= J // s
      simplify(I)
      gamma=Hecke.principal_gen(I.num)
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


  function expo(a::FinGenGrpAbElem)
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
        println(signs(K(correction),primes))
        while vect!=d.coeff
          el=el+correction
          vect=(lH(K(el))).coeff
        end
        return el*mC(b)
      end 
    end
  end 

  mp=MapRayClassGrp{typeof(X)}()
  mp.header = Hecke.MapHeader(X, Hecke.NfMaxOrdIdlSet(O), expo, disclog)
  mp.modulus_fin=m
  mp.modulus_inf=p
 
  return X, mp
  
end


Hecke.elem_type(A::Hecke.NfMaxOrdIdlSet) = NfMaxOrdIdl


doc"""
***

  function conductor(S::FinGenGrpAb, mS::FinGenGrpAbMap, R::FinGenGrpAb, mR::MapRayClassGrp)

  Return the conductor of the congruence subgroup S, mS of the Ray Class Group R,mR 
  
***
"""


function conductor(S::FinGenGrpAb, mS::FinGenGrpAbMap, R::FinGenGrpAb, mR::MapRayClassGrp)


  cond=mR.modulus_fin
  O=parent(cond).order

  L=factor(cond)
  divisors=collect(keys(L))

  E=divexact(order(R),order(S))
  Sgens=[image(mR*mS,S[i]) for i=1:ngens(S)]
  candidate=cond
  
  # Test the finite primes.
  
  while !isempty(divisors)
    p=divisors[length(divisors)]
    for j=1:L[p]
      candidate=cond*inv(p)
      simplify(candidate)
      candidate=candidate.num
      r, mr=ray_class_group(candidate,mR.modulus_inf)
      T, mT=quo(r, [mr\(Sgens[i]) for i=1:ngens(S)])
      E1=order(T)
      if E==E1
        cond=candidate 
      else
        break
      end
    end
    pop!(divisors)
  end

  # Test the infinite primes.
  
  if !isempty(mR.modulus_inf)
    candidate_inf=deepcopy(mR.modulus_inf)
    cond_inf=deepcopy(mR.modulus_inf)
    for i=1:length(infinite_primes)
      candidate_inf=[x for x in mR.modulus_inf for x !=mR.modulus_inf[i]]
      r,mr=ray_class_group(cond,candidate_inf)
      T,mT=quo(r, [mr\(Rgens[i]) for i=1:ngens(R)])
      E1=order(T)
      if E==E1
        cond_inf=candidate_inf
      else 
        candidate_inf=cond_inf
      end
    end
    return cond, cond_inf
  end
  return cond
  
end 


doc"""
***

  function isconductor(R::FinGenGrpAb, mR::Map, m::NfMaxOrdIdl, infinite_primes::Array{InfPlc,1}=[])

  Check if $m$ is the conductor of the congruence subgroup $S,mS$ of the Ray Class group R,mR
  
***
"""


function isconductor(S::FinGenGrpAb, mS::FinGenGrpAbMap, R::FinGenGrpAb, mR::MapRayClassGrp, m::NfMaxOrdIdl, infinite_places::Array{InfPlc,1}=InfPlc[])

  O=parent(m).order

  L=factor(m)
  divisors=collect(keys(L))

  E=divexact(order(R),order(S))
  Sgens=[image(mR*mS,S[i]) for i=1:ngens(S)]

  
  # Check the finite primes 
  
  for p in divisors
    candidate=m*inv(p)
    simplify(candidate)
    candidate=candidate.num
    r, mr=ray_class_group(candidate, infinite_places)
    T, mT=quo(r, [mr\(Sgens[i]) for i=1:ngens(S)])
    if E==order(T)
      return false
    end
  end

  # Check the infinite primes. To be changed.
  
  if !isempty(infinite_places)
    candidate_inf=deepcopy(infinite_places)
    for i=1:length(infinite_places)
      deleteat!(candidate_inf,i)
      r,mr=ray_class_group(m,candidate_inf)
      T,mT=quo(r, [mr\(Sgens[i]) for i=1:ngens(S)])
      if E==order(T)
        return false
      else 
        candidate_inf=deepcopy(infinite_places)
      end
    end
  end
  return true
  
end 



doc"""
***
  function norm_group2(f::Nemo.GenPoly, R::FinGenGrpAb, mR::MapRayClassGrp) -> Hecke.FinGenGrpAb, Hecke.FinGenGrpAbMap

 > Computes the subgroup of the Ray Class Group $R$ given by the norm of the extension generated by the roots of $f$ 
   Under GRH, it returns an error message if the extension is non-abelian

***
"""

function norm_group(f::Nemo.PolyElem, R::FinGenGrpAb, mR::Hecke.MapRayClassGrp)
  
  
  O=mR.modulus_fin.parent.order
  K=O.nf
  
  signs=signature(norm(f))

  if signs[1] !=0 && signs[2] !=0
    error("The extension is not normal")
  end

  d=discriminant(f)
  N=num(norm(K(d)))
  N1=fmpz(norm(mR.modulus_fin))
  n=degree(f)
  
  Q,mQ=quo(R,n)
  
  S,mS=snf(Q)
  mT=mR*inv(mQ)*inv(mS)
  M=rels(S)
  
  p=1
  Ox,x=O["y"]
  f=Ox([O(coeff(f,i)) for i=0:n])
  
  determinant=abs(det(M))
  listprimes=typeof(R[1])[]  
  new_mat=M

  B=log(abs(discriminant(O)))*degree(f)+log(N)
  B=4*B+2.5*degree(f)*degree(O)+5
  B=B^2
  
  #
  # Adding small primes until they generate the norm group
  #
  
  while determinant!= n 
    p=next_prime(p)
    if p>B
      error("The extension is not abelian!") #Bach bound says that the norm group must be generated by primes $\leq B$
    end
    if !divisible(N,p) && !divisible(N1,p) 
      L=prime_decomposition(O,p)
      for i=1:length(L)
        F,mF=ResidueField(O,L[i][1])
        Fz,z= F["z"]
        g=mF(f)
        D=factor(g)
        E=collect(keys(D.fac))
        candidate=mR\(((L[i][1]))^degree(E[1]))
        new_mat=vcat(new_mat,((mS*mQ)(candidate)).coeff)
        new_mat=hnf(new_mat)
        new_mat=submat(new_mat,1,1,ngens(S), ngens(S))  
        new_det=abs(det(new_mat))
        if determinant!=new_det
          push!(listprimes, candidate)
          determinant=new_det
        end
      end
    end
  end
  
  #
  # Computing the Hermite normal form of the subgroup
  #
  if !isempty(listprimes)
    subgrp=[el for el in listprimes]
    for i=1:ngens(R)
      push!(subgrp, n*R[i])
    end
    return sub(R, subgrp)
  else  
     return sub(R,[])
  end    

end




