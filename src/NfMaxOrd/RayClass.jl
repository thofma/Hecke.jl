
export iscoprime, ray_class_group 

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
# Given two integral ideals $a$,$b$, computes a $\gamma$ such 
# that $\gamma a$ is an integral ideal coprime to $b$
# $\gamma$ is chosen randomly
# The output is the ideal $a*\gamma$ and the element $\gamma$
#
function _coprime_ideal(a::NfMaxOrdIdl, b::NfMaxOrdIdl)
 
  O=parent(a).order
  K=nf(O)
 
  if iscoprime(a,b)
    return a,K(1)
  end
  J=inv(a)
  s=K(rand(J.num,5))//J.den  # Is the bound acceptable?
  I=s*a
  simplify(I)
  I = num(I)
  while !iscoprime(I,b)
    s=K(rand(J.num,5))//J.den  
    I=s*a
    simplify(I)
    I = num(I)
  end
  return I,s
 
end 

#
# Function that finds the generators of the infinite part
#

function _infinite_primes(O::NfMaxOrd, p::Array{Int,1}, m::NfMaxOrdIdl)

  K=O.nf
  S = DiagonalGroup([2 for i=1:length(p)])

  function logS(x::Array{Int, 1})
    return S([x[i] > 0 ? 0 : 1 for i=1:length(x)])
  end

  s = typeof(S[1])[]
  g = nf_elem[]
  u, mu = sub(S, s)
  b = 10
  cnt = 0
  while true
    a = rand(m, b)
    emb=Hecke.signs(K(a))
    t = logS([emb[i] for i in p])
    if !Hecke.haspreimage(mu, t)[1]
      push!(s, t)
      push!(g, K(a))
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
  r = nf_elem[]
  for i=1:length(p)
    y = haspreimage(hS,S[i])[2]
    push!(r, prod([g[i]^Int(y[i]) for i=1:length(p)]))
  end
  
  function exp(A::FinGenGrpAbElem)
    return prod([r[i]^(Int(A.coeff()))])
  end 

  function log(B::nf_elem)
    d=Hecke.signs(B)
    return logS([d[i] for i in p])
  end 
  
  return S, log,exp

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
function ray_class_group(m::NfMaxOrdIdl, primes=[])

#
# We compute the group using the sequence U -> (O/m)^* _> Cl^m -> Cl -> 1
# First of all, we compute all these groups with their own maps
#
  O=parent(m).order
  K=nf(O)

  C, mC = class_group(O)
  U, mU = unit_group(O)
  M, pi= quo(O,m)
  G, mG=unit_group(M)
  if !isempty(primes)
    H,lH,eH=_infinite_primes(O,primes,m)
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
    for j=1:cols(RG)
      B[i+rows(RC)+rows(RG),j]=a[1,j]
    end
  end 

#
# We compute the relation between generators of Cl and (O/m)^* in Cl^m
#

  P=[K(1) for i=1: ngens(C)]

  for i=1: ngens(C)
    if order(C[i])==1
      y=K(1)
    else 
      x, P[i]=_coprime_ideal(mC(C[i]), m)
      x=x^(Int(order(C[i])))
      y=Hecke.principal_gen(x)
    end
    b=(mG\(pi(O(y)))).coeff
    if primes != []
      b=hcat(b, (lH(K(y))).coeff)
    end 
    for j=1: ngens(G)
      B[i,j]=-b[1,j]
    end 
  end

  R=hcat(B,A)
  X=AbelianGroup(R)

#
# Discrete logarithm
#

  function disclog(J::NfMaxOrdIdl)

    if isone(J)
      return X([0 for i=1:ngens(X)])
    else
    L=mC\J
    t=K(1)
    s=ideal(O,1)
    for i=1:ngens(C)
      if Int(L.coeff[1,i])!=0
        t=t*P[i]^(Int(L.coeff[1,i]))
        s=s*mC(C[i])^(Int(L.coeff[1,i]))
      end
    end 
    I= J // s
    simplify(I)
    gamma=Hecke.principal_gen(I.num)
    alpha=K(gamma)* (t^(-1))
    y1=mG\(pi(O(num(alpha))))
    y2=mG\(pi(O(den(alpha))))
    y=y1.coeff - (y2.coeff)
    if primes!=[]
      z=lH(alpha)
      y=vcat(y, z.coeff)
    end 
    return X(hcat(y, L.coeff))
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
          if d.coeff!=0
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

  mp=MapRayClassGrp{typeof(X)}()
  mp.header = Hecke.MapHeader(X, Hecke.NfMaxOrdIdlSet(O), expo, disclog)
  mp.modulus_fin=m
 
  return X, mp
  
end



doc"""
***
  function norm_group(f::Nemo.GenPoly, R::FinGenGrpAb, mR::MapRayClassGrp) -> Hecke.FinGenGrpAb, Hecke.FinGenGrpAbMap

 > Compute the subgroup of the Ray Class Group $R$ given by the norm of the abelian extension generated by the roots of $f$ 

***
"""

function norm_group(f::Nemo.PolyElem, R::FinGenGrpAb, mR::Hecke.MapRayClassGrp)
  
  
  O=modulus.parent.order
  K=O.nf
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
  
  #
  # Adding small primes until they generate the norm group
  #
  
  while determinant!= n
    p=next_prime(p)
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


Hecke.elem_type(A::Hecke.NfMaxOrdIdlSet) = NfMaxOrdIdl


doc"""
***

  function conductor(R::FinGenGrpAb, mR::Map, m::NfMaxOrdIdl, infinite_primes::Array{Int,1}=[])

  Return the conductor of the congruence subgroup given by R 
  
***
"""


function conductor(R::FinGenGrpAb, mR::Map, m::NfMaxOrdIdl, infinite_primes::Array{Int,1}=[])

  O=parent(m).order

  L=factor(m)
  divisors=collect(keys(L))

  cond=m
  E=order(R)
  Rgens=[image(mR,R[i]) for i=1:ngens(R)]
  
  # I check the finite primes 
  
  while !isempty(divisors)
    p=divisors[length(divisors)]
    for j=1:L[p]
      candidate=m*inv(p)
      simplify(candidate)
      candidate=candidate.num
      S, mS=ray_class_group(candidate)
      T, mT=quo(S, [mS\(Rgens[i]) for i=1:ngens(R)])
      E1=order(T)
      if E==E1
        cond=candidate 
      else
        pop!(divisors)
        break
      end
    end
    pop!(divisors)
  end

  # I check the infinite primes. To be changed.
  
  if !isempty(infinite_primes)
    candidate_inf=infinite_primes
    cond_inf=infinite_primes
    for i=1:length(infinite_primes)
      candidate_inf=deleteat!(candidate_inf,i)
      R,mR=ray_class_group(cond,candidate_inf)
      T,mT=quo(S, [mS\(Rgens[i]) for i=1:ngens(R)])
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






