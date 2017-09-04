mutable struct ZpnGModule <: GModule
  R::GenResRing
  V::GrpAbFinGen
  G::Array{nmod_mat,1}
  p::Int
  
  function ZpnGModule(V::GrpAbFinGen,G::Array{T,1}) where T
    @assert ngens(V)==cols(G[1]) && ngens(V)==rows(G[1])
    z=new()
    z.G=G
    z.V=V
    z.R=parent(G[1][1,1]) 
    f=factor(z.R.modulus)
    @assert length(f.fac)==1
    z.p=Int(first(keys(f.fac)))
    return z
  end
  
end

#
#  Action of a matrix on an element of the group
#

function *(M::nmod_mat, x::GrpAbFinGenElem)

  G=parent(x)
  @assert ngens(G)==rows(M)
  R=parent(M[1,1]) 
  coeff=MatrixSpace(R,1,cols(M))()
  for i=1:cols(M)
    coeff[1,i]=x.coeff[1,i]
  end
  y=coeff*M
  return G(lift(y))
  
end


#
#  Smith Normal Form for a ZpnGModule
#


function Nemo.snf(M::ZpnGModule)

  A=M.V
  G=M.G
  if issnf(A)
    return M, GrpAbFinGenMap(A, A, MatrixSpace(ZZ,ngens(A),ngens(A))(1))
  end
  S,mS=snf(A)
  W=[mS\s for s in gens(S)]
  H=[]
  for i=1:length(G)
    N=MatrixSpace(M.R, 0,ngens(S))()
    for j=1:length(W)
      y=mS(G[i]*W[j])
      aux=MatrixSpace(M.R,1,ngens(S))()
      for k=1:ngens(S)
        aux[1,k]=y.coeff[1,k]
      end
      N=vcat(N,aux)
    end
    push!(H,N)
  end
  return ZpnGModule(S,H), mS
    
end


#
#  Given a list of square matrices G, returns a list of matrices given by the minors 
#  (n-s) x (n-s) of the matrices G[i] projected mod p 
#


function _change_ring(G, F, s::Int)
  
  G1=MatElem[]
  n=rows(G[1])
  for i=1:length(G)
    M=MatrixSpace(F,n-s+1,n-s+1)()
    for j=s:n
      for k=s:n
        M[j-s+1,k-s+1]=(G[i][j,k]).data
      end
    end
    push!(G1,M)
  end
  return G1

end

#
#  Cut the module in submodules with exponent p, returning the quotients p^i M /p^(i+1) M
#


function _mult_by_p(M::ZpnGModule)

  G=M.G
  V=M.V
  p=M.p
  @assert issnf(V)
  #
  #  First, the quotient M/pM
  #
  F,a=FiniteField(p,1,"a")
  n=ngens(V)
  Gq=_change_ring(G,F,1)
  spaces=[FqGModule(Gq)]
  #
  #  Now, the others
  #
  s=valuation(M.R.modulus,p)
  j=1
  for i=2:s
    while !divisible(V.snf[j],p^i)
      j+=1
    end
    GNew=_change_ring(G,F,j)
    push!(spaces, FqGModule(GNew))
  end
  return spaces  

end


function composition_factors(M::ZpnGModule)

  N,_=snf(M)
  list_sub=_mult_by_p(N)
  list=[]
  for x in list_sub
    append!(list, composition_factors(x))
  end
  for i=1:length(list)
    for j=i+1:length(list)
      if Hecke.isisomorphic(list[i][1], list[j][1])
        list[i][2]+=list[j][2]
        deleteat!(list,j)
      end    
    end
  end
  return list

end


function _exponent_p_sub(M::ZpnGModule)

  G=M.G
  V=M.V
  p=M.p
  F, a = FiniteField(p, 1, "a")
  hV = GrpAbFinGenMap(V, V, MatrixSpace(ZZ,ngens(V),ngens(V))(p))  #Can make it more efficient if necessary, working with matrices
  K,mK=Hecke.kernel(hV)
  S,mS=snf(K)
  G1=MatElem[]
  for g in G
    A=MatrixSpace(F,0,ngens(S))()
    for i=1:ngens(S)
      x=g*(mK(mS(S[i])))
      x=(mS\(haspreimage(mK,x)[2])).coeff
      A=vcat(A,x)
    end
    push!(G1,A)
  end
  return FqGModule(G1)
  
end


function minimal_submodules(M::ZpnGModule)
  
  
  R=M.R
  S,mS=snf(M)
  N=_exponent_p_sub(S)
  list_sub=minimal_submodules(N)
  list=nmod_mat[]
  v=[valuation(order(S.V[i]), M.p) for i=1:ngens(S.V)]
  for x in list_sub
    A=MatrixSpace(R,0, ngens(M.V))()
    for k=1:rows(x)
      A=vcat(A, (haspreimage( mS , S.V([ZZ(coeff(x[k,i],0))*((M.p)^(v[i]-1)) for i=1:ngens(S.V)]))[2]).coeff)
    end
    push!(list,A)
  end
  return list

end



function quo(M::ZpnGModule, S::MatElem)

  subm=[M.V(lift(sub(S,i:i, 1:cols(S)))) for i=1:rows(S)]
  return ZpnGModule(quo(M.V,subm)[1],M.G)
  
end


function submodules(M::ZpnGModule)
  
  R=M.R
  S,mS=snf(M)  
  minlist=minimal_submodules(S)
  list=nmod_mat[]
  
  #
  #  Find minimal submodules, factor out and recursion on the quotients
  #
  
  for x in minlist
    N=quo(S,x)
    newlist=submodules(N)
    for y in newlist
      push!(list,vcat(y,x))
    end
  end
  
  append!(list,minlist)
  #
  #  Eliminate redundance via Howell form
  #
  
  listhf=Array{nmod_mat,1}(length(list))
  for i=1:length(list)
    x=deepcopy(list[i])
    if cols(x)>rows(x)
      x=vcat(x,MatrixSpace(R,cols(list[i])-rows(list[i]), cols(list[i]))())
    end
    for j=1:cols(x)
      for k=1:rows(list[i])
        x[k,j]*=divexact(R.modulus, order(S.V[j]))
      end
    end
    howell_form!(x)
    listhf[i]=view(x,1:cols(x), 1:cols(x))
  end
  i=1
  while i<=length(list)
    j=i+1
    while j<=length(list)
      if listhf[i]==listhf[j]
        deleteat!(list,j)
        deleteat!(listhf,j)
      else 
        j+=1  
      end
    end
    i+=1
  end
  
  #
  #  Writing the submodules in terms of the given generators
  #
  
  W=MatrixSpace(R,1,ngens(M.V))
  for j=1:length(list)
    list[j]=vcat([W((haspreimage( mS , S.V([ list[j][k,i].data for i=1:ngens(S.V)]))[2]).coeff) for k=1:rows(list[j])] )
  end
  
  return list
  
end

function minimal_submodules(M::ZpnGModule, dim::Int)
  
  
  R=M.R
  S,mS=snf(M)
  N=_exponent_p_sub(S)
  list_sub=minimal_submodules(N, dim)
  list=Array{nmod_mat,1}(length(list_sub))
  v=[valuation(order(S.V[i]), M.p) for i=1:ngens(S.V)]
  for i=1:length(list)
    W=MatrixSpace(R,rows(x), ngens(M.V))
    list[i]= vcat([W((mS\(S.V([ZZ(coeff(x[k,i],0))*((M.p)^(v[i]-1)) for i=1:ngens(S.V)]))).coeff) for k=1:rows(x)])
  end
  return list

end

function submodules_with_struct(M::ZpnGModule, typesub::Array{Int,1})
  
  G=DiagonalGroup(typesub)
  @assert issnf(G)
  @assert divisible(fmpz(typesub[1]), M.p)
  for i=1:length(typesub)
    @assert length(factor(fmpz(typesub[i])).fac)==1
  end
  
  minlist=minimal_submodules(M, length(typesub))
  if typesub[length(typesub)]==M.p
    return minlist
  end
  i=1
  while !divisible(fmpz(typesub[i]),M.p^2)
    i+=1
  end
  typesub1=Int[]
  while i<=length(typesub)
    push!(typesub1, divexact(typesub[i],p))
  end
  list=[]
  for x in minlist
    N=quo(M,x)
    newlist=submodules(N, typesub1)
    if !isempty(newlist)
      t=[sub(x, i:i, 1:cols(y)) for i=1:rows(y)]
      for y in newlist
        s=vcat([sub(y, i:i, 1:cols(y)) for i=1:rows(y)], t)
        H=sub(M.V,s)
        if isisomorphic(G,H)
          push!(list,vcat(y,x))
        end
      end
    end
  end
  return list

end

function submodules_order(M::ZpnGModule, ord::Int)
  
  R=M.R
  S,mS=snf(M)
  N=_exponent_p_sub(S)
  lf=composition_factors(N)
  list=nmod_mat[]
  v=[valuation(order(S.V[i]), M.p) for i=1:ngens(S.V)]
  W=MatrixSpace(R,1, ngens(S.V))
  for i=1:ord-1
    minlist=minimal_submodules(N,i,lf)
    for x in minlist   
      A=vcat([W([ZZ(coeff(x[k,i],0))*((M.p)^(v[i]-1)) for i=1:ngens(S.V)]) for k=1:rows(x)])
      L=quo(S,A)
      newlist=submodules_order(L,ord-i)
      for i=1:length(newlist)
        push!(list,vcat(newlist[i],A))
      end
    end
  end
  
  #
  #  Check for redundance
  #
  
  listhf=Array{nmod_mat,1}(length(list))
  for i=1:length(list)
    x=deepcopy(list[i])
    if cols(list[i])>=rows(list[i])
      x=vcat(x,MatrixSpace(R,cols(list[i])-rows(list[i]), cols(list[i]))())
    end
    for j=1:cols(x)
      for k=1:rows(list[i])
        x[k,j]*=divexact(R.modulus, order(S.V[j]))
      end
    end
    howell_form!(x)
    listhf[i]=view(x,1:cols(x),1:cols(x))
  end
  i=1
  while i<=length(list)
    j=i+1
    while j<=length(list)
      if listhf[i]==listhf[j]
        deleteat!(list,j)
        deleteat!(listhf,j)
      else 
        j+=1  
      end
    end
    i+=1
  end
  
  #
  #  Write the submodules in terms of the set of given generators
  #
  
  W=MatrixSpace(R,1, ngens(M.V))
  for j=1:length(list)
    list[j]=vcat([W((haspreimage( mS , S.V([list[j][k,i].data for i=1:ngens(S.V)]))[2]).coeff)  for k=1:rows(list[j])])
  end
  
  #
  #  Add the minimal submodules
  # 
  
  minlist=minimal_submodules(N,ord, lf)
  for x in minlist
    push!(list, vcat([W((haspreimage(mS, S.V([ZZ(coeff(x[k,i],0))*((M.p)^(v[i]-1)) for i=1:ngens(S.V)]))[2]).coeff) for k=1:rows(x) ]))
  end
  return list
  
end


function submodules_with_quo_struct(M::ZpnGModule, typequo::Array{Int,1})
  
  R=M.R 
  S,mS=snf(M)
  wish=DiagonalGroup([(M.p)^typequo[i] for i=1:length(typequo)])
  
  #
  #  Matrices giving the action of the group on the dual module
  #

  G1=deepcopy(S.G)
  for i=1:length(G1)
    for j=1:ngens(S.V)-1
      for k=j+1:ngens(S.V)
        x=divexact(order(S.V[k]), order(S.V[j]))
        G1[i][j,k].data=divexact(G1[i][j,k].data, x)
        G1[i][k,j]*=x
      end
    end
    transpose!(G1[i])
  end
  #
  #  Dual Module and candidate submodules
  #
  M_dual=ZpnGModule(S.V, G1)
  candidates=submodules_order(M_dual,Int(sum(typequo)))
  i=1
  list=nmod_mat[]
  W=MatrixSpace(R,1,ngens(S.V))
  while i<=length(candidates)
  #
  #  First, compute the kernel of the corresponding homomorphisms
  #
    K=DiagonalGroup([R.modulus for i=1:rows(candidates[i])])
    mH=GrpAbFinGenMap(S.V,K,lift(transpose(candidates[i])))
    sg,msg=kernel(mH)
     
  #
  #  Check that the type is correct
  #
    sub=[msg(g) for g in gens(sg)]
    q,mq=quo(S.V,sub)
    if isisomorphic(q,wish)
      push!(list, vcat([W(x.coeff) for x in sub]))
      i+=1
    else
      deleteat!(candidates, i)
    end
  end
  
  
  #
  #  Write the submodules in terms of the given generators
  #
  W=MatrixSpace(R,1, ngens(M.V))
  for j=1:length(list)
    list[j]=vcat([W((haspreimage( mS , S.V([list[j][k,i].data for i=1:ngens(S.V)]))[2]).coeff)  for k=1:rows(list[j])])
  end  
  
  return list
  
end

