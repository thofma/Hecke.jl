
export stable_subgroups

add_verbose_scope(:StabSub)

###############################################################################
#
#  Tools for ZpnGModules
#
###############################################################################

function base_ring(M::ZpnGModule)
  return M.R
end

function show(io::IO, M::ZpnGModule)
  print(io, "Module over Z/", M.R.n, "Z with structure ", M.V)
end

#
#  Lifts a matrix from F_p to Z/p^nZ
#

function lift(M::fq_nmod_mat, R::Nemo.NmodRing)

  x=factor(fmpz(R.n))
  @assert length(x.fac)==1
  @assert order(parent(M[1,1]))==first(keys(x.fac))
  N=zero_matrix(R,nrows(M),ncols(M))
  for i=1:nrows(M)
    for j=1:ncols(M)
      N[i,j]=FlintZZ(coeff(M[i,j],0))
    end
  end
  return N
  
end

function lift(M::gfp_mat, R::Nemo.NmodRing)
  
  x=factor(fmpz(R.n))
  @assert length(x.fac)==1
  @assert order(parent(M[1,1]))==first(keys(x.fac))
  N=zero_matrix(R, nrows(M), ncols(M))
  for i=1:nrows(M)
    for j=1:ncols(M)
      N[i,j] = R(lift(M[i,j]))
    end
  end
  return N

end

#
#  Action of a matrix on an element of the group
#

function *(x::GrpAbFinGenElem, M::nmod_mat)

  G=parent(x)
  @assert ngens(G)==nrows(M)
  R=parent(M[1,1]) 
  coeff=zero_matrix(R,1,ncols(M))
  for i=1:ncols(M)
    coeff[1,i]=x.coeff[1,i]
  end
  y=coeff*M
  l = lift(y)
  l.base_ring = FlintZZ # TODO: Remove this once Nemo is updated
  return G(l)
end


#
#  Smith Normal Form for a ZpnGModule
#


function Nemo.snf(M::ZpnGModule)

  A=M.V
  G=M.G
  if issnf(A)
    return M, id_hom(A)
  end
  S,mS=snf(A)
  W=[mS(s) for s in gens(S)]
  R=M.R
  H=Array{nmod_mat,1}(undef, length(G))
  for i=1:length(G)
    N=zero_matrix(R, ngens(S),ngens(S))
    for j=1:length(W)
      y=mS\(W[j]*G[i])
      for k=1:ngens(S)
        N[j,k]=y.coeff[1,k]
      end
    end
    H[i]=N
  end
  return ZpnGModule(S,H), mS
    
end

function isstable(act::Array{T, 1}, mS::GrpAbFinGenMap) where T <: Map{GrpAbFinGen, GrpAbFinGen} 

  S=mS.header.domain
  for s in gens(S)
    x=mS(s)
    for g in act
      if !haspreimage(mS,g(x))[1]
        return false
      end
    end
  end
  return true

end

function issubmodule(M::ZpnGModule, S::nmod_mat)
  
  #@assert issnf(M.V)
  s, ms=subm_to_subg(M, S)
  for x in gens(s)
    el=ms(x)
    for g in M.G
      if !haspreimage(ms,el*g)[1]
        return false
      end
    end
  end
  return true
  
end

#
#  Given a group $G$ and a group of automorphisms of G, this function returns the corresponding ZpnGModule
#

function action(V::GrpAbFinGen, act::Array{T,1}) where T<: Map{GrpAbFinGen, GrpAbFinGen} 

  expon=Int(exponent(V))
  @assert length(factor(order(V)).fac)==1
  RR=ResidueRing(FlintZZ, expon, cached=false)
  act_mat=Array{nmod_mat,1}(undef, length(act))
  for z = 1:length(act)
    A =zero_matrix(RR, ngens(V), ngens(V))
    for i = 1:ngens(V)
      y=act[z](V[i])
      for j=1:ngens(V)
        A[i,j]=y.coeff[1,j]
      end
    end
    act_mat[z]=A
  end
  return ZpnGModule(V,act_mat)

end


#################################################################################
#
#  Duality
#
#################################################################################

#=
  To get the transpose map of a homomorphism, and so the action on the dual module,
  you need to transpose the matrix and multiply or the elements for a power of p, assuming that the group is in snf.
  Precisely, let p^e be the exponent of the group and let p^t_i be the powers of p appearing in the snf. Then 
  ( p^(e-t_1)     )                  ( p^(e-t_1)     )
  (          ...  )  x ^t A  = A  x  (          ...  )
  (              1)                  (              1)
=#


function dual_module(M::ZpnGModule)

  @assert issnf(M.V)
  G1=deepcopy(M.G)
  for i=1:length(G1)
    for j=1:ngens(M.V)-1
      for k=j+1:ngens(M.V)
        x=divexact(M.V.snf[k], M.V.snf[j])
        G1[i][j,k]=divexact(G1[i][j,k].data, x)
        G1[i][k,j]*=x
      end
    end
    transpose!(G1[i])
  end 
  return ZpnGModule(M.V, G1)
  
end

function _dualize(M::nmod_mat, V::GrpAbFinGen, v::Array{fmpz,1})    
  #
  #  First, compute the kernel of the corresponding homomorphisms
  # 
  K=DiagonalGroup([V.snf[end] for j=1:nrows(M)])
  A=lift(transpose(M))
  for j=1:nrows(A)
    for k=1:ncols(A)
      A[j,k]*=v[j]
    end
  end 
  mH=Hecke.GrpAbFinGenMap(V,K,A)
  newel=kernel_as_submodule(mH)
  return change_base_ring(newel, base_ring(M))

end

function _dualize_1(M::nmod_mat, snf_struct::Array{fmpz,1})

  A=nullspace(transpose(M))
  B=vcat(transpose(A),zero_matrix(M[1,1].parent, ncols(A),ncols(A)))
  for j=1:ncols(A)
    B[nrows(A)+j,j]=snf_struct[j]
  end
  S=nullspace(B)
  C=vcat(transpose(A),zero_matrix(M[1,1].parent, ncols(A),ncols(A)))
  return S*C
 
end

function kernel_as_submodule(h::GrpAbFinGenMap)
  G = domain(h)
  H = codomain(h)
  hn, t = hnf_with_transform(vcat(h.map, rels(H))) 
  for i=1:nrows(hn)
    if iszero_row(hn, i)
      return view(t, i:nrows(t), 1:ngens(G))
    end
  end
  error("JH")
end



########################################################################################################
#
#  Quotients and subgroups of ZpnGModules
#
########################################################################################################


function quo(M::ZpnGModule, S::nmod_mat)
  Q, mQ=quo(M.V, lift(S), false)
  return ZpnGModule(Q, M.G), mQ
end

function sub(M::ZpnGModule, S::nmod_mat)

  sg, msg=sub(M.V, lift(S), false)
  G=Array{nmod_mat,1}(undef, length(M.G))
  for k=1:length(M.G)
    A=zero_matrix(M.R, ngens(sg), ngens(sg))
    for i=1:ngens(sg)
      x=msg(sg[i])*M.G[k]
      x=haspreimage(msg, x)[2].coeff
      for j=1:ngens(sg)
        A[i,j]=x[1,j]
      end
    end
    G[k]=A
  end
  return ZpnGModule(sg,G), msg

end


function sub(M::ZpnGModule, n::Int)
  
  sg,msg=sub(M.V, n, false)
  G=Array{nmod_mat,1}(undef, length(M.G))
  for k=1:length(M.G)
    A=zero_matrix(M.R, ngens(sg), ngens(sg))
    for i=1:ngens(sg)
      x=msg(sg[i])*M.G[k]
      x=haspreimage(msg, x)[2].coeff
      for j=1:ngens(sg)
        A[i,j]=x[1,j]
      end
    end
    G[k]=A
  end
  return ZpnGModule(sg,G), msg
  
end


function _exponent_p_sub(M::ZpnGModule)

  @assert issnf(M.V)
  G = M.G
  V = M.V
  p = M.p
  F = GF(Int(p), cached=false)
  v = fmpz[divexact(V.snf[i], p) for i=1:ngens(V)]
  G1 = Array{gfp_mat,1}(undef, length(G))
  for s=1:length(G1)
    G1[s] = zero_matrix(F, ngens(V), ngens(V))
    for i=1:ngens(V)
      for j=1:ngens(V)
        if G[s][i,j] !=0 && v[i] <= v[j]
          G1[s][i,j] = divexact((G[s][i,j].data)*v[i], v[j])
        end
      end
    end
  end
  return ModAlgAss(G1)
  
end

function subm_to_subg(M::ZpnGModule, S::nmod_mat; op=sub)
  return op(M.V, lift(S))
end


##########################################################################
#
#  Minimal Submodules function
#
##########################################################################

function minimal_submodules(M::ZpnGModule, ord::Int=-1)
  
  R = M.R
  S, mS = snf(M)
  N = _exponent_p_sub(S)
  if ord == -1
    list_sub = minimal_submodules(N)
  else
    list_sub = minimal_submodules(N, ngens(S.V)-ord)
  end
  list = Array{nmod_mat,1}(undef, length(list_sub))
  v = Int[M.p^(valuation(S.V.snf[i], M.p)-1) for i=1:ngens(S.V)]
  W = MatrixSpace(R, 1, ngens(M.V), false)
  for z = 1:length(list)
    list[z] = vcat(nmod_mat[W((mS(S.V(fmpz[lift(list_sub[z][k,i])*v[i] for i=1:ngens(S.V)]))).coeff) for k=1:nrows(list_sub[z])])
  end
  return list

end

###########################################################################################
#
#  Maximal Submodules function
#
###########################################################################################


function maximal_submodules(M::ZpnGModule, ind::Int=-1)
  
  R = M.R
  S, mS = snf(M)
  N = dual_module(S)
  if ind == -1
    minlist = minimal_submodules(N)
  else 
    minlist = minimal_submodules(N,ind)
  end
  list=Array{nmod_mat,1}(undef, length(minlist))
  v=[divexact(fmpz(R.n),S.V.snf[j]) for j=1:ngens(S.V) ]
  for x in minlist
    K = DiagonalGroup([fmpz(R.n) for j=1:nrows(x)])
    A = lift(transpose(x))
    for j=1:nrows(A)
      for k=1:ncols(A)
        A[j,k]*=v[j]
      end
    end 
    mH = Hecke.GrpAbFinGenMap(S.V,K,A)
    sg, msg = kernel(mH)
    push!(list, vcat([ (mS(msg(y))).coeff for y in gens(sg)]))
  end
  return list

end


##########################################################################################
#
#  Composition factors and series
#
##########################################################################################
#
#  Given a list of square matrices G, it returns a list of matrices given by the minors 
#  (n-s) x (n-s) of the matrices G[i] mod p 
#
function _change_ring(G::Array{nmod_mat,1}, F::Nemo.FqNmodFiniteField, s::Int)
  
  G1=Array{fq_nmod_mat,1}(undef, length(G))
  n=nrows(G[1])
  for i=1:length(G)
    M=zero_matrix(F,n-s+1,n-s+1)
    for j=s:n
      for k=s:n
        M[j-s+1,k-s+1]=(G[i][j,k]).data
      end
    end
    G1[i] = M
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
  F = GF(p, cached=false)
  n = ngens(V)
  Gq = _change_ring(G, F, 1)
  spaces = ModAlgAss[ModAlgAss(Gq)]
  #
  #  Now, the others
  #
  s=valuation(fmpz(M.R.n),p)
  j=1
  for i=2:s
    while !divisible(V.snf[j],p^i)
      j+=1
    end
    GNew=_change_ring(G,F,j)
    push!(spaces, ModAlgAss(GNew))
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
    j=i+1
    while j<=length(list)
      if Hecke.isisomorphic(list[i][1], list[j][1])
        list[i][2]+=list[j][2]
        deleteat!(list,j)
      else 
        j+=1
      end    
    end
  end
  return list

end

###############################################################################
#
#  Submodules interface
#
###############################################################################

@doc Markdown.doc"""
    submodules(M::ZpnGModule; typequo, typesub, order)
Given a ZpnGModule M, the function returns all the submodules of M. 

"""
function submodules(M::ZpnGModule; typequo=Int[-1], typesub=Int[-1], ord=-1)

  if typequo!=[-1]
    return submodules_with_quo_struct(M,typequo)
  elseif typesub!=[-1]
    return submodules_with_struct(M,typesub)
  elseif ord!=-1
    return submodules_order(M,ord)
  else 
    return submodules_all(M)
  end
  
end

###############################################################################
#
#  Function to find all the submodules
#
###############################################################################

function submodules_all(M::ZpnGModule)
  
  R = M.R
  if isone(order(M.V))
    return (nmod_mat[])
  end 
  S,mS = snf(M)  
  minlist = minimal_submodules(S)
  list = nmod_mat[identity_matrix(R, length(S.V.snf)), zero_matrix(R,1,length(S.V.snf))]
  
  #
  #  Find minimal submodules, factor out and recursion on the quotients
  #
  
  for x in minlist
    N, _ = quo(S,x)
    newlist = submodules_all(N)
    for y in newlist
      push!(list,vcat(y,x))
    end
  end
  
  append!(list,minlist)
  #
  #  Eliminate redundance via Howell form
  #
  w=fmpz[divexact(fmpz(R.n), S.V.snf[j]) for j=1:ngens(S.V)]
  list=_no_redundancy(list, w)
  
  #
  #  Writing the submodules in terms of the given generators and returning an iterator
  #
  MatSnf=change_base_ring(mS.map, R)
  return (x*MatSnf for x in list)
  
end

###############################################################################
#
#  Submodules with given structure as a subgroup
#
###############################################################################

function main_submodules_cyclic(M::ZpnGModule, ord::Int)

  list = _submodules_with_struct_cyclic(M, ord)
  for step = 1:ord-1
    c = M.p^step 
    list1 = nmod_mat[]
    for x in list  
      L, _ = quo(M, x)
      newlist = _submodules_with_struct_cyclic(L, ord-step)
      for i = 1:length(newlist)
        if !iszero(c * M.V( lift(newlist[i]) ))
          push!(list1, newlist[i])
        end
      end
    end
    list = list1
  end
  return list
  
end

function _submodules_with_struct_cyclic(M::ZpnGModule, ord::Int)
  
  R = M.R
  #
  #  We search for an element in p^(ord-1)*G
  #
  s, ms = sub(M, M.p^(ord-1))
  S, mS = snf(s)
  N = _exponent_p_sub(S)
  submod = gfp_mat[]
  if N.dimension == 1
    push!(submod, identity_matrix(base_ring(N), 1))
  else
    @vtime :StabSub 1 submod = minimal_submodules(N, 1, composition_factors(N, dimension = 1))
  end
  list1 = Array{nmod_mat,1}(undef, length(submod))
  v = nmod[R(divexact(S.V.snf[i], M.p)) for i = 1:ngens(S.V)]
  for i = 1:length(submod)
    list1[i] = lift(submod[i], R)
    @assert nrows(list1[i]) == 1
    for k = 1:ncols(list1[i])
      list1[i][1, k] *= v[k]
    end
  end  
  MatSnf=change_base_ring(mS.map*ms.map, R)
  for j=1:length(list1)
    list1[j] = list1[j]*MatSnf
  end
  return list1

end

function _update_typesub(typesub::Vector{Int})
  i = 1
  while typesub[i] != typesub[end]
    i += 1
  end
  new_typesub = Array{Int, 1}(undef, length(typesub))
  for j = 1:i-1
    new_typesub[j] = typesub[j]
  end
  for j = i:length(new_typesub)
    new_typesub[j] = typesub[j] - 1
  end
  return new_typesub
end


function _submodules_with_struct_main(M::ZpnGModule, typesub::Array{Int,1})
  @assert issnf(M.V)
  p = M.p
  R = base_ring(M)
  #First iteration out of the loop.
  list = _submodules_with_struct(M, typesub)
  #Some data needed in the loop
  w = Vector{fmpz}(undef, ngens(M.V))
  for i = 1:length(w)
    w[i] = divexact(fmpz(R.n), M.V.snf[i])
  end
  new_typesub = _update_typesub(typesub)
  #Now, the iterative process.
  for i = 1:typesub[end]-1
    list1 = nmod_mat[]
    new_typesub1 = _update_typesub(new_typesub)
    diag = typesub - new_typesub1
    Gtest = snf(DiagonalGroup([p^x for x in diag]))[1]
    for x in list  
      L, _ = quo(M, x)
      newlist = _submodules_with_struct(L, new_typesub)
      
      for s = 1:length(newlist)
        newlist[s] = vcat(newlist[s], x)
      end
      #First, I sieve for the subgroups with the correct structure.
      for s = 1:length(newlist)
        t, mt = subm_to_subg(M, newlist[s])
        if isisomorphic(t, Gtest)
          push!(list1, newlist[s])
        end
      end
    end
    new_typesub = new_typesub1 
    #Now, a different sieving. I could have the same subgroup multiple times!
    if !isempty(list1)
      @vtime :StabSub 1 list1 = _no_redundancy(list1, w)
    end
    list = list1
  end
  return list
end

function _submodules_with_struct(M::ZpnGModule, typesub::Array{Int, 1})
  
  R = base_ring(M)
  s, ms = sub(M, M.p^(typesub[end]-1))
  S, mS = snf(s)
  N = _exponent_p_sub(S)
  
  i = 1
  while typesub[i] != typesub[end]
    i += 1
  end
  a = length(typesub) - i + 1
  
  @vtime :StabSub 1 submod = submodules(N, (N.dimension)-a)
  #
  #  Write the modules as elements of S
  #

  list1 = Array{nmod_mat, 1}(undef, length(submod))
  v = [divexact(S.V.snf[i], M.p) for i = 1:ngens(S.V)]
  for i = 1:length(submod)
    @inbounds list1[i] = lift(submod[i], R)
    for j = 1:nrows(list1[i])
      for k = 1:ncols(list1[i])
        @inbounds list1[i][j,k] *= v[k]
      end
    end 
  end 
  #and now as elements of M
  auxmat = mS.map*ms.map
  auxmat2 = change_base_ring(auxmat, R)
  for j = 1:length(list1)
    @inbounds list1[j] = list1[j]*auxmat2
  end
  return list1

end

function submodules_with_struct(M::ZpnGModule, typesub::Array{Int,1})
  # If the group is cyclic, it is easier 
  if length(typesub) == 1
    return main_submodules_cyclic(M, typesub[1])
  end
  sort!(typesub)
  return _submodules_with_struct_main(M, typesub)
end

function _no_redundancy(list::Array{nmod_mat,1}, w::Array{fmpz,1})

  R = base_ring(list[1])
  n = ncols(list[1])
  #
  #  Howell form of every candidate, embedding them in a free module
  #
  for i = 1:length(list)
    if n > nrows(list[i])
      @inbounds list[i] = vcat(list[i], zero_matrix(R, n-nrows(list[i]), ncols(list[i])))
    end
    for j=1:n
      for k=1:nrows(list[i])
        @inbounds list[i][k,j] *= w[j]
      end
    end
    howell_form!(list[i])
    list[i] = view(list[i], 1:n, 1:n)
  end

  #
  #  Now, check if they are equal
  #
  i=1
  list1 = nmod_mat[list[1]]
  for i = 2:length(list)
    found = false
    for j = 1:length(list1)
      if list[i] == list1[j]
        found = true
        break
      end
    end
    if !found
      push!(list1, list[i])
    end
  end
  
  #
  #  Write them again not embedded
  #
  for i=1:length(list1)
    for j=1:n
      for k=1:j
        list1[i][k,j] = divexact(list1[i][k,j].data, w[j])
      end
    end
  end
  return list1

end

###############################################################################
#
#  Submodules of given order
#
###############################################################################

function submodules_order(M::ZpnGModule, ord::Int)
  
  R=M.R
  S,mS=snf(M)
  @assert exponent(S.V)==fmpz(R.n)
  N=Hecke._exponent_p_sub(S)
  lf=composition_factors(N)
  list=nmod_mat[]
  v=fmpz[divexact(S.V.snf[i], M.p) for i=1:ngens(S.V)]
  for i=1:ord-1
    minlist=minimal_submodules(N,i,lf)
    for x in minlist  
      A=lift(x,R) 
      for s=1:nrows(A)
        for t=1:ncols(A)
          A[s,t]*=v[t]
        end
      end
      L, _=quo(S,A)
      newlist=Hecke.submodules_order(L,ord-i)
      for z=1:length(newlist)
        push!(list,vcat(newlist[z],A))
      end
    end
  end
  
  #
  #  Check for redundancy
  #
  w=fmpz[divexact(fmpz(R.n), S.V.snf[j]) for j=1:ngens(S.V)]
  list=_no_redundancy(list,w)
  
  #
  #  Write the submodules in terms of the set of given generators
  #
  
  MatSnf=change_base_ring(mS.map, R)
  for j=1:length(list)
    list[j]=list[j]*MatSnf #vcat([W(( mS( S.V([list[j][k,i].data for i=1:ngens(S.V)]))).coeff)  for k=1:nrows(list[j])])
  end
  
  #
  #  Add the minimal submodules
  # 
  
  minlist=minimal_submodules(N,ord, lf)
  for x in minlist
    push!(list, vcat([W((mS( S.V([FlintZZ(coeff(x[k,i],0))*((M.p)^(v[i]-1)) for i=1:ngens(S.V)]))).coeff) for k=1:nrows(x) ]))
  end
  return (x for x in list)
  
end

###############################################################################
#
#  Submodules with given structure of the quotient
#
###############################################################################

function submodules_with_quo_struct(M::ZpnGModule, typequo::Array{Int,1})
  
  R = base_ring(M)
  p = M.p 
  S, mS = snf(M)
  sort!(typequo)
  wish = DiagonalGroup(Int[p^i for i in typequo])

  if isisomorphic(wish, S.V)
    return (nmod_mat[zero_matrix(R, 1, ngens(M.V))])
  end
  if length(typequo) > length(S.V.snf)
    return (nmod_mat[])
  end
  for i = 1:length(typequo)
    if !divisible(S.V.snf[ngens(S.V)+1-i],fmpz((M.p)^typequo[length(typequo)+1-i]))
      return (nmod_mat[])
    end
  end

  #
  #  Dual Module and candidate submodules
  #
  M_dual = dual_module(S)
  candidates = submodules_with_struct(M_dual, typequo)
  #
  #  Dualize the modules
  #
  v = [divexact(S.V.snf[end],S.V.snf[j]) for j=1:ngens(S.V) ]
  list = (_dualize(x, S.V, v) for x in candidates) 
   
  #
  #  Write the submodules in terms of the given generators
  #
  MatSnf = change_base_ring(mS.map, R)
  return (final_check_and_ans(x, MatSnf, M) for x in list)
  
end

function final_check_and_ans(x::nmod_mat, MatSnf::nmod_mat, M::ZpnGModule)
  
  y=x*MatSnf
  @hassert :RayFacElem 1 issubmodule(M, y)
  return y 

end

##################################################################################
#
#  Stable Subgroups function
#
##################################################################################

@doc Markdown.doc"""
***
    stable_subgroups(R::GrpAbFinGen, quotype::Array{Int,1}, act::Array{T, 1}; op=sub)
    
Given a group R, an array of endomorphisms of the group and the type of the quotient, it returns all the stable 
subgroups of R such that the corresponding quotient has the required type.
"""
function stable_subgroups(R::GrpAbFinGen, act::Array{T, 1}; op = sub, quotype::Array{Int,1}=Int[-1], minimal::Bool = false) where T <: Map{GrpAbFinGen, GrpAbFinGen} 

  if quotype[1] != -1 && minimal
    error("Cannot compute minimal submodules with prescribed quotient type")
  end
  if quotype[1]!= -1
    #I write quotype as the diagonal entries of the snf form.
    DG = DiagonalGroup(quotype)
    quotype = map(Int, snf(DG)[1].snf)
  end
  c = lcm(quotype[end], Int(order(R)))
  Q, mQ = quo(R, c, false)
  lf = factor(order(Q)).fac
  list = []
  for p in keys(lf)
    
    x1 = valuation(lcm(quotype[end], Int(order(R))), p)
    if iszero(x1)
      continue
    end
    G, mG = psylow_subgroup(Q, p, false)
    S, mS = snf(G)
    
    #
    #  Action on the group: we need to distinguish between FqGModule and ZpnGModule (in the first case the algorithm is more efficient)
    #
    
    if x1 == 1
      
      F = GF(Int(p), cached = false)
      act_mat=Array{gfp_mat, 1}(undef, length(act))
      for w=1:length(act)
        act_mat[w] = zero_matrix(F,ngens(S), ngens(S))
      end
      for w=1:ngens(S)
        el=mG(mS(S[w]))
        for z=1:length(act)
          elz=mS\(haspreimage(mG, act[z](el))[2])
          for l=1:ngens(S)
            act_mat[z][w,l]=elz[l]
          end
        end
      end
      M = ModAlgAss(act_mat)
      #
      #  Searching for submodules
      #
      if quotype[1]!= -1
        quotype_p = Int[]
        for i=1:length(quotype)
          v = valuation(quotype[i],p)
          if v > 0
            push!(quotype_p,v)
          end
        end
        if Int(p)*quotype_p == S.snf
          plist1 = GrpAbFinGenElem[c*R[i] for i=1:ngens(R)]
          push!(list, (Vector{GrpAbFinGenElem}[plist1]))
          continue
        end
        ind = length(quotype_p)
        plist = submodules(M, ind)
      else
        if minimal
          plist = minimal_submodules(M)
        else
          plist = submodules(M)
        end
      end
      it = (_lift_and_construct(x, mQ, mG, mS, lcm(quotype[end], Int(order(R)))) for x in plist)
      push!(list, it)

    else    
    
      RR = ResidueRing(FlintZZ, Int(p)^x1, cached=false)
      act_mat1 = Array{nmod_mat,1}(undef, length(act))
      auxmat1 = hcat(mG.map', rels(Q)')
      auxmat2 = mS.map*mG.map
      for z=1:length(act)
        y = transpose(solve(auxmat1, (auxmat2*act[z].map)'))
        y = sub(y, 1:ngens(S), 1:ngens(G))*mS.imap
        act_mat1[z] = change_base_ring(y, RR)
      end
      
      #
      #  Searching for submodules
      #
      
      M1 = Hecke.ZpnGModule(S, act_mat1)
      if quotype[1]!= -1
        quotype_p=Int[]
        for i=1:length(quotype)
          v = valuation(quotype[i],p)
          if v>0
            push!(quotype_p, v)
          end
        end
        if Int(p)*quotype_p == S.snf
          plist1 = GrpAbFinGenElem[c*R[i] for i=1:ngens(R)]
          push!(list, ([plist1]))
          continue
        end
        plist = submodules(M1, typequo = quotype_p)
      else
        if minimal
          plist = minimal_submodules(M1)
        else
          plist = submodules(M1)
        end
      end
      it = (_lift_and_construct(x, mQ, mG, mS, lcm(quotype[end], Int(order(R)))) for x in plist)
      push!(list, it)
    end
  end
  if isempty(list)
    return ([])
  end

  if minimal
    res1 = collect(list[1])
    for j = 2:length(list)
      append!(res1, collect(list[j]))
    end
    return (op(R, cc) for cc in res1)
  else
     return ( op(R, vcat(cc...)) for cc in Iterators.product(list...))
  end
end




function _lift_and_construct(A::Zmodn_mat, mQ::GrpAbFinGenMap, mG::GrpAbFinGenMap, mS::GrpAbFinGenMap, c::Int)
  
  R=mQ.header.domain
  newsub=GrpAbFinGenElem[c*R[i] for i=1:ngens(R)]
  for i=1:nrows(A)
    y=view(A, i:i, 1:ncols(A))
    if !iszero(y)
      push!(newsub,mQ\(mG(mS(mS.header.domain(lift(y))))))
    end       
  end
  return newsub

end
