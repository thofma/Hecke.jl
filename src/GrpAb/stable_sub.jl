add_verbosity_scope(:StabSub)
add_assertion_scope(:StabSub)

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


#  Action of a matrix on an element of the group
function *(x::FinGenAbGroupElem, M::zzModMatrix)
  G = parent(x)
  @assert ngens(G) == nrows(M)
  R = base_ring(M)
  coeff = map_entries(R, x.coeff)
  y = coeff*M
  l = lift(y)
  return FinGenAbGroupElem(G, l)
end


#  Smith Normal Form for a ZpnGModule
function Nemo.snf(M::ZpnGModule)
  A = M.V
  G = M.G
  if is_snf(A)
    return M, id_hom(A)
  end
  R = base_ring(M)
  S, mS = snf(A)
  image_mS = map_entries(R, mS.map)
  preimage_mS = map_entries(R, mS.imap)
  H = Vector{zzModMatrix}(undef, length(G))
  for i=1:length(G)
    H[i] = image_mS*G[i]*preimage_mS
  end
  return ZpnGModule(S, H), mS
end

function is_stable(act::Vector{T}, mS::FinGenAbGroupHom) where T <: Map{FinGenAbGroup, FinGenAbGroup}

  S=mS.header.domain
  for s in gens(S)
    x=mS(s)
    for g in act
      if !has_preimage_with_preimage(mS,g(x))[1]
        return false
      end
    end
  end
  return true

end

function is_submodule(M::ZpnGModule, S::zzModMatrix)

  #@assert is_snf(M.V)
  s, ms = submodule_to_subgroup(M, S)
  for x in gens(s)
    el=ms(x)
    for g in M.G
      if !has_preimage_with_preimage(ms,el*g)[1]
        return false
      end
    end
  end
  return true

end

#
#  Given a group $G$ and a group of automorphisms of G, this function returns the corresponding ZpnGModule
#

function action(V::FinGenAbGroup, act::Vector{T}) where T<: Map{FinGenAbGroup, FinGenAbGroup}

  expon = Int(exponent(V))
  @hassert :StabSub 1 length(factor(order(V)).fac)==1
  RR = residue_ring(FlintZZ, expon, cached=false)[1]
  act_mat = Vector{zzModMatrix}(undef, length(act))
  for z = 1:length(act)
    A = zero_matrix(RR, ngens(V), ngens(V))
    for i = 1:ngens(V)
      y = act[z](V[i])
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

  @assert is_snf(M.V)
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

function _dualize(M::zzModMatrix, V::FinGenAbGroup, v::Vector{ZZRingElem})
  #  First, compute the kernel of the corresponding homomorphisms
  K = abelian_group(ZZRingElem[V.snf[end] for j=1:nrows(M)])
  A = lift(transpose(M))
  for j=1:nrows(A)
    for k=1:ncols(A)
      A[j, k] *= v[j]
    end
  end
  mH = Hecke.FinGenAbGroupHom(V, K, A)
  newel = kernel_as_submodule(mH)
  return change_base_ring(base_ring(M), newel)
end

function _dualize_1(M::zzModMatrix, snf_struct::Vector{ZZRingElem})

  A=kernel(transpose(M), side = :right)
  B=vcat(transpose(A),zero_matrix(M[1,1].parent, ncols(A),ncols(A)))
  for j=1:ncols(A)
    B[nrows(A)+j,j]=snf_struct[j]
  end
  S=kernel(B, side = :right)
  C=vcat(transpose(A),zero_matrix(M[1,1].parent, ncols(A),ncols(A)))
  return S*C

end

function kernel_as_submodule(h::FinGenAbGroupHom)
  G = domain(h)
  H = codomain(h)
  hn, t = hnf_with_transform(vcat(h.map, rels(H)))
  for i=1:nrows(hn)
    if is_zero_row(hn, i)
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


function quo(M::ZpnGModule, S::zzModMatrix)
  Q, mQ=quo(M.V, lift(S), false)
  return ZpnGModule(Q, M.G), mQ
end

function sub(M::ZpnGModule, S::zzModMatrix)

  sg, msg=sub(M.V, lift(S), false)
  G=Vector{zzModMatrix}(undef, length(M.G))
  for k=1:length(M.G)
    A=zero_matrix(M.R, ngens(sg), ngens(sg))
    for i=1:ngens(sg)
      x=msg(sg[i])*M.G[k]
      x=has_preimage_with_preimage(msg, x)[2].coeff
      for j=1:ngens(sg)
        A[i,j]=x[1,j]
      end
    end
    G[k]=A
  end
  return ZpnGModule(sg,G), msg

end


function sub(M::ZpnGModule, n::Int)

  if is_snf(M.V)
    return _sub_snf(M, n)
  end
  sg, msg = sub(M.V, n, false)
  R = base_ring(M)
  G = Vector{zzModMatrix}(undef, length(M.G))
  big_m = vcat(msg.map, rels(M.V))
  for k = 1:length(M.G)
    A = map_entries(R, msg.map)*M.G[k]
    fl, res = can_solve_with_solution(big_m, lift(A), side = :left)
    @assert fl
    G[k] = map_entries(R, view(res, 1:ngens(sg), 1:ngens(sg)))
  end
  return ZpnGModule(sg,G), msg

end

function _sub_snf(M::ZpnGModule, n::Int)
  V = M.V
  nfmpz = ZZRingElem(n)
  ind = 1
  while V.snf[ind] <= nfmpz
    ind += 1
  end
  invariants = Vector{ZZRingElem}(undef, length(V.snf)-ind+1)
  for i = ind:length(V.snf)
    invariants[i-ind+1] = divexact(V.snf[i], n)
  end
  Gnew = abelian_group(invariants)
  action = zzModMatrix[sub(x, ind:ngens(V), ind:ngens(V)) for x in M.G]
  mat_map = zero_matrix(FlintZZ, length(invariants), ngens(V))
  for i = 1:ngens(Gnew)
    mat_map[i, ind+i-1] = n
  end
  mGnew = hom(Gnew, M.V, mat_map)
  return ZpnGModule(Gnew, action), mGnew
end


function _exponent_p_sub(M::ZpnGModule; F::fpField = Native.GF(M.p, cached = false))
  @assert is_snf(M.V)
  G = M.G
  V = M.V
  p = M.p
  v = ZZRingElem[divexact(V.snf[i], p) for i=1:ngens(V)]
  G1 = Vector{fpMatrix}(undef, length(G))
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
  return Amodule(G1)

end

function submodule_to_subgroup(M::ZpnGModule, S::zzModMatrix)
  return sub(M.V, lift(S), false)
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
  list = Vector{zzModMatrix}(undef, length(list_sub))
  v = Int[M.p^(valuation(S.V.snf[i], M.p)-1) for i=1:ngens(S.V)]
  W = matrix_space(R, 1, ngens(M.V); cached=false)
  for z = 1:length(list)
    list[z] = reduce(vcat, [W((mS(S.V(ZZRingElem[lift(list_sub[z][k,i])*v[i] for i=1:ngens(S.V)]))).coeff) for k=1:nrows(list_sub[z])])
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
  list=Vector{zzModMatrix}(undef, length(minlist))
  v=[divexact(ZZRingElem(R.n),S.V.snf[j]) for j=1:ngens(S.V) ]
  for x in minlist
    K = abelian_group([ZZRingElem(R.n) for j=1:nrows(x)])
    A = lift(transpose(x))
    for j=1:nrows(A)
      for k=1:ncols(A)
        A[j,k]*=v[j]
      end
    end
    mH = Hecke.FinGenAbGroupHom(S.V,K,A)
    sg, msg = kernel(mH)
    push!(list, reduce(vcat, [(mS(msg(y))).coeff for y in gens(sg)]))
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
function _change_ring(G::Vector{zzModMatrix}, F::fpField, s::Int)

  G1 = Vector{fpMatrix}(undef, length(G))
  n = nrows(G[1])
  for i = 1:length(G)
    M = zero_matrix(F,n-s+1,n-s+1)
    for j = s:n
      for k = s:n
        M[j-s+1,k-s+1] = F(deepcopy((G[i][j,k]).data))
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
  G = M.G
  V = M.V
  p = M.p
  @assert is_snf(V)
  #  First, the quotient M/pM
  F = Native.GF(p, cached = false)
  n = ngens(V)
  Gq = _change_ring(G, F, 1)
  spaces = [Amodule(Gq)]
  #
  #  Now, the others
  #
  s = valuation(ZZRingElem(M.R.n),p)
  j = 1
  for i = 2:s
    while !is_divisible_by(V.snf[j], p^i)
      j += 1
    end
    GNew = _change_ring(G, F, j)
    push!(spaces, Amodule(GNew))
  end
  return spaces
end

function composition_factors_with_multiplicity(M::ZpnGModule; dimension::Int = -1)
  N, _ = snf(M)
  list_sub = _mult_by_p(N)
  list = Vector{Tuple{ModAlgAss{fpField, fpMatrix, matrix_algebra_type(fpField)}, Int}}()
  for x in list_sub
    append!(list, composition_factors_with_multiplicity(x, dimension = dimension))
  end
  final_list = Vector{Tuple{ModAlgAss{fpField, fpMatrix, matrix_algebra_type(fpField)}, Int}}()
  done = falses(length(list))
  for i = 1:length(list)
    if done[i]
      continue
    end
    done[i] = true
    mult = list[i][2]
    for j = i+1:length(list)
      if !done[j] && is_isomorphic(list[i][1], list[j][1])
        mult += list[j][2]
        done[j] = true
      end
    end
    push!(final_list, (list[i][1], mult))
  end
  return final_list
end

###############################################################################
#
#  Submodules interface
#
###############################################################################

@doc raw"""
    submodules(M::ZpnGModule; typequo, typesub, order)

Given a ZpnGModule $M$, the function returns all the submodules of $M$.

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
    return (zzModMatrix[])
  end
  S,mS = snf(M)
  minlist = minimal_submodules(S)
  list = zzModMatrix[identity_matrix(R, length(S.V.snf)), zero_matrix(R,1,length(S.V.snf))]

  #
  #  Find minimal submodules, factor out and recursion on the quotients
  #

  for x in minlist
    N, _ = quo(S, x)
    newlist = submodules_all(N)
    for y in newlist
      push!(list,vcat(y,x))
    end
  end

  append!(list,minlist)
  #
  #  Eliminate redundance via Howell form
  #
  w=ZZRingElem[divexact(ZZRingElem(R.n), S.V.snf[j]) for j=1:ngens(S.V)]
  list=_no_redundancy(list, w)

  #
  #  Writing the submodules in terms of the given generators and returning an iterator
  #
  MatSnf=change_base_ring(R, mS.map)
  return (x*MatSnf for x in list)

end

###############################################################################
#
#  Submodules with given structure as a subgroup
#
###############################################################################

function main_submodules_cyclic(M::ZpnGModule, ord::Int)

  lf = composition_factors_with_multiplicity(M, dimension = 1)
  if isempty(lf)
    return Vector{zzModMatrix}()
  end
  list = _submodules_with_struct_cyclic(M, ord, lf)
  for step = 1:ord-1
    c = ZZRingElem(M.p^step)
    list1 = zzModMatrix[]
    for x in list
      L, _ = quo(M, x)
      newlist = _submodules_with_struct_cyclic(L, ord-step, lf)
      for i = 1:length(newlist)
        mat_test = lift(newlist[i])
        mul!(mat_test, mat_test, c)
        el = FinGenAbGroupElem(M.V, mat_test)
        if !iszero(el)
          push!(list1, newlist[i])
        end
      end
    end
    list = list1
  end
  return list

end

function _submodules_with_struct_cyclic(M::ZpnGModule, ord::Int, lf)
  R = M.R
  #  We search for an element in p^(ord-1)*G
  s, ms = sub(M, M.p^(ord-1))
  S, mS = snf(s)
  N = _exponent_p_sub(S, F = coefficient_ring(lf[1][1]))
  @vtime :StabSub 1 submod = minimal_submodules(N, 1, lf)
  list1 = Vector{zzModMatrix}(undef, length(submod))
  v = zzModRingElem[R(divexact(S.V.snf[i], M.p)) for i = 1:ngens(S.V)]
  for i = 1:length(submod)
    list1[i] = lift(submod[i], R)
    @assert nrows(list1[i]) == 1
    for k = 1:ncols(list1[i])
      list1[i][1, k] *= v[k]
    end
  end
  MatSnf = change_base_ring(R, mS.map*ms.map)
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
  new_typesub = Vector{Int}(undef, length(typesub))
  for j = 1:i-1
    new_typesub[j] = typesub[j]
  end
  for j = i:length(new_typesub)
    new_typesub[j] = typesub[j] - 1
  end
  return new_typesub
end


function _submodules_with_struct_main(M::ZpnGModule, typesub::Vector{Int})
  @assert is_snf(M.V)
  p = M.p
  R = base_ring(M)
  #First iteration out of the loop.
  list = _submodules_with_struct(M, typesub)
  @vprintln :StabSub 1 "Subgroups at first step: $(length(list))"
  #Some data needed in the loop
  w = Vector{ZZRingElem}(undef, ngens(M.V))
  for i = 1:length(w)
    w[i] = divexact(ZZRingElem(R.n), M.V.snf[i])
  end
  new_typesub = _update_typesub(typesub)
  #Now, the iterative process.
  for i = 1:typesub[end]-1
    list1 = zzModMatrix[]
    new_typesub1 = _update_typesub(new_typesub)
    diag = typesub - new_typesub1
    Gtest = snf(abelian_group(Int[p^x for x in diag]))[1]
    order_test = order(Gtest)
    for x in list
      L, _ = quo(M, x)
      newlist = _submodules_with_struct(L, new_typesub)
      @vprintln :StabSub 1 "Candidates to be added at this step: $(length(newlist))"
      #First, I sieve for the subgroups with the correct structure.
      for s = 1:length(newlist)
        ord = ZZRingElem(1)
	      for t = 1:nrows(newlist[s])
          ord *= order(FinGenAbGroupElem(M.V, lift(view(newlist[s], t:t, 1:ncols(newlist[s])))))
	      end
        if ord >= order_test
          t1, mt1 = submodule_to_subgroup(M, newlist[s])
          if _special_is_isomorphic(t1, Gtest)
	          push!(list1, newlist[s])
	        end
        end
      end
      @vprintln :StabSub 1 "New till this point at this step: $(length(list1))"
    end
    new_typesub = new_typesub1
    list = list1
  end
  return list
end

function _special_is_isomorphic(G::FinGenAbGroup, Gtest::FinGenAbGroup)
  if is_snf(G)
    return G.snf == Gtest.snf
  end
  mat = hnf_modular_eldiv(G.rels, exponent(Gtest))
  mm = snf(mat)
  inv = ZZRingElem[mm[i, i] for i = 1:ncols(mm) if !isone(mm[i, i])]
  return inv == Gtest.snf
end

function _submodules_with_struct(M::ZpnGModule, typesub::Vector{Int})

  R = base_ring(M)
  s, ms = sub(M, M.p^(typesub[end]-1))
  S, mS = snf(s)
  N = _exponent_p_sub(S)

  i = 1
  while typesub[i] != typesub[end]
    i += 1
  end
  a = length(typesub) - i + 1

  @vtime :StabSub 1 submod = submodules(N, (dim(N))-a)
  #
  #  Write the modules as elements of S
  #

  list1 = Vector{zzModMatrix}(undef, length(submod))
  v = ZZRingElem[divexact(S.V.snf[i], M.p) for i = 1:ngens(S.V)]
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
  auxmat2 = change_base_ring(R, auxmat)
  for j = 1:length(list1)
    @inbounds list1[j] = list1[j]*auxmat2
  end
  return list1

end

function submodules_with_struct(M::ZpnGModule, typesub::Vector{Int})
  # If the group is cyclic, it is easier
  if length(typesub) == 1
    return main_submodules_cyclic(M, typesub[1])
  end
  sort!(typesub)
  return _submodules_with_struct_main(M, typesub)
end

function _no_redundancy(list::Vector{zzModMatrix}, w::Vector{ZZRingElem})

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
  list1 = zzModMatrix[list[1]]
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
  @assert exponent(S.V)==ZZRingElem(R.n)
  N=Hecke._exponent_p_sub(S)
  lf=composition_factors_with_multiplicity(N)
  list=zzModMatrix[]
  v=ZZRingElem[divexact(S.V.snf[i], M.p) for i=1:ngens(S.V)]
  for i=1:ord-1
    minlist=minimal_submodules(N,i,lf)
    for x in minlist
      A=lift(x,R)
      for s=1:nrows(A)
        for t=1:ncols(A)
          A[s,t]*=v[t]
        end
      end
      L, _=quo(S, A, false)
      newlist=Hecke.submodules_order(L,ord-i)
      for z=1:length(newlist)
        push!(list,vcat(newlist[z],A))
      end
    end
  end

  #
  #  Check for redundancy
  #
  w=ZZRingElem[divexact(ZZRingElem(R.n), S.V.snf[j]) for j=1:ngens(S.V)]
  list=_no_redundancy(list,w)

  #
  #  Write the submodules in terms of the set of given generators
  #

  MatSnf=map(mS.map, R)
  for j=1:length(list)
    list[j]=list[j]*MatSnf #reduce(vcat, [W(( mS( S.V([list[j][k,i].data for i=1:ngens(S.V)]))).coeff)  for k=1:nrows(list[j])])
  end

  #
  #  Add the minimal submodules
  #

  minlist=minimal_submodules(N,ord, lf)
  for x in minlist
    push!(list, reduce(vcat, [W((mS( S.V(ZZRingElem[FlintZZ(coeff(x[k,i],0))*((M.p)^(v[i]-1)) for i=1:ngens(S.V)]))).coeff) for k=1:nrows(x) ]))
  end
  return (x for x in list)

end

###############################################################################
#
#  Submodules with given structure of the quotient
#
###############################################################################

function submodules_with_quo_struct(M::ZpnGModule, typequo::Vector{Int})

  R = base_ring(M)
  p = M.p
  S, mS = snf(M)
  sort!(typequo)
  wish = abelian_group(Int[p^i for i in typequo])

  if is_isomorphic(wish, S.V)
    return (zzModMatrix[zero_matrix(R, 1, ngens(M.V))])
  end
  if length(typequo) > length(S.V.snf)
    return (zzModMatrix[])
  end
  for i = 1:length(typequo)
    if !is_divisible_by(S.V.snf[ngens(S.V)+1-i],ZZRingElem((M.p)^typequo[length(typequo)+1-i]))
      return (zzModMatrix[])
    end
  end


  #  Dual Module and candidate submodules
  M_dual = dual_module(S)
  candidates = submodules_with_struct(M_dual, typequo)

  #  Dualize the modules
  v = ZZRingElem[divexact(S.V.snf[end],S.V.snf[j]) for j=1:ngens(S.V) ]
  list = (_dualize(x, S.V, v) for x in candidates)

  #  Write the submodules in terms of the given generators
  MatSnf = change_base_ring(R, mS.map)
  return (final_check_and_ans(x, MatSnf, M) for x in list)

end

function final_check_and_ans(x::zzModMatrix, MatSnf::zzModMatrix, M::ZpnGModule)

  y=x*MatSnf
  @hassert :RayFacElem 1 is_submodule(M, y)
  return y

end

##################################################################################
#
#  Stable Subgroups function
#
##################################################################################

@doc raw"""
    stable_subgroups(R::FinGenAbGroup, quotype::Vector{Int}, act::Vector{T}; op=sub)

Given a group $R$, an array of endomorphisms of the group and the type of the quotient, it returns all the stable
subgroups of $R$ such that the corresponding quotient has the required type.
"""
function stable_subgroups(R::FinGenAbGroup, act::Vector{T}; op = sub, quotype::Vector{Int} = Int[-1], minimal::Bool = false) where T <: Map{FinGenAbGroup, FinGenAbGroup}
  subs = _stable_subgroups(R, act; quotype = quotype, minimal = minimal)
  #Finally, translate back to R.
  return (op(R, x) for x in subs)
end

function stable_subgroups_for_abexts(R::FinGenAbGroup, act::Vector{FinGenAbGroupHom}, quotype::Vector{Int})
  S, mS = snf(R)
  #I translate the action to S
  actS = Vector{FinGenAbGroupHom}(undef, length(act))
  for i = 1:length(act)
    imgs = Vector{FinGenAbGroupElem}(undef, ngens(S))
    for j = 1:length(imgs)
      imgs[j] = mS\(act[i](mS(S[j])))
    end
    actS[i] = hom(S, S, imgs, check = false)
  end
  subs_snf = _stable_subgroup_snf(S, actS; quotype = quotype)
  return (inv(mS)*quo(S, y, false)[2] for y in subs_snf)
end

function _stable_subgroups(R::FinGenAbGroup, act::Vector{T}; quotype::Vector{Int} = Int[-1], minimal::Bool = false) where T <: Map{FinGenAbGroup, FinGenAbGroup}
  if quotype[1] != -1 && minimal
    error("Cannot compute minimal submodules with prescribed quotient type")
  end
  if quotype[1]!= -1
    #I write quotype as the diagonal entries of the snf form.
    DG = abelian_group(quotype)
    quotype = Int[Int(x) for x in snf(DG)[1].snf]
  end
  c = lcm(quotype[end], exponent(R))
  Q, mQ = quo(R, c, false)
  S, mS = snf(Q)
  #I translate the action to S
  actS = Vector{FinGenAbGroupHom}(undef, length(act))
  for i = 1:length(act)
    imgs = Vector{FinGenAbGroupElem}(undef, ngens(S))
    for j = 1:length(imgs)
      imgs[j] = mS\(mQ(act[i](mQ\mS(S[j]))))
    end
    actS[i] = hom(S, S, imgs, check = false)
  end
  subs_snf = _stable_subgroup_snf(S, actS; quotype = quotype, minimal = minimal)
  return (FinGenAbGroupElem[mQ\mS(x) for x in y] for y in subs_snf)
end

function _stable_subgroup_snf(R::FinGenAbGroup, act::Vector{FinGenAbGroupHom}; quotype::Vector{Int} = Int[-1], minimal::Bool = false)
  @assert is_snf(R)
  c = exponent(R)
  lf = factor(c)
  list = Base.Generator[]
  for p in keys(lf.fac)
    x1 = valuation(c, p)
    G, mG = sylow_subgroup(R, p, false)
    S, mS = snf(G)
    comp = mS*mG

    #We need to distinguish between FqGModule and ZpnGModule (in the first case the algorithm is more efficient)
    if x1 == 1
      F = Native.GF(Int(p), cached = false)
      act_mat = Vector{fpMatrix}(undef, length(act))
      for w=1:length(act)
        act_mat[w] = zero_matrix(F, ngens(S), ngens(S))
      end
      for w = 1:ngens(S)
        el = mG(mS(S[w]))
        for z = 1:length(act)
          elz=mS\(has_preimage_with_preimage(mG, act[z](el))[2])
          for l = 1:ngens(S)
            act_mat[z][w,l] = elz[l]
          end
        end
      end
      M = Amodule(act_mat)
      #  Searching for submodules
      if quotype[1] != -1
        ind = 0
        for i = 1:length(quotype)
          if !is_coprime(quotype[i], p)
            ind += 1
          end
        end
        plist = submodules(M, ind)
      else
        if minimal
          plist = minimal_submodules(M)
        else
          plist = submodules(M)
        end
      end
      it = (_lift_and_construct(x, comp) for x in plist)
      push!(list, it)
    else

      RR = residue_ring(FlintZZ, Int(p)^x1, cached=false)[1]
      act_mat1 = Vector{zzModMatrix}(undef, length(act))
      for z=1:length(act)
        imgs = FinGenAbGroupElem[]
	      for w = 1:ngens(S)
	        el = act[z](comp(S[w]))
	        fl, el1 = has_preimage_with_preimage(mG, el)
	        @assert fl
          push!(imgs, mS\(el1))
	      end
        act_mat1[z] = map_entries(RR, hom(S, S, imgs).map)
      end

      #  Searching for submodules
      M1 = ZpnGModule(S, act_mat1)
      if quotype[1] != -1
        quotype_p = Int[]
        for i=1:length(quotype)
          v = valuation(quotype[i],p)
          if v>0
            push!(quotype_p, v)
          end
        end
        plist = submodules(M1, typequo = quotype_p)
      else
        if minimal
          plist = minimal_submodules(M1)
        else
          plist = submodules(M1)
        end
      end
      it = (_lift_and_construct(x, comp) for x in plist)
      push!(list, it)
    end
  end
  if isempty(list)
    return Base.Generator([])
  end

  if minimal
    res1 = collect(list[1])
    for j = 2:length(list)
      append!(res1, collect(list[j]))
    end
    return res1
  else
     return ( vcat(cc...) for cc in Iterators.product(list...))
  end
end

function _lift_and_construct(A::Zmodn_mat, mp::FinGenAbGroupHom)
  R = codomain(mp)
  G = domain(mp)
  newsub = FinGenAbGroupElem[]
  for i=1:nrows(A)
    if !is_zero_row(A, i)
      y = view(A, i:i, 1:ncols(A))
      el = FinGenAbGroupElem(G, lift(y))
      push!(newsub, mp(el))
    end
  end
  return newsub
end
