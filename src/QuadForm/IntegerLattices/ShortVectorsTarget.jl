########################################################################################
#
#            Short vectors with condition
#
########################################################################################

raw"""
    short_vectors_with_condition(L::ZZLat; search_fixed_vectors::Bool) -> Tuple{<:Vector, <:Vector}, Vector{ZZMatrix}

Return a list of vectors, that contains the orbits of the standard basis vectors under the reduced automorphism group $\mathrm{Aut}(L, \rho)$.
together with a list of $\mathrm{Aut}(L, \rho)$-invariant gram matrices where $\rho$ is a Weyl vector of the root sublattice of `L`.

# Input
- `search_fixed_vectors::Bool` -- take sums of vectors with the same invariants to obtain new invariant vectors. Use it to refine the invariant. Rinse and repeat.

# Output:
- a tuple `(V, G)` consiting of:
- a list of tuples `V = [(v_1, n_1), (v_2, n_2), ....]`; where `v_i` is a point of `L` and `n_i` an $\mathrm{Aut}(L,\rho)$ invariant of `v_i`, called its "norm".
- a list of symmetric integer matrices `G = [G_1, ..., G_k]`;
such that:
- `dot(v_i,G[j]*v_i) == (n_i)[j]` for all `i` in `1,...,rank(L)` and `j` in `1,...,k`.
- the standard basis vectors and their norms with respect to `G` are contained in `V`
"""
function short_vectors_with_condition(L::ZZLat;
                                      search_fixed_vectors::Bool=false,
                                      search_invariant_subspace::Bool=false,
                                      use_dual::Bool=false)
  return short_vectors_with_condition(ZZRingElem, L; search_fixed_vectors, search_invariant_subspace, use_dual)
end

function short_vectors_with_condition(T::Type,
                                      L::ZZLat;
                                      search_fixed_vectors::Bool=true,
                                      search_invariant_subspace::Bool=false,
                                      use_dual::Bool=false,)
  _data = _short_vectors_with_condition_preprocessing(L, use_dual)
  return _short_vectors_with_condition(T, _data...; search_fixed_vectors, search_invariant_subspace)
end


function short_vectors_with_condition(L1::ZZLat,
                                      L2::ZZLat)
  notisom = (Tuple{Vector{Int64},Vector{Int64}}[],ZZMatrix[],(Vector{Int64}[],Vector{Int64}[]))

  T = ZZRingElem
  # We disable the search for fixed vectors and invariant subspaces
  # because it would be difficult to match them
  search_fixed_vectors = false
  search_invariant_subspace = false
  if L1===L2
    return true, _short_vectors_with_condition(L1)
  end
  pre1, (root_type1, fundamental_roots1), invariant_matrix1 = _short_vectors_with_condition_preprocessing_with_root_data(L1)
  pre2, (root_type2, fundamental_roots2), invariant_matrix2 = _short_vectors_with_condition_preprocessing_with_root_data(L2)
  _V1 = Vector{Tuple{Vector{T},Vector{T}}}()
  _V2 = Vector{Tuple{Vector{T},Vector{T}}}()
  if root_type1 != root_type2 || rank(L1) != rank(L2) || det(L1) != det(L2)
    return false, notisom
  end
  n = rank(L1)

  L1,successive_sublattices1, B1, Binv1, projection_ranges1, projL1, projL_gram1, denoms1, target_fixed_part1, target_norms1,grams1 = pre1
  L2,successive_sublattices2, B2, Binv2, projection_ranges2, projL2, projL_gram2, denoms2, target_fixed_part2, target_norms2,grams2 = pre2

  R1 = basis_matrix(successive_sublattices1[1])
  R2 = basis_matrix(successive_sublattices2[1])
  proj1 = solve(R1, projL1[1];side=:left)
  proj2 = solve(R2, projL2[1];side=:left)
  if proj1 != proj2  # same root type and same embedding
    return false, notisom
  end
  T = Int
  target_fixed_part1_wrt_R2 = Tuple{Vector{ZZRingElem},ZZRingElem}[]
  r = nrows(R2)
  for (v,d) in target_fixed_part1
    # TODO: Inefficient ... just do one matrix multiplication instead
    v = matrix(QQ, 1, r, v)
    v1 = v*B1[1:r,:]
    w = ZZ.((solve(R1,v1;side=:left)*R2)*Binv2)
    push!(target_fixed_part1_wrt_R2, (w[1,1:r],d))
  end
  out1 = _short_vectors_with_condition(T,pre1...; search_fixed_vectors, search_invariant_subspace, mode=:auto)
  out2 = _short_vectors_with_condition(T,   L2,successive_sublattices2, B2, Binv2, projection_ranges2, projL2, projL_gram2, denoms2, target_fixed_part1_wrt_R2, target_norms1,grams2 ; search_fixed_vectors, search_invariant_subspace, mode=:iso)
  # can we do without?
  if length(_V1)!=length(_V2) || length(grams1)!=length(grams2)
    return false, notisom
  end
  return true, out1, out2
end

########################################################################################
#
#            Preprocessing
#
########################################################################################

function _short_vectors_with_condition_preprocessing(L::ZZLat, use_dual::Bool=false)
  root_types, fundamental_roots = _root_lattice_recognition_fundamental(L)
  fixed_space, isotypic_coinvariant_space, weyl_vector = _weyl_group(L, root_types, fundamental_roots)
  return _short_vectors_with_condition_preprocessing(L, fundamental_roots, weyl_vector, fixed_space, isotypic_coinvariant_space, :rank, use_dual)
end

function _short_vectors_with_condition_preprocessing_with_root_data(L::ZZLat; use_dual::Bool=false)
  root_types, fundamental_roots = _root_lattice_recognition_fundamental(L)
  fixed_space, isotypic_coinvariant_space, weyl_vector = _weyl_group(L, root_types, fundamental_roots)
  return _short_vectors_with_condition_preprocessing(L, fundamental_roots, weyl_vector, fixed_space, isotypic_coinvariant_space, :rank, use_dual), (root_types, fundamental_roots), fixed_space
end

function _short_vectors_with_condition_preprocessing(L::ZZLat,
                                                     fundamental_roots::Vector{ZZMatrix},
                                                     weyl_vector::Vector{QQFieldElem},
                                                     fixed_space,
                                                     isotypic_coinvariant_space,
                                                     sort::Symbol=:rank,
                                                     use_dual::Bool=false
                                                     )
  @assert rank(L)==degree(L)
  @hassert :Lattice 1 isone(basis_matrix(L))
  n = rank(L)
  V = ambient_space(L)
  R_fix = lattice(V, fixed_space; isbasis=true, check=false)
  R_cofix = [lattice(V, b; isbasis=true, check=false) for b in isotypic_coinvariant_space]
  R = reduce(vcat, fundamental_roots; init=zero_matrix(ZZ, 0, rank(L)))
  GZZ,_  = _integral_split_gram(L)
  Rperp = lattice(V, QQ.(kernel(GZZ*transpose(R); side=:left)); isbasis=true, check=false)
  successive_sublattices = append!([R_fix], R_cofix, _successive_sublattices(Rperp; use_dual))
  @vprintln :Lattice 1 "largest successive sublattice of rank $(maximum(rank.(successive_sublattices)[2:end]))"

  m = length(successive_sublattices)
  if sort == :rank
    # don't touch the first one
    sort!(view(successive_sublattices,2:m);by=rank);
  end

  # Compute L_1,  ... , L_n
  projL, projL_gram, projection_ranges,denoms,successive_sublattices = _grams_proj(L, successive_sublattices)
  m = length(successive_sublattices)
  B = reduce(vcat, projL)
  Binv,bi = integral_split(inv(B),ZZ)
  grams = _get_grams_std(projL_gram, projection_ranges, Binv)
  @assert isone(bi)

  target_norms = Vector{ZZRingElem}[zeros_array(ZZ, m) for i in 1:n]
  for k in 1:m
    for i in 1:n
      target_norms[i][k] = grams[k][i,i]
    end
  end
  rhoG = _numerator(weyl_vector)*GZZ
  r1 = projection_ranges[1]
  target_fixed_part = [(Binv[i, r1], rhoG[i]) for i in 1:n]

  return L, successive_sublattices, B, Binv, projection_ranges, projL, projL_gram, denoms, target_fixed_part, target_norms, grams
end


function _grams_proj(L::ZZLat, successive_sublattices::Vector{ZZLat}; split_further::Bool=false)
  rkLL = rank.(successive_sublattices)
  gramLZZ, _ = _integral_split_gram(L)
  V = ambient_space(L)
  F = reduce(vcat, [basis_matrix(i) for i in successive_sublattices])
  Fi = inv(F)
  r1 = 1
  r2 = rkLL[1]
  projL = QQMatrix[] # projL[i] = L_i := image(L->(L_1+...+L_i)\otimes QQ)
  projL_gram = ZZMatrix[] # lll reduced
  projection_ranges = UnitRange{Int64}[]
  denoms = ZZRingElem[]
  successive_sublattices1 = ZZLat[]
  for i in 1:length(successive_sublattices)
    push!(projection_ranges, r1:r2)
    Si = view(_hnf_integral(view(Fi, :, r1:r2), :upper_right), 1:1+r2-r1,:)*view(F, r1:r2, :)
    # do the following the hard way
    # Li = lll(lattice(rescale(V,denoms[i]; cached=false), Si; isbasis=true, check=false); _is_definite=true)
    SZ, di = integral_split(Si, ZZ)
    push!(denoms, di)
    Gi = divexact!(SZ*gramLZZ*transpose(SZ),di)
    if i > 1
      Gi, U = lll_gram_with_transform(Gi) # inplace variant caused segfault problems
      mul!(SZ, U, SZ)
      Si = set!(Si,SZ)
      mul!(Si, QQ(1,di))
    end
    if split_further
      # this part is not optimized, turned off by default
      Li = lattice(V, Si; isbasis=true, check=false)
      set_attribute!(Li,:_integral_split_gram=>(Gi, ZZ(1)))
      set_attribute!(Li,:is_lll_reduced=>true)
      if nrows(Si)>2 && i>1
        Li_split = _successive_sublattices(Li; use_dual=false)
        append!(successive_sublattices1, Li_split)
      else
        push!(successive_sublattices1, successive_sublattices[i])
      end
    end
    push!(projL, Si)
    push!(projL_gram, Gi)
    r1 += rkLL[i]
    if i<length(successive_sublattices)
      r2 += rkLL[i+1]
    end
  end
  if split_further
    return _grams_proj(L, successive_sublattices1;split_further=false)
  end
  return projL, projL_gram, projection_ranges, denoms, successive_sublattices
end


function _get_grams_std(projL_gram, projection_ranges, Binv)
  grams = ZZMatrix[]
  for (Gi,ri) in zip(projL_gram,projection_ranges)
    C = view(Binv,:, ri)
    Gi_std = C*Gi*transpose(C)
    push!(grams, Gi_std)
  end
  return grams
end

function _short_vectors_with_condition(::Type{CoeffType},
                                                L::ZZLat,
                                                successive_sublattices::Vector{ZZLat},
                                                B::QQMatrix,
                                                Binv::ZZMatrix,
                                                projection_ranges::Vector{UnitRange{Int}},
                                                projL::Vector{QQMatrix},
                                                projL_gram::Vector{ZZMatrix},
                                                denoms::Vector{ZZRingElem},
                                                target_fixed_part::Vector{Tuple{Vector{ZZRingElem}, ZZRingElem}},
                                                target_norms::Vector{Vector{ZZRingElem}},
                                                grams::Vector{ZZMatrix};
                                                search_fixed_vectors::Bool=true,
                                                search_invariant_subspace::Bool=false,
                                                mode::Symbol=:auto) where {CoeffType <: Union{Int, ZZRingElem}}
  # Let L_i := proj[i](L)
  # We lll reduce each L_i and work throughout with the basis
  # M = L_1 + L_2 + ... + L_n
  # Set flag_proj[i] = sum(proj[1:i]) : L --> L_1 + ... + L_i=:N_i and let M_i < N_i be the image
  # We build up the short vectors along the flag
  # M_1 < M_2 < M_3 < .... < M_n = L
  # The step M_i to M_{i+1} is via
  # M_{i+1} < M_i + L_{i+1}
  # and testing for integrality
  # In the postprocessing we transform from the basis of M to the basis of L.
  if CoeffType === ZZRingElem
    VectorType = Vector{ZZRingElem}
  else
    VectorType = LinearAlgebra.Adjoint{Int64, Vector{Int64}}
  end
  rkL = rank(L)
  gramZZ, _ = _integral_split_gram(L)
  V = ambient_space(L)
  rkLL = rank.(successive_sublattices)
  # heuristic to turn off the search
  if maximum(rkLL[2:end]; init=0)<8
    #search_invariant_subspace = false
  end

  L_in_L1toLn = hnf(Binv)
  successive_grams = [[CoeffType(i) for i in j] for j in projL_gram]
  toprojL1 = view(Binv,:,1:nrows(projL[1])) # L --> projL1

  # Keys: ([v1^2, v2^2,...,vi^2],[invariant_subspace_norms], v*G*weyl_vector^T, v1, [fixed_vector_stuff])
  # Key => list of vectors with these invariants
  # the coordinates of v1 are assured to be canonical(!), therefore this works also for isomorphism testing
  KeyType = Tuple{Vector{CoeffType}, Vector{CoeffType}, CoeffType, Vector{CoeffType}, Vector{CoeffType}}
  # Piece together the invariants of the targets
  normalized_targets = Vector{CoeffType}[]  # needed for _vector_sums
  target_invariants = Vector{KeyType}()
  n1 = rkLL[1]
  signs = Vector{Int}(undef, rank(L))
  for i in 1:rkL
    norms = target_norms[i]
    _v1, _v1_weyl = target_fixed_part[i]
    v1 = CoeffType.(_v1)
    v1_weyl = CoeffType(_v1_weyl)
    # transform from the basis of L to that of L_1
    if v1_weyl < 0
      v1 = -v1
      v1_weyl = -v1_weyl
      _sign = -1
    elseif v1_weyl > 0
      _sign = 1
    elseif v1_weyl == 0
      v1, _sign = _canonicalize_with_data!(v1)
    end
    signs[i] = _sign
    _key = (norms, CoeffType[], v1_weyl, v1, CoeffType[])
    push!(target_invariants, _key)
    if mode==:auto
      push!(normalized_targets, _sign*Binv[i,:])
    end
  end

  # Initialisation for the first projection (i = 1)
  short_vectors1 = Dict{KeyType, Vector{VectorType}}()
  for _b in target_invariants
    # We take only one representative up to sign, even if both show up in the targets
    (n,i,t,v1,f) = _b
    b = (n[1:1],i,t,v1,f)
    v1t = __not_adj(v1)
    if b in keys(short_vectors1)
      # different targets can have the same first projection
      if !(v1t in short_vectors1[b])
        push!(short_vectors1[b], v1t)
      end
    else
      short_vectors1[b]=[v1t]
    end
  end

  @vprintln :Lattice 1 "Ranks of successive sublattices $(rank.(successive_sublattices))"
  zeroCoeff = zero(CoeffType)
  for i in 2:length(projL)
    @vprintln :Lattice 1 "Round i=$i"
    @hassert :Lattice 1 all(allunique, values(short_vectors1))
    @hassert :Lattice 1 allunique(reduce(vcat, values(short_vectors1)))
    short_vectors2 = Dict{KeyType,Vector{VectorType}}()
    for a in Set((n[1][1:i], n[2:end]...) for n in target_invariants)
      short_vectors2[a] = VectorType[]
    end

    # prepare for integrality test
    #N_i = reduce(vcat, projL[j] for j in 1:i)
    ni = sum(nrows(projL[j]) for j in 1:i)
    Sf, _, Vf = __snf_with_transform(view(L_in_L1toLn,1:ni,1:ni), false, true, is_hnf=true)
    _eldivNi_mod_Mi = diagonal(Sf)
    n_ones = count(isone, _eldivNi_mod_Mi)
    for i in n_ones+1:ncols(Vf)
      Vf[:,i] = mod.(Vf[:,i] ,_eldivNi_mod_Mi[i])
    end
    eldivNi_mod_Mi = __not_adj(CoeffType.(_eldivNi_mod_Mi[n_ones+1:end]))
    r1 = sum(nrows(projL[j]) for j in 1:i-1)
    VfN_iminus1 = CoeffType.(collect(@view Vf[1:r1, n_ones+1:end]))
    VfLi = CoeffType.(collect(@view Vf[r1+1:end, n_ones+1:end]))

    @assert nrows(VfLi) == nrows(projL[i])
    @vprintln :Lattice 3 "elementary divisors $eldivNi_mod_Mi at stage i=$i"

    # prepare for filtering by norm
    target_norm_i = Set(n[1][i] for n in target_invariants)
    target_norm = Dict{CoeffType, Set{KeyType}}()
    for n in target_invariants
      # keep only the invariants valid at stage i
      a = n[1][i]
      b = (n[1][1:i-1], n[2:end]...)
      push!(get!(target_norm, a, Set{KeyType}()), b)
    end
    # prepare gluing data
    rank_i = nrows(projL[i])
    tmp_u = __zeros_array(CoeffType, ncols(VfN_iminus1))
    short_vectors1_by_glue = Dict{Vector{CoeffType},Dict{KeyType, Vector{VectorType}}}()
    for k1 in keys(short_vectors1)
      for a in short_vectors1[k1]
        a_mod_Mi =__mul_mod!(tmp_u, a, VfN_iminus1, eldivNi_mod_Mi)
        k = a_mod_Mi
        # take into account that short_vectors returns only non-zero vectors.
        if zeroCoeff in keys(target_norm) && k1 in target_norm[zeroCoeff] && iszero(k)
          push!(k1[1], zeroCoeff)
          #@assert !(-__vcat(a,__zeros_array(CoeffType, rank_i)) in reduce(vcat,values(short_vectors2))) k1
          push!(short_vectors2[k1], __vcat(a,__zeros_array(CoeffType, rank_i)))
          pop!(k1[1])
        end
        if k in keys(short_vectors1_by_glue)
          D = short_vectors1_by_glue[k]
          if k1 in keys(D)
            push!(D[k1], a)
          else
            D[k1] = [a]
          end
        else
          short_vectors1_by_glue[deepcopy(k)] = Dict(k1=>[a])
        end
      end
    end
    # the following gives an epsilon speedup
    #DNeg = Dict{Vector{Int},Vector{Int}}()
    #for k in keys(short_vectors1_by_glue)
    #  u = mod.((-).(k), eldivNi_mod_Mi')
    #  DNeg[u] = k
    #end
    # lower and upper bound for short vector enumeration of L_i
    ma = CoeffType(maximum(target_norm_i))
    mi = CoeffType(minimum(i for i in target_norm_i if !iszero(i);init=ma))
    @vprintln :Lattice 2 "Short vector round no $i: rank $(nrows(projL[i])) minimum $mi maximum $ma target $(sort(collect(target_norm_i)))"
    tmp_u1 = __zeros_array(CoeffType, ncols(VfLi))
    tmp_u2 = __zeros_array(CoeffType, ncols(VfLi))
    Gi = projL_gram[i] # already lll reduced
    tmp_s = __zeros_array(CoeffType, ncols(Gi))
    @vprintln :Lattice 5 "gram=$Gi"
    for (s, q) in __short_vectors(Gi, mi, ma)
      # This is the innermost loop - do as little as possible here
      q in target_norm_i || continue
      if CoeffType===ZZRingElem
        tmp_s = set!.(tmp_s, s)
      else
        tmp_s = s'
      end
      s_mod_Mi = __mul_mod!(tmp_u1, tmp_s, VfLi, eldivNi_mod_Mi)
      k1plus = s_mod_Mi
      if k1plus in keys(short_vectors1_by_glue)
        D = short_vectors1_by_glue[k1plus]
        for t in target_norm[q]
          t in keys(D) || continue
          Dt = D[t]
          push!(t[1], q)
          sv2t = short_vectors2[t]
          for b in Dt
            #@assert !(__vcat(b, -tmp_s) in reduce(vcat,values(short_vectors2)))
            push!(sv2t, __vcat(b, -tmp_s))
          end
          pop!(t[1])
        end
      end
      k1minus = __neg_mod!(tmp_u2, s_mod_Mi, eldivNi_mod_Mi)
      #if k1minus in keys(short_vectors1_by_glue)
      #if k1plus in keys(DNeg)
      #  k1minus = DNeg[k1plus]  # the dict variant is 0.2 ms faster ... not worth it
      #elsenormalized_targets
      #  continue
      #end
      if k1minus in keys(short_vectors1_by_glue)
        D = short_vectors1_by_glue[k1minus]
        for t in target_norm[q]
          t in keys(D) || continue
          iszero(t[1]) && iszero(t[5]) && continue # avoid overcounting
          Dt = D[t]
          push!(t[1], q)
          sv2t = short_vectors2[t]
          for b in Dt
            #@assert !(__vcat(b, tmp_s) in reduce(vcat,values(short_vectors2)))
            push!(sv2t, __vcat(b, deepcopy(tmp_s)))
          end
          pop!(t[1])
        end
      end
    end

    if search_fixed_vectors
      vs = _vector_sums(short_vectors2, projection_ranges[1:i], successive_grams) # with overflow
      @vprintln :Lattice 3 "$(length(vs)) fixed vectors at stage i=$i"
      target_invariants, signs = _update_targets(target_invariants, vs, normalized_targets, signs)
      target_invariants_i = [(k[1][1:i],k[2:end]...) for k in target_invariants]
      short_vectors2 = _update_short_vector_dict(short_vectors2, vs, target_invariants_i)
    end
    short_vectors1 = short_vectors2
    @vprintln :Lattice 2 "$(sum(length(i) for i in values(short_vectors1);init=0)) vectors at stage i=$i"
  end
  @hassert :Lattice 1 allunique(reduce(vcat, values(short_vectors1)))
  if search_invariant_subspace
    m = length(projection_ranges)
    # so how to get rid of duplicates?
    invariant_subspaces, rk1_invariant_subspaces = _search_invariant_subspaces(short_vectors1, projection_ranges)
    # under construction....
    rkL = rank(L)
    Gr = zero_matrix(ZZ, rkL, rkL)
    tmp_mat = zero(Gr)
    s = length(invariant_subspaces)
    # we inflate and then compress
    for j in 1:s
      S = invariant_subspaces[j]
      r = S.range
      i = findfirst(==(r), projection_ranges)
      Gi = projL_gram[i]
      C = view(S.B2, 1:rank(S),:)
      K = kernel(Gi*transpose(C);side=:left)
      CK = QQ.(vcat(C,K))
      CK_inv = inv(CK)
      toC = Binv[:,r]*CK_inv[:,1:nrows(C)]*C
      _GC = toC*Gi*transpose(toC)
      GC = numerator(_GC)
      addmul!(Gr, GC, rand(1:500))
    end
    for S in rk1_invariant_subspaces
      r = S.range
      i = findfirst(==(r), projection_ranges)
      Gi = projL_gram[i]
      C = view(S.B2, 1:rank(S),:)
      K = kernel(Gi*transpose(C);side=:left)
      CK = QQ.(vcat(C,K))
      CK_inv = inv(CK)
      for l in 1:rank(S)
        toC = Binv[:,r]*CK_inv[:,l:l]*C[l:l,:]
        _GC = toC*Gi*transpose(toC)
        GC = numerator(_GC)
        addmul!(Gr, GC, rand(1:500))
      end
    end
    _Gr = [CoeffType(i) for i in Gr]
    push!(grams, Gr)
    for i in 1:26
      k = target_invariants[i]
      push!(k[2],_Gr[i,i])
    end
  end



  if CoeffType===ZZRingElem
    _B = numerator(B)
    d = denominator(B)
  else
    _B = [CoeffType(i) for i in numerator(B)]
    d = CoeffType(denominator(B))
  end

  r1 = nrows(projL[1])
  lcmd = lcm(denoms)
  sc = div.(lcmd, denoms)
  grams[1] = gramZZ # we don't need the first projection, overwrite

  target_invariants_output = Vector{CoeffType}[]
  for i in 1:rank(L)
    signi = signs[i]
    (nrm_orig, nrm_extra, weyl, v1,fix) = target_invariants[i]
    nrm_orig[1] = divexact(dot(sc, nrm_orig),lcmd)  # since we set grams[1] = gram
    nrm = vcat(nrm_orig, nrm_extra)
    invariant = append!([weyl],v1,fix)
    # canonicalize?
    if signi == -1
      invariant .= (-).(invariant)
    end
    push!(target_invariants_output, invariant)
  end

  # assemble the output
  n_out = sum(length.(values(short_vectors1)))
  output = Vector{Tuple{Vector{CoeffType}, Vector{CoeffType}}}(undef, n_out)
  invariants = Vector{Vector{CoeffType}}(undef, n_out)
  discard = falses(n_out)
  i = 0
  for b in keys(short_vectors1)
    isempty(short_vectors1[b]) && continue  # can happen for targets coming from a non-isometric lattice
    (nrm_orig, nrm_extra, weyl, v1, fix) = b
    nrm = vcat(nrm_orig, nrm_extra)
    invariant = append!([weyl],v1,fix)
    minus_invariant = (-).(invariant)
    nrm[1] = divexact(dot(sc, nrm),lcmd)  # since we set grams[1] = gramL
    b1 = (nrm[1:length(nrm_orig)], nrm_extra, weyl, v1, fix)
    for z in short_vectors1[b]
      i = i+1
      # transform back to the basis of L
      vv = divexact.(__not_adj(z*_B), d)
      vv, _sign = _canonicalize_with_data!(vv)  # why do we canonicalize here?
      if isone(_sign)
        invariants[i] = invariant
      else
        invariants[i] = minus_invariant
      end
      if search_invariant_subspace
        s = dot(vv, _Gr, vv)
        nrmv = push!(deepcopy(nrm), s)
        push!(nrm_extra, s)
        if !(b1 in target_invariants)
          discard[i] = true
        end
        output[i] = (vv, nrmv)
        pop!(nrm_extra)
      else
        output[i] = (vv, deepcopy(nrm))
      end
    end
  end
  if search_invariant_subspace
    deleteat!(output, discard)
    deleteat!(invariants, discard)
  end


  if get_assertion_level(:Lattice) > 1
    @assert length(unique((output))) == length(output)
    n = rank(L)
    target_norms = [[CoeffType(grams[i][j,j]) for i in 1:length(grams)] for j in 1:n]
      c = 0
    for (v, n) in output
      @assert all(dot(v, grams[i], v) == n[i] for i in 1:length(grams)) "norms do not match with gram matrices"
      if mode==:auto
        #@assert n in target_norms
        if n in target_norms
          c +=1
        end
      end
    end
    # This test makes sense only in automorphism mode
    if mode == :auto
      E = CoeffType.(identity_matrix(ZZ, n))
      for i in 1:n
        ei = E[i,:]
        @assert any(ei==j[1] ||-ei==j[1] for j in output) "Basis vector e_$i is missing"
        j = findfirst(==(ei), first.(output))
      end
    end
  end
  @vprintln :Lattice 1 "computed $(length(output)) target vectors"
  @assert length(invariants) == length(output)
  return output, grams, (invariants, target_invariants_output)
end

########################################################################################
#
#            Subroutines for invariant subspace detection
#
########################################################################################
function _vector_sums(D::Dict, projection_ranges, successive_grams)
  result = Set{Tuple{Vector{Int},UnitRange{Int}}}()
  #r = last(projection_ranges[1]) + 1
  for v in values(D)
    isempty(v) && continue
    init = zero(__not_adj(v)[1])
    vs = ___sum(v; init)
    # if v1 is zero, then the sum is zero anyways
    all(iszero, vs[i] for i in projection_ranges[1]) && continue
    # project
    # the first one is already invariant anyways
    for i in 2:length(projection_ranges)
      r = projection_ranges[i]
      length(r)==1 && continue
      @inbounds all(iszero(vs[i]) for i in r) && continue
      vsr = _canonicalize!(vs[r])
      g = gcd(vsr)
      vsr = div.(vsr,g)# excludes duplicates up to sign
      push!(result, (successive_grams[i]*vsr,r))
    end
  end
  return collect(result)
end

# offset on first input
function _dot_product_with_offset(a, b, offset::Int)
  s = 0
  for i in eachindex(b)
    s += @inbounds a[i+offset] * b[i]
  end
  return s
end

function _update_targets(target_invariants, vector_sums, normalized_targets, signs)
  result = similar(target_invariants)
  n = length(result)
  for (i,v,k) in zip(1:n,normalized_targets, target_invariants)
    kk = deepcopy(k)
    for (vsr, r) in vector_sums
      s = _dot_product_with_offset(v, vsr, first(r)-1)
      push!(kk[5], s)
    end
    if iszero(k[1][1]) && iszero(k[5])
      # flip the sign, this is necessary, because we consider our vectors up to sign
      _,_sign = _canonicalize_with_data!(kk[5])
      normalized_targets[i] = _sign*normalized_targets[i]
      signs[i] *= _sign
    end
    result[i] = kk
  end
  return result, signs
end

function _update_short_vector_dict(D::Dict{KeyType,ValueType},
                                   vector_sums::Vector{Tuple{Vector{Int},UnitRange{Int}}},
                                   target_invariants::Vector{KeyType}) where {KeyType,ValueType<:Vector}
  isempty(vector_sums) && return D
  @hassert :Lattice 1 allunique(reduce(vcat,values(D)))
  Dnew = Dict{KeyType,ValueType}()
  for k in keys(D)
    T = Dict{Vector{Int},ValueType}()
    for v in D[k]
      h = Int[]
      for (vsr, r) in vector_sums
        s = _dot_product_with_offset(v, vsr, first(r)-1)
        push!(h, s)
      end
      push!(get!(T, h, ValueType()), v)
    end
    for (h,vv) in T
      kk = deepcopy(k)
      append!(kk[5], h)
      if iszero(k[1][1]) && iszero(k[5])
        _,sign = _canonicalize_with_data!(kk[5])
      else
        sign = 1
      end
      if kk in target_invariants
        # do the append!get! thing because both kk and "-kk" can appear
        if sign==-1
          vv .= (-).(vv)
        end
        append!(get!(Dnew,kk,ValueType()),vv)
      end
    end
  end
  @hassert :Lattice 1 allunique(reduce(vcat,values(Dnew)))
  return Dnew
end

rank(z::GrowingSubspace) = z.rank
degree(z::GrowingSubspace) = ncols(z.B1)

function push!(z::GrowingSubspace, x, offset=0)
  n = length(z.range)
  z.rank == n && return nothing
  B1 = z.B1
  B2 = z.B2
  nn = z.rank+1
  r = offset
  @inbounds for i in 1:n
    B1[nn,i] = x[r+i]
  end
  if !_reduce_modulo_rref(B1, z.rank, z.pivs, z.pure, z.dirty)
    # found something new
    rref!(B1)
    z.rank += 1
    z.dirty = true
    resize!(z.pivs, z.rank)
    resize!(z.pure, z.rank)
    rk = z.rank
    @inbounds for i in 1:n
      B2[rk, i] = x[r+i]
    end
  else
    z.dirty = false
  end
  nothing
end

function _search_invariant_subspaces(D::Dict, projection_ranges)
  subspaces = Set{GrowingSubspace{fpMatrix,ZZMatrix}}()
  subspaces1 = Set{GrowingSubspace{fpMatrix,ZZMatrix}}()  # collects invariant subspaces of rank 1, the rows of B2 are the rk 1 invariant subspaces, this is okay, since B2 does not get row reduced
  for i in 2:length(projection_ranges)
    r = projection_ranges[i]
    length(r)<2 && continue
    J1 = GrowingSubspace(r)
    for vv in values(D)
      J = GrowingSubspace(r)
      for v in vv
        push!(J, v, first(J.range)-1)
      end
      if 1 < J.rank < J.degree
        push!(subspaces, J)
      end
      if J.rank == 1
        w = J.B2[1,:]
        push!(J1, w)
      end
      if J1.rank == degree(J1)
        break
      end
    end
    J1.rank > 0 && push!(subspaces1,J1)
  end
  return collect(subspaces), collect(subspaces1)
end

########################################################################################
#
#            Helpers
#
########################################################################################

function ___sum(V::Vector{Vector{ZZRingElem}}; init::Vector)
  if eltype(init) === Int
    @assert false
    for i in 1:length(init)
      init[i] = 0
    end
  else
    init = zero!.(init)
  end
  for i in V
    add!.(init, i)
  end
  return init
end

function ___sum(V::Vector{<:LinearAlgebra.Adjoint}; init::Vector)
  for i in V
    init .= init .+ i'
  end
  return init
end

@inline function add!(z::Vector{QQFieldElem}, x::Vector{QQFieldElem}, y::Vector{QQFieldElem})
  @inbounds for i in 1:length(x)
    z[i] = add!(z[i], x[i], y[i])
  end
  return z
end

@inline function sub!(z::Vector{QQFieldElem}, x::Vector{QQFieldElem}, y::Vector{QQFieldElem})
  @inbounds for i in 1:length(x)
    z[i] = sub!(z[i], x[i], y[i])
  end
  return z
end

function mul!(z::Vector{QQFieldElem}, a::Vector{ZZRingElem}, b::QQMatrix)
  @ccall libflint.fmpq_mat_fmpz_vec_mul_ptr(z::Ptr{Ref{QQFieldElem}}, a::Ptr{Ref{ZZRingElem}}, length(a)::Int, b::Ref{QQMatrix})::Nothing
  return z
end

function _is_integral(x::Vector{QQFieldElem}, tmp::ZZRingElem)
  return all(isone(denominator!(tmp, i)) for i in x)
end


function _denominator(v::Vector{QQFieldElem})
  z = one(ZZ)
  tmp = ZZ()
  for i in 1:length(v)
    z = lcm!(z, z, denominator!(tmp, v[i]))
  end
  return z
end

function _numerator(v::Vector{QQFieldElem})
  d = _denominator(v)
  n = length(v)
  w = zeros_array(ZZ, n)
  tmp = QQ()
  @inbounds for i in 1:n
    numerator!(w[i], mul!(tmp, d, v[i]))
  end
  return w
end


__zeros_array(::Type{ZZRingElem}, x...) = zeros_array(ZZ, x...)
__zeros_array(::Type{Int}, x...) = zeros(Int, x)'
__vcat(x::Vector{ZZRingElem},y::Vector{ZZRingElem}) = vcat(x,y) # append! does not work
function __vcat(x::LinearAlgebra.Adjoint{Int64, Vector{Int64}}, y::LinearAlgebra.Adjoint{Int64, Vector{Int64}})
  return vcat(x',y')'
end



__norm!(gram::Matrix{Int}, v::Vector{Int}, tmp_v::Vector{Int}) = dot(v, gram, v)
__norm!(gram::ZZMatrix, v::Vector{ZZRingElem}, tmp_v::Vector{ZZRingElem}) = dot(mul!(tmp_v,v,gram),v) # this could be improved if necessary


@inline function __mul_mod!(u::Vector{S}, v::Vector{S}, A, moduli::Vector{S}) where {S<:ZZRingElem}
  #@assert length(v) == nrows(A)
  #@assert ncols(A)==length(moduli)==length(u)
  u = mul!(u, v, A)
  return mod!.(u, moduli)
end

@inline function __mul_mod!(u::S, v::S, A::Matrix{Int}, moduli::S) where {S<:LinearAlgebra.Adjoint{Int, Vector{Int}}}
  #@assert length(v) == nrows(A)
  #@assert ncols(A)==length(moduli)==length(u)
  u = LinearAlgebra.mul!(u, v, A)
  u .= mod.(u, moduli)
  return u'
end


@inline function __neg_mod!(u::S, v::S, moduli::S) where {S<:Vector{ZZRingElem}}
  #@assert length(u) == length(v)
  return mod!.(neg!.(u,v), moduli)
end

@inline function __neg_mod!(u::S, v, moduli::S) where {S<:LinearAlgebra.Adjoint{Int, Vector{Int}}}
  #@assert length(u) == length(v)
  #for i in eachindex(v)
  #  @inbounds u[i] = mod(-v[i], moduli[i])
  #end
  u' .= mod!.(neg!.(u',v), moduli')
  return u'
end

@inline __not_adj(x::Vector{ZZRingElem}) = x
@inline __not_adj(x) = x'

_to_VectorType(::Type{ZZRingElem}, x::Vector{QQFieldElem}) = ZZ.(x)
_to_VectorType(::Type{Int}, x::Vector{QQFieldElem}) = (Int.(ZZ.(x)))'


function __short_vectors(G::ZZMatrix, lb, ub)
  sv = __enumerate_gram(FinckePohstInt, G, lb, ub, Int, identity, identity, Int)
  return sv
end

(==)(a::T,b::T) where {T<:GrowingSubspace} = a.range==b.range && a.B1==b.B1  #not quite mathematically correct, but what we need
hash(x::GrowingSubspace, y::UInt) = hash((x.B1,x.range),y)


#
# type piracy
#
function set!(z::Nemo.QQMatrixOrPtr, x::Nemo.ZZMatrixOrPtr)
  @ccall libflint.fmpq_mat_set_fmpz_mat(z::Ref{Nemo.QQMatrixOrPtr}, x::Ref{Nemo.ZZMatrixOrPtr})::Nothing
  return z
end

function change_base_ring(P::QQField, x::ZZMatrix)
  z = zero_matrix(QQ,nrows(x), ncols(x))
  return set!(z,x)
end

function integral_split(x::ZZMatrix, R::ZZRing)
  return x, one(ZZ)
end
