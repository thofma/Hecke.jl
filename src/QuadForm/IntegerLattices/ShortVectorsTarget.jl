########################################################################################
#
#            Short vectors with condition
#
########################################################################################

raw"""
    short_vectors_with_condition(L::ZZLat; search_fixed_vectors::Bool, search_invariant_subspace::Bool, use_dual::Bool)

Return a list of vectors, that contains the orbits of the standard basis vectors
under the reduced automorphism group $\mathrm{Aut}(L, \rho)$
together with a list of $\mathrm{Aut}(L, \rho)$-invariant gram matrices
where $\rho$ is a Weyl vector of the root sublattice of `L`.
Also return a list of invariants and the invariants of the standard basis vectors.

# Input
- `search_fixed_vectors::Bool` -- take sums of vectors with the same invariants
  to obtain new invariant vectors. Use it to refine the invariant. Rinse and repeat.
- `search_invariant_subspace::Bool` -- compute the span of the vectors with the same invariants

# Output:
- a tuple `(V, G, (invariants,target_invariants))` consiting of:
- a list of tuples `V = [(v_1, n_1), (v_2, n_2), ....]`;
  where `v_i` is a point of `L` and `n_i=[n_i1,...,n_ik]` a list of integers
- a list of symmetric integer matrices `G = [G_1, ..., G_k]`;
such that:
- `dot(v_i,G[j]*v_i) == n_ij` for all `i` and for all `j` in `1,...,k`.
- the standard basis vectors and their norms with respect to `G` are contained in `V`
- `invariants` is a list of vectors of the form `[weyl_vector_contribution, v1_contribution, fixed_vector_contribution]`
  where `weyl_vector_contribution` is the contribution to the invariant coming from the weyl vector,
  `v1_contribution` is the contribution coming from the fixed part and `fixed_vector_contribution` is the contribution coming from the fixed vectors.
"""
function short_vectors_with_condition(L::ZZLat;
                                      search_fixed_vectors::Bool=false,
                                      search_invariant_subspace::Bool=false,
                                      use_dual::Bool=false, sort::Symbol=:rank)
  return short_vectors_with_condition(ZZRingElem, L; search_fixed_vectors, search_invariant_subspace, use_dual, sort)
end

function short_vectors_with_condition(T::Type,
                                      L::ZZLat;
                                      search_fixed_vectors::Bool=true,
                                      search_invariant_subspace::Bool=false,
                                      use_dual::Bool=false, sort::Symbol=:rank)
  _data = _short_vectors_with_condition_preprocessing(L; use_dual, sort)
  return _short_vectors_with_condition(T, _data...; search_fixed_vectors, search_invariant_subspace)
end


function short_vectors_with_condition(::Type{T}, L1::ZZLat,
                                      L2::ZZLat) where T
  _notisom = (Tuple{Vector{T},Vector{T}}[],ZZMatrix[],(Int[],Int[]))
  notisom = (false, _notisom, _notisom)
  # We disable the search for fixed vectors and invariant subspaces
  # because it would be difficult to match them
  search_fixed_vectors = false
  search_invariant_subspace = false
  pre1, (root_type1, fundamental_roots1), invariant_matrix1 = _short_vectors_with_condition_preprocessing_with_root_data(L1)
  pre2, (root_type2, fundamental_roots2), invariant_matrix2 = _short_vectors_with_condition_preprocessing_with_root_data(L2)
  _V1 = Vector{Tuple{Vector{T},Vector{T}}}()
  _V2 = Vector{Tuple{Vector{T},Vector{T}}}()
  if root_type1 != root_type2 || rank(L1) != rank(L2) || det(L1) != det(L2)
    return notisom
  end
  n = rank(L1)

  L1,successive_sublattices1, B1, Binv1, projection_ranges1, projL1, projL_gram1, denoms1, target_fixed_part1, target_norms1,grams1 = pre1
  L2,successive_sublattices2, B2, Binv2, projection_ranges2, projL2, projL_gram2, denoms2, target_fixed_part2, target_norms2,grams2 = pre2

  R1 = basis_matrix(successive_sublattices1[1])
  R2 = basis_matrix(successive_sublattices2[1])
  proj1 = solve(R1, projL1[1];side=:left)
  proj2 = solve(R2, projL2[1];side=:left)
  if proj1 != proj2 || denoms1!=denoms2 || length(projL1) != length(projL2)
    return notisom
  end
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
    return notisom
  end
  return true, out1, out2
end

########################################################################################
#
#            Preprocessing
#
########################################################################################

function _short_vectors_with_condition_preprocessing(L::ZZLat; use_dual::Bool=false, sort=:rank)
  root_types, fundamental_roots = _root_lattice_recognition_fundamental(L)
  fixed_space, isotypic_coinvariant_space, weyl_vector = _weyl_group(L, root_types, fundamental_roots)
  return _short_vectors_with_condition_preprocessing(L, fundamental_roots, weyl_vector, fixed_space, isotypic_coinvariant_space, sort, use_dual)
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
  @hassert :ShortVec 1 isone(basis_matrix(L))
  n = rank(L)
  V = ambient_space(L)
  R_fix = lattice(V, fixed_space; isbasis=true, check=false)
  R_cofix = [lattice(V, b; isbasis=true, check=false) for b in isotypic_coinvariant_space]
  R = reduce(vcat, fundamental_roots; init=zero_matrix(ZZ, 0, rank(L)))
  GZZ,_  = _integral_split_gram(L)
  Rperp = lattice(V, QQ.(kernel(GZZ*transpose(R); side=:left)); isbasis=true, check=false)
  successive_sublattices = append!([R_fix], R_cofix, _successive_sublattices(Rperp; use_dual=false))
  @vprintln :ShortVec 1 "largest successive sublattice of rank $(maximum(rank.(successive_sublattices)[2:end]))"
  m = length(successive_sublattices)
  if sort == :rank
    # don't touch the first one because it consists of the fixed part, i.e. the seeds
    view_successive = view(successive_sublattices,2:m)
    p = sortperm(view_successive; by=rank)
    p = append!([1], 1 .+ p)
    pinv = invperm(p)
    sort!(view_successive;by=rank)
    no_split = pinv[1:1+length(R_cofix)]
  elseif sort == :root
    # don't touch the first one because it consists of the fixed part, i.e. the seeds
    # do the root part first
    k = 1 + length(R_cofix)
    sort!(view(successive_sublattices,k:m);by=rank);
    no_split = collect(1:k)
  end
  # Compute L_1,  ... , L_n
  projL, projL_gram, projection_ranges,denoms,successive_sublattices = _grams_proj(L, successive_sublattices; split_further=use_dual, no_split)

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


function _grams_proj(L::ZZLat, successive_sublattices::Vector{ZZLat}; split_further::Bool=false, no_split=Int[])
  m = length(successive_sublattices)
  rkLL = rank.(successive_sublattices)
  gramLZZ, _ = _integral_split_gram(L)
  if split_further
    V = ambient_space(L)
    successive_sublattices1 = ZZLat[]
    sizehint!(successive_sublattices1, m)
  end
  F = reduce(vcat, [basis_matrix(i) for i in successive_sublattices])
  Fi = inv(F)
  r1 = 1
  r2 = rkLL[1]
  projL = Vector{QQMatrix}(undef, m) # projL[i] = L_i := image(L->(L_1+...+L_i)\otimes QQ)
  projL_gram = Vector{ZZMatrix}(undef, m) # lll reduced
  projection_ranges = Vector{UnitRange{Int64}}(undef, m)
  denoms = Vector{ZZRingElem}(undef, m)
  splitted_further=false
  for i in 1:m
    projection_ranges[i] = r1:r2
    Si = view(_hnf_integral(view(Fi, :, r1:r2), :upper_right), 1:1+r2-r1,:)*view(F, r1:r2, :)
    # do the following the hard way
    # Li = lll(lattice(rescale(V,denoms[i]; cached=false), Si; isbasis=true, check=false); _is_definite=true)
    SZ, di = integral_split(Si, ZZ)
    denoms[i] = di
    Gi = divexact!(SZ*gramLZZ*transpose(SZ),di)
    if i > 1
      Gi, U = lll_gram_with_transform(Gi) # inplace variant caused segfault problems
      SZ = mul!(SZ, U, SZ)
      Si = set!(Si,SZ)
      Si = mul!(Si, QQ(1,di))
    end
    if split_further
      # this part is not optimized, turned off by default
      if rkLL[i] > 1 && !(i in no_split)
        Li = lattice(V, Si; isbasis=true, check=false)
        set_attribute!(Li,:_integral_split_gram=>(Gi, ZZ(1)))
        set_attribute!(Li,:is_lll_reduced=>true)
        Li_split = _successive_sublattices(Li; use_dual=false)
        splitted_further = splitted_further || length(Li_split)>1
        append!(successive_sublattices1, Li_split)
      else
        push!(successive_sublattices1, successive_sublattices[i])
      end
    end
    projL[i] = Si
    projL_gram[i] = Gi
    r1 += rkLL[i]
    if i < m
      r2 += rkLL[i+1]
    end
  end
  if splitted_further
    sort!(view(successive_sublattices1, 2:length(successive_sublattices1)); by=rank)
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
  tmpZZ = ZZ()

  L_in_L1toLn = hnf(Binv)
  successive_grams = [_int_matrix_with_overflow(j, tmpZZ) for j in projL_gram]
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
    existing = get(short_vectors1, b, nothing)
    if !isnothing(existing)
      # different targets can have the same first projection
      if !(v1t in existing)
        push!(existing, v1t)
      end
    else
      short_vectors1[b]=[v1t]
    end
  end
  @vprintln :ShortVec 1 "Ranks of successive sublattices $(rank.(successive_sublattices))"
  zeroCoeff = zero(CoeffType)
  for i in 2:length(projL)
    @vprintln :ShortVec 1 "Round i=$i"
    @hassert :ShortVec 1 all(allunique, values(short_vectors1))
    @hassert :ShortVec 1 allunique(reduce(vcat, values(short_vectors1)))
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
    if CoeffType == Int
      _nc = ncols(Vf)
      _nr = nrows(Vf)
      VfN_iminus1 = _int_matrix_with_overflow(view(Vf, 1:r1, n_ones+1:_nc), tmpZZ)
      VfLi = _int_matrix_with_overflow(view(Vf, r1+1:_nr, n_ones+1:_nc), tmpZZ)
    else
      VfN_iminus1 = @view Vf[1:r1, n_ones+1:end]
      VfLi = @view Vf[r1+1:end, n_ones+1:end]
    end
    @assert nrows(VfLi) == nrows(projL[i])
    @vprintln :ShortVec 3 "elementary divisors $eldivNi_mod_Mi at stage i=$i"

    # prepare for filtering by norm
    target_norm_i = Set(n[1][i] for n in target_invariants)
    target_norm = Dict{CoeffType, Set{KeyType}}()
    for n in target_invariants
      # keep only the invariants valid at stage i
      a = n[1][i]
      b = (n[1][1:i-1], n[2:end]...)
      push!(get!(() -> Set{KeyType}(), target_norm, a), b)
    end

    # prepare gluing data
    rank_i = nrows(projL[i])
    tmp_u = __zeros_array(CoeffType, ncols(VfN_iminus1))
    short_vectors1_by_glue = Dict{Vector{CoeffType},Dict{KeyType, Vector{VectorType}}}()
    zero_target_norm = get(target_norm, zeroCoeff, nothing)
    for k1 in keys(short_vectors1)
      for a in short_vectors1[k1]
        a_mod_Mi =__mul_mod!(tmp_u, a, VfN_iminus1, eldivNi_mod_Mi)
        k = a_mod_Mi
        # take into account that short_vectors returns only non-zero vectors.
        if !isnothing(zero_target_norm) && k1 in zero_target_norm && iszero(k)
          push!(k1[1], zeroCoeff)
          #@assert !(-__vcat(a,__zeros_array(CoeffType, rank_i)) in reduce(vcat,values(short_vectors2))) k1
          push!(short_vectors2[k1], __vcat(a,__zeros_array(CoeffType, rank_i)))
          pop!(k1[1])
        end
        D = get(short_vectors1_by_glue, k, nothing)
        if !isnothing(D)
          vectors_for_key = get(D, k1, nothing)
          if !isnothing(vectors_for_key)
            push!(vectors_for_key, a)
          else
            D[k1] = [a]
          end
        else
          short_vectors1_by_glue[__copy_vector_key(k)] = Dict(k1=>[a])
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
    @vprintln :ShortVec 2 "Short vector round no $i: rank $(nrows(projL[i])) minimum $mi maximum $ma target $(sort(collect(target_norm_i)))"
    tmp_u1 = __zeros_array(CoeffType, ncols(VfLi))
    tmp_u2 = __zeros_array(CoeffType, ncols(VfLi))
    Gi = projL_gram[i] # already lll reduced
    tmp_s = __zeros_array(CoeffType, ncols(Gi))
    @vprintln :ShortVec 5 "gram=$Gi"
    for (s, q) in __short_vectors(Gi, mi, ma)
      # This is the innermost loop - do as little as possible here
      target_norm_q = get(target_norm, q, nothing)
      isnothing(target_norm_q) && continue
      if CoeffType===ZZRingElem
        tmp_s = set!.(tmp_s, s)
      else
        tmp_s = s'
      end
      s_mod_Mi = __mul_mod!(tmp_u1, tmp_s, VfLi, eldivNi_mod_Mi)
      k1plus = s_mod_Mi
      D = get(short_vectors1_by_glue, k1plus, nothing)
      if !isnothing(D)
        for t in target_norm_q
          Dt = get(D, t, nothing)
          isnothing(Dt) && continue
          push!(t[1], q)
          sv2t = short_vectors2[t]
          for b in Dt
            #@assert !(__vcat(b, -tmp_s) in reduce(vcat,values(short_vectors2)))
            #push!(sv2t, __vcat(b, -tmp_s))
            push!(sv2t, __vcat_neg(b, tmp_s))
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
      D = get(short_vectors1_by_glue, k1minus, nothing)
      if !isnothing(D)
        for t in target_norm_q
          Dt = get(D, t, nothing)
          isnothing(Dt) && continue
          iszero(t[1]) && iszero(t[5]) && continue # avoid overcounting
          push!(t[1], q)
          sv2t = short_vectors2[t]
          for b in Dt
            #@assert !(__vcat(b, tmp_s) in reduce(vcat,values(short_vectors2)))
            push!(sv2t, __vcat(b, __copy_before_vcat(tmp_s)))
          end
          pop!(t[1])
        end
      end
    end

    if search_fixed_vectors
      vs = _vector_sums(short_vectors2, projection_ranges[1:i], successive_grams) # with overflow
      @vprintln :ShortVec 3 "$(length(vs)) fixed vectors at stage i=$i"
      target_invariants, signs = _update_targets(target_invariants, vs, normalized_targets, signs)
      target_invariants_i = [(k[1][1:i],k[2:end]...) for k in target_invariants]
      short_vectors2 = _update_short_vector_dict(short_vectors2, vs, target_invariants_i)
    end
    short_vectors1 = short_vectors2
    @vprintln :ShortVec 2 "$(sum(length(i) for i in values(short_vectors1);init=0)) vectors at stage i=$i"

    @vprintln :ShortVec 2 "$(length(short_vectors1)) buckets"
  end
  @hassert :ShortVec 1 allunique(reduce(vcat, values(short_vectors1)))
  search_invariant_subspace = search_invariant_subspace && sum(length(v) for v in values(short_vectors1); init=0) > 100 # Todo: heuristic needs tuning
  if search_invariant_subspace
    invariant_gram = _add_invariant_subspace_data!(CoeffType, grams, target_invariants,
                                                   short_vectors1, projection_ranges,
                                                   projL_gram, Binv)
  end

  output, invariants, target_invariants_output = _postprocess_short_vectors_with_condition(CoeffType, B, denoms, gramZZ, grams, signs, target_invariants, short_vectors1)


  if get_assertion_level(:ShortVec) > 1
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
  @vprintln :ShortVec 1 "computed $(length(output)) target vectors"
  @assert length(invariants) == length(output)
  return output, grams, (invariants, target_invariants_output)
end

function _add_multiset_invariant!(sv, invariants, dual_root_orbits::Vector{Matrix{Int}})
  @assert length(sv) == length(invariants[1])
  l = length(sv)
  invs, target_invs = invariants
  for i in 1:l
    @inbounds v = sv[i][1]
    m = 0
    for R in dual_root_orbits 
      m = _signed_hash(multiset(R*v), m) # common signed hash
    end
    invs[i] = _signed_hash(invs[i], m) # common signed hash
  end
  for i in 1:length(target_invs)
    m = 0
    for R in dual_root_orbits
      m = _signed_hash(multiset(R[:,i]), m)
    end
    target_invs[i] = _signed_hash(target_invs[i], m)
  end
  S = Set(target_invs)
  for i in target_invs push!(S, -i) end
  mask = [i in S for i in invs]
  # todo: do this inplace
  return sv[mask], (invs[mask], target_invs)
end

function _postprocess_short_vectors_with_condition(::Type{CoeffType},
                                                   B::QQMatrix,
                                                   denoms::Vector{ZZRingElem},
                                                   gramZZ::ZZMatrix,
                                                   grams::Vector{ZZMatrix},
                                                   signs::Vector{Int},
                                                   target_invariants,
                                                   short_vectors) where {CoeffType}
  if CoeffType===ZZRingElem
    _B = numerator(B)
    d = denominator(B)
  else
    tmpZZ = ZZ()
    _BZZ,dBZZ = integral_split(B,ZZ)
    _B = _int_matrix_with_overflow(_BZZ, tmpZZ)
    d = CoeffType(dBZZ)
  end

  lcmd = lcm(denoms)
  sc = div.(lcmd, denoms)
  grams[1] = gramZZ # we don't need the first projection, overwrite

  # We replace the signed invariants by their signed hash
  _target_invariants_tmp = Vector{CoeffType}[]
  for i in eachindex(target_invariants)
    signi = signs[i]
    (nrm_orig, nrm_extra, weyl, v1,fix) = target_invariants[i]
    nrm_orig[1] = divexact(dot(sc, nrm_orig),lcmd)  # since we set grams[1] = gram, modifies target_invariants
    invariant = append!([weyl],v1,fix)
    if signi == -1
      invariant .= (-).(invariant)
    end
    push!(_target_invariants_tmp, invariant)
  end
  n_target_inv = length(unique(_target_invariants_tmp))
  signed_hash_seed = 0xc70d363fbd513942
  target_invariants_output = Int[]
  while true
    target_invariants_output = _signed_hash.(_target_invariants_tmp, signed_hash_seed)
    if length(unique(target_invariants_output))==n_target_inv
      break
    end
    signed_hash_seed += 1
  end

  n_out = sum(length(v) for v in values(short_vectors); init=0)
  output = Vector{Tuple{Vector{CoeffType}, Vector{CoeffType}}}(undef, n_out)
  invariants = Vector{Int}(undef, n_out)
  i = 0
  for b in keys(short_vectors)
     isempty(short_vectors[b]) && continue  # can happen for targets coming from a non-isometric lattice
    (nrm_orig, nrm_extra, weyl, v1, fix) = b
    nrm = vcat(nrm_orig, nrm_extra)
    invariant = _signed_hash(append!([weyl],v1,fix),signed_hash_seed)
    minus_invariant = -invariant
    nrm[1] = divexact(dot(sc, nrm_orig),lcmd)  # since we set grams[1] = gramL
    for z in short_vectors[b]
      i = i+1
      # transform back to the basis of L
      vv = divexact.(__not_adj(z*_B), d)
      vv, _sign = _canonicalize_with_data!(vv)  # why do we canonicalize here?
      if isone(_sign)
        invariants[i] = invariant
      else
        invariants[i] = minus_invariant
      end
      output[i] = (vv, copy(nrm))
    end
  end

  return output, invariants, target_invariants_output
end

########################################################################################
#
#            Subroutines for invariant subspace detection
#
########################################################################################
function _add_invariant_subspace_data!(::Type{CoeffType},
                                       grams::Vector{ZZMatrix},
                                       target_invariants,
                                       short_vectors,
                                       projection_ranges::Vector{UnitRange{Int}},
                                       projL_gram::Vector{ZZMatrix},
                                       Binv::ZZMatrix) where {CoeffType}
  m = length(projection_ranges)
  rkL = nrows(Binv)
  G = zero_matrix(ZZ, rkL, rkL)
  G_work = zero_matrix(ZZ, rkL, rkL)
  found_invariant_subspace = false
  tmpZZ = ZZ()
  range_to_index = Dict{UnitRange{Int}, Int}(projection_ranges[i] => i for i in 1:m)
  for r in projection_ranges
    i = range_to_index[r]
    Gi = projL_gram[i]
    Gr = zero_matrix(ZZ, length(r), length(r))
    tmpZZMatrix1 = zero_matrix(ZZ, length(r), length(r))
    tmpZZMatrix2 = zero_matrix(ZZ, length(r), length(r))
    invariant_subspaces, rk1_invariant_subspaces = _search_invariant_subspaces(short_vectors, r)
    found_invariant_subspace = found_invariant_subspace || !isempty(invariant_subspaces) || !iszero(nrows(rk1_invariant_subspaces))
    for C in invariant_subspaces
      K = kernel(Gi*transpose(C);side=:left)
      #store vcat(C,K) in tmpZZMatrix1
      tmpZZMatrix1[1:nrows(C),:] = C
      tmpZZMatrix1[nrows(C)+1:end,:] = K
      CK_inv,_ = pseudo_inv(tmpZZMatrix1)
      toC = mul!(tmpZZMatrix1, view(CK_inv,:,1:nrows(C)),C)
      GC = mul!(tmpZZMatrix1, toC, mul!(tmpZZMatrix2, Gi,transpose!(tmpZZMatrix2,toC)))
      addmul!(Gr, GC, rand([-1,1])*rand(1:50))
    end
    # we treat the rank one subspaces separately, because
    # one matrix inverse suffices to compute all the projections at once
    C = rk1_invariant_subspaces
    if !iszero(nrows(C))
     K = kernel(Gi*transpose(C);side=:left)
     #store vcat(C,K) in tmpZZMatrix1
     tmpZZMatrix1[1:nrows(C),:] = C
     tmpZZMatrix1[nrows(C)+1:end,:] = K
     CK_inv,_ = pseudo_inv(tmpZZMatrix1)
     for l in 1:nrows(C)
        toC = view(CK_inv,:,l:l)*view(C,l:l,:)
        GC = mul!(tmpZZMatrix1,toC,mul!(tmpZZMatrix1, Gi*transpose!(tmpZZMatrix1,toC)))
        addmul!(Gr, GC, rand([-1,1])*rand(1:50))
      end
    end
    for (a, ra) in enumerate(r), (b, rb) in enumerate(r)
      G_work[ra, rb] = Gr[a, b]
    end
    Binv_r = @view Binv[:,r]
    G = add!(G, Binv_r*Gr*transpose(Binv_r))
  end

  push!(grams, G)
  for i in 1:rkL
    k0 = target_invariants[i]
    target_invariants[i] = (k0[1], push!(copy(k0[2]), CoeffType(G[i,i])), k0[3], k0[4], k0[5])
  end
  invariant_gram = CoeffType === ZZRingElem ? G_work : _int_matrix_with_overflow(G_work, tmpZZ)
  _refine_short_vectors_by_gram!(CoeffType, short_vectors, invariant_gram)
  return found_invariant_subspace
end

function _refine_short_vectors_by_gram!(::Type{CoeffType},
                                        D::Dict{KeyType, ValueType},
                                        invariant_gram) where {CoeffType, KeyType, ValueType <: Vector}
  Dnew = Dict{KeyType, ValueType}()
  for k in keys(D)
    for v in D[k]
      vv = __not_adj(v)
      s = CoeffType(dot(vv, invariant_gram, vv))
      new_k2 = copy(k[2])
      push!(new_k2, s)
      kk = (k[1], new_k2, k[3], k[4], k[5])
      push!(get!(() -> ValueType(), Dnew, kk), v)
    end
  end
  empty!(D)
  merge!(D, Dnew)
  @hassert :ShortVec 1 allunique(reduce(vcat, values(D); init=eltype(ValueType)[]))
  return D
end

function _vector_sums(D::Dict, projection_ranges, successive_grams)
  result = Set{Tuple{Vector{Int},UnitRange{Int}}}()
  #r = last(projection_ranges[1]) + 1
  for v in values(D)
    isempty(v) && continue
    # if the first projection w1 is zero, then the sum is zero anyways
    w = v[1]
    all(iszero, w[i] for i in projection_ranges[1]) && continue
    init = zero(__not_adj(v[1]))
    vs = ___sum(v; init)
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
    # Only k[5] is extended; k[1..4] can be shared safely since they are not mutated.
    new_fix = copy(k[5])
    for (vsr, r) in vector_sums
      s = _dot_product_with_offset(v, vsr, first(r)-1)
      push!(new_fix, s)
    end
    if iszero(k[1][1]) && iszero(k[5])
      # flip the sign, this is necessary, because we consider our vectors up to sign
      _,_sign = _canonicalize_with_data!(new_fix)
      normalized_targets[i] = _sign*normalized_targets[i]
      signs[i] *= _sign
    end
    kk = (k[1], k[2], k[3], k[4], new_fix)
    result[i] = kk
  end
  return result, signs
end

function _update_short_vector_dict(D::Dict{KeyType,ValueType},
                                   vector_sums::Vector{Tuple{Vector{Int},UnitRange{Int}}},
                                   target_invariants::Vector{KeyType}) where {KeyType,ValueType<:Vector}
  @hassert :ShortVec 1 allunique(reduce(vcat,values(D)))
  Dnew = Dict{KeyType,ValueType}()
  target_invariants_lookup = Set{KeyType}(target_invariants)
  if isempty(vector_sums)
    for (k, vv) in D
      k in target_invariants_lookup || continue
      append!(get!(() -> ValueType(), Dnew, k), vv)
    end
    @hassert :ShortVec 1 allunique(reduce(vcat,values(Dnew); init=eltype(ValueType)[]))
    return Dnew
  end
  for k in keys(D)
    T = Dict{Vector{Int},ValueType}()
    for v in D[k]
      h = Int[]
      for (vsr, r) in vector_sums
        s = _dot_product_with_offset(v, vsr, first(r)-1)
        push!(h, s)
      end
      push!(get!(() -> ValueType(), T, h), v)
    end
    for (h,vv) in T
      # Only k[5] is extended; k[1..4] can be shared safely since they are not mutated.
      new_k5 = copy(k[5])
      append!(new_k5, h)
      kk = (k[1], k[2], k[3], k[4], new_k5)
      if iszero(k[1][1]) && iszero(k[5])
        _,sign = _canonicalize_with_data!(new_k5)
      else
        sign = 1
      end
      if kk in target_invariants_lookup
        # do the append!get! thing because both kk and "-kk" can appear
        if sign==-1
          vv .= (-).(vv)
        end
        append!(get!(() -> ValueType(), Dnew, kk), vv)
      end
    end
  end
  @hassert :ShortVec 1 allunique(reduce(vcat,values(Dnew)))
  return Dnew
end

rank(z::GrowingSubspace) = z.rank
degree(z::GrowingSubspace) = ncols(z.B1)

# satisfies _signed_hash(-x, seed) = -_signed_hash(x,seed)
function _signed_hash(x::Vector, seed::UInt)
  if iszero(x)
    return 0
  end
  x_can, sign = _canonicalize_with_data!(x)
  ret = sign*reinterpret(Int,hash(x_can, seed))
  # revert the sign change
  if sign<0
    neg!(x)
  end
  return ret
end

# for M a multiset define -M = {-x : x in M} as a multiset
# we want hash(-M) = -hash(M)  
function _signed_hash(M::MSet, seed::UInt=UInt(0))
    h = Int64(0)
    for (x, multiplicity) in M.dict
        h += reinterpret(Int, hash(multiplicity)) * reinterpret(Int, _signed_hash(x, seed))
    end
    return h
end

_signed_hash(M::MSet, h::Int) = _signed_hash(_signed_hash(M), h)

function _signed_hash(x::Int, seed::UInt=0)
  return sign(x)*reinterpret(Int, hash(abs(x), seed))
end 

# common signed hash
# _signed_hash(-x,-y) = -_signed_hash(x,y)
function _signed_hash(x::Int, y::Int)
  # canonicalize and hash the pair (x,y) 
  # than add the sign 
  if x < 0 
    return -reinterpret(Int, hash((-x,-y)))
  elseif iszero(x) && y < 0
    return -reinterpret(Int, hash((x,-y)))
  elseif iszero(x) && iszero(y)
    return 0
  else
    return reinterpret(Int, hash((x,y)))
  end
end

function neg!(x::Vector{ZZRingElem})
  for i in eachindex(x)
    @inbounds neg!(x[i])
  end
end

function _zero!(z::GrowingSubspace)
  zero!(z.B1)
  zero!(z.B2)
  z.rank = 0
  z.dirty=true
  zero!(z.pivs)
  resize!(z.pivs, z.rank)
  resize!(z.pure, z.rank)
end

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

function _search_invariant_subspaces(D::Dict, r::UnitRange{Int})
   # collects invariant subspaces of rank 1,
   # the rows of B2 are the rk 1 invariant subspaces,
   # this is okay, since B2 does not get row reduced
  subspaces = Set{ZZMatrix}()
  offset = first(r) - 1
  J1 = GrowingSubspace(r)
  J = GrowingSubspace(r)
  for vv in values(D)
    _zero!(J)
    for v in vv
      push!(J, v, offset)
      J.rank == J.degree && break
    end
    if 1 < J.rank < J.degree
      push!(subspaces, J.B2[1:J.rank,:])
    end
    if J.rank == 1
      w = J.B2[1,:]
      push!(J1, w)
    end
    if J1.rank == degree(J1)
      break
    end
  end
  return subspaces, J1.B2[1:J1.rank,:]
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
  px = parent(x)
  py = parent(y)
  z = Vector{Int}(undef, length(px) + length(py))
  copyto!(z, 1, px, 1, length(px))
  copyto!(z, length(px) + 1, py, 1, length(py))
  return adjoint(z)
end
# For ZZRingElem: vcat copies references to mutable objects, so must deepcopy before vcat.
# For Int: vcat already copies immutable Int values, so no deepcopy needed.
@inline __copy_before_vcat(x::Vector{ZZRingElem}) = deepcopy(x)
@inline __copy_before_vcat(x::LinearAlgebra.Adjoint{Int64, Vector{Int64}}) = x
# For ZZRingElem keys in Dict: elements are mutable, so deepcopy needed.
# For Int keys: elements are immutable, copy suffices.
@inline __copy_vector_key(k::Vector{Int}) = copy(k)
@inline __copy_vector_key(k::Vector{ZZRingElem}) = deepcopy(k)



@inline __vcat_neg(x::Vector{ZZRingElem}, y::Vector{ZZRingElem}) = __vcat(x, -y)

function __vcat_neg(x::LinearAlgebra.Adjoint{Int64, Vector{Int64}}, y::LinearAlgebra.Adjoint{Int64, Vector{Int64}})
  px = parent(x)
  py = parent(y)
  nx = length(px)
  ny = length(py)
  z = Vector{Int}(undef, nx + ny)
  copyto!(z, 1, px, 1, nx)
  @inbounds for i in 1:ny
    z[nx + i] = -py[i]
  end
  return adjoint(z)
end

function dot!(v::Vector{Int}, gram::Matrix{Int}, w::Vector{Int}, tmp::Vector{Int})
  LinearAlgebra.mul!(tmp, gram, w)
  return dot(tmp, v)
end

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
  pu = parent(u)
  pv = v isa LinearAlgebra.Adjoint ? parent(v) : v
  pm = parent(moduli)
  @inbounds for i in eachindex(pu)
    pu[i] = mod(-pv[i], pm[i])
  end
  return pu
end

@inline __not_adj(x::Vector{ZZRingElem}) = x
@inline __not_adj(x) = x'

_to_VectorType(::Type{ZZRingElem}, x::Vector{QQFieldElem}) = ZZ.(x)
_to_VectorType(::Type{Int}, x::Vector{QQFieldElem}) = (Int.(ZZ.(x)))'

# C = CholeskyIntegralDenom(G)
# __short_vectors_it(G, lb, ub; chol = C)
function __short_vectors_it(G::ZZMatrix, lb, ub; chol = CholeskyIntegralDenom(G))
  sv = __enumerate_gram(FinckePohstIntIterCtx, G, lb, ub, Int, identity, identity, Int; chol)
  return sv
end

function __short_vectors(G::ZZMatrix, lb, ub; chol = CholeskyIntegralDenom(G))
  #sv = __enumerate_gram(FinckePohstIntIterCtx, G, lb, ub, Int, identity, identity, Int)
  sv = __enumerate_gram(FinckePohstInt, G, lb, ub, Int, identity, identity, Int; chol)
  return sv
end

(==)(a::T,b::T) where {T<:GrowingSubspace} = a.range==b.range && a.B1==b.B1  #not quite mathematically correct, but what we need
hash(x::GrowingSubspace, y::UInt) = hash((x.B1,x.range),y)


# type piracy

function integral_split(x::ZZMatrix, R::ZZRing)
  return x, one(ZZ)
end




function _short_vectors_with_condition_direct(L::ZZLat; use_projections=true, use_dual=false, search_invariant_subspace=false, search_fixed_vectors=true)
  tmpZZ = ZZ()
  G, _ = _integral_split_gram(L)
  GInt = _int_matrix_with_overflow(G, tmpZZ)
  chol = CholeskyIntegralDenom(G)
  sv2 = __short_vectors(G, nothing, 2; chol)
  #sv = __short_vectors(G, nothing, maxL)
  #sv2 = @inbounds [i[1] for i in sv if i[2]==2]
  fundamental_roots = _fundamental_roots(sv2, GInt)

  V = ambient_space(L)
  n = rank(L)

  root_types, fundamental_roots = _root_lattice_recognition_fundamental(L, [matrix(ZZ, 1, n, i) for i in fundamental_roots])
  fixed_space, isotypic_coinvariant_space, weyl_vector, root_orbits = _weyl_group(L, root_types, fundamental_roots)
  if use_projections
    R_fix = lattice(V, fixed_space; isbasis=true, check=false)
    R_cofix = [lattice(V, b; isbasis=true, check=false) for b in isotypic_coinvariant_space]
    R = reduce(vcat, fundamental_roots; init=zero_matrix(ZZ, 0, rank(L)))
    Rperp = lattice(V, QQ.(kernel(G*transpose(R); side=:left)); isbasis=true, check=false)
    successive_sublattices = append!([R_fix], R_cofix, _successive_sublattices(Rperp; use_dual=false))
    @vprintln :ShortVec 1 "largest successive sublattice of rank $(maximum(rank.(successive_sublattices)[2:end]))"
    projL, projL_gram, projection_ranges,denoms,successive_sublattices = _grams_proj(L, successive_sublattices; split_further=use_dual)
    B = reduce(vcat, projL)
    Binv,bi = integral_split(inv(B),ZZ)
    @assert isone(bi)
    grams = _get_grams_std(projL_gram, projection_ranges, Binv)
    @assert isone(bi)
  else
    grams = ZZMatrix[]
  end


  return __short_vectors_with_condition_direct(G, GInt, grams, fixed_space, root_types, fundamental_roots, chol, root_orbits;
                                               search_invariant_subspace,
                                               search_fixed_vectors)
end


function __short_vectors_with_condition_direct(G, GInt, grams, fixed_space, root_types, fundamental_roots, chol, root_orbits; search_invariant_subspace=false, search_fixed_vectors=true)

  tmpZZ = ZZ()
  n = nrows(GInt)
  maxL = Int(maximum(diagonal(G))) # catches overflows
  fixed_space_dual = _int_matrix_with_overflow(fixed_space, tmpZZ)*GInt
  gramsInt = [_int_matrix_with_overflow(g, tmpZZ) for g in grams]
  if length(grams)>0 && !iszero(grams[1])
    gram2 = gramsInt[1]
    # try compression
    for i in 2:length(grams)
      grams_i = gramsInt[i]
      m = maximum(grams_i[i,i] for i in 1:n)
      gram2 = (m+1)*gram2 + grams_i
    end
    if maximum(gram2[i,i] for i in 1:n)>2^15
      gram2 = sum(rand([-1,1])*rand(1:15)*g for g in gramsInt)
    end
  else
    gram2 = zero(GInt)
  end
  use_projections = length(grams)>0


  target = Vector{Tuple{Vector{Int},Int,Int}}()
  for i in 1:n
    i1 = _canonicalize!(fixed_space_dual[:, i])
    i2 = GInt[i,i]
    i3 = gram2[i,i]
    k = (i1, i2, i3)
    push!(target, k)
  end
  target_1 = Set(i[1] for i in target)
  target_2 = Set(i[2] for i in target)
  target_12 = Set(i[1:2] for i in target)
  target_123 = Set(target)
  D = Dict{Tuple{Vector{Int},Int,Int},Vector{Vector{Int}}}()
  f = nrows(fixed_space_dual)
  vfix_buf = Vector{Int}(undef, f)
  tmp_gram2_v = Vector{Int}(undef, n)
  for (v, sq) in __short_vectors_it(G, nothing, maxL; chol)
    sq in target_2 || continue
    # we have the list of vectors only up to sign
    # take the representative with canonicalized vfix
    LinearAlgebra.mul!(vfix_buf, fixed_space_dual, v)
    _, si = _canonicalize_with_data!(vfix_buf)
    if !isone(si)
      neg!(v)
    end
    vfix_buf in target_1 || continue
    (vfix_buf, sq) in target_12 || continue
    if use_projections
      i3 = dot!(v, gram2, v, tmp_gram2_v)
       # if we take vector sums, we use the bad vectors for the sums and discard them after
       search_fixed_vectors || (vfix_buf, sq, i3) in target_123 || continue
    else
      i3 = 0
    end
    vfix = copy(vfix_buf)
    k = (vfix, sq, i3)
    push!(get!(D, k, Vector{Int}[]), copy(v))
  end

  vector_sums = Vector{Int}[]
  if search_fixed_vectors
    Dnew = Dict{Tuple{Vector{Int},Int,Int},Vector{Vector{Int}}}()
    while length(Dnew) != length(D)
      vector_sums = [GInt*sum(a) for (k,a) in D if !iszero(k[1])]
      empty!(Dnew)
      # update targets using the vector sums
      ns = length(vector_sums)
      vfix_ext_buf = Vector{Int}(undef, f + ns)
      for i in 1:n
        @inbounds for l in 1:f; vfix_ext_buf[l] = fixed_space_dual[l, i]; end
        @inbounds for (j, w) in enumerate(vector_sums); vfix_ext_buf[f+j] = w[i]; end
        tfix = _canonicalize!(copy(vfix_ext_buf))
        target[i] = (tfix, target[i][2], target[i][3])
      end
      target_set = Set(target)
      # update the keys using vector sums and filter vectors
      for k in keys(D)
        (i1,i2,i3) = k
        for v in D[k]
          @inbounds copyto!(vfix_ext_buf, 1, i1, 1, f)
          @inbounds for (j, w) in enumerate(vector_sums); vfix_ext_buf[f+j] = dot(v, w); end
          _, si = _canonicalize_with_data!(vfix_ext_buf)
          if !isone(si)
            v = neg!(v)
          end
          vfix_ext = copy(vfix_ext_buf)
          kv = (vfix_ext, i2, i3)
          kv in target_set || continue
          push!(get!(Dnew, kv, Vector{Int}[]), v)
          @inbounds copyto!(vfix_ext_buf, 1, i1, 1, f)
        end
      end
      D, Dnew = Dnew, D
    end
  end
  if search_invariant_subspace
    gram3 = _invariant_subspace_direct(G, D)
    m3 = maximum(gram3[i,i] for i in 1:n)
    gram2 = (m3+1)*gram2 + gram3
    Dnew = Dict{Tuple{Vector{Int},Int,Int},Vector{Vector{Int}}}()
    for k in keys(D)
      (i1,i2,i3) = k
      for v in D[k]
        tmp_gram2_v = LinearAlgebra.mul!(tmp_gram2_v, gram2, v)
        i3 = dot(v, tmp_gram2_v)
        kv = (i1,i2,i3)
        push!(get!(Dnew, kv, Vector{Int}[]), v)
      end
    end
    D = Dnew
    target_norm = [gram2[i,i] for i in 1:n]
    for i in 1:n
      (i1,i2,i3) = target[i]
      i3 = gram2[i,i]
      k = (i1,i2,i3)
      target[i]
    end
  end

  # compress the two gram matrices into one
  seed = UInt(0xc70d363fbd513942)
  l = sum(length.(values(D)))
  vector_set = Vector{Tuple{Vector{Int},Vector{Int}}}(undef, l)
  invariants = Vector{Int}(undef, l)
  i = 0
  for (k,vs) in D
    kk = [k[2],k[3]]
    for v in vs
      i = i+1
      v, si = _canonicalize_with_data!(v)
      vector_set[i] = (v, copy(kk))
      invariants[i] = si*_signed_hash(k[1], seed)
    end
  end
  # redo the target invariants to include the sign

  target_invariant = Vector{Int}(undef, n)
  mf = length(vector_sums)+nrows(fixed_space_dual)
  inv_tmp = Vector{Int}(undef, mf)
  for i in 1:n
    copyto!(inv_tmp, 1, fixed_space_dual[:, i])
    k = nrows(fixed_space_dual)
    for j in 1:length(vector_sums)
      inv_tmp[k+j] = vector_sums[j][i]
    end
    target_invariant[i] = _signed_hash(inv_tmp, seed)
  end
  target_invariant = [_signed_hash(append!(fixed_space_dual[:, i], [v[i] for v in vector_sums]), seed) for i in 1:n]
  weyl_group_order = _weyl_group_order(root_types)
  grams = ZZMatrix[G, matrix(ZZ,gram2)]

  if get_assertion_level(:ShortVec) > 1
    @assert length(unique((vector_set))) == length(vector_set)
    n = nrows(G)
    CoeffType = Int; mode=:auto
    target_norms = [[CoeffType(grams[i][j,j]) for i in 1:length(grams)] for j in 1:n]
    c = 0
    for (v, n) in vector_set
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
        @assert any(ei==j[1] ||-ei==j[1] for j in vector_set) "Basis vector e_$i is missing"
        j = findfirst(==(ei), first.(vector_set))
      end
    end
  end
  @vprintln :ShortVec 1 "computed $(length(vector_set)) target vectors"
  @assert length(invariants) == length(vector_set)
  return vector_set, grams, (invariants, target_invariant), weyl_group_order, fundamental_roots
end

function _invariant_subspace_direct(Gi, short_vectors)
  n = nrows(Gi)
  r = 1:n
  G = zero_matrix(ZZ,n , n)
  G_work = zero_matrix(ZZ, n, n)
  found_invariant_subspace = false
  tmpZZ = ZZ()
  Gr = zero_matrix(ZZ, n, n)
  tmpZZMatrix1 = zero_matrix(ZZ, n, n)
  tmpZZMatrix2 = zero_matrix(ZZ, n, n)
  invariant_subspaces, rk1_invariant_subspaces = _search_invariant_subspaces(short_vectors, r)
  found_invariant_subspace = found_invariant_subspace || !isempty(invariant_subspaces) || !iszero(nrows(rk1_invariant_subspaces))
  for C in invariant_subspaces
    K = kernel(Gi*transpose(C);side=:left)
    #store vcat(C,K) in tmpZZMatrix1
    tmpZZMatrix1[1:nrows(C),:] = C
    tmpZZMatrix1[nrows(C)+1:end,:] = K
    CK_inv,_ = pseudo_inv(tmpZZMatrix1)
    toC = mul!(tmpZZMatrix1, view(CK_inv,:,1:nrows(C)),C)
    GC = mul!(tmpZZMatrix1, toC, mul!(tmpZZMatrix2, Gi,transpose!(tmpZZMatrix2,toC)))
    addmul!(Gr, GC, rand([-1,1])*rand(1:50))
  end
  # we treat the rank one subspaces separately, because
  # one matrix inverse suffices to compute all the projections at once
  C = rk1_invariant_subspaces
  if !iszero(nrows(C))
    K = kernel(Gi*transpose(C);side=:left)
    #store vcat(C,K) in tmpZZMatrix1
    tmpZZMatrix1[1:nrows(C),:] = C
    tmpZZMatrix1[nrows(C)+1:end,:] = K
    CK_inv,_ = pseudo_inv(tmpZZMatrix1)
    for l in 1:nrows(C)
      toC = view(CK_inv,:,l:l)*view(C,l:l,:)
      GC = mul!(tmpZZMatrix1,toC,mul!(tmpZZMatrix1, Gi*transpose!(tmpZZMatrix1,toC)))
      addmul!(Gr, GC, rand([-1,1])*rand(1:50))
    end
  end
  return _int_matrix_with_overflow(Gr, tmpZZ)
end
