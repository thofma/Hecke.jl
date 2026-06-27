################################################################################
#
#  Automorphism groups
#
################################################################################

function _norm_one_sublattice_automorphism_group(L::ZZLat, sv::Vector; doauto=true)
  M = matrix(ZZ, first.(sv))
  # TODO: avoid the rational_span?
  V = rational_span(L)
  S = lattice(V, M; isbasis = true, check = false)
  s = rank(S)
  T = orthogonal_submodule(lattice(V), S)
  gensOS = ZZMatrix[]
  if doauto
    push!(gensOS, diagonal_matrix(ZZ, append!([-1], (1 for _ in 1:s-1)))) # diag(-1,1,...,1)
    for g in gens(SymmetricGroup(s))
      push!(gensOS, identity_matrix(ZZ, s) * g) # generators of S_n
    end
    orderOS = ZZ(2)^s * factorial(ZZ(s))
  else
    orderOS = 0
  end
  @hassert :Lattice 1 all(g -> g * gram_matrix(S) * transpose(g) == gram_matrix(S), gensOS)
  return S, T, gensOS, orderOS
end

# This is an internal function, which sets
# L.automorphism_group_generators
# L.automorphism_group_order
assert_has_automorphisms(L::ZZLat; kwargs...) = _assert_has_automorphisms_ZZLat(L; kwargs...)

# this gets overwritten in Oscar with a faster / more stable method
_assert_has_automorphisms_ZZLat(L; kwargs...) = __assert_has_automorphisms(L; kwargs...)

function __assert_has_automorphisms(
  L::ZZLat;
  redo::Bool=false,
  try_small::Bool=true,
  depth::Int=0,
  bacher_depth::Int=0,
  use_weyl::Bool=true,
  use_projections::Bool=true,
  use_norm_one::Bool=true,
  use_everything::Bool=true,
  compress::Bool=true,
  search_fixed_vectors::Bool=true,
  search_invariant_subspace::Bool=false,
  use_target_enum::Bool=true,
  short_vectors_direct::Bool=false,
  allow_short_vectors_direct::Bool=true,
  do_lll::Bool=true,
  use_dual::Bool=false,
)

  if !redo && isdefined(L, :automorphism_group_generators)
    return nothing
  end
  # Corner cases
  if rank(L) == 0
    L.automorphism_group_generators = ZZMatrix[identity_matrix(ZZ, 0)]
    L.automorphism_group_order = one(ZZRingElem)
    return nothing
  end

  if rank(L) == 1
    L.automorphism_group_generators = ZZMatrix[-identity_matrix(ZZ, 1)]
    L.automorphism_group_order = ZZ(2)
    return nothing
  end

  if !is_definite(L)
    @assert rank(L) == 2
    G = gram_matrix(L)
    d = denominator(G)
    GG = change_base_ring(ZZ, d*G)
    b = binary_quadratic_form(GG[1,1], 2*GG[1,2], GG[2,2])
    gens = transpose.(automorphism_group_generators(b))
    L.automorphism_group_generators = gens
    return nothing
  end


  # scale integral and positive definite and with trivial basis matrix
  d = sign(gram_matrix(L)[1,1])*denominator(gram_matrix(L))
  if !isone(d)
    _L = rescale(L, 1//d; cached=false)
  else
    _L = L
  end
  if !isone(basis_matrix(_L)) || rank(_L) != degree(_L)
    _L = lattice(rational_span(_L))
  end
  V = ambient_space(_L)
  GL = numerator(gram_matrix(_L))
  if use_everything
    use_weyl = true
    use_projections = true
    use_target_enum = true
    use_norm_one = true
    compress = true
  end
  # disable everything for big lattices
  if !(all(fits(Int,i) for i in GL))
    use_weyl = false
    use_projections = false
    use_target_enum = false
    use_norm_one = false
    compress = false
  end
  vector_set = []
  # Split off norm 1 vectors
  if use_norm_one && (sv = short_vectors(L, 0, Int(1)); length(sv) > 0)
    S, T, gensOS, orderOS = _norm_one_sublattice_automorphism_group(L, sv)
    __assert_has_automorphisms(T; redo, try_small, depth, bacher_depth, use_weyl,
                               use_projections, use_norm_one=false, search_fixed_vectors, search_invariant_subspace,
                               compress, use_target_enum, allow_short_vectors_direct)
    # we call directly .automorphism_group_generators, since we want the automorphisms as ZZMatrix
    # (with respect to the basis of T)
    gensOT = T.automorphism_group_generators
    orderOT = automorphism_group_order(T)
    ST = (vcat(basis_matrix(S), basis_matrix(T)))
    oneS = identity_matrix(ZZ, rank(S))
    oneT = identity_matrix(ZZ, rank(T))
    gens = ZZMatrix[numerator(inv(ST) * diagonal_matrix(g, oneT) * ST) for g in gensOS]
    append!(gens, (numerator(inv(ST) * diagonal_matrix(oneS, g) * ST) for g in gensOT))
    @hassert :Lattice 1 all(let gens = gens, GL = GL; i -> gens[i] * GL *
                            transpose(gens[i]) == GL; end, 1:length(gens))
    L.automorphism_group_generators = gens
    L.automorphism_group_order = orderOS * orderOT
    return nothing
  end
  invariants = (Int[],Int[])
  res = ZZMatrix[GL]
  is_lll = get_attribute(L, :is_lll_reduced, false)
  do_lll = !is_lll && do_lll
  if do_lll
    # Make the Gram matrix small
    Glll, T = lll_gram_with_transform(res[1])
    _L = integer_lattice(gram=Glll; cached=false)
    Ttr = transpose(T)
    res = [Glll]
    #res = ZZMatrix[T*g*Ttr for g in res]
  else
    Glll = GL
  end

  if maximum(abs.(gram_matrix(_L)))>ZZ(2)^62
    # temporary fix TODO to it in _short_vectors_with_condition
    use_target_enum = false
  end
  if use_weyl && use_projections && use_target_enum
    res, vector_set, invariants, weyl_group_order, fundamental_roots = _get_weyl_proj_and_vector_set(_L;force_direct=short_vectors_direct,
                                                                    search_fixed_vectors, search_invariant_subspace, use_dual, allow_short_vectors_direct)
    use_projections = false # already added projections
  elseif use_weyl
    error("not implemented")
  end
  if use_projections
    proj = _invariant_projections(_L)
    projZ = numerator.(proj)
    GZ = res[1]
    projgramZ = [i*GZ*transpose(i) for i in projZ]
    append!(res, projgramZ)
  end

  if get_assertion_level(:Lattice) > 1
    for (v, n) in vector_set
      @assert all(dot(v * res[i], v) == n[i] for i in 1:length(res))
    end
  end
  res_uncompressed = res
  faithful = true
  if compress && length(res) > 1 # nothing to compress if there is only a single
    res, vector_set = _compress_gram_matrices!(res, vector_set)
    res2, vector_set2 = copy(res), [(v,copy(n)) for (v,n) in vector_set] # backup to confirm computation
    @assert length(res2) == 2
    res, vector_set, faithful = _compress_two_matrices_try_faithful_and_small!(res, vector_set)
    @vprintln :Lattice 1 "Compression to one matrix successful: $faithful"
  end

  if get_assertion_level(:Lattice) > 1
    for (v, n) in vector_set
      @assert all(dot(v * res[i], v) == n[i] for i in 1:length(res))
    end
  end
  @label init_small
  C = ZLatAutoCtx(res)
  fl = false
  if try_small
    fl, Csmall = try_init_small(C; depth, bacher_depth, is_lll_reduced_known=true, vector_set, invariants)
    if fl
      _gens, order = auto(Csmall)
      gens = ZZMatrix[matrix(ZZ, g) for g in _gens]
    end
    if !faithful
      # it is unlikely, that the unfaithful compression created something too large
      # but let's try to do try_small_init with the uncommpressed version again
      # anything is cheaper than the large version
      faithful = true
      if !fl
        # try again without forced compression
        vector_set = vector_set2
        res = res2
        @goto init_small
      end
      Gint = _int_matrix_with_overflow(res2[1], ZZ())
      tmp_mat = zero(Gint)
      if any(mul!(tmp_mat, g,mul!(tmp_mat, Gint,transpose(g))) != Gint for g in _gens)
        # compression returned wrong outputs redo
        @vprintln :Lattice 1 "Compression returned wrong outputs, retrying with uncompressed data"
        vector_set = vector_set2
        res = res2
        @assert length(res) == 2
        @goto init_small
      end
    end
    !fl && @vprintln :Lattice 1 "Try init small failed; switching to large"
  end
  if !try_small || !fl
    C = ZLatAutoCtx(res_uncompressed)
    init(C; depth, bacher_depth, is_lll_reduced_known=true)
    gens, order = auto(C)
  end

  if use_weyl
    reduced_gens = copy(gens)
    _fundamental_roots = reduce(append!,[f[i:i,:] for i in 1:nrows(f)] for f in fundamental_roots; init=ZZMatrix[])
    _orbit_rep_fundamental = _orbit_representatives(reduced_gens, _fundamental_roots)
    _weyl_gens = _weyl_group_gens(Glll, fundamental_roots)
    append!(gens, _weyl_gens)
  end

  # Now translate back
  if do_lll
    Tinv = inv(T)
    for i in 1:length(gens)
      gens[i] = Tinv * gens[i] * T
    end

    if use_weyl # translate reduced generators back
      for i in 1:length(reduced_gens)
        reduced_gens[i] = Tinv * reduced_gens[i] * T
      end
    end
  end

  # Now gens are with respect to the basis of L
  @hassert :Lattice 1 all(let gens = gens; i -> change_base_ring(QQ, gens[i]) * GL *
                          transpose(change_base_ring(QQ, gens[i])) == GL; end, 1:length(gens))
  #@hassert :Lattice 1 use_weyl && all(let gens = reduced_gens; i -> change_base_ring(QQ, gens[i]) * GL *
  #                                    transpose(change_base_ring(QQ, gens[i])) == GL; end, 1:length(gens))
  L.automorphism_group_generators = gens
  if use_weyl
    # We have O(L) = W(L)x|Aut_red(L)
    # where Aut_red(L) = Aut(L,\rho) is the stabilizer of rho in O(L)
    # the Weyl vector \rho is preserved only up to sign
    # so we have computed Aut(L,{\pm \rho}) and its order
    if weyl_group_order > 1
      if use_target_enum && fl # fl because invariants are not used with ZZRingElem for now
        order_reduced = order
      else
        order_reduced = divexact(order, 2)  # the order of Aut(L, \rho)
      end
    else
      # when rho is trivial
      order_reduced = order
    end
    L.reduced_automorphism_group_order = order_reduced
    L.automorphism_group_order = order_reduced*weyl_group_order
    L.reduced_automorphism_group_generators = reduced_gens
  else
    L.automorphism_group_order = order
  end
  if @isdefined Csmall
    return Csmall
  else
    return nothing
  end
end

function _get_weyl_proj_and_vector_set(_L; search_fixed_vectors::Bool=true,
                                       search_invariant_subspace::Bool=false,
                                       use_dual::Bool=false,
                                       allow_short_vectors_direct::Bool=false,
                                       force_direct::Bool=false)
  tmp = ZZ()
  gramZZ, _ = _integral_split_gram(_L)
  gramInt = _int_matrix_with_overflow(gramZZ, tmp)
  chol = CholeskyIntegralDenom(gramZZ)
  sv2 = __short_vectors(gramZZ, nothing, 2; chol)
  n = rank(_L)
  fundamental_roots = [matrix(ZZ,1,n,i) for i in _fundamental_roots(sv2, gramInt)]

  root_types, fundamental_roots = _root_lattice_recognition_fundamental(_L, fundamental_roots)
  fixed_matrix, isotypic_cofix_spaces, weyl_vector = _weyl_group(_L, root_types, fundamental_roots)
  T = _short_vectors_with_condition_preprocessing(_L, fundamental_roots,weyl_vector, fixed_matrix, isotypic_cofix_spaces, :rank, use_dual)
  (_L, successive_sublattices, B, Binv, projection_ranges, projL,
  projL_gram, denoms, target_fixed_part, target_norms, grams) = T
  do_direct = allow_short_vectors_direct
  do_direct = do_direct && all(set!(tmp, mat_entry_ptr(gramZZ,i,i))<=4 for i in 1:n)
  do_direct = do_direct && any(rank(successive_sublattices[i])>=15 for i in 2:length(successive_sublattices)) && rank(successive_sublattices[1])<=4
  do_direct = do_direct || force_direct
  if !do_direct
    @vprintln :Lattice 2 "short vectors choosing target=true"
    @vtime :Lattice 2 vector_set, grams, invariants  = _short_vectors_with_condition(Int, T...; search_fixed_vectors, search_invariant_subspace)
  else
    @vprintln :Lattice 2 "short vectors choosing direct=true"
    @vtime :Lattice 2 vector_set, grams, invariants  = __short_vectors_with_condition_direct(gramZZ, gramInt, grams, fixed_matrix, root_types, fundamental_roots, chol; search_fixed_vectors, search_invariant_subspace)
  end
  if get_assertion_level(:Lattice) > 1
    for (v, n) in vector_set
      @assert all(dot(v * grams[i], v) == n[i] for i in 1:length(grams))
    end
  end
  if get_assertion_level(:Lattice) > 1
    for (v, n) in vector_set
      @assert all(dot(v * grams[i], v) == n[i] for i in 1:length(grams))
    end
  end
  @assert length(grams) == length(vector_set[1][2])
  weyl_group_order = _weyl_group_order(root_types)
  return grams, vector_set, invariants, weyl_group_order, fundamental_roots
end

function _compress_two_matrices_try_faithful_and_small!(res, vector_set)
  @assert length(res) == 2
  # we try to compress res[1] and res[2], such that we are "faithful"
  i0 = 2
  i1 = 1
  Sbound = maximum(i -> abs(i[2][i0]), vector_set)
  faithful = true
  _lambda = 2 * ZZ(Sbound) + 1
  # this test could be sped up
  Gnew = _lambda * res[i1] + res[i0]
  if !_fits_small_init([Gnew], vector_set)
    _lambda = next_prime(8 * ZZ(1) * maximum(abs, res[i0]) + 1, false)
    faithful = false
    Gnew = _lambda * res[i1] + res[i0]
    @assert _fits_small_init([Gnew], vector_set)
  end
  keep_separated = false
  if fits(Int, _lambda) && all(x -> fits(Int, x), Gnew)
    lambda = Int(_lambda)
    # we also need to check whether the new norms fit into Int
    lambdabits = nbits(lambda)
    maxnbitsbound = 8 * sizeof(Int) - lambdabits - 3 #
    for (i, (v, n)) in enumerate(vector_set)
      wnbits = max(nbits(n[i1]), nbits(n[i0]))
      if wnbits > maxnbitsbound
        # norm is getting too large, abort
        keep_separated = true
        break
      end
    end
  else
    keep_separated = true
  end
  if keep_separated
    return res, vector_set, true
  end

  res = [lambda * res[i1] + res[i0]]
  for (v, n) in vector_set
    n[1] = lambda * n[i1] + n[i0]
    resize!(n, 1)
  end
  return res, vector_set, faithful
end

function _fits_small_init(G::Vector{ZZMatrix}, vector_nbits::Int)
  bitbound = Int == Int64 ? 64 : 32
  abs_maxbits_vectors = Int == Int64 ? 30 : 15
  Gsnbits = maximum(maximum.(nbits, G)) + 1 # + 1 for the sign
  n = nrows(G[1])
  nrows_nbits = nbits(n)
  vectors = first.(vector_set)
  vectors_nbits = 0
  if vectors_nbits > abs_maxbits_vectors
    return false
  end
  if Gsnbits + vectors_nbits + nrows_nbits + 1 > bitbound
    return false
  end
  return true
end

function _fits_small_init(G::Vector{ZZMatrix}, vector_set::Vector)
  bitbound = Int == Int64 ? 64 : 32
  abs_maxbits_vectors = Int == Int64 ? 30 : 15
  Gsnbits = maximum(maximum.(nbits, G)) + 1 # + 1 for the sign
  n = nrows(G[1])
  nrows_nbits = nbits(n)
  vectors = first.(vector_set)
  vectors_nbits = 0
  for v in vectors
    vectors_nbits = max(vectors_nbits, maximum(nbits, v) + 1)
    if vectors_nbits > abs_maxbits_vectors
      return false
    end

    if Gsnbits + vectors_nbits + nrows_nbits + 1 > bitbound
      return false
    end
  end
  return true
end

# Given gram matrices G1,...,Gn, we construct
# - G1, a_2G_2 + ... + a_nG_n with a_i small, positive, and random
# - adjust the vector_set accordingly
function _compress_gram_matrices!(res::Vector{ZZMatrix}, vector_set::Vector)
  # determine the bound for the size of the gram matrix
  arangebit = 3
  arange = 1:2^arangebit-1
  bitbound = Int == Int64 ? 64 : 32
  r = nrows(res[1])
  nrows_nbits = nbits(r)
  vectors_nbits = 0
  for (v, _) in vector_set
    vectors_nbits = max(vectors_nbits, maximum(nbits, v) + 1)
  end
  # we want Gsmall_nbits + vectors_nbits + nrows_nbits + 1 <= bitbound
  # (this is the bound checked in try_small_init)
  # so Gsmall_nbits <= bitbound - vectors_nbits - nrows_nbits - 1
  # assume we combine r matrices with coefficients with 3 bits, then each Gram G
  # matrix must satisfy
  # 3 + nbits(r) + Gnbits <= bitbound - vectors_nbits - nrows_nbits - 1
  # Gnbits <= bitbound - vector_nbits - nrows_nbits - 1 - 3 - nbits(r)
  gramnbitsbound = bitbound - vectors_nbits - nrows_nbits - 1 - arangebit - nbits(length(res) - 1)
  I = collect(2:length(res))
  II = filter(i -> maximum(nbits, res[i]) <= gramnbitsbound, I)
  @assert length(I) == length(II)
  #if maximum(nbits, res[1]) <= gramnbitsbound && length(II) < length(I)
  #  #error("Some Gram matrices are too large. Interesting case?!")
  #  @vprintln :Lattice 1  "Removed Gram matrices with entries too large"
  #end
  I = II

  if length(I) == 0
    return res, vector_set
  end

  res_to_compress = @view res[I]
  l = length(res_to_compress)
  a = rand(arange, l)
  while any(iszero, a)
    a = rand(arange, l)
  end
  anbits = maximum(nbits, a)
  rnbits = nbits(r)
  normbitbound = 8 * sizeof(Int) - 1 - arangebit
  for (i, (v, n)) in enumerate(vector_set)
    w = n[I]
    wnbits = maximum(nbits, w)
    @assert wnbits <= normbitbound
    d = dot(a, w)
    @hassert :Lattice 1 d == dot(ZZ.(a), ZZ.(w))
    resize!(n, 2)
    n[2] = d
  end
  Gcompressed = sum(a[i]*res_to_compress[i] for i in 1:l)
  res = [res[1], Gcompressed]
  @assert _fits_small_init(res, vector_set)
  return res, vector_set
end

# documented in ../Lattices.jl
function automorphism_group_generators(
  L::ZZLat;
  ambient_representation::Bool = true,
  kwargs...,
)

  @req rank(L) in [0, 2] || is_definite(L) "The lattice must be definite or of rank at most 2"
  assert_has_automorphisms(L; kwargs...)

  gens = L.automorphism_group_generators
  if !ambient_representation
    return QQMatrix[ change_base_ring(QQ, g) for g in gens]
  else
    # Now translate to get the automorphisms with respect to basis_matrix(L)
    bm = basis_matrix(L)
    V = ambient_space(L)
    if rank(L) == rank(V)
      bminv = inv(bm)
      res = QQMatrix[bminv * change_base_ring(QQ, g) * bm for g in gens]
    else
      # Extend trivially to the orthogonal complement of the rational span
      !is_regular(V) &&
        error(
          """Can compute ambient representation only if ambient space is
             regular""")
      C = orthogonal_complement(V, basis_matrix(L))
      C = vcat(basis_matrix(L), C)
      Cinv = inv(C)
      D = identity_matrix(QQ, rank(V) - rank(L))
      res = QQMatrix[Cinv * diagonal_matrix(change_base_ring(QQ, g), D) * C for g in gens]
    end
    @hassert :Lattice 1 all(g * gram_matrix(V) * transpose(g) == gram_matrix(V)
                            for g in res)
    return res
  end
end

# documented in ../Lattices.jl
function automorphism_group_order(
  L::ZZLat;
  kwargs...,
)
  if isdefined(L, :automorphism_group_order)
    return L.automorphism_group_order
  end
  @req is_definite(L) "The lattice must be definite"
  assert_has_automorphisms(L; kwargs...)
  return L.automorphism_group_order
end

function reduced_automorphism_group_order(
  L::ZZLat;
  kwargs...,
)
  if isdefined(L, :reduced_automorphism_group_order)
    return L.reduced_automorphism_group_order
  end
  if isdefined(L, :automorphism_group_order)
    wg_order = _weyl_group_order(root_lattice_recognition(L)[1])
    L.reduced_automorphism_group_order = divexact(L.automorphism_group_order, wg_order)
  end
  @req is_definite(L) "The lattice must be definite"
  # overwrite use_weyl keyword, to compute the reduced information
  assert_has_automorphisms(L; kwargs..., use_weyl = true)
  return L.reduced_automorphism_group_order
end


# Helpers to find additional structure in the lattice

function _invariant_projections_and_sublattices(L::ZZLat, elem_type::Type{S}=Int; use_dual::Bool = false) where {S}
  # the first condition is a safeguard from a flint convention for isone
  if rank(L) != degree(L) || !isone(basis_matrix(L))
    L = lattice(rational_span(L))
  end
  LL, _ = _short_vector_generators_with_sublattice_2(L, S; up_to_sign=true, use_dual)
  return __projections(LL), LL
end

_invariant_projections(L::ZZLat) = _invariant_projections_and_sublattices(L)[1]

function  __projections(LL::Vector{ZZLat})
  B = vcat(basis_matrix.(LL)...)
  Bi = inv(B)
  n = degree(LL[1])
  projections = QQMatrix[]
  k = 0
  for i in 1:length(LL)
    k_i = rank(LL[i])
    E = zero_matrix(QQ, n, n)
    knew = k + k_i
    for j in k+1:knew
      E[j,j] =1
    end
    k = knew
    mul!(E, Bi, mul!(E, B)) # E = Bi*E*B
    push!(projections, E)
  end
  return projections
end



################################################################################
#
#  Isometry
#
################################################################################

# documented in ../Lattices.jl

function is_isometric(L::ZZLat, M::ZZLat; depth::Int = -1, bacher_depth::Int = 0)
  if L == M
    return true
  end

  if rank(L) != rank(M)
    return false
  end

  if rank(L) == 1
    return gram_matrix(L) == gram_matrix(M)
  end

  if is_definite(L) && is_definite(M)
    return is_isometric_with_isometry(L, M, depth = depth, bacher_depth = bacher_depth)[1]
  end

  if rank(L) == 2
    _A = gram_matrix(L)
    _B = gram_matrix(M)
    d = denominator(_A)
    A = change_base_ring(ZZ, d * _A)
    B = change_base_ring(ZZ, d * _B)
    q1 = binary_quadratic_form(ZZ, A[1,1], 2 * A[1,2], A[2,2])
    q2 = binary_quadratic_form(ZZ, B[1,1], 2 * B[1,2], B[2,2])
    return is_isometric(q1, q2)
  end

  return _is_isometric_indef(L, M)
end

function is_isometric_with_isometry(L::ZZLat, M::ZZLat; depth::Int = -1, bacher_depth::Int = 0)

  # cornercase
  if rank(L) == 0
    return true, zero_matrix(QQ, 0, 0)
  end

  if is_definite(L) && is_definite(M)
    return _is_isometric_with_isometry_definite(L, M; depth, bacher_depth)
  end

  error("Not implemented for indefinite lattices")
end

# assumes rank >0, definite, no genus check
_is_isometric_with_isometry_definite(L, M; kwargs...) = __is_isometric_with_isometry_definite(L, M; kwargs...)

function __is_isometric_with_isometry_definite(L::ZZLat, M::ZZLat; depth::Int = -1, bacher_depth::Int = 0, use_norm_one=true)
  if rank(L) != rank(M)
    return false, zero_matrix(QQ, 0, 0)
  end

  # cornercase
  if rank(L) == 0
    return true, zero_matrix(QQ, 0, 0)
  end

  i = sign(gram_matrix(L)[1,1])
  j = sign(gram_matrix(M)[1,1])
  @req i==j "The lattices must have the same signatures"

  if i < 0
    s = -1
  else
    s = 1
  end

  GL = gram_matrix(L)
  dL = denominator(GL)
  GLint = change_base_ring(ZZ, s * dL * GL)
  cL = content(GLint)
  GLint = divexact!.(GLint, cL)

  GM = gram_matrix(M)
  dM = denominator(GM)
  GMint = change_base_ring(ZZ, s * dM * GM)
  cM = content(GMint)
  GMint = divexact!.(GMint, cM)

  # GLint, GMint are integral, primitive scalings of GL and GM
  # If they are isometric, then the scalars must be identical.
  if dL//cL != dM//cM
    return false, zero_matrix(QQ, 0, 0)
  end

  # Now compute LLL reduced gram matrices
  GLlll, TL = lll_gram_with_transform(GLint)
  @hassert :Lattice 1 TL * change_base_ring(ZZ, s*dL*GL) * transpose(TL) == GLlll *cL
  GMlll, TM = lll_gram_with_transform(GMint)
  @hassert :Lattice 1 TM * change_base_ring(ZZ, s*dM*GM) * transpose(TM) == GMlll *cM

  # Setup for Plesken--Souvignier

  G1 = ZZMatrix[GLlll]
  G2 = ZZMatrix[GMlll]

  fl = (all(fits(Int,i) for i in GLlll)) && (all(fits(Int,i) for i in GMlll))
  if fl
    _L1 = integer_lattice(gram=G1[1];cached=false)
    _L2 = integer_lattice(gram=G2[1];cached=false)
    if use_norm_one
      sv1 = short_vectors(_L1, 0, Int(1))
      sv2 = short_vectors(_L2, 0, Int(1))
      length(sv1) == length(sv2) || return false, zero_matrix(QQ,0,0)
      if length(sv1)>0
        S1, T1, _, _ = _norm_one_sublattice_automorphism_group(_L1, sv1; doauto=false)
        S2, T2, _, _ = _norm_one_sublattice_automorphism_group(_L2, sv2; doauto=false)
        b,T = is_isometric_with_isometry(T1,T2)
        !b && return false, zero_matrix(QQ,0,0)
        B1 = vcat(basis_matrix(S1),basis_matrix(T1))
        B2 = vcat(basis_matrix(S2),basis_matrix(T2))
        T = inv!(B1)*diagonal_matrix(identity_matrix(QQ,rank(S1)),T)*B2
        # undo lll
        T = change_base_ring(QQ, inv(TL)*T*TM)
        @hassert :Lattice 1 T * gram_matrix(M) * transpose(T) == gram_matrix(L)
        return true, T
      end
    end
    b, out1,out2 = short_vectors_with_condition(Int, _L1, _L2)
    V1, grams1, invariants1 = out1
    V2, grams2, invariants2 = out2
    if !b
      return false, zero_matrix(QQ,0,0)
    end
    fl, CLsmall, CMsmall = _try_iso_setup_small(grams1, grams2, depth = depth, bacher_depth = bacher_depth; vector_set1=V1, vector_set2=V2, invariants1, invariants2)
  end
  if fl
    b, _T = isometry(CLsmall, CMsmall)
    T = matrix(ZZ, _T)
  else
    CL, CM = _iso_setup(ZZMatrix[GLlll], ZZMatrix[GMlll], depth = depth, bacher_depth = bacher_depth)
    b, T = isometry(CL, CM)
  end

  if b
    # undo LLL
    T = change_base_ring(QQ, inv(TL)*T*TM)
    @hassert :Lattice 1 T * gram_matrix(M) * transpose(T) == gram_matrix(L)
    return true, T
  else
    return false, zero_matrix(QQ, 0, 0)
  end
end

################################################################################
#
#  Isometry test indefinite lattices
#
################################################################################
@doc raw"""
    _decompose_in_reflections(G::QQMatrix, T::QQMatrix, p, nu) -> (err, Vector{QQMatrix})

Decompose the approximate isometry `T` into a product of reflections
and return the error.

The algorithm follows Shimada [Shim2018](@cite)
The error depends on the approximation error of `T`, i.e. $T G T^t - G$.

# Arguments
- `G::QQMatrix`: a diagonal matrix
- `T::QQMatrix`: an isometry up to some padic precision
- `p`: a prime number
"""
function _decompose_in_reflections(G::QQMatrix, T::QQMatrix, p)
  @assert is_diagonal(G)
  p = ZZ(p)
  if p == 2
    delta = 1
  else
    delta = 0
  end
  gammaL = [valuation(d, p) for d in diagonal(G)]
  gamma = minimum(gammaL)
  l = ncols(G)
  E = parent(G)(1)
  reflection_vectors = QQMatrix[]
  Trem = deepcopy(T)
  k = 1
  while k <= l
    g = Trem[k:k,:]
    bm = g - E[k:k,:]
    qm = bm * G * transpose(bm)
    if valuation(qm, p) <= gammaL[k] + 2*delta
      tau1 = reflection(G, bm)
      push!(reflection_vectors, bm)
      Trem = Trem * tau1
    else
      bp = g + E[k:k,:]
      qp = bp * G * transpose(bp)
      @assert valuation(qp, p) <= gammaL[k] + 2*delta
      tau1 = reflection(G, bp)
      tau2 = reflection(G, E[k:k,:])
      push!(reflection_vectors,bp)
      push!(reflection_vectors,E[k:k,:])
      Trem = Trem * tau1 * tau2
    end
    k += 1
  end
  reverse!(reflection_vectors)
  R = reduce(*, reflection(G, v) for v in reflection_vectors)
  err = valuation(T - R, p)
  return err, reflection_vectors
end


function _is_isometric_indef(L::ZZLat, M::ZZLat)
  @req rank(L)>=3 "Strong approximation needs rank at least 3"
  @req degree(L)==rank(L) "Lattice needs to be full for now"

  # scale integral
  n = rank(L)
  s = scale(M)
  M = rescale(M, s^-1; cached=false)
  L = rescale(L, s^-1; cached=false)
  @assert scale(M)==1
  @assert scale(L)==1
  g = genus(L)
  if g != genus(M)
    return false
  end
  S, isS = _improper_spinor_generators(g)
  if length(S)==0
    # unique spinor genus
    return true
  end
  f, r = _is_isometric_indef_approx(L, M)
  return is_zero(isS(QQ(r)))
end

function _is_isometric_indef_approx(L::ZZLat, M::ZZLat)
  # move to same ambient space
  qL = ambient_space(L)
  diag, trafo = Hecke._gram_schmidt(gram_matrix(qL), identity)
  qL1 = quadratic_space(QQ, diag; cached=false)

  L1 = lattice(qL1, basis_matrix(L)*inv(trafo), check=false)
  @hassert :Lattice 1 genus(L1) == genus(L)
  qM = ambient_space(M)
  b, T = is_isometric_with_isometry(qM, qL1)
  @assert b  # same genus implies isomorphic space
  M1 = lattice(qL1, basis_matrix(M)*T, check=false)
  @hassert :Lattice 1 genus(M1) == genus(L)
  r1 = index(M1,intersect(M1,L1))

  V = ambient_space(L1)
  gramV = gram_matrix(V)
  sL = 8//scale(dual(L1))
  bad = support(2*det(L1))
  extra = 10
  @label more_precision
  targets = Tuple{QQMatrix,ZZRingElem,Int}[]
  for p in bad
    vp = valuation(sL, p) + 1
    if valuation(r1, p)==0
      fp = identity_matrix(QQ, dim(qL1))
      push!(targets,(fp, p , vp))
      continue
    end
    # precision seems to deteriorate along the number of reflections
    precp = vp + 2*rank(L) + extra
    # Approximate an isometry fp: Lp --> Mp
    normalM1, TM1 = Hecke.padic_normal_form(gram_matrix(M1), p, prec=precp)
    normalL1, TL1 = Hecke.padic_normal_form(gram_matrix(L1), p, prec=precp)
    @assert normalM1 == normalL1
    TT = inv(TL1) * TM1
    fp = inv(basis_matrix(L1))* TT * basis_matrix(M1)
    d = det(fp)-1
    if !iszero(d) && valuation(d, p)<= vp
      # we want fp in SO(Vp)
      # compose with a reflection preserving Lp
      norm_gen = _norm_generator(normalL1, p) * TL1 * basis_matrix(L1)
      @assert valuation((norm_gen * gramV * transpose(norm_gen))[1,1],p)==valuation(norm(L1), p)
      fp = reflection(gramV, norm_gen) * fp
      d = det(fp)-1
      @assert  iszero(d) || valuation(d, p)>= vp
    end
    # double check that fp: Lp --> Mp
    M1fp = lattice(V, basis_matrix(L1) * fp, check=false)
    indexp = index(M1,intersect(M1fp, M1))
    @assert valuation(indexp,p)==0
    push!(targets,(fp, p, vp))
  end
  f = zero_matrix(QQ,0,0)
  try
    f = weak_approximation(V, targets)
  catch e
    if isa(e, ErrorException) && startswith(e.msg,"insufficient precision of fp")
      extra = extra + 5
      @goto more_precision
    else
      rethrow(e)
    end
  end

  L1f = lattice(V, basis_matrix(L1) * f, check=false)
  indexL1f_M1 = index(M1, intersect(L1f, M1))
  # confirm computation
  for p in bad
    v = valuation(indexL1f_M1, p)
    @assert v == 0 "$p: $v"
  end
  return f, indexL1f_M1
end

function _norm_generator(gram_normal, p)
  # the norm generator is the last diagonal entry of the first jordan block.
  # except if the last 2x2 block is a hyperbolic plane
  R = residue_ring(ZZ, p)[1]
  n = ncols(gram_normal)
  gram_normal = change_base_ring(ZZ, gram_normal)
  gram_modp = change_base_ring(R, gram_normal)
  ind,vals = _block_indices_vals(gram_modp, p)
  @assert vals[1]==0
  if length(ind)==1
    i = nrows(gram_normal)
  else
    i = ind[2]-1
  end
  E = identity_matrix(QQ, n)
  q = gram_normal[i,i]
  if q!=0 && valuation(q, p) <= 1
    return E[i:i,:]
  end
  @assert p==2
  return E[i:i,:] + E[i-1:i-1,:]
end



# Preprocessing for Plesken Souvignier
# return generators for the weyl group
# invariant gram matrices
# invariant vectors
function _weyl_group(L::ZZLat)
  root_types, fundamental_roots = _root_lattice_recognition_fundamental(L)
  return _weyl_group(L, root_types, fundamental_roots)
end

function _weyl_group(L::ZZLat, root_types, fundamental_roots::Vector{ZZMatrix})
  n = rank(L)
  GZ,_ = _integral_split_gram(L)
  if !isone(basis_matrix(L)) || rank(L) != degree(L)
    L = lattice(rational_span(L))
  end
  weyl_vector = zeros_array(QQ, degree(L))
  tmp_vector = zeros_array(QQ, degree(L))
  isotypic_cofix_spaces = ZZMatrix[]
  if length(root_types) == 0
    return zero_matrix(ZZ, 0, n), isotypic_cofix_spaces, weyl_vector
  end
  invariant_vectors = ZZMatrix[]
  F = reduce(vcat, fundamental_roots)
  F = transpose!(F, hnf!(transpose(F))) # speeds up elementary_divisors calls
  # saturate and solve are slow, we use
  # several calls to elementary_divisors instead
  #P = saturate(F)
  #D = solve(QQ.(F),QQ.(P); side=:left)
  glue_indices = Vector{Vector{ZZRingElem}}()
  j = 0
  nf = nrows(F)
  for f in fundamental_roots
    k = j + nrows(f)
    rows = Int[]
    sizehint!(rows, nf - nrows(f))
    for i in 1:j
      push!(rows, i)
    end
    for i in k+1:nf
      push!(rows, i)
    end
    #d = denominator(view(D,:,r))
    C = F[rows,:]
    ed = filter!(!isone, elementary_divisors(C))
    push!(glue_indices, ed)
    j = k
  end
  D = Dict{Tuple{Tuple{Symbol, Int}, Vector{ZZRingElem}}, Vector{ZZMatrix}}()
  for (t,g,f) in zip(root_types, glue_indices, fundamental_roots)
    k = (t,g)
    if haskey(D, k)
      push!(D[k], f)
    else
      D[k] = ZZMatrix[f]
    end
  end
  # We sort the keys to make the order of the output canonical:
  # in the sense that it defines an isometry Fix(L1_root) -> Fix(L2_root)
  # that extends to an isometry L1 -> L2
  sorted_keysD = sort!(collect(keys(D)))
  for k in sorted_keysD
    (t, d) = k
    blocks = D[k]
    isotypic = reduce(vcat, blocks)
    inv_vec = _invariant_vectors(t...)
    anti_inv_vec = _anti_invariant_vectors(t...)
    weyl_vector_t = _weyl_vector(t...)
    for f in blocks
      add!.(weyl_vector, mul!(tmp_vector, weyl_vector_t, f))
    end
    invariant_vectors_k = ZZMatrix[]
    sizehint!(invariant_vectors_k, length(inv_vec))

    representations_k = ZZMatrix[]
    for u in inv_vec
      s = u*blocks[1]
      for i in 2:length(blocks)
        addmul!(s, u,blocks[i])
      end
      push!(invariant_vectors_k, s)
      # the S_u co-fixed part
      length(blocks) > 1 || continue
    end
    invariant_vectors_k_mat = reduce(vcat, invariant_vectors_k)
    r = t[2]
    b = length(blocks)
    if (b > 4 && r > 2) || (b > 2 && r > 3) || (b > 1 && r>6) || (b==2 && r==6 && t[1]==:A)
      for u in inv_vec
        b>1 || continue
        s = reduce(vcat, u*(blocks[i]-blocks[i+1]) for i in 1:length(blocks)-1; init=zero_matrix(ZZ,0, n))
        push!(representations_k, s)
      end
      for u in anti_inv_vec
        # the S_u co-fixed part
        t = reduce(vcat, u*blocks[i] for i in 1:length(blocks); init=zero_matrix(ZZ,0, n))
        push!(representations_k, t)
      end
    elseif nrows(isotypic)!= nrows(invariant_vectors_k_mat)
      M = change_base_ring(QQ,isotypic*GZ*transpose(invariant_vectors_k_mat))
      isotypic_cofix_space = kernel(M, side= :left)*isotypic
      push!(representations_k, numerator(isotypic_cofix_space))
    end


    append!(invariant_vectors, invariant_vectors_k)
    append!(isotypic_cofix_spaces, representations_k)
  end

  fixed_matrix = reduce(vcat, invariant_vectors)
  @hassert :Lattice 1 all(all(isone,i*GZ*weyl_vector) for i in fundamental_roots)
  return fixed_matrix, isotypic_cofix_spaces, weyl_vector
end

# Return the vectors fixed by the reduced automorphism group.
function _invariant_vectors(s::Symbol, n::IntegerUnion)
  invs = ZZMatrix[]
  if s == :A
    # u_k = e_k + e_{k+1} + ... + e_{n+1-k}, for k = 1,...,ceil(n/2).
    # These are pairwise orthogonal w.r.t. the A_n Cartan matrix:
    #   <u_k, u_k> = 2, <u_k, u_l> = 0 for k != l.
    # They span the same subspace as the old vectors e_i+e_{n+1-i} (and the
    # middle e_{(n+1)/2} for n odd) via a lower-triangular change of basis.
    for k in 1:div(n+1, 2)
      v = zero_matrix(ZZ, 1, n)
      for j in k:(n+1-k)
        v[1, j] = 1
      end
      push!(invs, v)
    end
  elseif s == :D
    @assert n>=4
    if n == 4
      # The D_4 fixed subspace has restricted Gram matrix of type G_2
      # in the basis a = e_1 + e_2 + e_4, b = e_3. Hence a and a + 2b
      # are orthogonal and span the same invariant subspace.
      v1 = zero_matrix(ZZ, 1, n)
      v1[1, 1] = 1
      v1[1, 2] = 1
      v1[1, 4] = 1
      push!(invs, v1)

      v2 = zero_matrix(ZZ, 1, n)
      v2[1, 1] = 1
      v2[1, 2] = 1
      v2[1, 3] = 2
      v2[1, 4] = 1
      push!(invs, v2)
    else
      # With f_1 = e_1 + e_2 and f_i = e_{i+1} for i >= 2, the restricted
      # form on the fixed subspace is the C_{n-1} Cartan form with the long
      # root first. Thus u_k = f_1 + 2f_2 + ... + 2f_k are pairwise
      # orthogonal and span the same invariant subspace.
      for i in 2:n
        v = zero_matrix(ZZ, 1, n)
        v[1, 1] = 1
        v[1, 2] = 1
        for j in 3:i
          v[1, j] = 2
        end
        push!(invs, v)
      end
    end
  elseif s == :E
    @assert 8>=n>=6
    if n == 6
      # The E_6 fixed subspace is of type F_4. In Hecke's root ordering,
      # these cumulative invariant vectors are pairwise orthogonal and span
      # the same invariant subspace as e_3, e_6, e_1+e_5, e_2+e_4.
      v1 = zero_matrix(ZZ, 1, n)
      v1[1, 1] = 1
      v1[1, 5] = 1
      push!(invs, v1)

      v2 = zero_matrix(ZZ, 1, n)
      v2[1, 1] = 1
      v2[1, 2] = 2
      v2[1, 4] = 2
      v2[1, 5] = 1
      push!(invs, v2)

      v3 = zero_matrix(ZZ, 1, n)
      v3[1, 1] = 1
      v3[1, 2] = 2
      v3[1, 3] = 3
      v3[1, 4] = 2
      v3[1, 5] = 1
      push!(invs, v3)

      v4 = zero_matrix(ZZ, 1, n)
      v4[1, 1] = 1
      v4[1, 2] = 2
      v4[1, 3] = 3
      v4[1, 4] = 2
      v4[1, 5] = 1
      v4[1, 6] = 2
      push!(invs, v4)
    elseif n == 7 || n == 8
      if n == 7
        # Root the E_7 diagram at the trivalent node 3. Along each arm we use
        # the usual A-type cumulative vectors from the leaves inward; the last
        # vector is the unique integral one orthogonal to those arm vectors.
        v1 = zero_matrix(ZZ, 1, n)
        v1[1, 1] = 1
        push!(invs, v1)

        v2 = zero_matrix(ZZ, 1, n)
        v2[1, 1] = 1
        v2[1, 2] = 2
        push!(invs, v2)

        v3 = zero_matrix(ZZ, 1, n)
        v3[1, 6] = 1
        push!(invs, v3)

        v4 = zero_matrix(ZZ, 1, n)
        v4[1, 5] = 2
        v4[1, 6] = 1
        push!(invs, v4)

        v5 = zero_matrix(ZZ, 1, n)
        v5[1, 4] = 3
        v5[1, 5] = 2
        v5[1, 6] = 1
        push!(invs, v5)

        v6 = zero_matrix(ZZ, 1, n)
        v6[1, 7] = 1
        push!(invs, v6)

        v7 = zero_matrix(ZZ, 1, n)
        v7[1, 1] = 4
        v7[1, 2] = 8
        v7[1, 3] = 12
        v7[1, 4] = 9
        v7[1, 5] = 6
        v7[1, 6] = 3
        v7[1, 7] = 6
        push!(invs, v7)
      else
        # Same construction for E_8, now with arms of lengths 2, 4, and 1.
        v1 = zero_matrix(ZZ, 1, n)
        v1[1, 1] = 1
        push!(invs, v1)

        v2 = zero_matrix(ZZ, 1, n)
        v2[1, 1] = 1
        v2[1, 2] = 2
        push!(invs, v2)

        v3 = zero_matrix(ZZ, 1, n)
        v3[1, 7] = 1
        push!(invs, v3)

        v4 = zero_matrix(ZZ, 1, n)
        v4[1, 6] = 2
        v4[1, 7] = 1
        push!(invs, v4)

        v5 = zero_matrix(ZZ, 1, n)
        v5[1, 5] = 3
        v5[1, 6] = 2
        v5[1, 7] = 1
        push!(invs, v5)

        v6 = zero_matrix(ZZ, 1, n)
        v6[1, 4] = 4
        v6[1, 5] = 3
        v6[1, 6] = 2
        v6[1, 7] = 1
        push!(invs, v6)

        v7 = zero_matrix(ZZ, 1, n)
        v7[1, 8] = 1
        push!(invs, v7)

        v8 = zero_matrix(ZZ, 1, n)
        v8[1, 1] = 10
        v8[1, 2] = 20
        v8[1, 3] = 30
        v8[1, 4] = 24
        v8[1, 5] = 18
        v8[1, 6] = 12
        v8[1, 7] = 6
        v8[1, 8] = 15
        push!(invs, v8)
      end
    end
  elseif s == :I
    v = zero_matrix(ZZ, 1, n)
    v[1, 1] = 1
    push!(invs, v)
  else
    error("invalid root system")
  end
  return invs
end


function _anti_invariant_vectors(s::Symbol, n::IntegerUnion)
  invs = ZZMatrix[]
  if s == :A
    # Write w_j = e_j - e_{n+1-j}. The anti-invariant subspace is spanned by
    # these w_j, and the cumulative weighted sums below give an orthogonal
    # basis of the same subspace without using Gram-Schmidt.
    m = div(n, 2)
    if iseven(n)
      for k in 1:m
        v = zero_matrix(ZZ, 1, n)
        for j in k:m
          c = n + 1 - 2 * j
          v[1, j] = c
          v[1, n + 1 - j] = -c
        end
        push!(invs, v)
      end
    else
      for k in 1:m
        v = zero_matrix(ZZ, 1, n)
        for j in k:m
          c = div(n + 1, 2) - j
          v[1, j] = c
          v[1, n + 1 - j] = -c
        end
        push!(invs, v)
      end
    end
  elseif s == :D
    @assert n>=4
    if n == 4
      # For D_4 this is the non-trivial 2-dimensional irreducible summand.
      # In the basis a = e_1 - e_2, b = e_2 - e_4 the restricted form is the
      # A_2 Cartan form scaled by 2, so a and a + 2b are orthogonal.
      v = zero_matrix(ZZ, 2, n)
      v[1, 1] = 1
      v[1, 2] = -1
      v[2, 1] = 1
      v[2, 2] = 1
      v[2, 4] = -2
      push!(invs, v)
    else
      v = zero_matrix(ZZ, 1, n)
      v[1, 1] = 1
      v[1, 2] = -1
      push!(invs, v)
    end
  elseif s == :E
    @assert 8>=n>=6
    if n == 6
      # The E_6 anti-invariant subspace is 2-dimensional with the same
      # restricted form as in the D_4 case above.
      v1 = zero_matrix(ZZ, 1, n)
      v1[1, 1] = 1
      v1[1, 5] = -1
      push!(invs, v1)

      v2 = zero_matrix(ZZ, 1, n)
      v2[1, 1] = 1
      v2[1, 2] = 2
      v2[1, 4] = -2
      v2[1, 5] = -1
      push!(invs, v2)
    elseif n == 7 || n == 8
      # there are no anti-invariant vectors for E7 and E8
    end
  elseif s == :I
    # there are no anti-invariant vectors for I
  else
    error("invalid root system")
  end
  return invs
end


function improve_basis(L::ZZLat, j=1)
  #@assert is_strongly_well_rounded(L::ZZLat)
  G = gram_matrix(L)
  d = abs.(diagonal(G))
  m = minimum(d)
  i = findfirst(>(m), d[j:end])
  if i isa Nothing
    return false, L
  end
  i = i+j-1
  n = rank(L)
  E = identity_matrix(ZZ,n)
  found = false
  for v in shortest_vectors(L)
    if isone(abs(v[i]))
      E[i,i]=0
      for j in 1:n
        E[i,j] = v[j]
      end
      found = true
      break
    end
  end
  if !found && i<=rank(L)
    return improve_basis(L, i+1)
  end
  return found, lattice_in_same_ambient_space(L, E*basis_matrix(L))
end


# AI slop
"""
    _orbit_representatives(G::Vector{ZZMatrix}, v::Vector{Vector{ZZRingElem}})

Compute one representative of each orbit of the vectors in v under the right action of the group generated by G.

This is just a toy implementation for really small `v`.

# Arguments
- `G::Vector{ZZMatrix}`: Generator matrices for the group (invertible square matrices)
- `v::Vector{Vector{ZZRingElem}}`: A collection of vector whose orbits are to be partitioned; The collection must be closed under the action of ``G``.

# Returns
A vector containing one representative from each orbit.
"""
function _orbit_representatives(G::Vector{ZZMatrix}, v::Vector{S}) where {S<: Union{Vector{ZZRingElem},ZZMatrix}}
  visited = Set{S}()
  result = Vector{S}()
  isempty(v) && return v
  tmp = first(v)
  for vec in v
    if vec ∉ visited
      # Start new orbit with this unvisited vector
      queue = [vec]
      push!(visited, vec)

      # BFS to explore orbit
      idx = 1
      while idx <= length(queue)
          current_vec = queue[idx]
          idx += 1

        # Apply each generator to the current vector (right action)
        for matrix in G
          image = mul!(tmp,current_vec , matrix)
          if image ∉ visited
            image = deepcopy(image)
            push!(visited, image)
            push!(queue, image)
          end
        end
      end

      # Add one representative
      push!(result, first(queue))
    end
  end

  return result
end
