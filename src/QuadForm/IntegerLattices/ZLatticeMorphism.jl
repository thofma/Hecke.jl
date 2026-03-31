################################################################################
#
#  Automorphism groups
#
################################################################################

function _norm_one_sublattice_automorphism_group(L::ZZLat, sv::Vector)
  M = matrix(ZZ, first.(sv))
  # TODO: avoid the rational_span?
  V = rational_span(L)
  S = lattice(V, M; isbasis = true, check = false)
  s = rank(S)
  T = orthogonal_submodule(lattice(V), S)
  gensOS = [diagonal_matrix(ZZ, append!([-1], (1 for _ in 1:s-1)))] # diag(-1,1,...,1)
  for g in gens(SymmetricGroup(s))
    push!(gensOS, identity_matrix(ZZ, s) * g) # generators of S_n
  end
  orderOS = ZZ(2)^s * factorial(ZZ(s))
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
  depth::Int=-1,
  bacher_depth::Int=0,
  use_weyl::Bool=true,
  use_projections::Bool=true,
  use_norm_one::Bool=true,
  use_everything::Bool=false,
  compress::Bool=true,
  search_new_invariant_vectors::Bool=true,
  use_target_enum::Bool=true
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

  if use_everything
    use_weyl = true
    use_projections = true
    use_target_enum = true
    use_norm_one = true
    compress = true
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
  vector_set = []
  # Split off norm 1 vectors
  if use_norm_one && (sv = short_vectors(L, 0, Int(1)); length(sv) > 0)
    S, T, gensOS, orderOS = _norm_one_sublattice_automorphism_group(L, sv)
    __assert_has_automorphisms(T; redo, try_small, depth, bacher_depth, use_weyl, use_projections, use_norm_one=false, search_new_invariant_vectors, compress, use_target_enum)
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

  res = ZZMatrix[GL]
  is_lll = get_attribute(L, :is_lll_reduced, false)
  use_lll = false #!is_lll && !use_everything
  if use_lll
    # Make the Gram matrix small
    Glll, T = lll_gram_with_transform(res[1])
    _L = integer_lattice(gram=Glll; cached=false)
    Ttr = transpose(T)
    res = [Glll]
    #res = ZZMatrix[T*g*Ttr for g in res]
  end

  if maximum(abs.(gram_matrix(_L)))>ZZ(2)^62
    # temporary fix TODO to it in _short_vectors_with_condition
    use_target_enum = false
  end
  if use_weyl && use_projections && use_target_enum
    root_types, fundamental_roots = _root_lattice_recognition_fundamental(_L)
    weyl_group_gens, grams, weyl_group_order, (proj_root_inv, proj_root_coinv) = _weyl_group(_L, root_types, fundamental_roots)
    if length(grams) > 0
      gram_weyl_vector = grams[end]
    else
      gram_weyl_vector = nothing
    end
    proj, target_proj_root_inv, target_norms, denoms, grams = _short_vectors_with_condition_preprocessing(_L, root_types, fundamental_roots, grams, proj_root_inv, proj_root_coinv) #updates grams
    V, grams = _short_vectors_with_condition(Int, _L, proj, target_proj_root_inv, target_norms, denoms, grams; search_new_invariant_vectors)  # updates grams
    if get_assertion_level(:Lattice) > 1
      for (v, n) in V
        @assert all(dot(v * grams[i], v) == n[i] for i in 1:length(grams))
      end
    end
    append!(res, grams)
    vector_set = [(v, vcat([Int(inner_product(_L, v, v))], n)) for (v, n) in V]
    if get_assertion_level(:Lattice) > 1
      for (v, n) in vector_set
        @assert all(dot(v * res[i], v) == n[i] for i in 1:length(res))
      end
    end
    @assert length(res) == length(vector_set[1][2])
    use_projections = false # already added projections
  elseif use_weyl
    weyl_group_gens, weyl_gram_matrices, weyl_group_order,_ = _weyl_group(_L)
    if length(weyl_gram_matrices) > 0
      gram_weyl_vector = weyl_gram_matrices[end]
    else
      gram_weyl_vector = nothing
    end
    append!(res, weyl_gram_matrices)
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

  # if any(is_zero, res)
  #   @info "something is zero"
  # end

  if compress && length(res) > 1 # nothing to compress if there is only a single gram
    # res = [G_1,...,G_r]
    # G_1 is the Gram matrix of the lattice
    # G_{i0} is the Gram matrix corresponding to the Weyl vector
    # replace G_2,...,G_r by a_1 G_2 + ... + a_{r-1}G_r
    # but we must make sure that a_{i0 - 1} is large enough

    if use_weyl && gram_weyl_vector !== nothing
      index_gram_weyl_in_res = findfirst(==(gram_weyl_vector::ZZMatrix), res)
      res, vector_set = _compress_gram_matrices(res, vector_set, index_gram_weyl_in_res)
    else
      res, vector_set = _compress_gram_matrices(res, vector_set)
    end
  end
  if get_assertion_level(:Lattice) > 1
    for (v, n) in vector_set
      @assert all(dot(v * res[i], v) == n[i] for i in 1:length(res))
    end
  end

  known_short_vectors = (0, []) #
  C = ZLatAutoCtx(res)
  fl = false
  if try_small
    fl, Csmall = try_init_small(C; depth, bacher_depth, is_lll_reduced_known=true, vector_set, force=false)
    #@assert fl
    if fl
      _gens, order = auto(Csmall)
      gens = ZZMatrix[matrix(ZZ, g) for g in _gens]
    end
    !fl && @vprintln :Lattice 1 "Try init small failed; switching to large"
  end
  if !try_small || !fl
    init(C; depth, bacher_depth, known_short_vectors, is_lll_reduced_known=true)
    gens, order = auto(C)
  end

  if use_weyl
    reduced_gens = copy(gens)
    append!(gens, [ZZ.(i) for i in weyl_group_gens])
  end

  # Now translate back
  if use_lll
    Tinv = inv(T)
    for i in 1:length(gens)
      gens[i] = Tinv * gens[i] * T
    end

    if use_weyl # translate reduced generators back
      for i in 1:length(gens)
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
      order_reduced = divexact(order, 2)  # the order of Aut(L, \rho)
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
  return nothing
end

function _compress_gram_matrices(res::Vector{ZZMatrix}, vector_set::Vector, faithful = nothing)
  if length(res) <= 2
    return res, vector_set
  end
  r = nrows(res[1])
  if faithful === nothing # we just compress res[2],...,r[end]
    res_to_compress = @view res[2:end]
    l = length(res_to_compress)
    a = rand(-10:10, l)
    anbits = maximum(nbits, a)
    rnbits = nbits(r)
    maxnbitsbound = 8 * sizeof(Int) - anbits - rnbits - 2 # -2 for good measure
    for (i, (v, n)) in enumerate(vector_set)
      w = n[2:end]
      wnbits = maximum(nbits, w)
      @assert wnbits < maxnbitsbound
      resize!(n, 2)
      n[2] = dot(a, w)
    end
    Gcompressed = sum(a[i]*res_to_compress[i] for i in 1:l)
    res = [res[1], Gcompressed]
    return res, vector_set
  end

  i0 = faithful::Int #
  keep_faithful = false # we might find out that we cannot compress res[i0]

  l = length(res)
  grambound = ZZ(0)
  a = rand(-10:10, l) # we will only use a[2],...,a[l], but for indexing reasoons we make it larger
  for i in 2:l
    if i == i0
      continue
    end
    grambound += abs(a[i]) * sum(abs, res[i])
  end
  Sbound = maximum(i -> maximum(abs, i[2]), vector_set) # a bit crude, since we take all components
  _lambda = 8 * ZZ(Sbound)^2 * grambound + 1
  # TODO: once we hit this assertion, we need to
  # (a) sharpen the bound (2-norms); or
  # (b) pass to ZZ instead of Int (probably not a good idea); or
  # (c) try to compress fewer matrices
  if fits(Int, _lambda)
    a[i0] = Int(_lambda)
    # cannot compress all gram matrices, so keep weyl one separate
  else
    a[i0] = 0
    keep_faithful = true
  end

  anbits = maximum(nbits, a)
  rnbits = nbits(r)

  if !keep_faithful
    # have to check whether the new norms fit into Int
    maxnbitsbound = 8 * sizeof(Int) - anbits - rnbits - 1 # -1 for good measure
    for (i, (v, n)) in enumerate(vector_set)
      w = n[2:end]
      wnbits = maximum(nbits, w)
      if wnbits > maxnbitsbound
        # norm is getting too large, abort
        keep_faithful = true
        break
      end
    end
  end

  aI = a[2:end]
  if !keep_faithful
    # now compress
    @assert a[i0] != 0
    Gcompressed = sum(a[i]*res[i] for i in 2:l)
    res = [res[1], Gcompressed]
    for (i, (v, n)) in enumerate(vector_set)
      w = n[2:end]
      wnbits = maximum(nbits, w)
      resize!(n, 2)
      n[2] = dot(aI, w)
    end
    return res, vector_set
  end

  # can't compress in a way that preserves the additonal gram matrix

  if length(res) == 3
    return res, vector_set
  end

  Gcompressed = sum(a[i]*res[i] for i in 2:l if i != i0)
  I = [i for i in 2:l if i != i0]
  aI = a[I]
  res = [res[1], res[i0], Gcompressed]
  for (i, (v, n)) in enumerate(vector_set)
    w = n[I]
    wnbits = maximum(nbits, w)
    n[2] = n[i0]
    resize!(n, 3)
    n[3] = dot(aI, w)
  end
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
  @req is_definite(L) "The lattice must be definite"
   # overwrite use_weyl keyword, to compute the reduced information
  assert_has_automorphisms(L; kwargs..., use_weyl = true)
  return L.reduced_automorphism_group_order
end


# Helpers to find additional structure in the lattice

function _invariant_projections_and_sublattices(L::ZZLat)
  # the first condition is a safeguard from a flint convention for isone
  if rank(L) != degree(L) || !isone(basis_matrix(L))
    L = lattice(rational_span(L))
  end
  LL, _ = _short_vector_generators_with_sublattice_2(L; up_to_sign=true)
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

function __is_isometric_with_isometry_definite(L::ZZLat, M::ZZLat; depth::Int = -1, bacher_depth::Int = 0)
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
  GLint = divexact(GLint, cL)

  GM = gram_matrix(M)
  dM = denominator(GM)
  GMint = change_base_ring(ZZ, s * dM * GM)
  cM = content(GMint)
  GMint = divexact(GMint, cM)

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

  fl, CLsmall, CMsmall = _try_iso_setup_small(G1, G2, depth = depth, bacher_depth = bacher_depth)
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
      norm_gen = _norm_generator(normalL1, p) * inv(TL1) * basis_matrix(L1)
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
  if !isone(basis_matrix(L)) || rank(L) != degree(L)
    L = lattice(rational_span(L))
  end
  if length(root_types) == 0
    to_fix = zero_matrix(QQ, rank(L), rank(L))
    to_cofix = QQMatrix[] #[zero_matrix(QQ, rank(L), rank(L))]
    return ZZMatrix[], ZZMatrix[], ZZ(1), [to_fix, to_cofix]
  end
  invariant_grams = ZZMatrix[]
  invariant_vectors = ZZMatrix[]
  isotypical_coinvariant_projections = QQMatrix[]
  for t in Set(root_types)
    inv_vec = _invariant_vectors(t...)
    k = length(inv_vec)
    V = [zero_matrix(ZZ, 1, rank(L)) for i in 1:k]
    isotypic = zero_matrix(ZZ,0, rank(L))
    for i in 1:length(root_types)
      if root_types[i] == t
        V = V + [v*fundamental_roots[i] for v in inv_vec]
        isotypic = vcat(isotypic, fundamental_roots[i])  # how to do that allocation free?
      end
    end
    isotypic_lattice = lattice_in_same_ambient_space(L, isotypic)
    isotypic_cofix_lattice = basis_matrix(orthogonal_submodule(isotypic_lattice, QQ.(reduce(vcat,V))))
    to_isotypic_cofix = 1 - matrix(orthogonal_projection(ambient_space(L), isotypic_cofix_lattice))
    if !iszero(to_isotypic_cofix)
      push!(isotypical_coinvariant_projections, to_isotypic_cofix)
    end
    append!(invariant_vectors, V)
  end
  gramZ = ZZ.(gram_matrix(L))
  for v in invariant_vectors
    x = v*gramZ
    push!(invariant_grams, transpose(x)*x)
  end


  weyl_group_gens = ZZMatrix[]
  for roots in fundamental_roots
    for i in 1:nrows(roots)
      push!(weyl_group_gens, _reflection(gramZ, view(roots, i:i, :)))
    end
  end

  ord = one(ZZ)
  for s in root_types
    mul!(ord, _weyl_group_order(s...))
  end
  # inefficient
  amb = ambient_space(L)
  root_lat = lattice(amb, QQ.(reduce(vcat,fundamental_roots)))
  # in principle not needed because in the linear span of the invariant vectors.
  # but it can still help because it governs some signs
  rho = _weyl_vector(root_lat)
  gram_rho = ZZ.(4*transpose(rho*gramZ)*(rho*gramZ))
  push!(invariant_grams, gram_rho)

  fixed_lattice = QQ.(reduce(vcat, invariant_vectors))
  cofix_lattice = basis_matrix(orthogonal_submodule(root_lat, fixed_lattice))
  to_fix = 1 - matrix(orthogonal_projection(amb, fixed_lattice))
  #to_cofix = 1 - matrix(orthogonal_projection(amb, cofix_lattice))
  @hassert :Lattice 1 rank(to_fix+sum(isotypical_coinvariant_projections; init=zero_matrix(QQ,n,n)))==rank(root_lat)

  return weyl_group_gens, invariant_grams, ord, [to_fix,isotypical_coinvariant_projections]
end

function _invariant_vectors(s::Symbol, n::IntegerUnion)
  E = identity_matrix(ZZ, n)
  invs = ZZMatrix[]
  e(n) = E[n:n,:]
  if s == :A
    for i in 1:div(n,2)
      push!(invs, e(i)+e(n+1-i))
    end
    if !iszero(n%2)
      push!(invs, e(div(n+1,2)))
    end
  elseif s == :D
    @assert n>=4
    if n == 4
      push!(invs, e(1) + e(2) + e(4))
      push!(invs, e(3))
    else
      for i in 3:n
        push!(invs, e(i))
      end
      push!(invs, e(1)+e(2))
    end
  elseif s == :E
    @assert 8>=n>=6
    if n == 6
      for i in [3,6]
        push!(invs, e(i))
      end
      push!(invs, e(1) + e(5))
      push!(invs, e(2) + e(4))
    elseif n == 7 || n == 8
      for i in 1:n
        push!(invs, e(i))
      end
    end
  elseif s == :I
    push!(invs, e(1))
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
