export represents

################################################################################
#
#  Type from field
#
################################################################################

quadratic_space_type(K::S) where {S <: Field} =
    QuadSpace{S, dense_matrix_type(elem_type(S))}

################################################################################
#
#  Constructors
#
################################################################################

@doc raw"""
    quadratic_space(K::NumField, n::Int; cached::Bool = true) -> QuadSpace

Create the quadratic space over `K` with dimension `n` and Gram matrix
equals to the identity matrix.
"""
function quadratic_space(K::Field, n::Int; cached::Bool = true)
  @req n >= 0 "Dimension ($n) must be non negative"
  G = identity_matrix(K, n)
  return quadratic_space(K, G, cached = cached)
end

@doc raw"""
    quadratic_space(K::NumField, G::MatElem; cached::Bool = true) -> QuadSpace

Create the quadratic space over `K` with Gram matrix `G`.
The matrix `G` must be square and symmetric.
"""
function quadratic_space(K::Field, G::MatElem; check::Bool = true, cached::Bool = true)
  if check
    @req is_square(G) "Gram matrix must be square ($(nrows(G)) x $(ncols(G))"
    @req is_symmetric(G) "Gram matrix must be symmetric"
    @req (K isa NumField || K isa QQField)  "K must be a number field"
  end
  local Gc::dense_matrix_type(elem_type(K))
  if dense_matrix_type(elem_type(K)) === typeof(G)
    Gc = G
  else
    try
      Gc = change_base_ring(K, G)
      if typeof(Gc) !== dense_matrix_type(elem_type(K))
        error("Cannot convert entries of the matrix to the number field")
      end
      @hassert :Lattice 1 base_ring(Gc) === K
    catch e
      if !(e isa MethodError)
        rethrow(e)
      else
        error("Cannot convert entries of the matrix to the number field")
      end
    end
  end
  return QuadSpace(K, Gc, cached)
end

function rescale(q::QuadSpace, r; cached::Bool = true)
  r = fixed_field(q)(r)
  return quadratic_space(base_ring(q), r*gram_matrix(q), check=false)
end

################################################################################
#
#  Predicates
#
################################################################################

is_quadratic(V::QuadSpace) = true

ishermitian(V::QuadSpace) = false

_base_algebra(V::QuadSpace) = V.K

################################################################################
#
#  Properties
#
################################################################################

involution(V::QuadSpace) = identity

fixed_field(V::QuadSpace) = base_ring(V)

################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, V::QuadSpace)
  print(io, "Quadratic space over\n")
  println(io, base_ring(V))
  println(io, "with Gram matrix")
  print(io, gram_matrix(V))
end

################################################################################
#
#  Inner product
#
################################################################################

@inline _temp1(V::QuadSpace{S, T}) where {S, T} = V.temp1::Vector{elem_type(S)}

@inline _temp2(V::QuadSpace{S, T}) where {S, T} = V.temp2::elem_type(S)

# Internal version
function _inner_product!(res, V, v::Vector, w::Vector, temp1 = deepcopy(v),
                                                       temp2 = base_ring(V)())
  mul!(temp1, v, V)
  zero!(res)
  for i in 1:length(v)
    addmul!(res, temp1[i], w[i], temp2)
  end
  return res
end

function inner_product(V::QuadSpace, v::Vector, w::Vector)
  return inner_product!(base_ring(V)(), V, v, w)
end

function inner_product!(r, V::QuadSpace, v::Vector, w::Vector)
  return _inner_product!(r, gram_matrix(V), v, w, _temp1(V), _temp2(V))
end

function inner_product(V::QuadSpace{S,T}, v::T, w::T) where {S,T}
  G = gram_matrix(V)
  n = nrows(G)
  @req ncols(v) == n && n == ncols(w) "Dimension mismatch"
  if nrows(v) == ncols(G) && is_square(w)
    # v, w, G have same dimension
    # we allocate one matrix, which will also store the result
    z = deepcopy(w)
    z = transpose!(z, w)
    mul!(z, G, z)
    mul!(z, v, z)
    return z
  end
  return v * G * transpose(w)
end

function inner_product(V::QuadSpace{S,T}, v::T) where {S,T}
  G = gram_matrix(V)
  if nrows(v) == ncols(G)
    # v, w, G have same dimension
    z = deepcopy(v)
    z = transpose!(z, v)
    mul!(z, G, z)
    mul!(z, v, z)
    return z
  end
  return v * G * transpose(v)
end

################################################################################
#
#  Diagonalization
#
################################################################################

function diagonal(V::QuadSpace)
  g = gram_matrix(V)
  k, K = left_kernel(g)
  B = complete_to_basis(K)
  g = B[k+1:end,:]*g*transpose(B[k+1:end,:])
  D, _ = _gram_schmidt(g, involution(V))
  return append!(zeros(base_ring(V),k),diagonal(D))
end

################################################################################
#
#  Hasse and Witt invariant
#
################################################################################

# Auxiliary function which works with a diagonal
function _hasse_invariant(D::Vector, p)
  h = 1
  n = length(D)
  for i in 1:n
    for j in (i + 1):n
      h = h * hilbert_symbol(D[i], D[j], p)
    end
  end
  return h
end

@doc raw"""
    hasse_invariant(V::QuadSpace, p::Union{InfPlc, NfOrdIdl}) -> Int

Returns the Hasse invariant of the quadratic space `V` at `p`. This is equal
to the product of local Hilbert symbols $(a_i, a_j)_p$, $i < j$, where $V$ is
isometric to $\langle a_1, \dotsc, a_n\rangle$.
If `V` is degenerate return the hasse invariant of `V/radical(V)`.
"""
function hasse_invariant(V::QuadSpace, p)
  return _hasse_invariant([d for d in diagonal(V) if d!=0], p)
end

# This can be refactored to operate on the diagonal of a gram schmidt basis and
# the gram matrix.
# (Probably only on the diagonal of a gram schmidt basis)
function witt_invariant(L::QuadSpace, p)
  K = base_ring(L)
  h = hasse_invariant(L, p)
  n = dim(L) - dim_radical(L)
  d = det_ndeg(L)
  return _hasse_witt(K, h, n, d, p)
end

function det_ndeg(L::QuadSpace)
  D = diagonal(L)
  K = base_ring(L)
  return prod(K, [d for d in D if d!=0])
end

function dim_radical(L::QuadSpace)
  D = diagonal(L)
  return count([d==0 for d in D])
end

function _hasse_witt(K, h, n, d, p)
  n = mod(n, 8)
  if n == 3 || n == 4
    c = -d
  elseif n == 5 || n == 6
    c = K(-1)
  elseif n == 7 || n == 0
    c = d
  else
    c = K(1)
  end
  return h * hilbert_symbol(K(-1), c, p)
end

# di = determinant
# wi = witt invariant
# ni = rank
# Lam p. 117
function _witt_of_direct_sum(d1, w1, n1, d2, w2, n2, p)
  _n1 = mod(n1, 4)
  if _n1 == 0 || _n1 == 1
    disc1 = d1
  else
    disc1 = -d1
  end

  _n2 = mod(n2, 4)
  if _n2 == 0 || _n2 == 1
    disc2 = d2
  else
    disc2 = -d2
  end

  if mod(n1, 2) == mod(n2, 2)
    w3 = w1 * w2 * hilbert_symbol(disc1, disc2, p)
  elseif mod(n1, 2) == 1
    w3 = w1 * w2 * hilbert_symbol(-disc1, disc2, p)
  else
    @hassert :Lattice 1 mod(n2, 2) == 1
    w3 = w1 * w2 * hilbert_symbol(disc1, -disc2, p)
  end
  return d1 * d2, w3, n1 + n2
end

# n = rank, d = det
function _witt_hasse(s, n, d, p)
  nmod8 = mod(n, 8)
  K = parent(d)
  if nmod8 == 3 || nmod8 == 4
    c = -d
  elseif nmod8 == 5 || nmod8 == 6
    c = K(-1)
  elseif nmod8 == 7 || nmod8 == 0
    c = d
  else
    c = K(1)
  end
  return s * hilbert_symbol(K(-1), c, p)
end

function witt_invariant(L::QuadSpace, p::InfPlc)
  if is_complex(p)
    return 1
  end

  h = hasse_invariant(L, p)
  dett = det(L)
  K = base_ring(L)
  n = mod(dim(L), 8)
  if n == 3 || n == 4
    c = -dett
  elseif n == 5 || n == 6
    c = K(-1)
  elseif n == 7 || n == 0
    c = dett
  else
    c = K(1)
  end
  @hassert :Lattice 1 !iszero(c)
  if is_negative(c, p)
    return -h
  else
    return h
  end
end

@doc raw"""
    witt_invariant(V::QuadSpace, p::Union{InfPlc, NfOrdIdl}) -> Int

Returns the Witt invariant of the quadratic space `V` at `p`.

See [Definition 3.2.1, Kir16].
"""
witt_invariant(V::QuadSpace, p)

################################################################################
#
#  Local isometry
#
################################################################################

function is_isometric(L::QuadSpace, M::QuadSpace, p)
  GL = gram_matrix(L)
  GM = gram_matrix(M)
  if GL == GM
    return true
  end

  return rank(GL) == rank(GM) &&
         is_local_square(det(GL) * det(GM), p) &&
         hasse_invariant(L, p) == hasse_invariant(M, p)
end

function is_isometric(L::QuadSpace, M::QuadSpace, p::InfPlc)
  if rank(L) != rank(M)
    return false
  end

  if is_complex(p)
    return true
  end

  DL = diagonal(L)
  DM = diagonal(M)

  if count(x==0 for x in DL) != count(x==0 for x in  DM)
    return false
  end
  return count(x -> is_negative(x, p), DL) == count(x -> is_negative(x, p), DM)
end

################################################################################
#
#  Quadratic form with given invariants
#
################################################################################

function _quadratic_form_invariants(M::QQMatrix; minimal = true)
  G, _ = _gram_schmidt(M, identity)
  ker = count(d==0 for d in diagonal(G))
  D = [d for d in diagonal(G) if d!=0]
  sup = ZZRingElem[]
  for i in 1:length(D)
    for (p, e) in factor(numerator(D[i]))
      if isodd(e)
        push!(sup, p)
      end
    end
    for (p, e) in factor(denominator(D[i]))
      if isodd(e)
        push!(sup, p)
      end
    end
  end
  push!(sup, ZZRingElem(2))
  sup = unique!(sup)
  F = Dict{ZZRingElem, Int}()
  for p in sup
    e = _hasse_invariant(D, p)
    if e == -1 | !minimal
      F[p] = e
    end
  end
  I = [ (inf, count(x -> x < 0, D)) ]
  nu = numerator(prod(D))
  de = denominator(prod(D))
  return ncols(M), ker, squarefree_part(de * nu), F, I
end

function _quadratic_form_invariants(M; minimal = true)
  return _quadratic_form_invariants(M, maximal_order(base_ring(M)), minimal = minimal)
end

function _quadratic_form_invariants(M, O; minimal = true)
  G, _ = _gram_schmidt(M, identity)
  ker = count(d==0 for d in diagonal(G))
  D = [d for d in diagonal(G) if d!=0]

  K = base_ring(M)
  sup = Dict{ideal_type(O), Bool}()
  for i in 1:length(D)
    f = factor(D[i] * O)
    for (P, e) in f
      if isodd(e)
        sup[P] = true
      end
    end
  end
  for (P, e) in prime_decomposition(O, 2)
    sup[P] = true
  end
  F = Dict{ideal_type(O), Int}()
  for P in keys(sup)
    e = _hasse_invariant(D, P)
    if e == -1 || !minimal
      F[P] = e
    end
  end
  I = [ (P, count(x -> is_negative(x, P), D)) for P in real_places(K) ];
  return ncols(M), ker, reduce(*, D, init = one(K)), F, I
end

@doc raw"""
    invariants(M::QuadSpace)
          -> FieldElem, Dict{NfOrdIdl, Int}, Vector{Tuple{InfPlc, Int}}

Returns a tuple `(n, k, d, H, I)` of invariants of `M`, which determine the
isometry class completely. Here `n` is the dimension. The dimension of the kernel
is `k`. The element `d` is the determinant of a Gram matrix of the non-degenerate part,
`H` contains the non-trivial Hasse invariants
and `I` contains for each real place the negative index of inertia.

Note that `d` is determined only modulo squares.
"""
invariants(V::QuadSpace) = _quadratic_form_invariants(gram_matrix(V))

################################################################################
#
#  Global isometry
#
################################################################################

function is_isometric(M::QuadSpace, L::QuadSpace)
  if gram_matrix(M) == gram_matrix(L)
    return true
  end
  n1, k1, d1, H1, I1 = invariants(M)
  n2, k2, d2, H2, I2 = invariants(L)
  return n1==n2 && k1==k2 && I1 == I2 && H1 == H2 && is_square(d1 * d2)[1]
end

################################################################################
#
#  Quadratic form with given invariants
#
################################################################################

# The following is over Q
function _quadratic_form_with_invariants(dim::Int, det::ZZRingElem,
                                         finite::Vector{ZZRingElem}, negative::Int)
#{Computes a quadratic form of dimension Dim and determinant Det that has Hasse invariants -1 at the primes in Finite.
 #The number of negative entries of the real signature is given in Negative}
  @hassert :Lattice 1 dim >= 1
  @hassert :Lattice 1 !iszero(det)
  @hassert :Lattice 1 negative in 0:dim

  sign(det) != (-1)^(negative % 2) && error("Real place information does not match the sign of the determinant")

  if dim == 1
    !isempty(finite) && error("Impossible Hasse invariants")
    return matrix(FlintQQ, 1, 1, ZZRingElem[det])
  end

  finite = unique(finite)
  @hassert :Lattice 1 all(is_prime(p) for p in finite)

  if dim == 2
    ok = all(Bool[!is_local_square(-det, p) for p in finite])

    if !ok
      #q = ZZRingElem[p for p in finite if is_local_square(-det, p)][1]
      if is_local_square(-det, q)
        error("A binary form with determinant $det must have Hasse invariant +1 at the prime $q")
      end
    end
  end

  # product formula check

  !iseven((negative % 4 >= 2 ? 1 : 0) + length(finite)) && error("The number of places (finite or infinite) with Hasse invariant -1 must be even")

  # reduce the number of bad primes
  det = squarefree_part(det)

  local det0::ZZRingElem
  local finite0::Vector{ZZRingElem}

  dim0 = dim
  det0 = det
  finite0 = copy(finite)
  negative0 = negative

  #// Pad with ones
  k = max(0, dim - max(3, negative))
  D = ones(Int, k)
  dim = dim - k

  local PP::Vector{ZZRingElem}

  #// Pad with minus ones
  if dim >= 4
    @hassert :Lattice 1 dim == negative
    k = dim - 3
    d = (-1)^k
    f = (k % 4 >= 2) ? Set(ZZRingElem[2]) : Set(ZZRingElem[])
    PP = append!(ZZRingElem[p for (p, e) in factor(2 * det)], finite)
    PP = unique!(PP)
    finite = ZZRingElem[ p for p in PP if hilbert_symbol(d, -det, p) * (p in f ? -1 : 1) * (p in finite ? -1 : 1) == -1]
    finite = unique!(finite)
    D = append!(D, Int[-1 for i in 1:k])
    det = isodd(k) ? -det : det
    dim = 3
    negative = 3
  end

  # ternary case
  if dim == 3
    #// The primes at which the form is anisotropic
    PP = append!(ZZRingElem[p for (p, e) in factor(2 * det)], finite)
    PP = unique!(PP)
    PP = filter!(p -> hilbert_symbol(-1, -det, p) != (p in finite ? -1 : 1), PP)
    #// Find some a such that for all p in PP: -a*Det is not a local square
    #// TODO: Find some smaller a?! The approach below is very lame.
    a = prod(ZZRingElem[det % p == 0 ? one(FlintZZ) : p for p in PP])
    if negative == 3
      a = -a
      negative = 2
    end

    PP = append!(ZZRingElem[p for (p, e) in factor(2 * det * a)], finite)
    PP = unique!(PP)
    finite = ZZRingElem[ p for p in PP if hilbert_symbol(a, -det, p) * (p in finite ? -1 : 1) == -1]
    det = squarefree_part(det * a)
    dim = 2
    push!(D, a)
  end

  #// The binary case
  a = _find_quaternion_algebra(QQFieldElem(-det)::QQFieldElem, finite::Vector{ZZRingElem}, negative == 2 ? PosInf[inf] : PosInf[])
  Drat = map(FlintQQ, D)
  Drat = append!(Drat, QQFieldElem[a, squarefree_part(FlintZZ(det * a))])

  M = diagonal_matrix(Drat)

  _, _, d, f, n = _quadratic_form_invariants(M)

  @hassert :Lattice 1 dim0 == length(Drat)
  @hassert :Lattice 1 d == det0
  @hassert :Lattice 1 issetequal(collect(keys(f)), finite0)
  @hassert :Lattice 1 n[1][2] == negative0
  return M
end

function _quadratic_form_with_invariants(dim::Int, det::QQFieldElem,
                                         finite::Vector{ZZRingElem}, negative::Int)
  _det = numerator(det) * denominator(det)
  return _quadratic_form_with_invariants(dim, _det, finite, negative)
end

#{Computes a quadratic form of dimension Dim and determinant Det that has Hasse invariants -1 at the primes in Finite.
# The number of negative entries of the i-th real signature is given in Negative[i]}
function _quadratic_form_with_invariants(dim::Int, det::nf_elem, finite::Vector, negative::Dict{<:InfPlc, Int})
  @hassert :Lattice 1 dim >= 1
  @hassert :Lattice 1 !iszero(det)
  K::AnticNumberField = parent(det)
  inf_plcs = real_places(K)
  @hassert :Lattice 1 length(inf_plcs) == length(negative)
  # All real places must be present
  @hassert :Lattice 1 all(Bool[0 <= c <= dim for (_, c) in negative])
  # Impossible negative entry at plc
  @hassert :Lattice 1 all(Bool[sign(det, p) == (-1)^(negative[p]) for p in inf_plcs])
  # Information at the real place plc does not match the sign of the determinant

  if dim == 1
    @hassert :Lattice 1 isempty(finite) # Impossible Hasse invariants
    return matrix(K, 1, 1, nf_elem[det])
  end

  local OK::order_type(K)

  if !isempty(finite)
    OK = order(finite[1])::order_type(K)
    @hassert :Lattice 1 is_maximal(OK)
  else
    OK = maximal_order(K)::order_type(K)
  end

  finite = unique(finite)

  # Finite places check

  if dim == 2
    ok = all(Bool[!is_local_square(-det, p) for p in finite])
    if !ok
      q = eltype(finite)[p for p in finite if is_local_square(-det, p)][1]
      error("A binary form with determinant $det must have Hasse invariant +1 at the prime $q")
    end
  end

  @hassert :Lattice 1 iseven(length(InfPlc[ p for (p, n) in negative if n % 4 >= 2]) + length(finite))
 #   "The number of places (finite or infinite) with Hasse invariant -1 must be even";

 # // OK, a space with these invariants must exist.
 # // For final testing, we store the invariants.

  dim0 = dim
  det0 = det
  finite0 = copy(finite)
  finite = copy(finite)
  negative = copy(negative)
  negative0 = copy(negative)

  # det = _reduce_modulo_squares(det)

  valneg = collect(values(negative))
  push!(valneg, 3)
  k = max(0, dim - maximum(valneg))
  D = elem_type(K)[one(K) for i in 1:k]
  dim = dim - k
  local D2::Vector{nf_elem}
  local D::Vector{nf_elem}
  if dim >= 4
    D0, dim, det, finite, negative = _quadratic_space_dim_big(dim, det, negative, finite, K, OK)
    append!(D,D0)
  end
#  // The ternary case
  if dim == 3
    PP = append!(support(K(2), OK), finite)
    append!(PP, support(det, OK))
    PP = unique!(PP)
    PP = ideal_type(OK)[p for p in PP if hilbert_symbol(K(-1), -det, p) != (p in finite ? -1 : 1)]
#    // The primes at which the form is anisotropic

#    // Find some a such that for all p in PP: -a*Det is not a local square
#    // TODO: Find some smaller a?! The approach below is very lame.
#    // We simply make sure that a*Det has valuation 1 at each prime in PP....

    if length(PP) == 0
      a = one(K)
    else
      a = approximate(Int[(1 + valuation(det, p)) % 2 for p in PP], PP)
    end
#    // Fix the signs of a if necessary.
    s = signs(a)
    idx = InfPlc[ p for (p, n) in negative if n in [0, 3]]
    S = Int[ negative[p] == 0 ? s[_embedding(p)] : -s[_embedding(p)] for p in idx]
    if length(PP) > 0
      b = _weak_approximation_coprime(idx, S, prod(PP))
      @hassert :Lattice 1 is_coprime(b * OK, prod(PP))
    else
      b = _weak_approximation_coprime(idx, S, 1 * OK)
    end
    a = a * b

#    // Adjust invariants for the last time:
    s = signs(a)
    for p in InfPlc[p for (p,c) in negative if s[_embedding(p)] < 0]
      negative[p] = negative[p] - 1
    end
    PP = support(K(2))
    append!(PP, support(det, OK))
    append!(PP, support(a, OK))
    append!(PP, finite)
    PP = unique!(PP)
    finite = ideal_type(OK)[p for p in PP if hilbert_symbol(a, -det, p) * (p in finite ? -1 : 1) == -1]
    det = det * a
    # TODO: reduce det
    push!(D, a)
  end


#  // The binary case
  a = _find_quaternion_algebra(-det::nf_elem, finite::Vector{NfOrdIdl}, InfPlc[p for (p, n) in negative if n == 2])
  push!(D, a)
  push!(D, det * a)
  M = diagonal_matrix(D)

  _,_,d, f, n = _quadratic_form_invariants(M, OK)

  @hassert :Lattice 1 dim0 == length(D)
  @hassert :Lattice 1 is_square(d * det0)[1]
  @hassert :Lattice 1 issetequal(collect(keys(f)), finite0)
  @hassert :Lattice 1 issetequal(n, collect((p, n) for (p, n) in negative0))

  return M
end


function _quadratic_space_dim_big(dim, det, negative, finite, K, OK)
  #    // Pad with minus ones
  k = min(dim - 3, minimum(values(negative)))
  D2 = elem_type(K)[-one(K) for i in 1:k]
  dim = dim - k
  for (p, n) in negative
    negative[p] = n - k
  end
  #    // Pad with other entries
  while dim >= 4
    V = InfPlc[]
    _signs = Int[]
    for (p, n) in negative
      if n == 0
        push!(V, p)
        push!(_signs, +1)
      elseif n == dim
        push!(V, p)
        push!(_signs, -1)
      end
    end

    x = _weak_approximation(V, _signs)::nf_elem
    s = signs(x)
    #@hassert :Lattice 1 all(Bool[sign(x, V[i]) == _signs[i] for i in 1:length(V)])
    let negative = negative, dim = dim
      k = minimum(vcat(Int[dim - 3], Int[s[_embedding(p)] == 1 ? (dim - c) : c for (p, c) in negative]))
    end
    D2 = append!(D2, elem_type(K)[x for i in 1:k])
    dim = dim - k
    for (p, n) in negative
      if s[_embedding(p)] == -1
        negative[p] = negative[p] - k
      end
    end
  end
  # readjust the invariants
  local _d::nf_elem
  local _f::Dict{NfAbsOrdIdl{AnticNumberField,nf_elem},Int64}
  _,_,_d, _f = _quadratic_form_invariants(diagonal_matrix(D2))

  PP = append!(support(K(2)*det, OK), finite)
  PP = append!(PP, keys(_f))
  PP::Vector{ideal_type(OK)} = unique!(PP)
  local _finite::Vector{ideal_type(OK)}
  let finite = finite
    _finite = ideal_type(OK)[ p for p in PP if hilbert_symbol(_d, -det, p) * (haskey(_f, p) ? -1 : 1) * (p in finite ? -1 : 1) == -1]::Vector{ideal_type(OK)}
  end
  finite = _finite

  det::nf_elem = det * _d
  #    # TODO: reduce det modulo squares
  return D2, dim, det, finite, negative
end

################################################################################
#
#  Isotropic
#
################################################################################

is_isotropic(V::QuadSpace, p::InfPlc) = _isisotropic(V, p)

function _isisotropic(D::Array, p)
  n = length(D)
  if n == 0
    return false
  end
  K = parent(D[1])
  d = reduce(*, D, init = one(K))
  if d == 0
    return true
  elseif n <= 1
    return false
  elseif n == 2
    return is_local_square(-d, p)
  elseif n == 3
    return _hasse_invariant(D, p) == hilbert_symbol(K(-1), -d, p)
  elseif n == 4
    return !is_local_square(d, p) || (_hasse_invariant(D, p) == hilbert_symbol(K(-1), K(-1), p))
  else
    return true
  end
end

is_isotropic(V::QuadSpace{QQField,QQMatrix}, p::Int) = is_isotropic(V, ZZ(p))
is_isotropic(V::QuadSpace{QQField,QQMatrix}, p::PosInf) = _isisotropic(diagonal(V), p)

function is_isotropic(V::QuadSpace, p)
  @hassert :Lattice 1 base_ring(V) == nf(order(p))
  d = det(V)
  n = rank(V)
  K = base_ring(V)
  if d == 0
    return true
  elseif n <= 1
    return false
  elseif n == 2
    return is_local_square(-d, p)
  elseif n == 3
    return hasse_invariant(V, p) == hilbert_symbol(K(-1), K(-1), p)
  elseif n == 4
    return !is_local_square(d, p) || (hasse_invariant(V, p) == hilbert_symbol(K(-1), K(-1), p))
  else
    return true
  end
end

################################################################################
#
#  Embeddings
#
################################################################################

# This is O'Meara, 63:21
#
# n, a, ha = dimension, determinant (class) and Hasse symbol of first space
# Similar for m, a, hb
# p is the prime ideal
function _can_locally_embed(n::Int, da, ha::Int, m::Int, db, hb::Int, p)
  de = m - n
  if de < 0
    return false
  end
  if de == 0
    return is_local_square(da * db, p) && ha == hb
  elseif de == 1
    return ha * hilbert_symbol(da * db, da, p) == hb
  elseif de == 2 && is_local_square(-da * db, p)
    # Test if U \perp H \cong V
    # H has Hasse invariant 1
    return ha * hilbert_symbol(da, -1, p) == hb
  else
    return true
  end
end

function is_locally_represented_by(U::QuadSpace, V::QuadSpace, p)
  rU = dim(U) - rank(U)
  rV = dim(V) - rank(V)
  if rU > 0 || rV > 0
    error("not implemented for degenerate spaces")
  end
  n, da, ha = rank(U), det(U), hasse_invariant(U, p)
  m, db, hb = rank(V), det(V), hasse_invariant(V, p)
  return _can_locally_embed(n, da, ha, m, db, hb, p)
end

# We are using O'Meara p. 160 ff.
#
# We need to test if U is represented by V at all places of K.
#
# If the place is complex, there is only the trivial restriction (ranks)
# If the place is real, we have to check if the signatures fit.
#
# If p does not divide 2 * dU * dV and h(U) = 1 = h(V) (Hasse-invariant),
# then U is represented by V locally at p. This follows from the local
# characterization. But the Hasse invariant is zero outside the support
# of the diagonal. Thus we get only finitely many conditions.

function is_represented_by(U::QuadSpace, V::QuadSpace)
  rU = dim(U) - rank(U)
  rV = dim(V) - rank(V)
  if rU > 0 || rV > 0
    error("not implemented for degenerate spaces")
  end

  v = rank(V) - rank(U)
  if v < 0
    return false
  end

  if v == 0
    return is_isometric(U, V)
  end

  K = base_ring(U)

  rlp = real_embeddings(K)

  dU = diagonal(U)
  dV = diagonal(V)

  rkU = rank(U)
  rkV = rank(V)

  negU = Int[ count(x -> is_negative(x, P), dU) for P in rlp ]
  signU = Tuple{Int, Int}[ (i, rkU - i) for i in negU]

  negV = Int[ count(x -> is_negative(x, P), dV) for P in rlp ]
  signV = Tuple{Int, Int}[ (i, rkV - i) for i in negV]

  for i in 1:length(rlp)
    if signU[i][1] > signV[i][1] || signU[i][2] > signV[i][2]
      return false
    end
  end

  OK = maximal_order(K)

  ds = elem_type(OK)[]

  for d in dU
    push!(ds, OK(numerator(d)))
    push!(ds, OK(denominator(d)))
  end

  for d in dV
    push!(ds, OK(numerator(d)))
    push!(ds, OK(denominator(d)))
  end

  push!(ds, OK(2))

  lp = coprime_base(ds)

  # lp is a list of coprime integral ideals, such that elements in ds factor
  # over lp. But these ideals are not necessarily prime.

  for a in lp
    for p in support(a)
      if !is_locally_represented_by(U, V, p)
        return false
      end
    end
  end

  return true
end

################################################################################
#
#  Isometry computation
#
################################################################################

function _solve_conic_affine(A, B, a)
  # Solve Au^2 + B*w^2 = a
  # Gives one solutation

  # a = u^2 + B/A v^2 = (u - sqrt(B/A)v)(u + sqrt(B/A)) = N(u + v sqrt(B/A))

  K = parent(A)

  if K isa AnticNumberField
    if degree(K) == 1
      fl, _u1, _w1 = _solve_conic_affine(coeff(A, 0), coeff(B, 0), coeff(a, 0))
      return fl, K(_u1), K(_w1)
    end
  end

  _fl, _d = is_square_with_sqrt(-B//A)

  if _fl
    # so a/A = u^2 + B/A w^2 = u^2 - (-B/A) w^2 = u^2 - _d^2 w^2 = (u - _d w) (u + _d w)
    # we solve a/A = u - _d w and 1 = v + _d w
    M = matrix(K, 2, 2, [one(K), one(K), -_d, _d])
    rhs = matrix(K, 1, 2, [a//A, one(K)])
    __fl, _w = can_solve_with_solution(M, rhs, side = :left)
    @hassert :Lattice 1 __fl
    @hassert :Lattice 1 a//A == _w[1]^2 + B//A * _w[2]^2
    u1 = _w[1]
    w1 = _w[2]
    @hassert :Lattice 1 u1^2 * A + w1^2 * B == a
  else
    Kz, z = polynomial_ring(K, "z", cached = false)
    D = -B//A
    de = denominator(D)
    L, _ = number_field(z^2 - de^2 * D)
    fl, _n = is_norm(L, a//(A) * de^2)

    if !fl
      return false, zero(K), zero(K)
    end

    if L isa AnticNumberField
      n = evaluate(_n)
    else
      n = _n
    end

    @hassert :Lattice 1 norm(n) == a//(A) * de^2

    u1, w1 = coeff(n, 0)//de, coeff(n, 1)
  end

  @hassert :Lattice 1 u1^2 * A + w1^2 * B == a

  return true, u1, w1
end

function _solve_conic_affine(A, B, a, t)
  # Solve Au^2 + B*w^2 = a
  # Gives one solutation and a parametrization
  # This assumes that a solution exists!

  # a/A = u^2 + B/A w^2 = (u + sqrt(-B/A)w)(u - sqrt(B/A)) = N(u + v sqrt(B/A))

  K = parent(A)

  _fl, _d = is_square_with_sqrt(-B//A)

  if _fl
    # so a/A = u^2 + B/A w^2 = u^2 - (-B/A) w^2 = u^2 - _d^2 w^2 = (u - _d w) (u + _d w)
    # we solve a/A = u - _d w and 1 = v + _d w
    M = matrix(K, 2, 2, [one(K), one(K), -_d, _d])
    rhs = matrix(K, 1, 2, [a//A, one(K)])
    __fl, _w = can_solve_with_solution(M, rhs, side = :left)
    @hassert :Lattice 1 __fl
    @hassert :Lattice 1 a//A == _w[1]^2 + B//A * _w[2]^2
    u1 = _w[1]
    w1 = _w[2]
    @hassert :Lattice 1 u1^2 * A + w1^2 * B == a
  else
    Kz, z = polynomial_ring(K, "z", cached = false)
    D = -B//A
    de = denominator(D)
    L, _ = number_field(z^2 - de^2 * D)
    fl, _n = is_norm(L, a//(A) * de^2)

    @hassert :Lattice 1 fl

    if L isa AnticNumberField
      n = evaluate(_n)
    else
      n = _n
    end

    @hassert :Lattice 1 norm(n) == a//(A) * de^2

    u1, w1 = coeff(n, 0)//de, coeff(n, 1)
  end

  @hassert :Lattice 1 u1^2 * A + w1^2 * B == a
  u = (-A * u1 + B * t^2 * u1 - 2 * B * t * w1)//(A + B * t^2)
  w = (-2 * A * t * u1   + A * w1 - B * t^2 * w1)//(A + B * t^2)

  @hassert :Lattice 1 u^2 * A + w^2 * B == a

  return true, u1, w1, u, w
end

# Return true, T such that T * [A 0; 0 B] T^t = [a 0; 0 b] or false, 0 if no such T exists.
function _isisometric_with_isometry_dan(A, B, a, b)
  K = parent(A)

  Kkt, (k, t) = polynomial_ring(K, ["k", "t"], cached = false)

  fl, u1, w1, u, w = _solve_conic_affine(A, B, a, t)
  if !fl
    return false, zero_matrix(K, 0, 0)
  end

  fl, s3, v3, s, v = _solve_conic_affine(B, A, b, k)
  if !fl
    return false, zero_matrix(K, 0, 0)
  end

  lin = ((2 * (-2 * A^2 * B * s3 * t * u1 + A^3 * u1 * v3 - A^2 * B * t^2 * u1 * v3 + A^2 * B * s3 * w1 - A * B^2 * s3 * t^2 * w1 + 2 * A^2 * B * t * v3 * w1))) * k - (-2 * A^2 * B * s3 * u1 +  2 * A * B^2 * s3 * t^2 * u1 - 4 * A^2 * B * t * u1 * v3 - 4 * A * B^2 * s3 * t * w1 + 2 * A^2 * B * v3 * w1 - 2 * A * B^2 * t^2 * v3 * w1)
  sq = 4 * A * B * (A + B * t^2)^2 * (B * s3^2 + A * v3^2) * (A * u1^2 + B * w1^2)

  junk = 4 * (-2 * A^2 * B * s3 * t * u1 + A^3 * u1 * v3 - A^2 * B * t^2 * u1 * v3 + A^2 * B * s3 * w1 -  A * B^2 * s3 * t^2 * w1 + 2 * A^2 * B * t * v3 * w1) * (B + A * k^2) * (A + B * t^2)

  local uu
  local ww
  local ss
  local vv

  i = -1

  denu = denominator(u)
  denw = denominator(w)
  dens = denominator(s)
  denv = denominator(v)

  while true
    i += 1
    t0 = K(i)

    if iszero(A + B * t0^2)
      continue
    end

    @hassert :Lattice 1 !iszero(A + B * t0^2)

    middle = A * u * v + B * s * w

    @hassert :Lattice 1 lin^2 - sq == junk * middle

    _sq = sq(zero(K), t0)

    fl, rt = is_power(_sq, 2)

    if !fl
      return false, zero_matrix(K, 0, 0)
    end

    k0 = (rt + (-2 * A^2 * B * s3 * u1 +  2 * A * B^2 * s3 * t^2 * u1 - 4 * A^2 * B * t * u1 * v3 - 4 * A * B^2 * s3 * t * w1 + 2 * A^2 * B * v3 * w1 - 2 * A * B^2 * t^2 * v3 * w1))//((2 * (-2 * A^2 * B * s3 * t * u1 + A^3 * u1 * v3 - A^2 * B * t^2 * u1 * v3 + A^2 * B * s3 * w1 - A * B^2 * s3 * t^2 * w1 + 2 * A^2 * B * t * v3 * w1)))

    if iszero(denominator(k0)(zero(K), t0))
      continue
    end

    kk = numerator(k0)(zero(K), t0)//denominator(k0)(zero(K), t0)

    #@hassert :Lattice 1 !iszero(junk(kk, t0))
    #@hassert :Lattice 1 !iszero(B + A * kk^2)

    if iszero(denu(kk, t0)) || iszero(denw(kk, t0)) || iszero(dens(kk, t0)) ||
                                                            iszero(denv(kk, t0))
      continue
    end

    uu = numerator(u)(kk, t0)//denominator(u)(kk, t0)
    ww = numerator(w)(kk, t0)//denominator(w)(kk, t0)
    ss = numerator(s)(kk, t0)//denominator(s)(kk, t0)
    vv = numerator(v)(kk, t0)//denominator(v)(kk, t0)
    break
  end

  T = matrix(K, 2, 2, elem_type(K)[uu, ww, vv, ss])
  D1 = diagonal_matrix([A, B])
  D2 = diagonal_matrix([a, b])
  @hassert :Lattice 1 T * D1 * transpose(T) == D2

  return true, T
end

function _isisometric_with_isometry_rank_2(V::QuadSpace, W::QuadSpace)
  if !is_isometric(V, W)
    return false, zero_matrix(base_ring(V), 0, 0)
  end

  @req max(rank(V), rank(W)) <= 2 "Rank must be <= 2"

  K = base_ring(V)

  GV = gram_matrix(V)
  GW = gram_matrix(W)

  DV, MV = _gram_schmidt(gram_matrix(V), involution(V))
  DW, MW = _gram_schmidt(gram_matrix(W), involution(W))

  A, B = DV[1, 1], DV[2, 2]
  a, b = DW[1, 1], DW[2, 2]

  @hassert :Lattice 1 MV * GV * transpose(MV) == diagonal_matrix([A, B])
  @hassert :Lattice 1 MW * GW * transpose(MW) == diagonal_matrix([a, b])

  if a * b != A * B
    c = (A * B)//(a * b)
    bp = b * c
    @hassert :Lattice 1 a * bp == A * B
    fl, T = _isisometric_with_isometry_dan(A, B, a, bp)
    @hassert :Lattice 1 fl
    cc = inv(sqrt(c))
    M = matrix(K, 2, 2, [1, 0, 0, inv(cc)])
    T = inv(M) * T
  else
    fl, T = _isisometric_with_isometry_dan(A, B, a, b)
    @hassert :Lattice 1 fl
  end

  @hassert :Lattice 1 T * DV * transpose(T) == DW

  # T * DV * T^t == DW
  # T * MV * GV * (T * MV)^t == MW * GW * MW^t
  # GV = MV^-1 * T^-1 * MW * GW * (MV^-1 * T^-1 * MW)^t

  T = inv(MV) * inv(T) * MW
  @hassert :Lattice 1 T * GW * transpose(T) == GV
  return true,  T
end

################################################################################
#
#  Isotropic vector
#
################################################################################

_to_gf2(x) = x == 1 ? 0 : 1

function is_isotropic_with_vector(q::QuadSpace{QQField, QQMatrix})
  ok, S = _isotropic_subspace(q)
  if !ok
    z = zeros(base_ring(q), dim(q))
    return false, z
  end
  # confirm the computation
  v = elem_type(base_ring(q))[S[1,i] for i in 1:ncols(S)]
  @hassert :Lattice 1 inner_product(q,v,v)==0
  @hassert :Lattice 1 !all(x==0 for x in v)
  return true, v
end

@doc raw"""
    _isotropic_subspace(q::QuadSpace{QQField, QQMatrix}) -> Bool, QQMatrix

Return if `q` is isotropic and the basis of an isotropic subspace.

Requires the factorization of the determinant of `q`.
"""
function _isotropic_subspace(q::QuadSpace{QQField, QQMatrix})
  # See Denis Simon - Quadratic equations in dimensions 4, 5 and more
  # https://simond.users.lmno.cnrs.fr/maths/Dim4.pdf
  # We do not do exactly the same thing since we are lazy but it should work.
  # what we do is not proven, but the output is tested at least
  if !is_isotropic(q)
    return false, zero_matrix(QQ, 0, dim(q))
  end
  # treat the degenerate case
  if !isregular(q)
    g = gram_matrix(q)
    r, B = left_kernel(g)
    C = _basis_complement(B)
    G = gram_matrix(q,C)
    q1 = quadratic_space(QQ, G)
    @hassert :Lattice 1 is_regular(q1)
    ok, v = _isotropic_subspace(q1)
    @hassert :Lattice 0 ok
    v = vcat(B, v*C)
    return true, v
  end
  # create an even lattice in some rescaling of q
  p, z, n = signature_tuple(q)
  e = 1
  if n > p
    e = -1
  end
  d = denominator(gram_matrix(q))
  if d!=1
    e = e*d
  end
  q = rescale(q, e)
  L = lattice(q)
  if mod(norm(L)//scale(L),2) == 1
    e = 2*e
    L = rescale(L, 2)
  end
  # Denis Simon's indefinite LLL may succeed in finding a zero for a
  # unimodular lattice and maybe we are lucky for a non-unimodular one
  M = maximal_even_lattice(L)
  M = lll(M)
  G = gram_matrix(M)
  if G[1,1] == 0
    i = 1
    while iszero(G[1:i+1, 1:i+1])
      i = i+1
    end
    v = basis_matrix(M)[1:i,:]
    return true, v
  end
  # embed in H^k for H the hyperbolic plane
  D = rescale(discriminant_group(M),-1)
  (p,_,n) = signature_tuple(q)
  a = p - n
  if a == 0 && !is_trivial(D.ab_grp)
    s = (1, 1)
  else
    s = (0, a)
  end
  R = representative(genus(D, s))
  LL, inj = direct_sum(M, R)
  MM = maximal_even_lattice(LL)
  # MM is sum of hyperbolic planes -> Simon should succeed
  ok, H = _maximal_isotropic_subspace_unimodular(MM)
  @assert ok
  i = divexact(rank(MM), 2)
  # the  totally isotropic subspace H has large enough dimension so that its
  # intersection with L is non-trivial (and isotropic) -> we win
  VV = ambient_space(MM)
  iso = preimage(inj[1], lattice(VV, H))
  @hassert :Lattice 0 rank(iso) >0
  @hassert :Lattice 0 gram_matrix(iso)==0
  B = basis_matrix(iso)::dense_matrix_type(base_field(M))
  return true, B
end

function _maximal_isotropic_subspace_unimodular(L)
  if !is_isotropic(rational_span(L))
    return false, zero_matrix(QQ,0,degree(L))
  end
  L = lll(L)
  G = gram_matrix(L)
  iso = _isotropic_subspace_unimodular_gram_no_lll(G)
  # complete to a hyperbolic subspace
  B = solve_left(change_base_ring(ZZ,G*transpose(iso)), identity_matrix(ZZ,nrows(iso)))
  H = vcat(iso, B)*basis_matrix(L)
  L1 = orthogonal_submodule(L, lattice(ambient_space(L), H))
  @assert abs(det(L1))==1
  _, B2 = _maximal_isotropic_subspace_unimodular(L1)

  B1 = iso*basis_matrix(L)

  return true, vcat(B1, B2)
end

function _isotropic_subspace_unimodular_gram_no_lll(G)
  # search for zeros directly
  n = nrows(G)
  E = identity_matrix(ZZ,n)
  if G[1,1] == 0
    i = 1
    while iszero(G[1:i+1, 1:i+1])
      i = i+1
    end
    v = E[1:i,:]
    return v
  end
  for i in 1:n
    if G[i,i] == 0
      return E[i,:]
    end
  end
  D, T = _gram_schmidt(G, identity)
  d = [det(G[1:i,1:i]) for i in 1:n]
  for i in 2:n
    for j in i+1:n
      if d[i]//d[i-1] == - d[j]//d[j-1]
        v = (T[i,:]+T[j,:])
        v = change_base_ring(ZZ,denominator(v)*v)
        return v
      end
    end
  end
  @assert false "please tell us about this failing example"
end


function _isisotropic_with_vector(F::QQMatrix)
  Q,a = rationals_as_number_field()
  FQ = change_base_ring(Q, F)
  b, v = _isisotropic_with_vector(FQ)
  v = QQFieldElem[QQ(x) for x in v]
  return b, v
end

# F must be symmetric
function _isisotropic_with_vector(F::MatrixElem)
  K = base_ring(F)
  local T::typeof(F)
  local vv::typeof(F)
  _D, T = _gram_schmidt(F, identity, false)
  local D::Vector{elem_type(base_ring(F))} # Fix compiler bug on julia 1.3
  local __D::Vector{elem_type(base_ring(F))} # Fix compiler bug on julia 1.3
  local v::Vector{elem_type(base_ring(F))}
  D = diagonal(_D)
  i = findfirst(==(zero(K)), D)
  if i isa Int
    return true, elem_type(K)[T[i, j] for j in 1:ncols(T)]
  end

  R = maximal_order(K)
  local P::Vector{ideal_type(R)}
  P = ideal_type(R)[]

  if length(D) <= 1
    return false, elem_type(K)[]
  end

  for i in 1:length(D)
    for j in (i + 1):length(D)
      if D[i] == -D[j]
        return true, elem_type(K)[T[i, k] + T[j, k] for k in 1:ncols(T)]
      end
    end
  end

  fl, y = is_square_with_sqrt(-D[1]//D[2])
  if fl
    return true, elem_type(K)[T[1, k] + y * T[2, k] for k in 1:ncols(T)]
  elseif length(D) == 2
    return false, elem_type(K)[]
  end

  if length(D) == 3
    fl, a, b = _solve_conic_affine(D[1], D[2], -D[3])
    if fl
      v = elem_type(K)[a, b, one(K)]
      vma = matrix(K, 1, length(v), v) * T
      @hassert :Lattice 1 vma * F * transpose(vma) == 0
      return true, elem_type(K)[vma[1, i] for i in 1:ncols(vma)]
    else
      return false, elem_type(K)[]
    end
  elseif length(D) == 4
    fl, v = _isisotropic_with_vector(diagonal_matrix(D[3], D[4]))
    if fl
      return true, elem_type(K)[v[1] * T[3, k] + v[2] * T[4, k] for k in 1:ncols(T)]
    end

    for v in real_places(K)
      if !_isisotropic(D, v)
        return false, elem_type(K)[]
      end
    end

    for d in append!(elem_type(K)[K(2)], D)
      for (p, _) in factor(d * R)
        if p in P
          continue
        end
        if !_isisotropic(D, p)
          return false, elem_type(K)[]
        else
          push!(P, p)
        end
      end
    end

    # At this point we know that the space is isotropic.
    # But we need to determine the vector.

    # Find x != 0 such that <D[1], D[2]> and <-D[3], -D[4]> both represent x.

    rlp = real_places(K)

    _target = append!(Int[_to_gf2(hilbert_symbol(D[1], D[2], p)) for p in P], Int[_to_gf2(hilbert_symbol(-D[3], -D[4], p)) for p in P])

    I = eltype(rlp)[]

    for p in rlp
      s = sign(D[1], p)
      if s == sign(D[2], p)
        push!(I, p)
        push!(_target, _to_gf2(s))
      else
        s = sign(-D[3], p)
        if s == sign(-D[4], p)
          push!(I, p)
          push!(_target, _to_gf2(s))
        end
      end
    end

    V = abelian_group(Int[2 for i in 1:length(_target)])
    target = V(_target)
    # Find x such that target equals the vector
    # [ _to_gf2_(hilbert_symbol(-D[1] * D[2], x, p)) for p in ] vcat
    # [ _to_gf2(hilbert_symbol(-D[3]*D[4], x, p)) for p in P ] vcat
    # [ _to_gf2(sign(x, p) for p in I ]
    if iszero(target)
      x = one(K)
    else
      found = false
      S, mS = sub(V, elem_type(V)[], false)
      basis = elem_type(K)[]
      signsV = elem_type(V)[]
      L, mL = sunit_group_fac_elem(P)
      Q, mQ = quo(L, 2, false)
      for q in gens(Q)
        x = evaluate(mL(mQ\q))
        _v = append!(Int[_to_gf2(hilbert_symbol(-D[1] * D[2], x, p)) for p in P], Int[_to_gf2(hilbert_symbol(-D[3] * D[4], x, p)) for p in P])
        _v = append!(_v, Int[_to_gf2(sign(x, p)) for p in I])

        ss = V(_v)
        fl, _ = haspreimage(mS, ss)
        if !fl
          push!(signsV, ss)
          push!(basis, x)
          S, mS = sub(V, signsV, false)
          if haspreimage(mS, target)[1]
            found = true
            break
          end
        end
      end

      # Still not found

      Cl, mCl = class_group(R)
      A = abelian_group(fill(0, length(P)))
      hh = hom(A, Cl, [mCl\(p) for p in P])
      SS, mSS = image(hh, false)
      Q, mQ = quo(Cl, [mSS(SS[i]) for i in 1:ngens(SS)])

      p  = 2
      while !found
        p = next_prime(p)
        lp = prime_decomposition(R, p)
        for (q, _) in lp
          if q in P
            continue
          end
          o = order(mQ(mCl\(q)))
          c = -(hh\(o * (mCl\(q))))
          fl, _x = is_principal(q * prod(P[i]^Int(c.coeff[i]) for i in 1:length(P)))
          x = elem_in_nf(_x)
          _v = append!(Int[_to_gf2(hilbert_symbol(-D[1] * D[2], x, p)) for p in P], Int[_to_gf2(hilbert_symbol(-D[3] * D[4], x, p)) for p in P])
          _v = append!(_v, Int[_to_gf2(sign(x, p)) for p in I])
          _s = V(_v)
          if haspreimage(mS, _s + target)[1]
            push!(basis, x)
            push!(signsV, _s)
            found = true
            break
          end
        end
      end

      FF = GF(2, cached = false)
      fl, expo = can_solve_with_solution(matrix(FF, length(signsV), length(_target), [ s.coeff[1, i] for s in signsV, i in 1:length(_target)]), matrix(FF, 1, length(_target), _target), side = :left)
      @hassert :Lattice 1 fl

      x = evaluate(FacElem(basis, map(ZZRingElem, [lift(expo[1, i]) for i in 1:length(basis)])))
    end
    ok, v = _isisotropic_with_vector(diagonal_matrix([D[1], D[2], -x]))
    @hassert :Lattice 1 ok
    ok, w = _isisotropic_with_vector(diagonal_matrix([D[3], D[4],  x]))
    @hassert :Lattice 1 ok
    v = inv(v[3]) .* v
    w = inv(w[3]) .* w
    vv = matrix(K, 1, 4, [v[1], v[2], w[1], w[2]]) * T
    @hassert :Lattice 1 vv * F * transpose(vv) == 0
    return true, elem_type(K)[vv[1, i] for i in 1:4]
  else
    # Dimension >= 5, we need to only take care of the real places
    rlp = real_places(K)
    okk = all(let D = D; v -> _isisotropic(D, v); end, rlp)
    if !okk
      return false, elem_type(K)[]
    end

    # We need D[3..5] to yield both signs at every real place
    found = false
    for i in 1:length(D), j in (i + 1):length(D)
      if all(let D = D; p -> sign(D[i], p) != sign(D[j], p); end, rlp)
        TT = identity_matrix(K, nrows(F))
        found = true
        if i != 3
          swap_cols!(TT, 3, i)
        end
        if j != 4
          swap_cols!(TT, 4, j)
        end
        T = TT * T
        _D = (T * F * transpose(T))
        @hassert :Lattice 1 is_diagonal(_D)
        D = diagonal(_D)
        break
      end
    end
    local fix::Vector{Int}
    local signs::Vector{Int}
    local s::Int
    if !found
      fix = Int[]
      signs = Int[]
      for i in 1:length(rlp)
        s = sign(D[4], rlp[i])
        if s != sign(D[5], rlp[i])
          continue
        end
        if s == sign(D[4], rlp[i])
          _a = _real_weak_approximation(_embedding(rlp[i]), _embedding(rlp[fix]))::elem_type(K)
          a = inv(_a)::elem_type(K)
          j = findfirst(Bool[sign(D[j], rlp[i]) != s for j in 1:length(D)])::Int
          r = 0
          while true
            r += 1
            t = D[4] + a^(2*r)*D[j]
            if sign(t, rlp[i]) != s && all(Bool[sign(t, rlp[fix[k]]) == signs[k] for k in 1:length(fix)])
              break
            end
          end
          b = -a^r * D[j]//D[4]
          vvv = [T[4, k] for k in 1:ncols(T)]
          for k in 1:ncols(T)
            T[4, k] = T[4, k] + a^r * T[j, k]
          end
          for k in 1:ncols(T)
            T[j, k] = T[j, k] + b * vvv[k]
          end
        end
        push!(fix, i)
        push!(signs, -s)
        _D = T * F * transpose(T)
        @hassert :Lattice 1 is_diagonal(_D)
        D = diagonal(_D)
      end
    end
    ok, v = _isisotropic_with_vector(diagonal_matrix(D[3:5]))


    if ok
      res = Vector{elem_type(K)}(undef, ncols(T))
      for k in 1:ncols(T)
        res[k] = v[1] * T[3, k] + v[2] * T[4, k] + v[3] * T[5, k]
      end
      return true, res
    end

    # We scale to make D[1], D[2] integral

    Dorig = copy(D)

    if !is_integral(D[1])
      d = denominator(D[1])
      if is_square(d)
        D[1] = d * D[1]
        scalex =  sqrt(d)
      else
        D[1] = d^2 * D[1]
        scalex = d
      end
    else
      scalex = one(ZZ)
    end

    if !is_integral(D[2])
      d = denominator(D[2])
      if is_square(d)
        D[2] = d * D[2]
        scaley =  sqrt(d)
      else
        D[2] = d^2 * D[2]
        scaley = d
      end
    else
      scaley = one(ZZ)
    end

    X = Tuple{elem_type(K), elem_type(K)}[]
    M = ideal_type(R)[]
    __D = append!(elem_type(K)[K(2)], D)
    PP = Set{ideal_type(R)}()
    for d in __D
      for p in support(d, R)
        push!(PP, p)
      end
    end

    for p in PP
      if _isisotropic(D[3:5], p)
        continue
      end

      local x::elem_type(K)
      local y::elem_type(K)

      if _isisotropic([D[3], D[4], D[5], D[1]], p)
        x = one(K)
        y = zero(K)
      elseif _isisotropic([D[3], D[4], D[5], D[2]], p)
        x = zero(K)
        y = one(K)
      else
        # now D[1] and D[2] represent necessarily the same class
        # leaving this class is enough
        V1 = valuation(D[1], p)
        V2 = valuation(D[2], p)
        V = max(V1, V2)
        pi = elem_in_nf(uniformizer(p))
        k, h = residue_field(order(p), p)
        hext = extend(h, K)
        y = pi^(div(V - V2, 2))
        yy = pi^(div(V - V1, 2))
        cnt = 1
        while true
          cnt += 1
          @hassert :Lattice 1 cnt <= 1000
          x = (hext\rand(k)) * yy
          if _isisotropic(elem_type(K)[D[3], D[4], D[5], x^2 * D[1] + y^2 * D[2]], p)
            break
          end
        end
      end
      push!(X, (x, y))
      push!(P, p)
      V = valuation(x^2 * D[1] + y^2 * D[2], p) + 1
      if is_dyadic(p)
        V = V + 2 * ramification_index(p)
      end
      push!(M, p^V)
    end
    @hassert :Lattice 1 length(P) != 0

    xx::elem_type(K) = elem_in_nf(crt(elem_type(R)[R(x[1]) for x in X], M))
    yy::elem_type(K) = elem_in_nf(crt(elem_type(R)[R(x[2]) for x in X], M))
    t = xx^2 * D[1] + yy^2 * D[2]
    xx = scalex * xx
    yy = scaley * yy
    @hassert :Lattice 1 t == xx^2 * Dorig[1] + yy^2 * Dorig[2]
    ok, w = _isisotropic_with_vector(diagonal_matrix(elem_type(K)[D[3], D[4], D[5], t]))
    @hassert :Lattice 1 ok
    @hassert :Lattice 1 w[1]^2 * D[3] + w[2]^2 * D[4] + w[3]^2 * D[5] + w[4]^2 * t == 0
    w = inv(w[4]) .* w
    vv = matrix(K, 1, ncols(T), append!(elem_type(K)[xx, yy, w[1], w[2], w[3]],
                                        elem_type(K)[zero(K) for i in 1:(nrows(T) - 5)])) * T
    vv = lcm(ZZRingElem[denominator(vv[1, i]) for i in 1:ncols(vv)]) * vv
    @hassert :Lattice 1 vv * F * transpose(vv) == 0
    return true, elem_type(K)[vv[1, i] for i in 1:ncols(vv)]
  end
end

function _quadratic_form_decomposition(F::MatrixElem)
  # Decompose F into an anisotropic kernel, an hyperbolic space and its radical
  @req is_symmetric(F) "Matrix must be symmetric"
  K = base_ring(F)
  r, Rad = left_kernel(F)
  @hassert :Lattice 1 nrows(Rad) == r
  RadComp = _find_direct_sum(Rad)
  newF = RadComp * F * transpose(RadComp)
  H = similar(F, 0, ncols(F))
  CurBas = RadComp

  while true
    fl, HH = _find_hyperbolic_subspace(newF)
    if fl
      @hassert :Lattice 1 iszero(sub(HH, 1:1, 1:ncols(HH)) * newF  * transpose(sub(HH, 1:1, 1:ncols(HH))))
      H = vcat(H, HH * CurBas)
      CurBas = _orthogonal_complement(newF, HH) * CurBas
      newF = CurBas * F * transpose(CurBas)
    else
      break
    end
  end

  @hassert :Lattice 1 iseven(nrows(H))
  if nrows(H) > 0
    D = diagonal_matrix([matrix(K, 2, 2, [1, 0, 0, -1]) for i in 1:div(nrows(H), 2)])
    @hassert :Lattice 1 is_isometric(quadratic_space(K, H * F * transpose(H)), quadratic_space(K, D))
  end

  @hassert :Lattice 1 iszero(Rad * F * transpose(Rad))

  #H * F * transpose(H), CurBas * F * transpose(CurBas), Rad * F * transpose(Rad)
  return CurBas, H, Rad
end

function _find_hyperbolic_subspace(F)
  K = base_ring(F)
  iso, v = _isisotropic_with_vector(F)
  if !iso
    return false, F
  end
  vv = matrix(K, 1, length(v), v)

  # Find basis vector which has non-trivial product with v
  o = F * transpose(vv)
  i = findfirst(j -> !iszero(o[j, 1]), 1:nrows(o))
  @hassert :Lattice 1 i isa Int
  H = vcat(vv, zero_matrix(base_ring(F), 1, ncols(F)))
  H[2, i] = inv(o[i, 1])
  GG = H * F * transpose(H)

  if !iszero(GG[2, 2])
    al = -GG[2, 2]//2
    for i in 1:ncols(H)
      H[2, i] = al * H[1, i] + H[2, i]
    end
    GG = H * F * transpose(H)
  end

  @hassert :Lattice 1 iszero(GG[1, 1])
  @hassert :Lattice 1 iszero(GG[2, 2])
  @hassert :Lattice 1 isone(GG[1, 2])
  @hassert :Lattice 1 isone(GG[2, 1])

  return true, H
end

function _find_direct_sum(B::MatrixElem)
  # I am very lazy
  C = B
  r = nrows(B)
  K = base_ring(B)
  piv = Int[]
  for i in 1:ncols(B)
    z = zero_matrix(K, 1, ncols(B))
    z[1, i] = one(K)
    CC = vcat(C, z)
    _r = rank(CC)
    if _r == r
      continue
    else
      r = _r
      push!(piv, i)
      C = CC
    end
  end
  l = length(piv)
  @hassert :Lattice 1 nrows(B) + l == ncols(B)
  Z = zero_matrix(K, l, ncols(B))
  for i in 1:length(piv)
    Z[i, piv[i]] = one(K)
  end
  return Z
end

function _orthogonal_complement(F::MatrixElem, B::MatrixElem)
  r, R = left_kernel(F * transpose(B))
  @hassert :Lattice 1 nrows(R) == r
  if !iszero(det(F))
    @hassert :Lattice 1 nrows(R) + nrows(B) == nrows(F)
  end
  return R
end

function _maximal_isotropic_subspace(F::MatElem)
  _, H, R = _quadratic_form_decomposition(F)
  return vcat(sub(H, collect(1:2:nrows(H)), collect(1:ncols(H))), R)
end

function _isisometric_with_isometry(F, G)
  K = base_ring(F)

  if nrows(F) != nrows(G)
    return false, F
  end

  A1, H1, R1 = _quadratic_form_decomposition(F)
  A2, H2, R2 = _quadratic_form_decomposition(G)
  if nrows(H1) != nrows(H2) || nrows(R1) != nrows(R2)
    return false, F
  end

  _, _, _d1, _H1, _I1 = _quadratic_form_invariants(A1 * F * transpose(A1))
  _, _, _d2, _H2, _I2 = _quadratic_form_invariants(A2 * G * transpose(A2))
  if !(_I1 == _I2 && _H1 == _H2 && is_square(_d1 * _d2)[1])
    return false, F
  end

  @hassert :Lattice 1 nrows(H1) == nrows(H2) && nrows(R1) == nrows(R2)

  X = zero_matrix(K, 0, ncols(F))
  Y = zero_matrix(K, 0, ncols(F))

  while nrows(A1) > 0
    GA1 = A1 * F * transpose(A1)
    GA2 = A2 * G * transpose(A2)
    ok, v = _isisotropic_with_vector(diagonal_matrix(GA1, -GA2))
    @hassert :Lattice 1 ok
    n = div(length(v), 2)
    _x = matrix(K, 1, n, v[1:n])
    _y = matrix(K, 1, n, v[(n+1):2*n])
    @hassert :Lattice 1 _x * GA1 * transpose(_x) == _y * GA2 *  transpose(_y)
    x = matrix(K, 1, n, v[1:n]) * A1
    y = matrix(K, 1, n, v[(n+1):2*n]) * A2
    @hassert :Lattice 1 x * F * transpose(x) == y * G * transpose(y)
    X = vcat(X, x)
    Y = vcat(Y, y)
    @hassert :Lattice 1 X * F * transpose(X) == Y * G * transpose(Y)
    _A1 = _orthogonal_complement(GA1, matrix(K, 1, n, v[1:n]))
    A1 = _A1 * A1
    _A2 = _orthogonal_complement(GA2, matrix(K, 1, n, v[(n + 1):2*n]))
    A2 = _A2 * A2
  end

  @hassert :Lattice 1 X * F * transpose(X) == Y * G * transpose(Y)
  @hassert :Lattice 1 H1 * F * transpose(H1) == H2  *  G * transpose(H2)

  M = inv(vcat(X, H1, R1)) * vcat(Y, H2, R2)

  @hassert :Lattice 1 M * G * transpose(M) == F

  return true, M
end

@doc raw"""
    is_isometric_with_isometry(V::QuadSpace, W::QuadSpace)

Returns wether $V$ and $W$ are isometric together with an isometry in case it
exists. The isometry is given as an invertible matrix $T$ such that
$T G_W T^t = G_V$, where $G_V$, $G_W$ are the Gram matrices.
"""
function is_isometric_with_isometry(V::QuadSpace{F,M}, W::QuadSpace{F,M}) where {F,M}
  @req base_ring(V) == base_ring(W) "base rings do not aggree"
  GV = gram_matrix(V)
  GW = gram_matrix(W)
  if rank(V) > 2 || rank(W) > 2 || iszero(discriminant(V)) || iszero(discriminant(W))
    return _isisometric_with_isometry(GV, GW)
  else
    return _isisometric_with_isometry_rank_2(V, W)
  end
end

function _real_weak_approximation(s, I)
  K = number_field(s)
  a = gen(K)
  while true
    x = simplest_inside(real(evaluate(a, s, 10)))
    a = 2 * (a - x)
    if all(t -> t == s || abs(evaluate(a, t)) >= 2, I)
      break
    end
  end
  @hassert :Lattice 1 abs(evaluate(a, s)) < 1//2
  return a
end

################################################################################
#
#  Is isotropic
#
################################################################################

is_isotropic(q::QuadSpace) = is_isotropic(isometry_class(q))


function _isisotropic_with_vector_finite(M)
  n = ncols(M)
  k = base_ring(M)
  _test(v) = iszero(matrix(k, 1, n, v) * M * matrix(k, n, 1, v))
  @hassert :Lattice 1 k isa Field && characteristic(k) != 2
  if n == 0
    ;
  elseif n == 1
    if iszero(M[1, 1])
      return true, elem_type(k)[one(k)]
    end
  else
    if n <= 3
      G, T = _gram_schmidt(M, identity, false) # might be non-degenerate
    else
      G, T = _gram_schmidt(sub(M, 1:3, 1:3), identity, false) # might be non-degenerate
      B = zero_matrix(k, 3, n)
      B[1, 1] = 1
      B[2, 2] = 1
      B[3, 3] = 1
      T = T * B
    end
    for i in 1:ncols(G)
      if iszero(G[i, i])
        el = elem_type(k)[T[i, j] for j in 1:ncols(T)]
        @hassert :Lattice _test(el)
        return true, el
      end
    end

    if n == 2
      ok, s = is_square_with_sqrt(-divexact(G[1, 1], G[2, 2]))
      if ok
        el = elem_type(k)[T[1, i] + s*T[2, i] for i in 1:ncols(T)]
        @hassert :Lattice _test(el)
        return true, el
      end
    else
      while true
        x = rand(k)
        y = rand(k)
        ok, z = is_square_with_sqrt(divexact(-x^2 * G[1, 1] - y^2 * G[2, 2], G[3, 3]))
        if (ok && (!iszero(x) || !iszero(y)))
          el = elem_type(k)[x*T[1, i] + y*T[2, i] + z * T[3, i] for i in 1:ncols(T)]
          @hassert :Lattice _test(el)
          return true, el
        end
      end
    end
  end
  return false, elem_type(k)[]
end

@doc raw"""
    signature_tuple(q::QuadraticSpace{QQField,QQMatrix) ->Tuple{Int,Int,Int}

Return the number of (positive, zero, negative) inertia of this rational quadratic space.
"""
function signature_tuple(q::QuadSpace{QQField,QQMatrix})
  D = diagonal(q)
  pos = count(d>0 for d in D)
  zero = count(d==0 for d in D)
  neg = count(d<0 for d in D)
  return (pos, zero, neg)
end

@doc raw"""
    signature_tuple(q::QuadraticSpace{QQField,QQMatrix}, p::InfPlc)
    -> Tuple{Int,Int,Int}

Return the number of (positive, zero, negative) inertia over the completion
of `q` at the infinite place `p`.
"""
function signature_tuple(q::QuadSpace, p::InfPlc)
  D = diagonal(q)
  pos = count(is_positive(d, p) for d in D if d!=0)
  zero = count(d==0 for d in D)
  neg = count(is_negative(d, p) for d in D)
  return pos, zero, neg
end

@doc raw"""
    signature_tuples(q::QuadraticSpace{QQField,QQMatrix})
    -> Dict{Union{PosInf,InfPlc},Tuple{Int,Int,Int}}

Return a dictionary containing
the number of (positive, zero, negative) inertia over the completion
of `q` at the infinite place `p`.
"""
function signature_tuples(q::QuadSpace)
  P = real_places(base_ring(q))
  return Dict{eltype(P), Tuple{Int, Int, Int}}((p,signature_tuple(q, p)) for p in P)
end

################################################################################
# Abstract Isometry Classes of Quadratic spaces
################################################################################

function localclass_quad_type(K)
  return LocalQuadSpaceCls{typeof(K), ideal_type(order_type(K)), elem_type(K)}
end

function local_quad_space_class(K, prime, n, d, hasse_inv, k)
  g = localclass_quad_type(K)(K)
  g.K = K
  g.p = prime
  g.dim = n
  g.dim_rad = k
  g.det = d  # determinant of the non-degenerate part
  g.hass_inv = hasse_inv
  return g
end

function _is_valid(g::LocalQuadSpaceCls)
  0 <= g.dim_rad <= g.dim || return false
  dim = g.dim - g.dim_rad
  if dim == 0
    g.hass_inv == 1 || return false
    return is_local_square(g.det, g.p)
  end
  if dim == 1
    return g.hass_inv == 1
  end
  if dim == 2
    if g.hass_inv == -1 && is_local_square(-g.det, g.p)
      return false
    end
  end
  return true
end

local_quad_space_class(K, prime::IntegerUnion, n, d, hasse_inv, k)=local_quad_space_class(K,ideal(ZZ,prime),n,d,hasse_inv,k)

base_ring(G::LocalQuadSpaceCls) = G.K
prime(G::LocalQuadSpaceCls) = G.p

@doc raw"""
    det_nondegenerate_part(g::QuadSpaceCls) -> Int

Return the determinant of the quotient of this quadratic space by its radical.
"""
det_nondegenerate_part(g::LocalQuadSpaceCls) = g.det

det_ndeg(g::LocalQuadSpaceCls) = det_nondegenerate_part(g)

dim(G::LocalQuadSpaceCls) = G.dim
dim_radical(G::LocalQuadSpaceCls) = G.dim_rad
hasse_invariant(G::LocalQuadSpaceCls) = G.hass_inv

@doc raw"""
    isometry_class(V::QuadSpace, p) -> LocalQuadSpaceCls

Return the abstract isometry class of the completion of the quadratic space `V`
at `p`."""
function isometry_class(V::QuadSpace, p)
  diag = diagonal(V)
  d = prod([d for d in diag if d!=0])
  r = count([x==0 for x in diag])
  h = hasse_invariant(V, p)
  n = dim(V)
  return local_quad_space_class(base_ring(V), p , n , d, h, r)
end

function isometry_class(V::QuadSpace, p::IntegerUnion)
  isometry_class(V, ideal(ZZ, p))
end

function witt_invariant(G::LocalQuadSpaceCls)
  if isdefined(G, :witt_inv)
    return G.witt_inv
  end
  K = base_ring(G)
  h = hasse_invariant(G)
  n = dim(G) - G.dim_rad
  d = G.det
  p = prime(G)
  w = _hasse_witt(K, h, n, d, p)
  G.witt_inv = w
  return G.witt_inv
end

function Base.show(io::IO, G::LocalQuadSpaceCls)
  n = dim(G)
  d = G.det
  h = hasse_invariant(G)
  p = prime(G)
  compact = get(io, :compact, false)
  if compact
    print(io,"$G.P $n $d $h")
  else
    print(io, "Abstract local quadratic space over ")
    print(IOContext(io, :compact => true), base_ring(G))
    print(io, " at ")
    print(IOContext(io, :compact => true), p)
    println(io, " of ")
    print(io, "Dimension $n, determinant $d, Hasse invariant $h")
  end
end

function Base.:(==)(G1::LocalQuadSpaceCls, G2::LocalQuadSpaceCls)
  if G1 === G2
    return true
  end
  if base_ring(G1) != base_ring(G2)
    error("abstract quadratic spaces over different fields do not compare")
  end
  if prime(G1) != prime(G2)
    error("abstract local quadratic spaces over different primes "
          *"do not compare")
  end
  if dim_radical(G1) != dim_radical(G2)
    return false
  end
  if dim(G1) != dim(G2)
    return false
  end
  if hasse_invariant(G1) != hasse_invariant(G2)
    return false
  end
  return is_local_square(G1.det*G2.det, prime(G1))
end

@doc raw"""
    Base.:(+)(G1::LocalQuadSpaceCls, G2::LocalQuadSpaceCls)
    -> LocalQuadSpaceCls

Return the isometry class of the direct sum.
"""
function Base.:(+)(G1::LocalQuadSpaceCls, G2::LocalQuadSpaceCls)
  @req base_ring(G1) == base_ring(G2) "base fields must be equal"
  @req prime(G1) == prime(G2) "base primes must be equal"
  K = base_ring(G1)
  p = prime(G1)
  n = dim(G1) + dim(G2)
  r1 = dim_radical(G1)
  r2 = dim_radical(G2)
  r = r1 + r2
  d = det_nondegenerate_part(G1)*det_nondegenerate_part(G2)
  _,w,_ = _witt_of_direct_sum(G1.det, witt_invariant(G1), dim(G1)-r1,
                                 G2.det, witt_invariant(G2), dim(G2)-r2, p)
  h = _witt_hasse(w, n - r, d, p)
  return local_quad_space_class(K, p, n, d, h, r)
end

direct_sum(G1::LocalQuadSpaceCls, G2::LocalQuadSpaceCls) = G1 + G2

@doc raw"""
    Base.:(-)(G1::LocalQuadSpaceCls, G2::LocalQuadSpaceCls)
    -> LocalQuadSpaceCls

Return `G3` such that `G1 = G2+G3` or throw an error out if it does not exist.
"""
function Base.:(-)(G1::LocalQuadSpaceCls, G2::LocalQuadSpaceCls)
  @req base_ring(G1) == base_ring(G2) "base fields must be equal"
  @req prime(G1) == prime(G2) "base primes must be equal"
  @req dim_radical(G2) == 0 "the second form must be regular to apply Witt cancellation"
  K = base_ring(G1)
  p = prime(G1)
  n = dim(G1) - dim(G2)
  d = det_nondegenerate_part(G1) * det_nondegenerate_part(G2)
  r = dim_radical(G1) - dim_radical(G2)
  H = local_quad_space_class(K, p, n, d, 1, r)
  if H + G2 != G1
    H = local_quad_space_class(K, p, n, d, -1, r)
  end
  # confirm
  @hassert :Lattice 1 H + G2 == G1
  return H
end

@doc raw"""
    represents(V::LocalQuadSpaceCls, x)

Return if the quadratic space `V` over the field $K$ represents `x in K`.

Note that any quadratic form represents `0`.
"""
function represents(V::LocalQuadSpaceCls, x)
  if x == 0
    return true
  end
  q = quadratic_space(base_ring(V), base_ring(V)[x;])
  V2 = isometry_class(q, prime(V))
  return represents(V, V2)
end

function is_isotropic(G1::LocalQuadSpaceCls)
  if dim_radical(G1) > 0
    return true
  end
  n = dim(G1) - dim_radical(G1)
  if n == 1
    return false
  end
  # if it is isotropic there is a hyperbolic plane
  H = quadratic_space(base_ring(G1), base_ring(G1)[0 1; 1 0])
  G2 = isometry_class(H, prime(G1))
  return represents(G1, G2)
end

@doc raw"""
    represents(G1::LocalQuadSpaceCls, G2::LocalQuadSpaceCls)

Return if `G1` represents the quadratic space `G2`.
"""
function represents(G1::LocalQuadSpaceCls, G2::LocalQuadSpaceCls)
  @req base_ring(G1) == base_ring(G2) "base fields must be equal"
  @req prime(G1) == prime(G2) "base primes must be equal"
  G = G1 - G2
  return _is_valid(G)
end

################################################################################

function class_quad_type(K)
  return QuadSpaceCls{typeof(K), ideal_type(order_type(K)), elem_type(K), place_type(K)}
end

function _is_valid(q::QuadSpaceCls{K}) where {K}
  q.dim >= q.dim_rad >= 0 || return false

  @hassert :Lattice 1 !iszero(q.det)
  dim = q.dim - q.dim_rad
  neg_hasse = [p for p in keys(q.LGS) if hasse_invariant(q.LGS[p])==-1]

  if dim == 0
    return issquare(q.det) && length(neg_hasse)==0
  end
  inf_plcs = keys(q.signature_tuples)
  all(Bool[sign(q.det, K === QQField ? p : _embedding(p)) == (-1)^(q.signature_tuples[p][3]) for p in inf_plcs]) || return false
  # Information at the real place plc does not match the sign of the determinant

  if dim == 1
    length(neg_hasse) ==0 || return false  # Impossible Hasse invariants
  end

  # Finite places check
  if dim == 2
    all(!is_local_square(-q.det, p) for p in neg_hasse) || return false
  end

  neg_hasse_inf = count(s[3] % 4 >= 2 for s in values(q.signature_tuples))
  iseven(neg_hasse_inf + length(neg_hasse)) || return false
  #   "The number of places (finite or infinite) with Hasse invariant -1 must be even";

  # // OK, a space with these invariants must exist.
  return true
end

function Base.show(io::IO, G::QuadSpaceCls)
  K = base_ring(G)
  n = dim(G)
  d = det(G)
  S = signature_tuples(G)
  P = [p for p in keys(G.LGS) if hasse_invariant(G.LGS[p])==-1]
  print(IOContext(io, :compact => true), "Abstract quadratic space over ",
        K, " of dimension $n, determinant $d, negative Hasse invariants at ",P,
        " signature tuples ", values(S))
end

function Base.:(==)(G1::QuadSpaceCls, G2::QuadSpaceCls)
  @req base_ring(G1) == base_ring(G2) "isometry classes over different fields do not compare"
  if G1 === G2
    return true
  end
  if dim(G1) != dim(G2)
    return false
  end
  S1 = G1.signature_tuples
  S2 = G2.signature_tuples
  if S1 != S2
    return false
  end
  if !is_square_with_sqrt(G1.det*G2.det)[1]
    return false
  end
  P = union(Set(keys(G1.LGS)),Set(keys(G2.LGS)))
  return all(local_symbol(G1, p) == local_symbol(G2,p) for p in P)
end

@doc raw"""
    isometry_class(q::QuadSpace) -> QuadSpaceCls

Return the abstract isometry class of `q`.
"""
@attr class_quad_type(base_ring(q)) function isometry_class(q::QuadSpace)
  K = base_ring(q)
  n, k, d, P, sig = invariants(q)
  LGS = Dict{ideal_type(order_type(K)),localclass_quad_type(K) }()
  for p in keys(P)
    if P[p] == -1
      gp = local_quad_space_class(K, p, n, d, -1, k)
      if K == QQ
        p = ideal(ZZ,p)
      end
      LGS[p] = gp
    end
  end
  G = class_quad_type(K)(K)
  G.LGS = LGS
  G.dim = n
  G.det = d
  G.dim_rad = k
  sig_tuples = Dict((s[1], (n-k-s[2], k, s[2])) for s in sig)
  G.signature_tuples = sig_tuples
  return G
end

# Access
dim(g::QuadSpaceCls) = g.dim

function det(g::Union{QuadSpaceCls,LocalQuadSpaceCls})
  if g.dim_rad == 0
    return g.det
  else
    return base_ring(g)(0)
  end
end

@doc raw"""
    det_nondegenerate_part(g::QuadSpaceCls) -> Int

Return the determinant of the quotient of this quadratic space by its kernel.
"""
det_nondegenerate_part(g::QuadSpaceCls) = g.det

det_ndeg(g::QuadSpaceCls) = det_nondegenerate_part(g)

base_ring(g::QuadSpaceCls) = g.K

@doc raw"""
    dim_radical(g::QuadSpaceCls) -> Int

Return the dimension of the kernel of this quadratic space.
"""
dim_radical(g::QuadSpaceCls) = g.dim_rad

function local_symbols(g::QuadSpaceCls)
  return copy(g.LGS)
end

@doc raw"""
    local_symbol(g::QuadSpaceCls, p) -> LocalQuadSpaceCls

Return the isometry class of the localization of (a representative of)
`g` at a prime `p`.
"""
function local_symbol(g::QuadSpaceCls{S,T,U,V}, p::T) where {S,T,U,V}
  if p in keys(g.LGS)
    return g.LGS[p]
  else
    K = base_ring(g)
    return local_quad_space_class(K, p, dim(g), det_ndeg(g), 1, dim_radical(g))
  end
end

local_symbol(g::QuadSpaceCls{S,T,U,V}, p::IntegerUnion)  where {S<:QQField, T<:ZZIdl, U <:QQFieldElem, V<:Union{QQFieldElem,PosInf}} = local_symbol(g,ideal(ZZ,p))

function signature_tuples(g::QuadSpaceCls)
  return copy(g.signature_tuples)
end

function signature_tuple(g::QuadSpaceCls, p::InfPlc)
  return g.signature_tuples[p]
end

function signature_tuple(g::QuadSpaceCls{QQField})
  return g.signature_tuples[inf]
end

function is_isotropic(G1::QuadSpaceCls)
  if dim_radical(G1) > 0
    return true
  end
  n = dim(G1) - dim_radical(G1)
  if n == 1
    return false
  end
  # if it is isotropic there is a hyperbolic plane
  H = quadratic_space(base_ring(G1), base_ring(G1)[0 1; 1 0])
  G2 = isometry_class(H)
  return represents(G1, G2)
end
# Representation
@doc raw"""
    represents(g1::QuadSpaceCls, g2::QuadSpaceCls) -> Bool

Return if `g1` represents the regular space `g2`.
"""
function represents(g1::QuadSpaceCls, g2::QuadSpaceCls)
  g = g1 - g2
  return _is_valid(g)
end


@doc raw"""
    represents(g1::QuadSpaceCls, x) -> Bool

Return if `g1` represents `x`.

Note that any quadratic space represents `0`.
"""
function represents(g1::QuadSpaceCls, x)
  K = base_ring(g1)
  x = K(x)
  if x == 0
    return true
  end
  q = quadratic_space(K, matrix(K, 1, 1, [x]))
  g2 = isometry_class(q)
  return represents(g1, g2)
end

function _common_hasse_support(g1,g2,d)
  K = base_ring(g1)
  P = union(Set(keys(g1.LGS)),Set(keys(g2.LGS)))
  if K == QQ
    sup = Set(ideal(ZZ, p) for p in support(d))
    push!(sup,ideal(ZZ, 2))
  else
    sup = support(d)
    for p in prime_ideals_over(maximal_order(K),2)
      push!(sup, p)
    end
  end
  P = union(P, sup)
  return P
end

# Direct sum
@doc raw"""
    direct_sum(g1::QuadSpaceCls, g2::QuadSpaceCls) -> QuadSpaceCls

Return the isometry class of the direct sum of two representatives.
"""
function direct_sum(g1::QuadSpaceCls{S,T,U},g2::QuadSpaceCls{S,T,U}) where {S,T,U}
  @req base_ring(g1) == base_ring(g2) "must be defined over the same base ring"
  K = base_ring(g1)
  g = class_quad_type(K)(K)
  g.dim = dim(g1) + dim(g2)
  g.dim_rad = dim_radical(g1) + dim_radical(g2)
  g.det = g1.det*g2.det
  g.LGS = Dict{T, LocalQuadSpaceCls{S, T, U}}()
  P =  _common_hasse_support(g1, g2, g.det)
  for p in P
    s = local_symbol(g1, p) + local_symbol(g2, p)
    if hasse_invariant(s)==-1
      g.LGS[p] = s
    end
  end
  g.signature_tuples = Dict{place_type(K), Tuple{Int,Int,Int}}()
  for p in real_places(K)
    s1 = g1.signature_tuples[p]
    s2 = g2.signature_tuples[p]
    g.signature_tuples[p] = (s1[1]+s2[1], s1[2]+s2[2], s1[3]+s2[3])
  end
  return g
end

@doc raw"""
    +(g1::QuadSpaceCls, g2::QuadSpaceCls) -> QuadSpaceCls

Return the isometry class of the direct sum of two representatives.
"""
function Base.:(+)(g1::QuadSpaceCls{S,T,U},g2::QuadSpaceCls{S,T,U}) where {S,T,U}
  return direct_sum(g1, g2)
end

function Base.:(-)(g1::QuadSpaceCls{S,T,U},g2::QuadSpaceCls{S,T,U}) where {S,T,U}
  @req base_ring(g1) == base_ring(g2) "must be defined over the same base ring"
  @req dim_radical(g2) == 0 "the second form must be regular to apply Witt cancellation"
  K = base_ring(g1)
  g = class_quad_type(K)(K)
  g.dim = dim(g1) - dim(g2)
  g.dim_rad = dim_radical(g1) - dim_radical(g2)
  g.det = g1.det*g2.det
  g.LGS = Dict{T, LocalQuadSpaceCls{S, T, U}}()
  P =  _common_hasse_support(g1,g2,g.det)
  for p in P
    s = local_symbol(g1, p) - local_symbol(g2, p)
    if hasse_invariant(s)==-1
      g.LGS[p] = s
    end
  end
  g.signature_tuples = Dict{Union{InfPlc,PosInf}, Tuple{Int,Int,Int}}()
  for p in real_places(K)
    s1 = g1.signature_tuples[p]
    s2 = g2.signature_tuples[p]
    t = (s1[1]-s2[1], s1[2]-s2[2], s1[3]-s2[3])
    #@req all(x>=0 for x in t) "the quadratic space g1 must represent g2"
    # we now allow virtual classes
    g.signature_tuples[p] = t
  end
  @hassert :Lattice 1 g + g2 == g1
  return g
end

# representatives
@doc raw"""
    representative(g::QuadSpaceCls) -> QuadSpace

Return a quadratic space in this isometry class.
"""
function representative(g::QuadSpaceCls)
  K = base_ring(g)
  k = dim_radical(g)
  n = dim(g)
  d = det_ndeg(g) # not det(g)
  d = numerator(d)*denominator(d)
  lgs = local_symbols(g)
  finite = [p for p in keys(lgs) if hasse_invariant(lgs[p])==-1]
  sig = signature_tuples(g)
  negative = Dict{place_type(K),Int}(Tuple{place_type(K), Int}[(a, b[3]) for (a, b) in sig])
  q = _quadratic_form_with_invariants(n-k,d,finite,negative)
  ker = zero_matrix(K, k, k)
  q = diagonal_matrix([q,ker])
  return quadratic_space(K, q)
end

@doc raw"""
    representative(g::QuadSpaceCls{QQField,ZZIdl,QQFieldElem})
    -> QuadSpace{QQField, QQMatrix}

Return a quadratic space in this isometry class.
"""
function representative(g::QuadSpaceCls{QQField,ZZIdl,QQFieldElem})
  K = base_ring(g)
  k = dim_radical(g)
  n = dim(g)
  d = det_ndeg(g)  # not det(g)
  d = numerator(d)*denominator(d)^2
  lgs = local_symbols(g)
  finite = [gen(p) for p in keys(lgs) if hasse_invariant(lgs[p])==-1]
  negative = signature_tuple(g)[3]
  q = _quadratic_form_with_invariants(n-k, d, finite, negative)
  ker = zero_matrix(K, k, k)
  q = diagonal_matrix([q,ker])
  return quadratic_space(K, q)
end


quadratic_space(g::QuadSpaceCls) = representative(g)
represents(q::QuadSpace, x::QuadSpace) = represents(isometry_class(q), isometry_class(x))
represents(q::QuadSpace, x) = represents(isometry_class(q), x)
