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

@doc Markdown.doc"""
    quadratic_space(K::NumField, n::Int) -> QuadSpace

Create the quadratic space over `K` with dimension `n` and Gram matrix
equal to the identity matrix.
"""
function quadratic_space(K::Field, n::Int)
  G = identity_matrix(K, n)
  return QuadSpace(K, G)
end

@doc Markdown.doc"""
    quadratic_space(K::NumField, G::Int) -> QuadSpace

Create the quadratic space over `K` with Gram matrix `G`.
The matrix `G` must be square and symmetric.
"""
function quadratic_space(K::Field, G::MatElem)
  return QuadSpace(K, G)
end

################################################################################
#
#  Predicates
#
################################################################################

isquadratic(V::QuadSpace) = true

ishermitian(V::QuadSpace) = true

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

# TODO: Make this non-allocating using an additonal temporary vector
function _inner_product(V, v, w)
  mv = matrix(base_ring(V), 1, nrows(V), v)
  mw = matrix(base_ring(V), ncols(V), 1, w)
  return (mv * V * mw)[1, 1]
end

inner_product(V::QuadSpace, v::Vector, w::Vector) = _inner_product(gram_matrix(V), v, w)

################################################################################
#
#  Diagonalization
#
################################################################################

function diagonal(V::QuadSpace)
  D, _ = _gram_schmidt(gram_matrix(V), involution(V))
  return diagonal(D)
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

@doc Markdown.doc"""
    hasse_invariant(V::QuadSpace, p::Union{InfPlc, NfOrdIdl}) -> Int

Returns the Hasse invariant of the quadratic space `V` at `p`. This is equal
to the product of local Hilbert symbols $(a_i, a_j)_p$, $i < j$, where $V$ is
isometric to $\langle a_1,\dotsc,a_n\rangle$.
"""
function hasse_invariant(V::QuadSpace, p)
  return _hasse_invariant(diagonal(V), p)
end

# This can be refactored to operate on the diagonal of a gram schmidt basis and
# the gram matrix.
# (Probably only on the diagonal of a gram schmidt basis)
function witt_invariant(L::QuadSpace, p::NfOrdIdl)
  h = hasse_invariant(L, p)
  F = gram_matrix(L)
  dett = det(F)
  K = base_ring(L)
  ncolsFmod8 = mod(ncols(F), 8)
  if ncolsFmod8 == 3 || ncolsFmod8 == 4
    c = -dett
  elseif ncolsFmod8 == 5 || ncolsFmod8 == 6
    c = K(-1)
  elseif ncolsFmod8 == 7 || ncolsFmod8 == 0
    c = dett
  else
    c = K(1)
  end
  return h * hilbert_symbol(K(-1), c, p)
end

# di = determinant
# wi = witt invariant
# ni = rank
# Lam p. 117
function _witt_of_orthgonal_sum(d1, w1, n1, d2, w2, n2, p)
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

  if n1 % 2 == n2 % 2
    w3 = w1 * w2 * hilbert_symbol(disc1, disc2, p)
  elseif n1 % 2 == 1
    w3 = w1 * w2 * hilbert_symbol(-disc1, disc2, p)
  else
    @assert n2 % 2 == 1
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
  if iscomplex(p)
    return 1
  end

  h = hasse_invariant(L, p)
  F = gram_matrix(L)
  dett = det(F)
  K = base_ring(L)
  ncolsFmod8 = mod(ncols(F), 8)
  if ncolsFmod8 == 3 || ncolsFmod8 == 4
    c = -dett
  elseif ncolsFmod8 == 5 || ncolsFmod8 == 6
    c = K(-1)
  elseif ncolsFmod8 == 7 || ncolsFmod8 == 0
    c = dett
  else
    c = K(1)
  end
  @assert !iszero(c)
  if isnegative(c, p)
    return -h
  else
    return h
  end
end

@doc Markdown.doc"""
    witt_invariant(V::QuadSpace, p::Union{InfPlc, NfOrdIdl}) -> Int

Returns the Witt invariant of the quadratic space `V` at `p`.

See [Definition 3.2.1, Kir16].
"""
witt_invariant(V::QuadSpace, p)

################################################################################
#
#  Local equivalence
#
################################################################################

function isequivalent(L::QuadSpace, M::QuadSpace, p::NfOrdIdl)
  GL = gram_matrix(L)
  GM = gram_matrix(M)
  if GL == GM
    return true
  end

  return rank(GL) == rank(GM) &&
         islocal_square(det(GL) * det(GM), p) &&
         hasse_invariant(L, p) == hasse_invariant(M, p)
end

function isequivalent(L::QuadSpace, M::QuadSpace, p::InfPlc)
  if rank(L) != rank(M)
    return false
  end

  if iscomplex(p)
    return true
  end

  DL = diagonal(L)
  DM = diagonal(M)
  return count(x -> isnegative(x, p), DL) == count(x -> isnegative(x, p), DM)
end

################################################################################
#
#  Quadratic form with given invariants
#
################################################################################

function _quadratic_form_invariants(M::fmpq_mat; minimal = true)
  G, _ = _gram_schmidt(M, identity)
  D = diagonal(G)
  sup = fmpz[]
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
  push!(sup, fmpz(2))
  sup = unique!(sup)
  F = Dict{fmpz, Int}()
  for p in sup
    e = _hasse_invariant(D, p)
    if e == -1 | !minimal
      F[p] = e
    end
  end
  I = [ (inf, count(x -> x < 0, D)) ]
  nu = numerator(prod(D))
  de = denominator(prod(D))
  return squarefree_part(de * nu), F, I
end

function _quadratic_form_invariants(M; minimal = true)
  return _quadratic_form_invariants(M, maximal_order(base_ring(M)), minimal = minimal)
end

function _quadratic_form_invariants(M, O; minimal = true)
  G, _ = _gram_schmidt(M, identity)
  D = diagonal(G)
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
  I = [ (P, count(x -> isnegative(x, P), D)) for P in real_places(K) ];
  return reduce(*, D, init = one(K)), F, I
end

@doc Markdown.doc"""
    invariants(M::QuadSpace)
          -> FieldElem, Dict{NfOrdIdl, Int}, Vector{Tuple{InfPlc, Int}}

Returns a triple `(d, H, I)` of invariants of `M`, which determine the
equivalence class completely. The element `d` is the determinant of a Gram
matrix, `H` contains the non-trivial Hasse invariants and `I` contains for
each real place the negative index of inertia.

Note that `d` is determined only modulo squares.
"""
invariants(V::QuadSpace) = _quadratic_form_invariants(gram_matrix(V))

################################################################################
#
#  Global equivalence
#
################################################################################

@doc Markdown.doc"""
    isequivalent(M::QuadSpace, L::QuadSpace) -> Bool

Tests if `M` and `L` are equivalent.
"""
function isequivalent(M::QuadSpace, L::QuadSpace)
  if gram_matrix(M) == gram_matrix(L)
    return true
  end
  d1, H1, I1 = invariants(M)
  d2, H2, I2 = invariants(L)
  return I1 == I2 && H1 == H2 && issquare(d1 * d2)[1]
end

################################################################################
#
#  Quadratic form with given invariants
#
################################################################################

# The following is over Q
function _quadratic_form_with_invariants(dim::Int, det::fmpz,
                                         finite::Vector{fmpz}, negative::Int)
#{Computes a quadratic form of dimension Dim and determinant Det that has Hasse invariants -1 at the primes in Finite.
 #The number of negative entries of the real signature is given in Negative}
  @assert dim >= 1
  @assert !iszero(det)
  @assert negative in 0:dim

  sign(det) != (-1)^(negative % 2) && throw(error("Real place information does not match the sign of the determinant"))

  if dim == 1
    !isempty(finite) && throw(error("Impossible Hasse invariants"))
    return matrix(FlintQQ, 1, 1, fmpz[det])
  end
 
  finite = unique(finite)
  @assert all(isprime(p) for p in finite)

  if dim == 2
    ok = all(!islocal_square(-det, p) for p in finite)
    if !ok
      q = [p for p in finite if islocal_square(-det, p)][1]
      throw(error("A binary form with determinant $det must have Hasse invariant +1 at the prime $q"))
    end
  end

  # product formula check
  
  !iseven((negative % 4 >= 2 ? 1 : 0) + length(finite)) && throw(error("The number of places (finite or infinite) with Hasse invariant -1 must be even"))

  # reduce the number of bad primes
  det = squarefree_part(det)

  dim0 = dim
  det0 = det
  finite0 = copy(finite)
  negative0 = negative

#  // Pad with ones
  k = max(0, dim - max(3, negative))
  D = ones(Int, k)
  dim = dim - k

#  // Pad with minus ones
  if dim >= 4
    @assert dim == negative
    k = dim - 3
    d = (-1)^k
    f = (k % 4 >= 2) ? Set(fmpz[2]) : Set(fmpz[])
    PP = append!(fmpz[p for (p, e) in factor(2 * det)], finite)
    PP = unique!(PP)
    finite = fmpz[ p for p in PP if hilbert_symbol(d, -det, p) * (p in f ? -1 : 1) * (p in finite ? -1 : 1) == -1]
    finite = unique!(finite)
    D = append!(D, Int[-1 for i in 1:k])
    det = isodd(k) ? -det : det
    dim = 3
    negative = 3
  end

  # ternary case
  if dim == 3
#    // The primes at which the form is anisotropic
    PP = append!(fmpz[p for (p, e) in factor(2 * det)], finite)
    PP = unique!(PP)
    PP = filter!(p -> hilbert_symbol(-1, -det, p) != (p in finite ? -1 : 1), PP)
#    // Find some a such that for all p in PP: -a*Det is not a local square
#    // TODO: Find some smaller a?! The approach below is very lame.
    a = prod(det % p == 0 ? one(FlintZZ) : p for p in PP)
    if negative == 3
      a = -a
      negative = 2
    end

    PP = append!(fmpz[p for (p, e) in factor(2 * det * a)], finite)
    PP = unique!(PP)
    finite = fmpz[ p for p in PP if hilbert_symbol(a, -det, p) * (p in finite ? -1 : 1) == -1]
    det = squarefree_part(det * a)
    dim = 2
    push!(D, a)
  end

#  // The binary case
  a = _find_quaternion_algebra(fmpq(-det), finite, negative == 2 ? PosInf[inf] : PosInf[])
  Drat = map(FlintQQ, D)
  Drat = append!(Drat, fmpq[a, squarefree_part(FlintZZ(det * a))])

  M = diagonal_matrix(Drat)
  
  d, f, n = _quadratic_form_invariants(M)

  @assert dim0 == length(Drat)
  @assert d == det0
  @assert issetequal(collect(keys(f)), finite0)
  @assert n[1][2] == negative0
  return M
end

function _quadratic_form_with_invariants(dim::Int, det::fmpq,
                                         finite::Vector{fmpz}, negative::Int)
  _det = numerator(det) * denominator(det)
  return _quadratic_form_with_invariants(dim, _det, finite, negative)
end

#{Computes a quadratic form of dimension Dim and determinant Det that has Hasse invariants -1 at the primes in Finite.
# The number of negative entries of the i-th real signature is given in Negative[i]}
function _quadratic_form_with_invariants(dim::Int, det::nf_elem, finite::Vector, negative::Dict{InfPlc, Int})
  @assert dim >= 1
  @assert !iszero(det)
  K = parent(det)
  inf_plcs = real_places(K)
  @assert length(inf_plcs) == length(negative)
  # All real places must be present
  @assert all(Bool[0 <= c <= dim for (_, c) in negative])
  # Impossible negative entry at plc
  @assert all(sign(det, p) == (-1)^(negative[p]) for p in inf_plcs)
  # Information at the real place plc does not match the sign of the determinant

  if dim == 1
    @assert isempty(finite) # Impossible Hasse invariants
    return matrix(K, 1, 1, nf_elem[det])
  end

  local OK::order_type(K)

  if !isempty(finite)
    OK = order(finite[1])
    @assert ismaximal(OK)
  else
    OK = maximal_order(K)
  end

  finite = unique(finite)

  # Finite places check

  if dim == 2
    ok = all(!islocal_square(-det, p) for p in finite)
    if !ok
      q = eltype(finite)[p for p in finite if islocal_square(-det, p)][1]
      throw(error("A binary form with determinant $det must have Hasse invariant +1 at the prime $q"))
    end
  end

  @assert iseven(length([ p for (p, n) in negative if n % 4 >= 2]) + length(finite))
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

  k = max(0, dim - max(3, maximum(values(negative))))
  D = elem_type(K)[one(K) for i in 1:k]
  dim = dim - k
  local D2::Vector{nf_elem}
  local D::Vector{nf_elem}

  if dim >= 4
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
      #@assert all(Bool[sign(x, V[i]) == _signs[i] for i in 1:length(V)])
      let negative = negative, dim = dim
        k = minimum(vcat(Int[dim - 3], Int[s[p] == 1 ? (dim - c) : c for (p, c) in negative]))
      end
      D2 = append!(D2, elem_type(K)[x for i in 1:k])
      dim = dim - k
      for (p, n) in negative
        if s[p] == -1
          negative[p] = negative[p] - k
        end
      end
    end

    local _d::nf_elem
    local _f::Dict{NfAbsOrdIdl{AnticNumberField,nf_elem},Int64}
    _d, _f = _quadratic_form_invariants(diagonal_matrix(D2))

    PP = append!(support(K(2), OK), finite)
    PP = unique!(PP)
    local _finite::Vector{ideal_type(OK)}
    let finite = finite
      _finite = ideal_type(OK)[ p for p in PP if hilbert_symbol(_d, -det, p) * (haskey(_f, p) ? -1 : 1) * (p in finite ? -1 : 1) == -1]
    end
    finite = _finite

    D = append!(D, D2)

    det::nf_elem = det * _d
#    # TODO: reduce det modulo squares
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
    S = Int[ negative[p] == 0 ? s[p] : -s[p] for p in idx]
    if length(PP) > 0
      b = _weak_approximation_coprime(idx, S, prod(PP))
      @assert iscoprime(b * OK, prod(PP))
    else
      b = _weak_approximation_coprime(idx, S, 1 * OK)
    end
    a = a * b

#    // Adjust invariants for the last time:
    s = signs(a)
    for p in InfPlc[p for (p,c) in negative if s[p] < 0]
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

  d, f, n = _quadratic_form_invariants(M, OK)
  @assert dim0 == length(D)
  @assert issquare(d * det0)[1]
  @assert issetequal(collect(keys(f)), finite0)
  @assert issetequal(n, collect((p, n) for (p, n) in negative0))

  return M
end

################################################################################
#
#  Isotropic
#
################################################################################

isisotropic(V::QuadSpace, p::InfPlc) = _isisotropic(V, p)

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
    return islocal_square(-d, p)
  elseif n == 3
    return _hasse_invariant(D, p) == hilbert_symbol(K(-1), -d, p)
  elseif n == 4
    return !islocal_square(d, p) || (_hasse_invariant(D, p) == hilbert_symbol(K(-1), K(-1), p))
  else
    return true
  end
end

function isisotropic(V::QuadSpace, p)
  @assert base_ring(V) == nf(order(p))
  d = det(V)
  n = rank(V)
  K = base_ring(V)
  if d == 0
    return true
  elseif n <= 1
    return false
  elseif n == 2
    return islocal_square(-d, p)
  elseif n == 3
    return hasse_invariant(V, p) == hilbert_symbol(K(-1), K(-1), p)
  elseif n == 4
    return !islocal_square(d, p) || (hasse_invariant(V, p) == hilbert_symbol(K(-1), K(-1), p))
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
# p is the prime idela
function _can_locally_embed(n::Int, da, ha::Int, m::Int, db, hb::Int, p)
  de = m - n
  if de == 0
    return islocal_square(da * db, p) && ha == hb
  elseif de == 1
    return ha * hilbert_symbol(da * db, da, p) == hb
  elseif de == 2 && islocal_square(-da * db, p)
    # Test if U \perp H \cong V
    # U has Hasse invariant 1
    return islocal_square(-da * db, p) && da * hilbert_symbol(da, -1, p) == db
  else
    return true
  end
end

function can_locally_embed(U::QuadSpace, V::QuadSpace, p)
  n, da, ha = rank(U), det(U), hasse_invariant(U, p)
  m, db, hb = rank(V), det(V), hasse_invariant(V, p)
  return _can_locally_embed(n, da, ha, m, db, hb, p)
end

################################################################################
#
#  Isometry computation
#
################################################################################

function _solve_conic(a::Integer, b::Integer, c::Integer)
  _solve_conic(fmpq(a), fmpq(b), fmpq(c))
end

function _solve_conic(a, b, c, u, v)

  K = parent(a) 
	@assert !iszero(a)
	@assert !iszero(b)
	@assert !iszero(c)

	fl, z = ispower(-b//a, 2)
	if fl
    x, y, z = z, K(1), K(0)
    @goto finish
  end

	fl, z = ispower(-c//a, 2)
	if fl
    x, y, z = z, K(0), K(1)
    @goto finish
  end

  Kx, x = PolynomialRing(K, "x", cached = false)
  d = -b//a
  den = denominator(d)
  L, y = number_field(x^2 - d * den^2)
  _Ls, _LstoL = simplify(L)
  fl, _n = isnorm(L, -c//a)
  if L isa AnticNumberField
    n = evaluate(_n)
  else
    n = _n
  end
  if fl
    x, y, z = coeff(n, 0), coeff(n, 1) * den, K(1)
    @goto finish
  end

  return false, a, a, a, u, u, u

  @label finish

  @assert x^2 * a + y^2 * b + z^2 * c == 0

  # Cremona, Conic paper
  # x = Q1(U, V) = ax0U^2 + 2by0UV − bx0V^2
  # y = Q2(U, V) = −ay0U^2 + 2ax0UV + by0V^2
  # z = Q3(U, V) = az0U^2 + bz0V^2

  q1 = a * x * u^2 + 2 * b * y * u * v - b * x * v^2
  q2 = -a * y * u^2 + 2*a*x*u*v + b*y*v^2
  q3 = a*z*u^2 + b*z*v^2

  @assert a * q1^2 + b * q2^2 + c * q3^2 == 0

  return true, x, y, z, q1, q2, q3
end

function _isisometric_with_isometry(a1, a2, b1, b2)
  # I assume that they are isometric ...
  #
  # I want to find an isometry from (a1, a2) to (b1, b2)
  # Let us call the matrix (a b; c d)
  # Then a^2 a_1 + b^2 a_2 = z1^2 * b1 and
  #
  
  K = parent(a1)
  Kuv, (u, v) = PolynomialRing(K, ["u", "v"], cached = false)
  
  fl, _aa, _bb, _z1, a, b, z1 = _solve_conic(a1, a2, -b1, u, v)
  @show _aa, _bb, _z1
  @assert fl
  
  # a^2 a_1 + b^2 a_2 = z2^2 b2 and
  fl, _cc, _dd, _z2, c, d, z2 = _solve_conic(a1, a2, -b2, u, v)
  @show _cc, _dd, _z2
  @assert fl

  @show _aa * _cc * a1 + _bb * _dd * a2

  @show a
  @show b
  @show c
  @show d
  
  # a * c * a1 + b * d * a2 = 0
  
  @show z1, z2

  s =  a * c * a1 + b * d * a2
  if s == 0
    return _aa, _bb, _cc, _dd, _z1, _z2
  end
  _a, _b, _c = coeff(s, u^4), coeff(s, u^2 * v^2), coeff(s, v^4)
  @show _a, _b, _c
  @show s
  if 4 * _a * _c == _b^2
    @assert 4*_c*s == (_b * u^2 + 2 * _c * v^2)^2
    # u^2//v^2 = -b/c
    fl, z = ispower(-(2 * _c)//_b, 2)
    # (u/v)^2 == -2c/b
    @assert fl
    v = one(K)
    u = z
    @assert b * u^2 + 2 * c * v^2 == 0
    @assert s(u, v) == 0
  end


  # This should be a parabola?
end

function _solve_conic_affine(A, B, a)
  # Solve Au^2 + B*w^2 = a
  # Gives one solutation

  # a = u^2 + B/A v^2 = (u - sqrt(B/A)v)(u + sqrt(B/A)) = N(u + v sqrt(B/A))

  K = parent(A)

  Kz, z = PolynomialRing(K, "z", cached = false)
  D = -B//A
  de = denominator(D)
  L, _ = number_field(z^2 - de^2 * D)
  fl, _n = isnorm(L, a//(A) * de^2)

  if !fl
    return false, zero(K), zero(K)
  end

  if L isa AnticNumberField
    n = evaluate(_n)
  else
    n = _n
  end

  @assert norm(n) == a//(A) * de^2

  u1, w1 = coeff(n, 0)//de, coeff(n, 1)

  @assert u1^2 * A + w1^2 * B == a

  return true, u1, w1
end

function _solve_conic_affine(A, B, a, t)
  # Solve Au^2 + B*w^2 = a
  # Gives one solutation and a parametrization
  # This assumes that a solution exists!

  # a = u^2 + B/A v^2 = (u - sqrt(B/A)v)(u + sqrt(B/A)) = N(u + v sqrt(B/A))

  K = parent(A)

  Kz, z = PolynomialRing(K, "z", cached = false)
  D = -B//A
  de = denominator(D)
  L, _ = number_field(z^2 - de^2 * D)
  fl, _n = isnorm(L, a//(A) * de^2)

  @assert fl

  if L isa AnticNumberField
    n = evaluate(_n)
  else
    n = _n
  end

  @assert norm(n) == a//(A) * de^2

  u1, w1 = coeff(n, 0)//de, coeff(n, 1)

  @assert u1^2 * A + w1^2 * B == a
  u = (-A * u1 + B * t^2 * u1 - 2 * B * t * w1)//(A + B * t^2)
  w = (-2 * A * t * u1   + A * w1 - B * t^2 * w1)//(A + B * t^2)

  @assert u^2 * A + w^2 * B == a

  return true, u1, w1, u, w
end

# Return true, T such that T * [A 0; 0 B] T^t = [a 0; 0 b] or false, 0 if no such T exists.
function _isisometric_with_isometry_dan(A, B, a, b)
  K = parent(A)
  
  Kkt, (k, t) = PolynomialRing(K, ["k", "t"], cached = false)

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

  t0 = K(1)
  @assert !iszero(A + B * t0^2)

  middle = A * u * v + B * s * w

  @assert lin^2 - sq == junk * middle

  _sq = sq(0, t0)

  fl, rt = ispower(_sq, 2)

  if !fl
    return false, zero_matrix(K, 0, 0)
  end

  k0 = (rt + (-2 * A^2 * B * s3 * u1 +  2 * A * B^2 * s3 * t^2 * u1 - 4 * A^2 * B * t * u1 * v3 - 4 * A * B^2 * s3 * t * w1 + 2 * A^2 * B * v3 * w1 - 2 * A * B^2 * t^2 * v3 * w1))//((2 * (-2 * A^2 * B * s3 * t * u1 + A^3 * u1 * v3 - A^2 * B * t^2 * u1 * v3 + A^2 * B * s3 * w1 - A * B^2 * s3 * t^2 * w1 + 2 * A^2 * B * t * v3 * w1)))

  kk = numerator(k0)(0, t0)//denominator(k0)(0, t0)

  @assert !iszero(junk(kk, t0))
  @assert !iszero(B + A * kk^2)

  uu = numerator(u)(kk, t0)//denominator(u)(kk, t0)
  ww = numerator(w)(kk, t0)//denominator(w)(kk, t0)
  ss = numerator(s)(kk, t0)//denominator(s)(kk, t0)
  vv = numerator(v)(kk, t0)//denominator(v)(kk, t0)

  T = matrix(K, 2, 2, [uu, ww, vv, ss])
  D1 = diagonal_matrix([A, B])
  D2 = diagonal_matrix([a, b])
  @assert T * D1 * transpose(T) == D2

  return true, T
end

@doc Markdown.doc"""
    isisometric_with_isometry(V::QuadSpace, W::QuadSpace)

Returns wether $V$ and $W$ are isometric together with an isometry in case it
exists. The isometry is given as an invertible matrix $T$ such that
$T G_W T^t = G_V$, where $G_V$, $G_W$ are the Gram matrices.
"""
function isequivalent_with_isometry(V::QuadSpace, W::QuadSpace)
  if !isequivalent(V, W)
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

  @assert MV * GV * transpose(MV) == diagonal_matrix([A, B])
  @assert MW * GW * transpose(MW) == diagonal_matrix([a, b])

  fl, T = _isisometric_with_isometry_dan(A, B, a, b)
  @assert fl

  @assert T * DV * transpose(T) == DW

  # T * DV * T^t == DW
  # T * MV * GV * (T * MV)^t == MW * GW * MW^t
  # GV = MV^-1 * T^-1 * MW * GW * (MV^-1 * T^-1 * MW)^t

  T = inv(MV) * inv(T) * MW
  @assert T * GW * transpose(T) == GV
  return true,  T
end

################################################################################
#
#  Isotropic vector
#
################################################################################

_to_gf2(x) = x == 1 ? 0 : 1
#ToGF2:= func< a,b,p | HilbertSymbol(a,b,p) eq 1 select 0 else 1 >;
#SignGF2:= func< x, p | Evaluate(x, p) lt 0 select 1 else 0 >;
#MyFact:= func< R, d | Type(R) eq RngInt select FactorizationOfQuotient(Rationals() ! d) else Factorization(R*d) >;

# F must be symmetric

function _isisotropic_with_vector(F::MatrixElem)
  K = base_ring(F)
  _D, T = _gram_schmidt(F, identity, false)
  D = diagonal(_D)
  i = findfirst(==(zero(K)), D)
  if i isa Int
    return true, elem_type(K)[T[i, j] for j in 1:ncols(T)]
  end

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

  fl, y = issquare_with_root(-D[1]//D[2])
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
      @assert vma * F * transpose(vma) == 0
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

    R = maximal_order(K)
    P = ideal_type(R)[]
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
      signs = elem_type(V)[]
      L, mL = sunit_group_fac_elem(P)
      Q, mQ = quo(L, 2, false)
      for q in gens(Q)
        x = evaluate(mL(mQ\q))
        _v = append!(Int[_to_gf2(hilbert_symbol(-D[1] * D[2], x, p)) for p in P], Int[_to_gf2(hilbert_symbol(-D[3] * D[4], x, p)) for p in P])
        _v = append!(_v, Int[_to_gf2(sign(x, p)) for p in I])
        s = V(_v)
        fl, _ = haspreimage(mS, s) 
        if !fl
          push!(signs, s)
          push!(basis, x)
          S, mS = sub(V, signs, false)
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
          fl, _x = isprincipal(q * prod(P[i]^Int(c.coeff[i]) for i in 1:length(P)))
          x = elem_in_nf(_x)
          _v = append!(Int[_to_gf2(hilbert_symbol(-D[1] * D[2], x, p)) for p in P], Int[_to_gf2(hilbert_symbol(-D[3] * D[4], x, p)) for p in P])
          _v = append!(_v, Int[_to_gf2(sign(x, p)) for p in I])
          s = V(_v)
          if haspreimage(mS, s + target)[1]
            push!(basis, x)
            push!(signs, s)
            found = true
            break
          end
        end
      end

      FF = GF(2, cached = false)
      fl, expo = can_solve(matrix(FF, length(signs), length(_target), [ s.coeff[1, i] for s in signs, i in 1:length(_target)]), matrix(FF, 1, length(_target), _target), side = :left)
      @assert fl

      x = evaluate(FacElem(basis, map(fmpz, [lift(expo[1, i]) for i in 1:length(basis)])))
    end
    ok, v = _isisotropic_with_vector(diagonal_matrix([D[1], D[2], -x]))
    @assert ok
    ok, w = _isisotropic_with_vector(diagonal_matrix([D[3], D[4],  x]))
    @assert ok
    v = inv(v[3]) .* v
    w = inv(w[3]) .* w
    v = matrix(K, 1, 4, [v[1], v[2], w[1], w[2]]) * T
    @assert v * F * v' == 0
    return true, elem_type(K)[v[1, i] for i in 1:4]
  else
    # Dimension >= 5, we need to only take care of the real places
    ok = all(v -> _isisotropic(D, v), real_places(K))
    if !ok
      return false, elem_type(K)[]
    end

    # We need D[3..5] to yield both signs at every real place
    rlp = real_places(K)
    found = false
    for i in 1:length(D), j in (i + 1):length(D)
      if all(p -> sign(D[i], p) != sign(D[j], p), rlp)
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
        @assert isdiagonal(_D)
        D = diagonal(_D)
        break
      end
    end
    if !found
      fix = Int[]
      signs = Int[]
      for i in 1:length(rlp)
        s = sign(D[4], rlp[i])
        if s != sign(D[5], rlp[i])
          continue
        end
        if s == sign(D[4], rlp[i])
          _a = _real_weak_approximation(rlp[i], rlp[fix])
          a = inv(_a)
          j = findfirst(Bool[sign(D[j], rlp[i]) != s for j in 1:length(D)])::Int
          r = 0
          while true
            r += 1
            t = D[4] + a^(2*r)*D[j]
            if sign(t, rlp[i]) != s && all(sign(t, rlp[fix[k]]) == signs[k] for k in 1:length(fix))
              break
            end
          end
          b = -a^r * D[j]//D[4]
          v = [T[4, k] for k in 1:ncols(T)]
          for k in 1:ncols(T)
            T[4, k] = T[4, k] + a^r * T[j, k]
          end
          for k in 1:ncols(T)
            T[j, k] = T[j, k] + b * v[k]
          end
        end
        push!(fix, i)
        push!(signs, -s)
        _D = T * F * transpose(T)
        @assert isdiagonal(_D)
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

    R = maximal_order(K)
    P = ideal_type(R)[]
    X = Tuple{elem_type(K), elem_type(K)}[]
    M = ideal_type(R)[]
    for p in Set([ p for d in append!(nf_elem[K(2)], D) for p in support(d, R)])
      if _isisotropic(D[3:5], p)
        continue
      end
      
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
        k, h = ResidueField(order(p), p)
        hext = extend(h, K)
        y = pi^(div(V - V2, 2))
        yy = pi^(div(V - V1, 2))
        cnt = 1
        while true
          cnt += 1
          @assert cnt <= 1000
          x = (hext\rand(k)) * yy
          if _isisotropic(elem_type(K)[D[3], D[4], D[5], x^2 * D[1] + y^2 * D[2]], p)
            break
          end
        end
      end
      push!(X, (x, y))
      push!(P, p)
      V = valuation(x^2 * D[1] + y^2 * D[2], p) + 1
      if isdyadic(p)
        V = V + 2 * ramification_index(p)
      end
      @show p, V
      push!(M, p^V)
    end
    @assert length(P) != 0

    xx = elem_in_nf(crt([R(x[1]) for x in X], M))
    yy = elem_in_nf(crt([R(x[2]) for x in X], M))
    t = xx^2 * D[1] + yy^2 * D[2]
    ok, w = _isisotropic_with_vector(diagonal_matrix(elem_type(K)[D[3], D[4], D[5], t]))
    @assert ok
    @assert w[1]^2 * D[3] + w[2]^2 * D[4] + w[3]^2 * D[5] + w[4]^2 * t == 0
    w = inv(w[4]) .* w
    v = matrix(K, 1, ncols(T), append!(elem_type(K)[xx, yy, w[1], w[2], w[3]], [zero(K) for i in 1:(nrows(T) - 5)])) * T
    v = lcm(fmpz[denominator(v[1, i]) for i in 1:ncols(v)]) * v
    @assert v * F * transpose(v) == 0
    return true, elem_type(K)[v[1, i] for i in 1:ncols(v)]
  end
end

function _quadratic_form_decomposition(F::MatrixElem)
  # Decompose F into an anisotropic kernel, an hyperbolic space and its radical
  @req issymmetric(F) "Matrix must be symmetric"
  K = base_ring(F)
  r, Rad = left_kernel(F)
  @assert nrows(Rad) == r
  RadComp = _find_direct_sum(Rad)
  newF = RadComp * F * RadComp'
  H = similar(F, 0, ncols(F))
  CurBas = RadComp

  while true
    fl, HH = _find_hyperbolic_subspace(newF)
    if fl
      @assert iszero(sub(HH, 1:1, 1:ncols(HH)) * newF  * sub(HH, 1:1, 1:ncols(HH))')
      H = vcat(H, HH * CurBas)
      CurBas = _orthogonal_complement(newF, HH) * CurBas
      newF = CurBas * F * CurBas'
    else
      break
    end
  end

  @assert iseven(nrows(H))
  if nrows(H) > 0
    D = diagonal_matrix([matrix(K, 2, 2, [1, 0, 0, -1]) for i in 1:div(nrows(H), 2)])
    @assert isequivalent(quadratic_space(K, H * F * H'), quadratic_space(K, D))
  end

  @assert iszero(Rad * F * Rad')

  #H * F * H', CurBas * F * CurBas', Rad * F * Rad'
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
  o = F * vv'
  i = findfirst(j -> !iszero(o[j, 1]), 1:nrows(o))
  @assert i isa Int
  H = vcat(vv, zero_matrix(base_ring(F), 1, ncols(F)))
  H[2, i] = inv(o[i, 1])
  GG = H * F * H'

  if !iszero(GG[2, 2])
    al = -GG[2, 2]//2 
    for i in 1:ncols(H)
      H[2, i] = al * H[1, i] + H[2, i]
    end
    GG = H * F * H'
  end

  @assert iszero(GG[1, 1])
  @assert iszero(GG[2, 2])
  @assert isone(GG[1, 2])
  @assert isone(GG[2, 1])

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
  @assert nrows(B) + l == ncols(B)
  Z = zero_matrix(K, l, ncols(B))
  for i in 1:length(piv)
    Z[i, piv[i]] = one(K)
  end
  return Z
end

function _orthogonal_complement(F::MatrixElem, B::MatrixElem)
  r, R = left_kernel(F * transpose(B))
  @assert nrows(R) == r
  if !iszero(det(F))
    @assert nrows(R) + nrows(B) == nrows(F)
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

  _d1, _H1, _I1 = _quadratic_form_invariants(A1 * F * A1')
  _d2, _H2, _I2 = _quadratic_form_invariants(A2 * G * A2')

  if !(_I1 == _I2 && _H1 == _H2 && issquare(_d1 * _d2)[1])
    return false, F
  end

  @assert nrows(H1) == nrows(H2) && nrows(R1) == nrows(R2)

  X = zero_matrix(K, 0, ncols(F))
  Y = zero_matrix(K, 0, ncols(F))

  while nrows(A1) > 0
    GA1 = A1 * F * A1'
    GA2 = A2 * G * A2'
    ok, v = _isisotropic_with_vector(diagonal_matrix(GA1, -GA2))
    @assert ok
    n = div(length(v), 2)
    _x = matrix(K, 1, n, v[1:n])
    _y = matrix(K, 1, n, v[(n+1):2*n])
    @assert _x * GA1 * _x' == _y * GA2 *  _y'
    x = matrix(K, 1, n, v[1:n]) * A1
    y = matrix(K, 1, n, v[(n+1):2*n]) * A2
    @assert x * F * x' == y * G * y'
    X = vcat(X, x)
    Y = vcat(Y, y)
    @assert X * F * X' == Y * G * Y'
    _A1 = _orthogonal_complement(GA1, matrix(K, 1, n, v[1:n]))
    A1 = _A1 * A1
    _A2 = _orthogonal_complement(GA2, matrix(K, 1, n, v[(n + 1):2*n]))
    A2 = _A2 * A2
  end

  @assert X * F * X' == Y * G * Y'
  @assert H1 * F * H1' == H2  *  G * H2'

  M = inv(vcat(X, H1, R1)) * vcat(Y, H2, R2) 

  @assert M * G * M' == F

  return true, M
end

function isisometric_with_isometry(V::QuadSpace, W::QuadSpace)
  GV = gram_matrix(V)
  GW = gram_matrix(W)
  return _isisometric_with_isometry(GV, GW)
end

function _real_weak_approximation(s, I)
  K = NumberField(s)
  a = gen(K)
  while true
    x = simplest_inside(real(evaluate(a, s, 10)))
    a = 2 * (a - x)
    if all(t -> t == s || abs(evaluate(a, t)) >= 2, I)
      break
    end
  end
  @assert abs(evaluate(a, s)) < 1//2
  return a
end
