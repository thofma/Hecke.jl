export ambient_space, rank, gram_matrix, inner_product, involution,
       islocal_square, isequivalent, isrationally_equivalent, quadratic_space,
       hermitian_space, diagonal, invariants, hasse_invariant, witt_invariant, orthogonal_basis, fixed_field

################################################################################
#
#  Types and constructors
#
################################################################################

abstract type AbsSpace{S} end

abstract type AbsLat{S} end

mutable struct QuadSpace{S, T} <: AbsSpace{S}
  K::S
  gram::T
  @declare_other

  function QuadSpace(K::S, G::T) where {S, T}
    # I also need to check if the gram matrix is Hermitian
    if dense_matrix_type(elem_type(S)) === T
      z = new{S, T}(K, G)
    else
      try
        Gc = change_base_ring(K, G)
        if typeof(Gc) !== dense_matrix_type(elem_type(S))
          throw(error("Cannot convert entries of the matrix to the number field"))
        end
        z = new{S, dense_matrix_type(elem_type(S))}(K, Gc)
        return z
      catch e
        rethrow(e)
        throw(error("Cannot convert entries of the matrix to the number field"))
      end
    end
  end
end

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

mutable struct HermSpace{S, T, U, W} <: AbsSpace{S}
  E::S
  K::T
  gram::U
  involution::W
  @declare_other

  function HermSpace(E::S, gram::U) where {S, U}
    # I also need to check if the gram matrix is Hermitian
    if dense_matrix_type(elem_type(S)) === U
      gramc = gram
    else
      try
        gramc = change_base_ring(E, gram)
        if typeof(gramc) !== dense_matrix_type(elem_type(S))
          throw(error("Cannot convert entries of the matrix to the number field"))
        end
      catch e
        throw(error("Cannot convert entries of the matrix to the number field"))
      end
    end

    @assert degree(E) == 2
    A = automorphisms(E)
    a = gen(E)
    if A[1](a) == a
      involution = A[2]
    else
      involution = A[1]
    end

    K = base_field(E)

    z = new{S, typeof(K), dense_matrix_type(elem_type(S)), typeof(involution)}(E, K, gramc, involution)
    return z
  end
end

@doc Markdown.doc"""
    hermitian_space(K::NumField, n::Int) -> HermSpace

Create the Hermitian space over `K` with dimension `n` and Gram matrix equal to
the identity matrix. The number field `K` must be a quadratic extension, that
is, `degree(K) == 2` must hold.
"""
function hermitian_space(K::NumField, n::Int)
  G = identity_matrix(K, n)
  return HermSpace(K, G)
end

@doc Markdown.doc"""
    hermitian_space(K::NumField, G::MatElem) -> HermSpace

Create the Hermitian space over `K` with Gram matrix equal to the identity
matrix. The matrix `G` must be square and Hermitian with respect to the non-trivial
automorphism of `K`. The number field `K` must be a quadratic extension, that
is, `degree(K) == 2` must hold.
"""
function hermitian_space(K::NumField, G::MatElem)
  return HermSpace(K, G)
end

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

function Base.show(io::IO, V::HermSpace)
  print(io, "Hermitian space over\n")
  println(io, base_ring(V))
  println(io, "with Gram matrix")
  print(io, gram_matrix(V))
end

################################################################################
#
#  Basic invariants
#
################################################################################

@doc Markdown.doc"""
    isquadratic(V::AbsSpace) -> Bool

Returns whether $V$ is quadratic.
"""
isquadratic(V::AbsSpace)

isquadratic(V::QuadSpace) = true

isquadratic(V::HermSpace) = false

@doc Markdown.doc"""
    ishermitian(V::AbsSpace) -> Bool

Returns whether $V$ is hermitian.
"""
ishermitian(V::AbsSpace)

ishermitian(V::QuadSpace) = true

ishermitian(V::HermSpace) = false

@doc Markdown.doc"""
    rank(V::AbsSpace) -> Int

Return the rank of the space `V`.
"""
rank(L::AbsSpace) = nrows(L.gram)

@doc Markdown.doc"""
    dim(V::AbsSpace) -> Int

Return the dimension of the space `V`.
"""
dim(V::AbsSpace) = rank(V)

@doc Markdown.doc"""
    gram_matrix(V::AbsSpace) -> MatElem

Return the Gram matrix of `V`.
"""
gram_matrix(V::AbsSpace) = V.gram

# Once we have quaternion spaces the following makes more sense
_base_algebra(V::QuadSpace) = V.K

_base_algebra(V::HermSpace) = V.E

@doc Markdown.doc"""
    base_ring(V::AbsSpace) -> NumField

Return the base field of `V`.
"""
base_ring(V::AbsSpace) = _base_algebra(V)

involution(V::QuadSpace) = identity

involution(V::HermSpace) = V.involution

@doc Markdown.doc"""
    fixed_field(V::AbsSpace) -> NumField

Return the fixed field of `V`.
"""
fixed_field(::AbsSpace)

fixed_field(V::QuadSpace) = base_ring(V)

fixed_field(V::HermSpace) = V.K

@doc Markdown.doc"""
    involution(V::AbsSpace) -> NumField

Return the involution of `V`.
"""
involution(V::AbsSpace)

# Maybe cache this

@doc Markdown.doc"""
    isregular(V::AbsSpace) -> Bool

Return whether `V` is regular, that is, if the Gram matrix
has full rank.
"""
function isregular(V::AbsSpace)
  G = gram_matrix(V)
  return rank(G) == nrows(G)
end

################################################################################
#
#  Determinant and discriminant
#
################################################################################

function det(V::QuadSpace)
  return det(gram_matrix(V))
end

function det(V::HermSpace)
  d = det(gram_matrix(V))
  @assert all(iszero(coeff(d, i)) for i in 1:degree(base_ring(V)) - 1)
  return coeff(d, 0)
end

@doc Markdown.doc"""
    det(V::AbsSpace) -> FieldElem

Returns the determinant of the space `V`.

In case `V` is Hermitian, the result is an element of the fixed field.
"""
det(::AbsSpace)

@doc Markdown.doc"""
    discriminant(V::AbsSpace) -> FieldElem

Returns the discriminant of the space `V`.

In case `V` is Hermitian, the result is an element of the "smaller field".
"""
function discriminant(V::AbsSpace)
  d = det(V)
  n = mod(rank(V), 4)
  if n == 0 || n == 1
    return d
  else
    return -d
  end
end

function _discriminant(G)
  d = det(G)
  if n == 0 || n == 1
    return d
  else
    return -d
  end
end

################################################################################
#
#  Computing inner products
#
################################################################################

@doc Markdown.doc"""
    gram_matrix(V::AbsSpace, M::MatElem) -> MatElem

Returns the gram matrix of the rows of `M`.
"""
function gram_matrix(V::AbsSpace{T}, M::MatElem{S}) where {S, T}
  if S === elem_type(T)
    return M * gram_matrix(V) * transpose(_map(M, involution(V)))
  else
    Mc = change_base_ring(base_ring(V), M)
    return Mc * gram_matrix(V) * transpose(_map(Mc, involution(V)))
  end
end

@doc Markdown.doc"""
    gram_matrix(V::AbsSpace, S::Vector{Vector}) -> MatElem

Returns the gram matrix of the sequence `S`.
"""
function gram_matrix(V::AbsSpace{T}, S::Vector{Vector{U}}) where {T, U}
  m = zero_matrix(base_ring(V), length(S), rank(V))
  for i in 1:length(S)
    if length(S[i]) != rank(V)
      throw(error("Vectors must be of length $(rank(V))"))
    end
    for j in 1:rank(V)
      m[i, j] = S[i][j]
    end
  end
  return gram_matrix(V, m)
end

function _inner_product(V, v, w)
  mv = matrix(base_ring(V), 1, nrows(V), v)
  mw = matrix(base_ring(V), ncols(V), 1, w)
  return (mv * V * mw)[1, 1]
end

function _inner_product(G, v, w, involution)
  return _inner_product(G, v, [involution(x) for x in w])
end

inner_product(V::QuadSpace, v::Vector, w::Vector) = _inner_product(gram_matrix(V), v, w)

inner_product(V::HermSpace, v::Vector, w::Vector) = _inner_product(gram_matrix(V), v, w, involution(V))

@doc Markdown.doc"""
    inner_product(V::AbsSpace, v::Vector, w::Vector) -> FieldElem

Returns the inner product of `v` and `w` with respect to `V`.
"""
inner_product(V::AbsSpace, v::Vector, w::Vector)

################################################################################
#
#  Diagonalization
#
################################################################################

function diagonal(V::QuadSpace)
  D, _ = _gram_schmidt(gram_matrix(V), involution(V))
  return diagonal(D)
end

function diagonal(V::HermSpace)
  D, _ = _gram_schmidt(gram_matrix(V), involution(V))
  return [ coeff(d, 0) for d in diagonal(D) ]
end

@doc Markdown.doc"""
    orthogonal_basis(V::AbsSpace) -> MatElem

Returns a matrix `M`, such that the rows of `M` form an orthgonal basis of `V`.
"""
function orthogonal_basis(V::AbsSpace)
  _, B = _gram_schmidt(gram_matrix(V), involution(V))
  return B
end

@doc Markdown.doc"""
    diagonal(V::AbsSpace) -> Vector{FieldElem}

Returns a vector of elements $a_1,\dotsc,a_n$ such that `V` is isometric to
the diagonal space $\langle a_1,\dotsc,a_n \rangle$.

The elements will be contained in the fixed field of `V`.
"""
diagonal(V::AbsSpace)

################################################################################
#
#  Gram-Schmidt
#
################################################################################

# Clean this up
function _gram_schmidt(M::MatElem, a)
  F = deepcopy(M)
  K = base_ring(F)
  n = nrows(F)
  S = identity_matrix(K, n)
  okk = isdiagonal(F)
  if !okk
    for i in 1:n
      if iszero(F[i,i])
        T = identity_matrix(K, n)
        ok = 0
        for j in (i + 1):n
          if !iszero(F[j, j])
            ok = j
            break
          end
        end
        #ok = findfirst(j -> !iszero(F[j, j]), (i + 1):n)
        if ok != 0 # ok !== nothing
          #j = ok + i # findfirst gives the index
          j = ok
          T[i,i] = 0
          T[j,j] = 0
          T[i,j] = 1
          T[j,i] = 1
        else
          ok = 0
          for j in (i + 1):n
            if !iszero(F[i, j])
              ok = j
              break
            end
          end
          if ok == 0
            error("Matrix is not of full rank")
          end
          #ok = findfirst(j -> !iszero(F[i, j]), (i + 1):n)
          #if ok === nothing
          #  error("Matrix is not of full rank")
          #end
          j = ok
          T[i, j] = 1 // (2 * F[j, i])
        end
        S = T * S
        F = T * F * transpose(_map(T, a))
      end
      T = identity_matrix(K, n)
      for j in (i + 1):n
        T[j, i] = divexact(-F[j, i], F[i, i])
      end
      F = T * F * transpose(_map(T, a))
      S = T * S
    end
    @assert isdiagonal(F)
  end
  return F, S
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

function hasse_invariant(L::HermSpace, p)
  throw(error("The space must be quadratic"))
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

function witt_invariant(L::HermSpace, p)
  throw(error("The space must be quadratic"))
end

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

  return rank(GL) == rank(GM) && islocal_square(det(GL) * det(GM), p) && hasse_invariant(L, p) == hasse_invariant(M, p)
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

# hermitian case

function isequivalent(L::HermSpace{AnticNumberField}, M::HermSpace{AnticNumberField}, p::fmpz)
  return _isequivalent(L, M, p)
end

function isequivalent(L::HermSpace, M::HermSpace, p::NfOrdIdl)
  return _isequivalent(L, M, p)
end

function _isequivalent(L::HermSpace, M::HermSpace, p)
  base_ring(L) != base_ring(M) && error("Both spaces must have the same base field")
  A = gram_matrix(L)
  B = gram_matrix(M)
  if A == B
    return true
  end

  if rank(L) != rank(M)
    return false
  end

  return islocal_norm(base_ring(L), det(L) * det(M), p)[1]
end

function isequivalent(L::HermSpace, M::HermSpace, P::InfPlc)
  if L == M
    return true
  end

  if iscomplex(P)
    return true
  end

  DL = diagonal(L)
  DM = diagonal(M)
  iL = count(d -> isnegative(d, P), DL)
  iM = count(d -> isnegative(d, P), DM)
  return iL == iM
end

@doc Markdown.doc"""
    isequivalent(L::AbsSpace, M::AbsSpace, p::Union{InfPlc, NfOrdIdl}) -> Bool

Returns whether `L` and `M` are equivalent over the completion at `p`.
"""
isequivalent(L::AbsSpace, M::AbsSpace, p)

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
  G, _ = _gram_schmidt(M, identity)
  D = diagonal(G)
  K = base_ring(M)
  O = maximal_order(K)
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
  return prod(D), F, I
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

function isequivalent(M::HermSpace, L::HermSpace)
  if gram_matrix(M) == gram_matrix(L)
    return true
  end

  if rank(M) != rank(L)
    return false
  end

  E = base_ring(M)
  # I could replace this with a islocal_norm at the ramified primes + primes
  # dividing right hand side
  return isnorm(E, det(M) * det(L))[1]
end

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
  return M;
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
  @assert all(c in 0:dim for (_, c) in negative)
  # Impossible negative entry at plc
  @assert all(sign(det, p) == (-1)^(negative[p]) for p in inf_plcs)
  # Information at the real place plc does not match the sign of the determinant

  if dim == 1
    @assert isempty(finite) # Impossible Hasse invariants
    return matrix(K, 1, 1, nf_elem[det])
  end

  if !isempty(finite)
    OK = maximal_order(K)
  else
    OK = oder(finite[1])
    @assert ismaximal(OK)
  end

  finite = unique(finite)

  # Finite places check

  if dim == 2
    ok = all(!islocal_square(-det, p) for p in finite)
    if !ok
      q = [p for p in finite if islocal_square(-det, p)][1]
      throw(error("A binary form with determinant $det must have Hasse invariant +1 at the prime $q"))
    end
  end

  @assert iseven(length([ p for (p, n) in negative if n % 4 >= 2]) + length(finite))
#    "The number of places (finite or infinite) with Hasse invariant -1 must be even";
#
#  // OK, a space with these invariants must exist.
#  // For final testing, we store the invariants.

  dim0 = dim
  det0 = det
  finite0 = copy(finite)
  negative0 = copy(negative)

  # det = _reduce_modulo_squares(det)

  k = max(0, dim - max(3, maximum(values(negative))))
  D = elem_type(K)[one(K) for i in 1:k]
  dim = dim - k

  if dim >= 4
#    // Pad with minus ones
    k = min(dim - 3, minimum(values(negative)))
    D2 = elem_type(K)[-one(K) for i in 1:k]
    dim = dim - k
    negative = Dict{InfPlc, Int}(p => (n - k) for (p, n) in negative)
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
      @show V, _signs

      x = _weak_approximation(V, _signs)
      @show x
      s = signs(x)
      @assert all(i -> sign(x, V[i]) == _signs[i], 1:length(V))
      k = minimum(vcat(Int[dim - 3], [s[p] == 1 ? (dim - c) : c for (p, c) in negative]))
      @show k
      D2 = append!(D2, elem_type(K)[x for i in 1:k])
      dim = dim - k
      for (p, n) in negative
        if s[p] == -1
          negative[p] = negative[p] - k
        end
      end
      @show negative
    end

    _d, _f = _quadratic_form_invariants(diagonal_matrix(D2))
    @show _d, _f

    PP = append!(support(K(2)), finite)
    PP = unique!(PP)
    finite = ideal_type(OK)[ p for p in PP if hilbert_symbol(_d, -det, p) * (haskey(_f, p) ? -1 : 1) * (p in finite ? -1 : 1) == -1]
    @show finite
    D = append!(D, D2)
    det = det * _d
    # TODO: reduce det modulo squares
  end

#  // The ternary case
  if dim == 3
    PP = append!(support(K(2)), finite)
    append!(PP, support(det))
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
      b = _weak_approximation_coprime(idx, S)
    end
    a = a * b

#    // Adjust invariants for the last time:
    s = signs(a)
    for p in InfPlc[p for (p,c) in negative if s[p] < 0]
      negative[p] = negative[p] - 1
    end
    PP = support(K(2))
    append!(PP, support(det))
    append!(PP, support(a))
    append!(PP, finite)
    PP = unique!(PP)
    finite = ideal_type(OK)[p for p in PP if hilbert_symbol(a, -det, p) * (p in finite ? -1 : 1) == -1]
    det = det * a
    # TODO: reduce det
    push!(D, a)
  end


#  // The binary case
  a = _find_quaternion_algebra(-det, finite, [p for (p, n) in negative if n == 2])
  push!(D, a)
  push!(D, det * a)
  M = diagonal_matrix(D)

  d, f, n = _quadratic_form_invariants(M)
  @assert dim0 == length(D)
  @assert issquare(d * det0)[1]
  @assert issetequal(collect(keys(f)), finite0)
  @assert issetequal(n, collect((p, n) for (p, n) in negative0))

  return M
end

################################################################################
#
#  Definitness
#
################################################################################

# TODO: Add this functionality for Hermitian spaces

# Returns 0 if V is not definite
# Returns an element a != 0 such that a * canonical_basis of V has
# positive Gram matrix
function _isdefinite(V::AbsSpace)
  K = base_ring(V)
  R = maximal_order(K)
  if !istotally_real(K) || (ishermitian(V) && !istotally_complex(K))
    return zero(R)
  end
  D = diagonal(V)
  signs_to_consider = Tuple{InfPlc, Int}[]
  for v in real_places(K)
    S = Int[sign(d, v) for d in D]
    if length(unique(S)) != 1
      return zero(R)
    else
      push!(signs_to_consider, (v, S[1]))
    end
  end
  if length(signs_to_consider) == 1
    return R(signs_to_consider[1][2])
  else
    return element_with_signs(K, signs_to_consider)
  end
end

function ispositive_definite(V::AbsSpace)
  E = base_ring(V)
  if isquadratic(V)
    K = E
  else
    K = base_field(E)
  end
  if !istotally_real(K)
    return false
  end
  D = diagonal(V)
  for d in D
    if !istotally_positive(d)
      return false
    end
  end
  return true
end

function isnegative_definite(V::AbsSpace)
  E = base_ring(V)
  if isquadratic(V)
    K = E
  else
    K = base_field(E)
  end

  if !istotally_real(K)
    return false
  end
  D = diagonal(V)
  for d in D
    if !istotally_positive(-d)
      return false
    end
  end
  return true
end

function isdefinite(V::AbsSpace)
  return ispositive_definite(V) || isnegative_definite(V)
end

################################################################################
#
#  Isotropic
#
################################################################################

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

function isisotropic(V::HermSpace, q)
  if nf(order(q)) == base_ring(V)
    p = minimum(q)
  else
    p = q
  end
  @assert fixed_field(V) == nf(order(p))
  r = rank(V)
  if r >= 3
    return true
  elseif r == 0
    return false
  end
  d = det(V)
  if r == 1
    return d == 0
  end
  return islocal_norm(base_ring(V), -d, p)
end

isisotropic(V::QuadSpace, p::InfPlc) = _isisotropic(V, p)

isisotropic(V::HermSpace, p::InfPlc) = _isisotropic(V, p)

function _isisotropic(V::AbsSpace, p::InfPlc)
  n = rank(V)
  d = det(V)
  E = base_ring(V)
  if d == 0
    return true
  elseif n <= 1
    return false
  elseif iscomplex(p)
    return true
  else
    D = diagonal(V)
    return length(unique!([sign(d, p) for d in D])) == 2
  end
end

function _islocally_hyperbolic_hermitian_detclass(rk, d, E, K, p)
  if isodd(rk)
    return false
  end
  if d == 1
    if iseven(div(rk, 2))
      return true
    else
      return islocal_norm(E, K(-1), p)
    end
  else
    if iseven(div(rk, 2))
      return false
    else
      return !islocal_norm(E, K(-1), p)
    end
  end
end

function islocally_hyperbolic(V::HermSpace, p)
  rk = rank(V)
  if isodd(rk)
    return false
  end
  return islocal_norm(base_ring(V), det(V) * (-1)^(div(rk, 2)), p)
end

################################################################################
#
#  Helper functions (sort them later)
#
################################################################################

function image(f::NfRelToNfRelMor{T, T}, I::NfRelOrdIdl{T, S}) where {T, S}
  #f has to be an automorphism!!!!
  O = order(I)
  @assert ismaximal(O) # Otherwise the order might change
  K = nf(O)

  B = absolute_basis(I)

  if I.is_prime == 1
    lp = prime_decomposition(O, minimum(I))
    for (Q, e) in lp
      if I.splitting_type[2] == e
        if all(b -> f(b) in Q, B)
          return Q
        end
      end
    end
  end

  pb = pseudo_basis(I)
  pm = basis_pmatrix(I)

  m = zero(matrix(pm))

  c = coefficient_ideals(pm)

  for i in 1:length(pb)
    cc = coordinates(O(f(pb[i][1])))
    for j in 1:length(cc)
      m[i, j] = cc[j]
    end
  end

  J = ideal(O, pseudo_matrix(m, c))

  if isdefined(I, :minimum)
    J.minimum = I.minimum
  end

  J.has_norm = I.has_norm

  if isdefined(I, :norm)
    J.norm = I.norm
  end

  if isdefined(I, :is_prime)
    J.is_prime = I.is_prime
  end

  if isdefined(I, :splitting_type)
    J.splitting_type = I.splitting_type
  end

  return J
end

function image(f::NfRelToNfRelMor{T, T}, I::NfRelOrdFracIdl{T, S}) where {T, S}
  #S has to be an automorphism!!!!
  O = order(I)
  @assert ismaximal(O) # Otherwise the order might change
  K = nf(O)

  pb = pseudo_basis(I)

  z = sum(b * (f(a) * O) for (a, b) in pb)
  return z
end

# An element is locally a square if and only if the quadratic defect is 0, that is
# the valuation is inf.
# (see O'Meara, Introduction to quadratic forms, 3rd edition, p. 160)
function islocal_square(a, p)
  return quadratic_defect(a, p) isa PosInf
end

function _map(a::AbstractAlgebra.MatrixElem, f)
  z = similar(a)
  for i in 1:nrows(a)
    for j in 1:ncols(a)
      z[i, j] = f(a[i, j])
    end
  end
  return z
end

# I think I need a can_change_base_ring version

function element_with_signs(K, D::Dict{InfPlc, Int})
  return _element_with_signs(K, D)
end

function _element_with_signs(K, D)
  OK = maximal_order(K)
  G, mG = carlos_units(OK)
  r = real_places(K)
  z = id(G)
  for (v, s) in D
    for i in 1:length(r)
      if s == 1
        ss = 0
      else
        ss = 1
      end

      if v == r[i]
        z = z + ss * G[i]
      end
    end
  end
  return mG(z)
end

function element_with_signs(K, P::Vector{InfPlc}, S::Vector{Int})
  return _element_with_signs(K, zip(P, S))
end

function element_with_signs(K, A::Vector{Tuple{InfPlc, Int}})
  return _element_with_signs(K, A)
end

function prime_ideals_up_to(O::NfRelOrd, n::Union{Int, fmpz})
  p = 2
  z = ideal_type(O)[]
  while p <= n
    lp = prime_decomposition(base_ring(O), p)
    for q in lp
      if norm(q[1]) > n
        continue
      else
        lq = prime_decomposition(O, q[1])
        for Q in lq
          if absolute_norm(Q[1]) <= n
            push!(z, Q[1])
          end
        end
      end
    end
    p = next_prime(p)
  end
  return sort!(z, by = a -> absolute_norm(a))
end

################################################################################
#
#  Restriction of scalars
#
################################################################################

function restrict_scalars(V::AbsSpace, K::Field = FlintQQ, alpha = one(base_ring(V)))
  E = base_ring(V)
  n = rank(V)
  d = absolute_degree(E)
  B = absolute_basis(E)
  v = elem_type(E)[zero(E) for i in 1:n]
  w = elem_type(E)[zero(E) for i in 1:n]
  G = zero_matrix(FlintQQ, d * n, d * n)
  r = 1
  c = 1
  indices = Vector{Tuple{Int, Int}}(undef, n * d)
  for i in 1:n
    for bi in 1:length(B)
      v[i] = B[bi]
      c = 1
      for j in 1:n
        for bj in 1:length(B)
          w[j] = B[bj]
          G[r, c] = trace(alpha * inner_product(V, v, w), FlintQQ)
          w[j] = zero(E)
          c = c + 1
        end
      end
      v[i] = zero(E)
      indices[r] = (i, bi)
      r = r + 1
    end
  end
  
  VabstoV = function(v)
    @assert length(v) == d * n
    z = Vector{elem_type(E)}(undef, n)
    for i in 1:n
      z[i] = zero(E)
    end
    for k in 1:(d * n)
      (i, j) = indices[k]
      z[i] = z[i] + v[k] * B[j]
    end
    return z
  end

  VtoVabs = function(w)
    z = Vector{fmpq}(undef, d * n)
    k = 1
    for i in 1:n
      y = w[i]
      for j in 1:d
        z[k] = absolute_coeff(y, j - 1)
        k = k + 1
      end
    end
    return z
  end

  return quadratic_space(FlintQQ, G), VabstoV, VtoVabs
end

# Careful, starts at 0!
function absolute_coeff(z::nf_elem, i)
  return coeff(z, i)
end

function absolute_coeff(z::NumFieldElem, i)
  d = absolute_degree(base_field(parent(z)))
  rowindex = fld(i, d)
  colindex = (i % d)
  return absolute_coeff(coeff(z, rowindex), colindex)
end

function absolute_basis(K::NumField)
  k = base_field(K)
  kabs = absolute_basis(k)
  res = elem_type(K)[]
  for b in basis(K)
    for bb in kabs
      push!(res, bb * b)
    end
  end
  return res
end

function absolute_basis(K::NumField{fmpq})
  return basis(K)
end

#

istotally_real(::FlintRationalField) = true

istotally_positive(x::fmpq) = x > 0

# This function is really slow...
function denominator(M::fmpq_mat)
  d = one(FlintZZ)
  for i in 1:nrows(M)
    for j in 1:ncols(M)
      d = lcm!(d, d, denominator(M[i, j]))
    end
  end
  return d
end

function _weak_approximation_coprime(IP, S, M)
  R = order(M)
  A, _exp, _log = infinite_primes_map(R, IP, M)

  t = (1 + _exp(A([ S[j] == 1 ? 0 : -1 for j in 1:length(IP)])))
  @assert all(i -> sign(t, IP[i]) == S[i], 1:length(IP))
  return t
end
