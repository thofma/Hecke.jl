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
    return hasse_invariant(L, p) == hilbert_symbol(K(-1), K(-1), p)
  elseif n == 4
    return !islocal_square(d, p) || (hasse_invariant(L, p) == hilbert_symbol(K(-1), K(-1), p))
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

function isisotropic(V::AbsSpace, p::InfPlc)
  n = rank(V)
  d = det(V)
  E = base_ring(L)
  if d == 0
    return true
  elseif n <= 1
    return false
  elseif iscomplex(p)
    return true
  else
    D = diagonal(V)
    return length(unique!([sign(evaluate(d, p)) for d in p])) == 2
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

function (K::AnticNumberField)(a::NfRelElem{nf_elem})
  K != base_field(parent(a)) && error("Cannot coerce")
  for i in 2:degree(parent(a))
    @assert coeff(a, i - 1) == 0
  end
  return coeff(a, 0)
end

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

