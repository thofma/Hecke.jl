export ambient_space, rank, gram_matrix, inner_product, involution, ishermitian, isquadratic, isregular,
       islocal_square, isequivalent, isrationally_equivalent, quadratic_space,
       hermitian_space, diagonal, invariants, hasse_invariant, witt_invariant, orthogonal_basis, fixed_field

################################################################################
#
#  Creation
#
################################################################################

################################################################################
#
#  Basic invariants
#
################################################################################

@doc Markdown.doc"""
    rank(V::AbsSpace) -> Int

Return the rank of the quadratic space `V`.
"""
rank(L::AbsSpace) = rank(L.gram)

@doc Markdown.doc"""
    dim(V::AbsSpace) -> Int

Return the dimension of the space `V`.
"""
dim(V::AbsSpace) = nrows(V.gram)

@doc Markdown.doc"""
    gram_matrix(V::AbsSpace) -> MatElem

Return the Gram matrix of `V`.
"""
gram_matrix(V::AbsSpace) = V.gram

# Once we have quaternion spaces the following makes more sense

@doc Markdown.doc"""
    base_ring(V::AbsSpace) -> NumField

Return the base field of `V`.
"""
base_ring(V::AbsSpace) = _base_algebra(V)

@doc Markdown.doc"""
    fixed_field(V::AbsSpace) -> NumField

Return the fixed field of `V`.
"""
fixed_field(::AbsSpace)

@doc Markdown.doc"""
    involution(V::AbsSpace) -> NumField

Return the involution of `V`.
"""
involution(V::AbsSpace)

################################################################################
#
#  Predicates
#
################################################################################

# TODO: Maybe cache this?
@doc Markdown.doc"""
    isregular(V::AbsSpace) -> Bool

Return whether `V` is regular, that is, if the Gram matrix
has full rank.
"""
function isregular(V::AbsSpace)
  return rank(V) == dim(V)
end

@doc Markdown.doc"""
    isquadratic(V::AbsSpace) -> Bool

Returns whether $V$ is a quadratic space.
"""
isquadratic(::AbsSpace)

@doc Markdown.doc"""
    ishermitian(V::AbsSpace) -> Bool

Returns whether $V$ is a Hermitian space.
"""
ishermitian(::AbsSpace)

################################################################################
#
#  Determinant and discriminant
#
################################################################################

function det(V::AbsSpace)
  d = det(gram_matrix(V))
  return fixed_field(V)(d)
end

@doc Markdown.doc"""
    det(V::AbsSpace) -> FieldElem

Returns the determinant of the space `V` as an element of the fixed field.
"""
det(::AbsSpace)

@doc Markdown.doc"""
    discriminant(V::AbsSpace) -> FieldElem

Returns the discriminant of the space `V` as an element of the fixed field.
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
  n = nrows(G)
  if mod(n, 4) == 0 || mod(n, 4) == 1
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
function _gram_schmidt(M::MatElem, a, nondeg = true)
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
            if nondeg
              error("Matrix is not of full rank")
            end
          else
            j = ok
            T[i, j] = 1 // (2 * F[j, i])
          end
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
#  Local equivalence
#
################################################################################

@doc Markdown.doc"""
    isequivalent(L::AbsSpace, M::AbsSpace, p::Union{InfPlc, NfOrdIdl}) -> Bool

Returns whether `L` and `M` are equivalent over the completion at `p`.
"""
isequivalent(L::AbsSpace, M::AbsSpace, p)

################################################################################
#
#  Definitness
#
################################################################################

# Returns 0 if V is not definite
# Returns an element a != 0 such that a * canonical_basis of V has
# positive Gram matrix
function _isdefinite(V::AbsSpace)
  K = fixed_field(V)
  R = maximal_order(K)
  if !istotally_real(K) || (ishermitian(V) && !istotally_complex(K))
    return zero(K)
  end
  D = diagonal(V)
  signs_to_consider = Tuple{InfPlc, Int}[]
  for v in real_places(K)
    S = Int[sign(d, v) for d in D]
    if length(unique(S)) != 1
      return zero(K)
    else
      push!(signs_to_consider, (v, S[1]))
    end
  end
  if length(signs_to_consider) == 1
    return K(signs_to_consider[1][2])
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

isisotropic(V::AbsSpace, p::InfPlc) = _isisotropic(V, p)

# this is badly written, no need to compute d
function _isisotropic(D::Vector{fmpq}, p::PosInf)
  n = length(D)
  if n <= 1
    return false
  end
  E = parent(D[1])
  d = reduce(*, D, init = one(E))
  if d == 0
    return true
  elseif n <= 1
    return false
  else
    return length(unique!(fmpq[sign(d) for d in D])) == 2
  end
end

# this is badly written, no need to compute d
function _isisotropic(D::Vector, p::InfPlc)
  n = length(D)
  if n <= 1
    return false
  end
  E = parent(D[1])
  d = reduce(*, D, init = one(E))
  if d == 0
    return true
  elseif n <= 1
    return false
  elseif iscomplex(p)
    return true
  else
    return length(unique!(Int[sign(d, p) for d in D])) == 2
  end
end

# this looks wrong
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
    return length(unique!(Int[sign(d, p) for d in D])) == 2
  end
end

################################################################################
#
#  Restriction of scalars
#
################################################################################

# TODO: Use absolute_coordinates 
function restrict_scalars(V::AbsSpace, K::FlintRationalField,
                                       alpha = one(base_ring(V)))
  E = base_ring(V)
  n = rank(V)
  d = absolute_degree(E)
  B = absolute_basis(E)
  v = elem_type(E)[zero(E) for i in 1:n]
  w = elem_type(E)[zero(E) for i in 1:n]
  G = zero_matrix(FlintQQ, d * n, d * n)
  r = 1
  c = 1
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
      r = r + 1
    end
  end

  return quadratic_space(FlintQQ, G), VecSpaceRes(E, rank(V))
end

################################################################################
#
#  Orthogonal complement
#
################################################################################

@doc Markdown.doc"""
    orthogonal_complement(V::AbsSpace, M::MatElem)

Given a space $V$ and a subspace $W$ with basis matrix $M$, returns a basis
matrix of the orthogonal complement of $W$.
"""
function orthogonal_complement(V::AbsSpace, M::MatElem)
  N = gram_matrix(V) * _map(transpose(M), involution(V))
  r, K = left_kernel(N)
  @assert r == nrows(K)
  return K
end

################################################################################
#
#  Orthogonal sum
#
################################################################################

# TODO: Make this a proper coproduct with injections?
function orthogonal_sum(V::QuadSpace, W::QuadSpace)
  @req base_ring(V) === base_ring(W) "Base fields must be equal"
  G = diagonal_matrix(gram_matrix(V), gram_matrix(W))
  return quadratic_space(base_ring(V), G)
end

function orthogonal_sum(V::HermSpace, W::HermSpace)
  @req base_ring(V) === base_ring(W) "Base fields must be equal"
  G = diagonal_matrix(gram_matrix(V), gram_matrix(W))
  return hermitian_space(base_ring(V), G)
end
