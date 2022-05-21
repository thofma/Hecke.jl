export ambient_space, rank, gram_matrix, inner_product, involution, ishermitian, is_quadratic, is_regular,
       is_local_square, is_isometric, is_rationally_isometric, is_isotropic, quadratic_space,
       hermitian_space, diagonal, invariants, hasse_invariant, witt_invariant, orthogonal_basis, fixed_field,
       restrict_scalars, orthogonal_complement

################################################################################
#
#  Maps
#
################################################################################

mutable struct AbsSpaceMor{D, T} <: Map{D, D, HeckeMap, AbsSpaceMor}
  header::MapHeader{D, D}
  matrix::T

  function AbsSpaceMor(V::D, W::D, B::T) where {D, T}
    z = new{D, T}()
    z.header = MapHeader{D, D}(V, W)
    z.matrix = B
    return z
  end
end

function hom(V::AbsSpace, W::AbsSpace, B::MatElem; check::Bool = false)
  @req base_ring(V) == base_ring(W) "Spaces must have the same base field"
  @req nrows(B) == dim(V) && ncols(B) == dim(W) """
  Dimension mismatch. Matrix ($(nrows(B))x$(ncols(B))) must be of
  dimensions $(dim(V))x$(dim(W)).
  """
  if check
    GV = gram_matrix(V)
    GW = gram_matrix(W)
    fl = B * GW * transpose(_map(B, involution(W))) == GV
    if !fl
      error("Matrix does not define a morphism of spaces")
    end
  end
  return AbsSpaceMor(V, W, B)
end

function image(f::AbsSpaceMor, v::Vector)
  V = domain(f)
  w = matrix(base_ring(V), 1, length(v), v) * f.matrix
  return vec(collect(w))
end

function compose(f::AbsSpaceMor, g::AbsSpaceMor)
  @req codomain(f) === domain(g) "incompatible morphisms"
  return hom(domain(f), codomain(g), f.matrix * g.matrix)
end

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

Return the rank of the space `V`.
"""
rank(L::AbsSpace) = rank(L.gram)

@doc Markdown.doc"""
    dim(V::AbsSpace) -> Int

Return the dimension of the space `V`.
"""
dim(V::AbsSpace) = nrows(V.gram)

@doc Markdown.doc"""
    gram_matrix(V::AbsSpace) -> MatElem

Return the Gram matrix of the space `V`.
"""
gram_matrix(V::AbsSpace) = V.gram

# Once we have quaternion spaces the following makes more sense

@doc Markdown.doc"""
    base_ring(V::AbsSpace) -> NumField

Return the algebra over which the space `V` is defined.
"""
base_ring(V::AbsSpace) = _base_algebra(V)

@doc Markdown.doc"""
    fixed_field(V::AbsSpace) -> NumField

Return the fixed field of the space `V`.
"""
fixed_field(::AbsSpace)

@doc Markdown.doc"""
    involution(V::AbsSpace) -> NumField

Return the involution of the space `V`.
"""
involution(V::AbsSpace)

################################################################################
#
#  Predicates
#
################################################################################

# TODO: Maybe cache this?
@doc Markdown.doc"""
    is_regular(V::AbsSpace) -> Bool

Return whether the space `V` is regular, that is, if the Gram matrix
has full rank.
"""
function is_regular(V::AbsSpace)
  return rank(V) == dim(V)
end

@doc Markdown.doc"""
    is_quadratic(V::AbsSpace) -> Bool

Return whether the space `V` is quadratic.
"""
is_quadratic(::AbsSpace)

@doc Markdown.doc"""
    ishermitian(V::AbsSpace) -> Bool

Return whether the space `V` is hermitian.
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

Return the determinant of the space `V` as an element of its fixed field.
"""
det(::AbsSpace)

@doc Markdown.doc"""
    discriminant(V::AbsSpace) -> FieldElem

Return the discriminant of the space `V` as an element of its fixed field.
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

Return the Gram matrix of the rows of `M` with respect to the Gram matrix of the space `V`.
"""
function gram_matrix(V::AbsSpace{T}, M::MatElem{S}) where {S, T}
  @req ncols(M) == dim(V) "Matrix must have $(dim(V)) columns ($(ncols(M)))"
  if S === elem_type(T)
    return M * gram_matrix(V) * transpose(_map(M, involution(V)))
  else
    Mc = change_base_ring(base_ring(V), M)
    return Mc * gram_matrix(V) * transpose(_map(Mc, involution(V)))
  end
end

@doc Markdown.doc"""
    gram_matrix(V::AbsSpace, S::Vector{Vector}) -> MatElem

Return the Gram matrix of the sequence `S` with respect to the Gram matrix of the space `V`.
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

Return the inner product of `v` and `w` with respect to the bilinear form of the space `V`.
"""
inner_product(V::AbsSpace, v::Vector, w::Vector)

@doc Markdown.doc"""
    inner_product(V::AbsSpace, v::MatElem, w::MatElem) -> MatElem

Shortcut for `v * gram_matrix(V) * adjoint(w)`.
"""
inner_product(V::AbsSpace, v::MatElem, w::MatElem)

_inner_product(L::AbsLat, v, w) = inner_product(ambient_space(L), v, w)

################################################################################
#
#  Diagonalization
#
################################################################################

@doc Markdown.doc"""
    orthogonal_basis(V::AbsSpace) -> MatElem

Return a matrix `M`, such that the rows of `M` form an orthgonal basis of the space `V`.
"""
function orthogonal_basis(V::AbsSpace)
  _, B = _gram_schmidt(gram_matrix(V), involution(V))
  return B
end

@doc Markdown.doc"""
    diagonal(V::AbsSpace) -> Vector{FieldElem}

Return a vector of elements $a_1,\dotsc,a_n$ such that the space `V` is isometric to
the diagonal space $\langle a_1,\dotsc,a_n \rangle$.

The elements are contained in the fixed field of `V`.
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
  T = identity_matrix(K, n)
  okk = is_diagonal(F)
  if !okk
    for i in 1:n
      if iszero(F[i,i])
        zero!(T)
        for i in 1:nrows(T)
          T[i, i] = 1
        end
        ok = 0
        for j in (i + 1):n
          if !iszero(F[j, j])
            ok = j
            break
          end
        end
        if ok != 0 # ok !== nothing
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
        if ok == 0
          continue
        end

        #S = T * S
        S = mul!(S, T, S)
        #F = T * F * transpose(_map(T, a))
        F = mul!(F, T, F)
        F = mul!(F, F, transpose(_map(T, a)))
      end

      zero!(T)
      for i in 1:nrows(T)
        T[i, i] = 1
      end

      for j in (i + 1):n
        T[j, i] = divexact(-F[j, i], F[i, i])
      end
      #F = T * F * transpose(_map(T, a))
      F = mul!(F, T, F)
      F = mul!(F, F, transpose(_map(T, a)))
      #S = T * S
      S = mul!(S, T, S)
    end
    @assert is_diagonal(F)
  end
  @hassert :Lattice 1 S * M * transpose(_map(S, a)) == F
  return F, S
end

################################################################################
#
#  Local isometry
#
################################################################################

@doc Markdown.doc"""
    is_isometric(L::AbsSpace, M::AbsSpace, p::Union{InfPlc, NfOrdIdl}) -> Bool

Return whether the spaces `L` and `M` are isometric over the completion at `p`.
"""
is_isometric(L::AbsSpace, M::AbsSpace, p)

################################################################################
#
#  Global isometry
#
################################################################################

@doc Markdown.doc"""
    is_isometric(L::AbsSpace, M::AbsSpace) -> Bool

Return whether the spaces `L` and `M` are isometric.
"""
is_isometric(L::AbsSpace, M::AbsSpace)

################################################################################
#
#  Definitness
#
################################################################################

# Returns 0 if V is not definite
# Returns an element a != 0 such that a * canonical_basis of V has
# positive Gram matrix
function _isdefinite(V::AbsSpace)
  E = base_ring(V)
  K = fixed_field(V)
  if (!is_totally_real(K)) || (ishermitian(V) && !is_totally_complex(E))
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

@doc Markdown.doc"""
    is_positive_definite(V::AbsSpace) -> Bool

Return whether the space `V` is positive definite.
"""
function is_positive_definite(V::AbsSpace)
  E = base_ring(V)
  K = fixed_field(V)
  if (!is_totally_real(K)) || (ishermitian(V) && !is_totally_complex(E))
    return false
  end
  D = diagonal(V)
  for d in D
    if !is_totally_positive(d)
      return false
    end
  end
  return true
end

@doc Markdown.doc"""
    is_negative_definite(V::AbsSpace) -> Bool

Return whether the space `V` is negative definite.
"""
function is_negative_definite(V::AbsSpace)
  E = base_ring(V)
  K = fixed_field(V)
  if (!is_totally_real(K)) || (ishermitian(V) && !is_totally_complex(E))
    return false
  end
  D = diagonal(V)
  for d in D
    if !is_totally_positive(-d)
      return false
    end
  end
  return true
end

@doc Markdown.doc"""
    is_definite(V::AbsSpace) -> Bool

Return whether the space `V` is definite.
"""
function is_definite(V::AbsSpace)
  return is_positive_definite(V) || is_negative_definite(V)
end

################################################################################
#
#  Isotropic
#
################################################################################

@doc Markdown.doc"""
    is_isotropic(V::AbsSpace, p::Union{NfOrdIdl, InfPlc}) -> Bool

Given a space `V` and a place `p` in the fixed field `K` of `V`, return
whether the completion of `V` at `p` is isotropic.
"""
is_isotropic(::AbsSpace, p)

is_isotropic(V::AbsSpace, p::InfPlc) = _isisotropic(V, p)

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
  elseif is_complex(p)
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
  elseif is_complex(p)
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

  return quadratic_space(FlintQQ, G, check = false), VecSpaceRes(E, rank(V))
end

################################################################################
#
#  Orthogonal complement
#
################################################################################

@doc Markdown.doc"""
    orthogonal_complement(V::AbsSpace, M::MatElem)

Given a space `V` and a subspace `W` with basis matrix `M`, returns a basis
matrix of the orthogonal complement of `W` inside `V`.
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

function _orthogonal_sum(V::AbsSpace, W::AbsSpace)
  K = base_ring(V)
  G = diagonal_matrix(gram_matrix(V), gram_matrix(W))
  n = dim(V) + dim(W)
  i1 = zero_matrix(K, dim(V), n)
  for i in 1:dim(V)
    i1[i, i] = 1
  end
  i2 = zero_matrix(K, dim(W), n)
  for i in 1:dim(W)
    i2[i, i + dim(V)] = 1
  end
  return G, i1, i2
end

@doc Markdown.doc"""
    orthogonal_sum(V::AbsSpace, W::AbsSpace) -> AbsSpace, AbsSpaceMor, AbsSpaceMor

Given two spaces `V` and `W` of the same kind (either both hermitian or both quadratic)
and defined over the same algebra, return their orthogonal sum $V \oplus W$. It is given with
the two natural embeddings $V \to V\oplus W$ and $W \to V\oplus W$.
"""
orthogonal_sum(V::AbsSpace, W::AbsSpace)

function orthogonal_sum(V::QuadSpace, W::QuadSpace)
  @req base_ring(V) === base_ring(W) "Base algebra must be equal"
  G, i1, i2 = _orthogonal_sum(V, W)
  VplusW = quadratic_space(base_ring(V), G)
  f1 = hom(V, VplusW, i1)
  f2 = hom(W, VplusW, i2)
  return VplusW, f1, f2
end

function orthogonal_sum(V::HermSpace, W::HermSpace)
  @req base_ring(V) === base_ring(W) "Base algebra must be equal"
  G, i1, i2 = _orthogonal_sum(V, W)
  VplusW = hermitian_space(base_ring(V), G)
  f1 = hom(V, VplusW, i1)
  f2 = hom(W, VplusW, i2)
  return VplusW, f1, f2
end

################################################################################
#
#  Embeddings
#
################################################################################

@doc Markdown.doc"""
    is_locally_represented_by(U::T, V::T, p::NfOrdIdl) where T <: AbsSpace -> Bool

Given two spaces `U` and `V` over the same algebra `E`, and a prime ideal `p` in
the maximal order $\mathcal O_K$ of their fixed field `K`, return whether `U` is
represented by `V` locally at `p`, i.e. whether $U_p$ embeds in $V_p$.
"""
is_locally_represented_by(::AbsSpace, ::AbsSpace, p)

@doc Markdown.doc"""
    is_represented_by(U::T, V::T) where T <: AbsSpace -> Bool

Given two spaces `U` and `V` over the same algebra `E`, return whether `U` is
represented by `V`, i.e. whether `U` embeds in `V`.
"""
is_represented_by(::AbsSpace, ::AbsSpace)

