export ambient_space, rank, gram_matrix, inner_product, involution, ishermitian, is_quadratic, is_regular,
       is_local_square, is_isometric, is_rationally_isometric, is_isotropic, is_isotropic_with_vector, quadratic_space,
       hermitian_space, diagonal, invariants, hasse_invariant, witt_invariant, orthogonal_basis, fixed_field,
       restrict_scalars, orthogonal_complement, orthogonal_projection

################################################################################
#
#  Maps
#
################################################################################

function hom(V::AbstractSpace, W::AbstractSpace, B::MatElem; check::Bool = false)
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
  return AbstractSpaceMor(V, W, B)
end

function image(f::AbstractSpaceMor, v::Vector)
  V = domain(f)
  w = matrix(base_ring(V), 1, length(v), v) * f.matrix
  return vec(collect(w))
end

@attr Bool function is_injective(f::AbstractSpaceMor)
  return rank(f.matrix) == nrows(f.matrix)
end

function image(f::AbstractSpaceMor, L::AbstractLat)
  V = domain(f)
  @req V==ambient_space(L) "L not in domain"
  W = codomain(f)
  if is_injective(f)
    B = pseudo_matrix(L)
    fB = matrix(B)*f.matrix
    PB = pseudo_matrix(fB, B.coeffs)
    return lattice(W, PB)
  else
    error("not implemented")
  end
end

function image(f::AbstractSpaceMor, L::ZLat)
  V = domain(f)
  @req V==ambient_space(L) "L not in domain"
  W = codomain(f)
  B = basis_matrix(L)*f.matrix
  isbasis = is_injective(f)
  return lattice(W, B, isbasis=isbasis, check=false)
end

function preimage(f::AbstractSpaceMor, L::ZLat)
  V = domain(f)
  W = codomain(f)
  @req W==ambient_space(L) "L not in codomain"
  ok, B = can_solve_with_solution(f.matrix, basis_matrix(L), side=:left)
  if !ok
    # intersect with the image
    L1 = intersect(lattice(W, f.matrix) , L)
    L2 = primitive_closure(L, L1)
    ok, B = can_solve_with_solution(f.matrix, basis_matrix(L2), side=:left)
    @assert ok
  end
  return lattice(V, B)
end

function compose(f::AbstractSpaceMor, g::AbstractSpaceMor)
  @req codomain(f) === domain(g) "incompatible morphisms"
  return hom(domain(f), codomain(g), f.matrix * g.matrix)
end

################################################################################
#
#  Creation
#
################################################################################

@doc raw"""
    rescale(q::AbstractSpace, r) -> AbstractSpace

For $q=(V,\Phi)$ return the space $(V, r \Phi)$.
"""
rescale(q::AbstractSpace, r)


################################################################################
#
#  Basic invariants
#
################################################################################

@doc raw"""
    rank(V::AbstractSpace) -> Int

Return the rank of the space `V`.
"""
@attr Int rank(L::AbstractSpace) = rank(L.gram)

@doc raw"""
    dim(V::AbstractSpace) -> Int

Return the dimension of the space `V`.
"""
dim(V::AbstractSpace) = nrows(V.gram)

@doc raw"""
    gram_matrix(V::AbstractSpace) -> MatElem

Return the Gram matrix of the space `V`.
"""
gram_matrix(V::AbstractSpace) = V.gram

# Once we have quaternion spaces the following makes more sense

@doc raw"""
    base_ring(V::AbstractSpace) -> NumField

Return the algebra over which the space `V` is defined.
"""
base_ring(V::AbstractSpace) = _base_algebra(V)

@doc raw"""
    fixed_field(V::AbstractSpace) -> NumField

Return the fixed field of the space `V`.
"""
fixed_field(::AbstractSpace)

@doc raw"""
    involution(V::AbstractSpace) -> NumField

Return the involution of the space `V`.
"""
involution(V::AbstractSpace)

################################################################################
#
#  Predicates
#
################################################################################

@doc raw"""
    is_regular(V::AbstractSpace) -> Bool

Return whether the space `V` is regular, that is, if the Gram matrix
has full rank.
"""
function is_regular(V::AbstractSpace)
  return rank(V) == dim(V)
end

@doc raw"""
    is_quadratic(V::AbstractSpace) -> Bool

Return whether the space `V` is quadratic.
"""
is_quadratic(::AbstractSpace)

@doc raw"""
    ishermitian(V::AbstractSpace) -> Bool

Return whether the space `V` is hermitian.
"""
ishermitian(::AbstractSpace)

################################################################################
#
#  Determinant and discriminant
#
################################################################################

@attr elem_type(fixed_field(V)) function det(V::AbstractSpace{S}) where S
  d = det(gram_matrix(V))
  return fixed_field(V)(d)
end

@doc raw"""
    det(V::AbstractSpace) -> FieldElem

Return the determinant of the space `V` as an element of its fixed field.
"""
det(::AbstractSpace)

@doc raw"""
    discriminant(V::AbstractSpace) -> FieldElem

Return the discriminant of the space `V` as an element of its fixed field.
"""
function discriminant(V::AbstractSpace)
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

@doc raw"""
    gram_matrix(V::AbstractSpace, M::MatElem) -> MatElem

Return the Gram matrix of the rows of `M` with respect to the Gram matrix of the space `V`.
"""
function gram_matrix(V::AbstractSpace{T}, M::MatElem{S}) where {S, T}
  @req ncols(M) == dim(V) "Matrix must have $(dim(V)) columns ($(ncols(M)))"
  if S === elem_type(T)
    return M * gram_matrix(V) * transpose(_map(M, involution(V)))
  else
    Mc = change_base_ring(base_ring(V), M)
    return Mc * gram_matrix(V) * transpose(_map(Mc, involution(V)))
  end
end

@doc raw"""
    gram_matrix(V::AbstractSpace, S::Vector{Vector}) -> MatElem

Return the Gram matrix of the sequence `S` with respect to the Gram matrix of the space `V`.
"""
function gram_matrix(V::AbstractSpace{T}, S::Vector{Vector{U}}) where {T, U}
  m = zero_matrix(base_ring(V), length(S), rank(V))
  for i in 1:length(S)
    if length(S[i]) != rank(V)
      error("Vectors must be of length $(rank(V))")
    end
    for j in 1:rank(V)
      m[i, j] = S[i][j]
    end
  end
  return gram_matrix(V, m)
end

@doc raw"""
    inner_product(V::AbstractSpace, v::Vector, w::Vector) -> FieldElem

Return the inner product of `v` and `w` with respect to the bilinear form of the space `V`.
"""
inner_product(V::AbstractSpace, v::Vector, w::Vector)

@doc raw"""
    inner_product(V::AbstractSpace, v::MatElem, w::MatElem) -> MatElem

Shortcut for `v * gram_matrix(V) * adjoint(w)`.
"""
inner_product(V::AbstractSpace, v::MatElem, w::MatElem)

_inner_product(L::AbstractLat, v, w) = inner_product(ambient_space(L), v, w)

################################################################################
#
#  Diagonalization
#
################################################################################

@doc raw"""
    orthogonal_basis(V::AbstractSpace) -> MatElem

Return a matrix `M`, such that the rows of `M` form an orthogonal basis of the space `V`.
"""
function orthogonal_basis(V::AbstractSpace)
  G = gram_matrix(V)
  r, Rad = left_kernel(G)
  if r > 0
    basis_nondeg = _basis_complement(Rad)
    G_nondeg = gram_matrix(V, basis_nondeg)
  else
    G_nondeg = G
  end
  _, B = _gram_schmidt(G_nondeg, involution(V))
  if r > 0
    B = vcat(Rad, B*basis_nondeg)
  end
  return B
end

@doc raw"""
    diagonal(V::AbstractSpace) -> Vector{FieldElem}

Return a vector of elements $a_1,\dotsc,a_n$ such that the space `V` is isometric to
the diagonal space $\langle a_1,\dotsc,a_n \rangle$.

The elements are contained in the fixed field of `V`.
"""
diagonal(V::AbstractSpace)

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

@doc raw"""
    is_isometric(L::AbstractSpace, M::AbstractSpace, p::Union{InfPlc, NfOrdIdl}) -> Bool

Return whether the spaces `L` and `M` are isometric over the completion at `p`.
"""
is_isometric(L::AbstractSpace, M::AbstractSpace, p)

################################################################################
#
#  Global isometry
#
################################################################################

@doc raw"""
    is_isometric(L::AbstractSpace, M::AbstractSpace) -> Bool

Return whether the spaces `L` and `M` are isometric.
"""
is_isometric(L::AbstractSpace, M::AbstractSpace)

################################################################################
#
#  Definitness
#
################################################################################

# Returns 0 if V is not definite
# Returns an element a != 0 such that a * canonical_basis of V has
# positive Gram matrix
function _isdefinite(V::AbstractSpace)
  E = base_ring(V)
  K = fixed_field(V)
  if (!is_totally_real(K)) || (ishermitian(V) && !is_totally_complex(E))
    return zero(K)
  end
  D = diagonal(V)
  signs_to_consider = Tuple{embedding_type(K), Int}[]
  for v in real_embeddings(K)
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

@doc raw"""
    is_positive_definite(V::AbstractSpace) -> Bool

Return whether the space `V` is positive definite.
"""
function is_positive_definite(V::AbstractSpace)
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

@doc raw"""
    is_negative_definite(V::AbstractSpace) -> Bool

Return whether the space `V` is negative definite.
"""
function is_negative_definite(V::AbstractSpace)
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

@doc raw"""
    is_definite(V::AbstractSpace) -> Bool

Return whether the space `V` is definite.
"""
function is_definite(V::AbstractSpace)
  return is_positive_definite(V) || is_negative_definite(V)
end

################################################################################
#
#  Isotropic
#
################################################################################

@doc raw"""
    is_isotropic(V::AbstractSpace) -> Bool

Return if the space `V` is isotropic.

A space $(V, \Phi)$ is called isotropic if there is a non-zero $v \in V$
with $\Phi(v,v) = 0$.
"""
is_isotropic(::AbstractSpace)

@doc raw"""
    is_isotropic_with_vector(V::AbstractSpace) -> Bool, Vector

Return if the space `V` is isotropic and an isotropic vector.
"""
is_isotropic_with_vector(::AbstractSpace)

@doc raw"""
    is_isotropic(V::AbstractSpace, p::Union{NfOrdIdl, InfPlc}) -> Bool

Given a space `V` and a place `p` in the fixed field `K` of `V`, return
whether the completion of `V` at `p` is isotropic.
"""
is_isotropic(::AbstractSpace, p)

is_isotropic(V::AbstractSpace, p::InfPlc) = _isisotropic(V, p)

function _isisotropic(D::Vector{QQFieldElem}, p::PosInf)
  n = length(D)
  if any(iszero(d) for d in D)
    return true
  elseif n <= 1
    return false
  else
    return length(unique!(QQFieldElem[sign(d) for d in D])) == 2
  end
end

function _isisotropic(D::Vector, p::InfPlc)
  n = length(D)
  if any(iszero(d) for d in D)
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
function _isisotropic(V::AbstractSpace, p::InfPlc)
  n = rank(V)
  d = det(V)
  if dim(V) != rank(V) # degenerate
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

# TODO: Change VecSpaceRes/SpaceRes to allow restriction of scalars
# to non rational subfields
@doc raw"""
    restrict_scalars(V::AbstractSpace, K::QQField,
                                  alpha::FieldElem = one(base_ring(V)))
                                                          -> QuadSpace, AbstractSpaceRes

Given a space $(V, \Phi)$ and a subfield `K` of the base algebra `E` of `V`, return the
quadratic space `W` obtained by restricting the scalars of $(V, \alpha\Phi)$ to `K`,
together with the map `f` for extending the scalars back.
The form on the restriction is given by ``Tr \circ \Phi`` where ``Tr: E \to K`` is the trace form.
The rescaling factor $\alpha$ is set to 1 by default.

Note that for now one can only restrict scalars to $\mathbb Q$.
"""
function restrict_scalars(V::AbstractSpace, K::QQField,
                                       alpha::FieldElem = one(base_ring(V)))
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
  Vres = quadratic_space(FlintQQ, G, check = false)
  VrestoV = AbstractSpaceRes(Vres, V, identity_matrix(QQ, rank(Vres)), identity_matrix(E, rank(V)))
  return Vres, VrestoV
end

################################################################################
#
#  Orthogonal complement
#
################################################################################

@doc raw"""
    orthogonal_complement(V::AbstractSpace, M::T) where T <: MatElem -> T

Given a space `V` and a subspace `W` with basis matrix `M`, return a basis
matrix of the orthogonal complement of `W` inside `V`.
"""
function orthogonal_complement(V::AbstractSpace, M::MatElem)
  N = gram_matrix(V) * _map(transpose(M), involution(V))
  r, K = left_kernel(N)
  @assert r == nrows(K)
  return K
end

@doc raw"""
    orthogonal_projection(V::AbstractSpace, M::T) where T <: MatElem -> AbstractSpaceMor

Given a space `V` and a non-degenerate subspace `W` with basis matrix `M`,
return the endomorphism of `V` corresponding to the projection onto the
complement of `W` in `V`.
"""
function orthogonal_projection(V::AbstractSpace, M::MatElem)
  _Q = inner_product(V, M, M)
  @req rank(_Q) == nrows(_Q) "Subspace must be non-degenerate for the inner product on V"
  U = orthogonal_complement(V, M)
  B = vcat(U, M)
  p = vcat(U, zero(M))
  pr = inv(B)*p
  return hom(V, V, pr)
end

################################################################################
#
#  Direct sums
#
################################################################################

function _biproduct(x::Vector{T}) where T <: AbstractSpace
  @req length(x) >= 2 "Input must contain at least two quadratic spaces"
  K = base_ring(x[1])
  @req all(i -> base_ring(x[i]) === K, 2:length(x)) "All spaces must be defined over the same field"
  @req is_quadratic(x[1]) ? all(i -> is_quadratic(x[i]), 2:length(x)) : all(i -> ishermitian(x[i]), 1:length(x)) "Spaces must be all hermitian or all quadratic"
  G = diagonal_matrix(gram_matrix.(x))
  V = is_quadratic(x[1]) ? quadratic_space(K, G) : hermitian_space(K, G)
  n = sum(dim.(x))
  inj = AbstractSpaceMor[]
  proj = AbstractSpaceMor[]
  dec = 0
  for W in x
    iW = zero_matrix(K, dim(W), n)
    pW = zero_matrix(K, n, dim(W))
    for i in 1:dim(W)
      iW[i, i+dec] = 1
      pW[i+dec, i] = 1
    end
    iW = hom(W, V, iW)
    pW = hom(V, W, pW)
    push!(inj, iW)
    push!(proj, pW)
    dec += dim(W)
  end
  @assert dec == n
  return V, inj, proj
end

@doc raw"""
    direct_sum(x::Vararg{T}) where T <: AbstractSpace -> T, Vector{AbstractSpaceMor}
    direct_sum(x::Vector{T}) where T <: AbstractSpace -> T, Vector{AbstractSpaceMor}

Given a collection of quadratic or hermitian spaces $V_1, \ldots, V_n$,
return their direct sum $V := V_1 \oplus \ldots \oplus V_n$,
together with the injections $V_i \to V$.

For objects of type `AbstractSpace`, finite direct sums and finite direct
products agree and they are therefore called biproducts.
If one wants to obtain `V` as a direct product with the projections $V \to V_i$,
one should call `direct_product(x)`.
If one wants to obtain `V` as a biproduct with the injections $V_i \to V$ and
the projections $V \to V_i$, one should call `biproduct(x)`.
"""
function direct_sum(x::Vector{T}) where T <: AbstractSpace
  @req length(x) >= 2 "Input must consist of at least two spaces"
  V, inj, = _biproduct(x)
  return V, inj
end

direct_sum(x::Vararg{AbstractSpace}) = direct_sum(collect(x))

@doc raw"""
    direct_product(x::Vararg{T}) where T <: AbstractSpace -> T, Vector{AbstractSpaceMor}
    direct_product(x::Vector{T}) where T <: AbstractSpace -> T, Vector{AbstractSpaceMor}

Given a collection of quadratic or hermitian spaces $V_1, \ldots, V_n$,
return their direct product $V := V_1 \times \ldots \times V_n$,
together with the projections $V \to V_i$.

For objects of type `AbstractSpace`, finite direct sums and finite direct
products agree and they are therefore called biproducts.
If one wants to obtain `V` as a direct sum with the injections $V_i \to V$,
one should call `direct_sum(x)`.
If one wants to obtain `V` as a biproduct with the injections $V_i \to V$ and
the projections $V \to V_i$, one should call `biproduct(x)`.
"""
function direct_product(x::Vector{T}) where T <: AbstractSpace
  @req length(x) >= 2 "Input must consist of at least two spaces"
  V, _, proj = _biproduct(x)
  return V, proj
end

direct_product(x::Vararg{AbstractSpace}) = direct_product(collect(x))

@doc raw"""
    biproduct(x::Vararg{T}) where T <: AbstractSpace -> T, Vector{AbstractSpaceMor}, Vector{AbstractSpaceMor}
    biproduct(x::Vector{T}) where T <: AbstractSpace -> T, Vector{AbstractSpaceMor}, Vector{AbstractSpaceMor}

Given a collection of quadratic or hermitian spaces $V_1, \ldots, V_n$,
return their biproduct $V := V_1 \oplus \ldots \oplus V_n$, together
with the injections $V_i \to V$ and the projections $V \to V_i$.

For objects of type `AbstractSpace`, finite direct sums and finite direct
products agree and they are therefore called biproducts.
If one wants to obtain `V` as a direct sum with the injections $V_i \to V$,
one should call `direct_sum(x)`.
If one wants to obtain `V` as a direct product with the projections $V \to V_i$,
one should call `direct_product(x)`.
"""
function biproduct(x::Vector{T}) where T <: AbstractSpace
  @req length(x) >= 2 "Input must consisy of at least two spaces"
  return _biproduct(x)
end

biproduct(x::Vararg{AbstractSpace}) = biproduct(collect(x))

################################################################################
#
#  Embeddings
#
################################################################################

@doc raw"""
    is_locally_represented_by(U::T, V::T, p::NfOrdIdl) where T <: AbstractSpace -> Bool

Given two spaces `U` and `V` over the same algebra `E`, and a prime ideal `p` in
the maximal order $\mathcal O_K$ of their fixed field `K`, return whether `U` is
represented by `V` locally at `p`, i.e. whether $U_p$ embeds in $V_p$.
"""
is_locally_represented_by(::AbstractSpace, ::AbstractSpace, p)

@doc raw"""
    is_represented_by(U::T, V::T) where T <: AbstractSpace -> Bool

Given two spaces `U` and `V` over the same algebra `E`, return whether `U` is
represented by `V`, i.e. whether `U` embeds in `V`.
"""
is_represented_by(::AbstractSpace, ::AbstractSpace)

