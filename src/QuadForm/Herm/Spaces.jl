################################################################################
#
#  Constructors
#
################################################################################

@doc raw"""
    hermitian_space(E::NumField, n::Int; cached::Bool = true) -> HermSpace

Create the hermitian space over `E` with dimension `n` and Gram matrix equals to
the identity matrix. The number field `E` must be a quadratic extension, that
is, $degree(E) == 2$ must hold.
"""
function hermitian_space(E::NumField, n::Int; cached::Bool = true)
  G = identity_matrix(E, n)
  return hermitian_space(E, G; cached)
end

@doc raw"""
    hermitian_space(E::NumField, gram::MatElem; cached::Bool = true) -> HermSpace

Create the hermitian space over `E` with Gram matrix equals to `gram`. The matrix `gram`
must be square and hermitian with respect to the non-trivial automorphism of `E`.
The number field `E` must be a quadratic extension, that is, $degree(E) == 2$ must hold.
"""
function hermitian_space(E::NumField, gram::MatElem; cached::Bool = true)
  @req degree(E) == 2 "E must be a quadratic extension"
  if dense_matrix_type(elem_type(typeof(E))) === typeof(gram)
    gramc = gram
  else
    try
      gramc = change_base_ring(E, gram)
      if typeof(gramc) !== dense_matrix_type(elem_type(E))
        error("Cannot convert entries of the matrix to the number field")
      end
    catch e
      if !(e isa MethodError)
        rethrow(e)
      else
        error("Cannot convert entries of the matrix to the number field")
      end
    end
  end

  involutionV = involution(E)

  @req gramc == transpose(map_entries(involutionV, gramc)) "$gram must be hermitian"

  K = base_field(E)

  return HermSpace(E, K, gramc, involutionV, cached)
end

function rescale(V::HermSpace, r, cached::Bool=true)
  E = base_ring(V)
  K = fixed_field(V)
  r = K(r)
  return HermSpace(E, K, r*gram_matrix(V), involution(V), cached)
end

################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, ::MIME"text/plain", V::HermSpace)
  io = pretty(io)
  println(io, "Hermitian space of dimension $(dim(V))")
  print(io, Indent(), "over ", Lowercase())
  Base.show(io, MIME"text/plain"(), base_ring(V))
  println(io, Dedent())
  println(io, "with gram matrix")
  Base.show(io, MIME"text/plain"(), gram_matrix(V))
end

function show(io::IO, V::HermSpace)
  if is_terse(io)
    print(io, "Hermitian space")
  else
    print(io, "Hermitian space of dimension $(dim(V))")
  end
end

################################################################################
#
#  Absolute field
#
################################################################################

# this is used internally to accelerate computations by passing to an absolute
# field
function absolute_simple_field(V::HermSpace)
  c = get_attribute(V, :absolute_simple_field)
  if c === nothing
    Eabs, EabsToE = absolute_simple_field(base_ring(V))
    set_attribute!(V, :absolute_field => (Eabs, EabsToE))
    return Eabs, EabsToE
  else
    return c::Tuple{AbsSimpleNumField, morphism_type(AbsSimpleNumField, RelSimpleNumField{AbsSimpleNumFieldElem})}
  end
end

################################################################################
#
#  Predicates
#
################################################################################

is_quadratic(V::HermSpace) = false

is_hermitian(V::HermSpace) = true

_base_algebra(V::HermSpace) = V.E

################################################################################
#
#  Properties
#
################################################################################

involution(V::HermSpace) = V.involution

fixed_field(V::HermSpace) = V.K

################################################################################
#
#  Inner product
#
################################################################################

function _inner_product(G, v, w, involution)
  res = base_ring(G)()
  return _inner_product!(res, G, v, [involution(x) for x in w])
end

function inner_product(V::HermSpace, v::Vector, w::Vector)
  _inner_product(gram_matrix(V), v, w, involution(V))
end

inner_product(V::HermSpace{S,T,U,W}, v::U, w::U) where {S,T,U,W} =
                        v*gram_matrix(V)*map_entries(involution(V), transpose(w))

################################################################################
#
#  Diagonalization
#
################################################################################

diagonal(V::HermSpace) = _diagonal(V, false)[1]

diagonal_with_transform(V::HermSpace) = _diagonal(V)

function _diagonal(V::HermSpace, with_transform::Bool = true)
  E = base_ring(V)
  g = gram_matrix(V)
  K = kernel(g, side = :left)
  k = nrows(K)
  B = complete_to_basis(K)
  g = B[k+1:end,:]*g*transpose(B[k+1:end,:])
  D, U = _gram_schmidt(g, involution(V))
  diagE = append!(zeros(base_ring(V),k), diagonal(D))
  diagK = map(fixed_field(V), diagE)
  !with_transform && return diagK, matrix(E, 0, 0, elem_type(E)[])
  B[k+1:end, :] = U*view(B, k+1:nrows(B), :)
  return diagK, B
end

################################################################################
#
#  Hasse and Witt invariant
#
################################################################################

function hasse_invariant(L::HermSpace, p)
  error("The space must be quadratic")
end

function witt_invariant(L::HermSpace, p)
  error("The space must be quadratic")
end

################################################################################
#
#  Local isometry
#
################################################################################

function is_isometric(L::HermSpace, M::HermSpace, p::ZZRingElem)
  K = fixed_field(L)
  p = p*maximal_order(K)
  return _isisometric(L, M, p)
end

function is_isometric(L::HermSpace, M::HermSpace, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  return _isisometric(L, M, p)
end

function _isisometric(L::HermSpace, M::HermSpace, p)
  base_ring(L) != base_ring(M) && error("Both spaces must have the same base field")
  A = gram_matrix(L)
  B = gram_matrix(M)
  if A == B
    return true
  end

  if rank(L) != rank(M)
    return false
  end

  return is_local_norm(base_ring(L), det(L) * det(M), p)[1]
end

function is_isometric(L::HermSpace, M::HermSpace, P::InfPlc)
  if L == M
    return true
  end

  if rank(L) != rank(M)
    return false
  end

  if is_complex(P)
    return true
  end

  DL = diagonal(L)
  DM = diagonal(M)
  iL = count(d -> is_negative(d, P), DL)
  iM = count(d -> is_negative(d, P), DM)
  return iL == iM
end

################################################################################
#
#  Global isometry
#
################################################################################

function is_isometric(M::HermSpace, L::HermSpace)
  @req is_regular(M) && is_regular(L) "The spaces must be both regular"
  @req base_ring(M) === base_ring(L) "The spaces must be defined over the same ring"
  if gram_matrix(M) == gram_matrix(L)
    return true
  end

  if rank(M) != rank(L)
    return false
  end

  E = base_ring(M)
  K = base_field(E)
  infp = real_places(K)

  if any(v -> !is_isometric(M, L, v), infp)
    return false
  end

  return is_norm(E, det(M) * det(L))[1]
end


################################################################################
#
#  Isotropic spaces
#
################################################################################

function is_isotropic(V::HermSpace, q::T) where T <: NumFieldOrderIdeal
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
  return is_local_norm(base_ring(V), -d, p)
end

################################################################################
#
#  Hyperbolic spaces
#
################################################################################

@doc raw"""
    is_locally_hyperbolic(V::Hermspace, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> Bool

Return whether the completion of the hermitian space `V` over $E/K$ at the prime
ideal `p` of $\mathcal O_K$ is hyperbolic.
"""
function is_locally_hyperbolic(V::HermSpace, p)
  rk = rank(V)
  if isodd(rk)
    return false
  end
  return is_local_norm(base_ring(V), det(V) * (-1)^(div(rk, 2)), p)
end

################################################################################
#
#  Embeddings
#
################################################################################

# Hermitian forms are uniquely determined by their rank and determinant class
# Thus there is no restriction to embeddings.

function is_locally_represented_by(U::HermSpace, V::HermSpace, p)
  if rank(U) > rank(V)
    return false
  elseif rank(U) == rank(V)
    return is_isometric(U, V, p)
  else
    return true
  end
end

# There are no restrictions, since spaces are uniquely determined by their
# rank and determinant.

function is_represented_by(U::HermSpace, V::HermSpace)
  v = rank(V) - rank(U)
  if v < 0
    return false
  elseif v == 0
    return is_isometric(U, V)
  else
    return true
  end
end

