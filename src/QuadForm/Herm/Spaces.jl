################################################################################
#
#  Constructors
#
################################################################################

@doc Markdown.doc"""
    hermitian_space(E::NumField, n::Int; cached::Bool = true) -> HermSpace

Create the hermitian space over `E` with dimension `n` and Gram matrix equals to
the identity matrix. The number field `E` must be a quadratic extension, that
is, $degree(E) == 2$ must hold.
"""
function hermitian_space(E::NumField, n::Int; cached::Bool = true)
  G = identity_matrix(E, n)
  return hermitian_space(E, G, cached = cached)
end

@doc Markdown.doc"""
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

################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, V::HermSpace)
  print(io, "Hermitian space over\n")
  println(io, base_ring(V))
  println(io, "with Gram matrix")
  print(io, gram_matrix(V))
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
    return c::Tuple{AnticNumberField, NfToNfRel}
  end
end

################################################################################
#
#  Predicates
#
################################################################################

isquadratic(V::HermSpace) = false

ishermitian(V::HermSpace) = true

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
  return _inner_product(G, v, [involution(x) for x in w])
end

function inner_product(V::HermSpace, v::Vector, w::Vector)
  _inner_product(gram_matrix(V), v, w, involution(V))
end

################################################################################
#
#  Diagonalization
#
################################################################################

function diagonal(V::HermSpace)
  D, _ = _gram_schmidt(gram_matrix(V), involution(V))
  return map(fixed_field(V), diagonal(D))
end

################################################################################
#
#  Hasse and Witt invariant
#
################################################################################

function hasse_invariant(L::HermSpace, p)
  throw(error("The space must be quadratic"))
end

function witt_invariant(L::HermSpace, p)
  throw(error("The space must be quadratic"))
end

################################################################################
#
#  Local isometry
#
################################################################################

function isisometric(L::HermSpace, M::HermSpace, p::fmpz)
  K = fixed_field(L)
  p = p*maximal_order(K)
  return _isisometric(L, M, p)
end

function isisometric(L::HermSpace, M::HermSpace, p::NfOrdIdl)
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

  return islocal_norm(base_ring(L), det(L) * det(M), p)[1]
end

function isisometric(L::HermSpace, M::HermSpace, P::InfPlc)
  if L == M
    return true
  end
  
  if rank(L) != rank(M)
    return false
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

################################################################################
#
#  Global isometry
#
################################################################################

function isisometric(M::HermSpace, L::HermSpace)
  @req isregular(M) && isregular(L) "The spaces must be both regular"
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
  
  if any(v -> !isisometric(M, L, v), infp)
    return false
  end

  return isnorm(E, det(M) * det(L))[1]
end


################################################################################
#
#  Isotropic spaces
#
################################################################################

@doc Markdown.doc"""
    isisotropic(V::Hermspace, p::NfOrdIdl) -> Bool

Return whether the completion of the hermitian space `V` over $E/K$ at the prime 
ideal `p` of $O_K$ is isotropic.
"""
function isisotropic(V::HermSpace, q::T) where T <: NumFieldOrdIdl
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

################################################################################
#
#  Hyperbolic spaces
#
################################################################################

@doc Markdown.doc"""
    islocally_hyperbolic(V::Hermspace, p::NfOrdIdl) -> Bool

Return whether the completion of the hermitian space `V` over $E/K$ at the prime 
ideal `p` of $O_K$ is hyperbolic.
"""
function islocally_hyperbolic(V::HermSpace, p)
  rk = rank(V)
  if isodd(rk)
    return false
  end
  return islocal_norm(base_ring(V), det(V) * (-1)^(div(rk, 2)), p)
end

################################################################################
#
#  Embeddings
#
################################################################################

# Hermitian forms are uniquely determined by their rank and determinant class
# Thus there is no restriction to embeddings.

@doc Markdown.doc"""
    islocally_represented_by(U::HermSpace, V::HermSpace, p::NfOrdIdl) -> Bool

Given two hermitian spaces `U` and `V` over $E/K$ and a prime ideal `p` of $O_K$, 
return whether `U` is represented by `V` locally at `p`.
"""
function islocally_represented_by(U::HermSpace, V::HermSpace, p)
  if rank(U) > rank(V)
    return false
  elseif rank(U) == rank(V)
    return isisometric(U, V, p)
  else
    return true
  end
end

# There are no restrictions, since spaces are uniquely determined by their
# rank and determinant.

@doc Markdown.doc"""
    isrepresented_by(U::HermSpace, V::HermSpace) -> Bool

Given two hermitian spaces `U` and `V`, return whether `U` is represented by `V`, 
that is, whether `U` embeds into `V`.
"""
function isrepresented_by(U::HermSpace, V::HermSpace)
  v = rank(V) - rank(U)
  if v < 0
    return false
  elseif v == 0
    return isisometric(U, V)
  else
    return true
  end
end

