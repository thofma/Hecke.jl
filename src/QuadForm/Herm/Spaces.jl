################################################################################
#
#  Constructors
#
################################################################################

@doc Markdown.doc"""
    hermitian_space(K::NumField, n::Int; cached = true) -> HermSpace

Create the Hermitian space over `K` with dimension `n` and Gram matrix equal to
the identity matrix. The number field `K` must be a quadratic extension, that
is, `degree(K) == 2` must hold.
"""
function hermitian_space(K::NumField, n::Int; cached::Bool = false)
  G = identity_matrix(K, n)
  return hermitian_space(K, G, cached = cached)
end

@doc Markdown.doc"""
    hermitian_space(E::NumField, G::MatElem; cached = true) -> HermSpace

Create the Hermitian space over `K` with Gram matrix equal to the identity
matrix. The matrix `G` must be square and Hermitian with respect to the non-trivial
automorphism of `K`. The number field `K` must be a quadratic extension, that
is, `degree(K) == 2` must hold.
"""
function hermitian_space(E::NumField, gram::MatElem; cached::Bool = true)
  # I also need to check if the gram matrix is Hermitian
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

  @assert degree(E) == 2
  A = automorphisms(E)
  a = gen(E)
  if A[1](a) == a
    involution = A[2]
  else
    involution = A[1]
  end

  K = base_field(E)

  return HermSpace(E, K, gramc, involution, cached)
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

ishermitian(V::HermSpace) = false

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

function isisometric(L::HermSpace{AnticNumberField}, M::HermSpace{AnticNumberField}, p::fmpz)
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
#  Isotropic
#
################################################################################

isisotropic(V::HermSpace, p::InfPlc) = _isisotropic(V, p)

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

################################################################################
#
#  Hyperbolic spaces
#
################################################################################

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
#  Embeddings
#
################################################################################

# Hermitian forms are uniquely determined by their rank and determinant class
# Thus there is no restriction to embeddings.

@doc Markdown.doc"""
    islocally_represented_by(U::HermSpace, V::HermSpace, p)

Return whether $U$ is represented by $V$ locally at $\mathfrak p$.
"""
function islocally_represented_by(U::HermSpace, V::HermSpace, p)
  if rank(U) < rank(V)
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
    isrepresented_by(U::HermSpace, V::HermSpace)

Return whether $U$ is represented by $V$, that is, whether $U$ embeds into $V$.
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
