################################################################################
#
#  Constructors
#
################################################################################

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
function absolute_field(V::HermSpace)
  c = get_special(V, :absolute_field)
  if c === nothing
    Eabs, EabsToE, KtoE = absolute_field(base_ring(V))
    set_special(V, :absolute_field => (Eabs, EabsToE, KtoE))
    return Eabs, EabsToE, KtoE
  else
    return c::Tuple{AnticNumberField,Hecke.NfToNfRel,NfToNfMor}
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
#  Local equivalence
#
################################################################################

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

################################################################################
#
#  Global equivalence
#
################################################################################

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
