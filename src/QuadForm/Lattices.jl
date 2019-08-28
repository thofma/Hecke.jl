mutable struct QuadLat{S, T, U} <: AbsLat{S}
  space::QuadSpace{S, T}
  pmat::U
  gram::T

  function QuadLat(K::S, G::T, P::U) where {S, T, U}
    space = QuadSpace(K, G)
    z = new{S, T, U}(space, P)
    return z
  end

  function QuadLat(K::S, G::T) where {S, T}
    n = nrows(G)
    M = pseudo_matrix(identity_matrix(K, n))
    return QuadLat(K, G, M)
  end
end

mutable struct HermLat{S, T, U, V, W} <: AbsLat{S}
  space::HermSpace{S, T, U, W}
  pmat::V
  gram::T

  function HermLat(E::S, G::U, P::V) where {S, U, V}
    @assert degree(E) == 2
    A = automorphisms(E)
    a = gen(E)
    if A[1](a) == a
      involution = A[2]
    else
      involution = A[1]
    end

    K = base_field(E)

    space = HermSpace(E, K, G, involution)
      
    z = new{S, typeof(K), U, V, typeof(involution)}(space, P)
    return z
  end

  function HermLat(E::S, G::U) where {S, U}
    n = nrows(G)
    M = pseudo_matrix(identity_matrix(E, n))
    return HermLat(E, G, M)
  end
end

function diagonal(L::AbsLat)
  D, _ = _gram_schmidt(gram_matrix_of_basis(L), involution(L))
  return diagonal(D)
end


pseudo_matrix(L::AbsLat) = L.pmat

coefficient_ideals(L::AbsLat) = coefficient_ideals(pseudo_matrix(L))

basis_matrix(L::AbsLat) = matrix(pseudo_matrix(L))


ambient_space(L::AbsLat) = L.space

rank(L::AbsLat) = nrows(L.pmat)


base_algebra(L::QuadLat) = L.space.K

base_algebra(L::HermLat) = L.space.E

involution(L::QuadLat) = identity

involution(L::HermLat) = involution(ambient_space(L))

function gram_matrix_of_basis(L::AbsLat)
  return gram_matrix(ambient_space(L), L.pmat.matrix)
end

function degree(L::AbsLat)
  return dim(ambient_space(L))
end

# Check if one really needs minimal
# Steinitz form is not pretty
function generators(L::AbsLat; minimal::Bool = true)
  St = _steinitz_form(pseudo_matrix(L), Val{false})
  d = nrows(St)
  n = degree(L)
  T = elem_type(base_algebra(L))
  v = Vector{T}[]
  for i in 1:(d - 1)
    @assert isprincipal(coefficient_ideals(St)[i])[1]
    push!(v, T[basis_matrix(L)[i, j] for j in 1:d])
  end

  I = numerator(coefficient_ideals(St)[d])
  den = denominator(coefficient_ideals(St)[d])
  if minimal && base_algebra(L) isa AnticNumberField
    b, a = isprincipal(I)
    if b
      push!(v, T[base_algebra(L)(a)//den * basis_matrix(L)[n, j] for j in 1:d])
    end
    return v
  end

  _assure_weakly_normal_presentation(I)
  push!(v, T[base_algebra(L)(I.gen_one)//den * basis_matrix(L)[n, j] for j in 1:d])
  push!(v, T[base_algebra(L)(I.gen_two)//den * basis_matrix(L)[n, j] for j in 1:d])

  return v
end

function discriminant(L::AbsLat)
  d = det(gram_matrix_of_basis(L))
  v = involution(L)
  C = coefficient_ideals(L)
  I = prod(J for J in C)
  return d * I * v(I)
end

function hasse_invariant(L::QuadLat, p)
  return _hasse_invariant(diagonal(L), p)
end

function hasse_invariant(L::HermLat, p)
  throw(error("The lattice must be quadratic"))
end

function witt_invariant(L::QuadLat, p::NfOrdIdl)
  h = hasse_invariant(L, p)
  F = gram_matrix_of_basis(L)
  dett = det(F)
  K = base_algebra(L)
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

function witt_invariant(L::QuadLat, p::InfPlc)
  if iscomplex(p)
    error("Dont' know what to do. Markus returns false")
  end

  h = hasse_invariant(L, p)
  F = gram_matrix_of_basis(L)
  dett = det(F)
  K = base_algebra(L)
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

function isrationally_equivalent(L::QuadLat, M::QuadLat, p::NfOrdIdl)
  GL = gram_matrix_of_basis(L)
  GM = gram_matrix_of_basis(M)
  if GL == GM
    return true
  end

  return rank(GL) == rank(GM) && islocal_square(det(GL) * det(GM), p) && hasse_invariant(L, p) == hasse_invariant(M, p)
end

function isequivalent(L::QuadLat, M::QuadLat, p::InfPlc)
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


