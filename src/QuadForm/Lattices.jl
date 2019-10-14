export *, +, absolute_basis, absolute_basis_matrix, ambient_space, bad_primes,
       basis_matrix, can_scale_totally_positive, change_uniformizer,
       coefficient_ideal, degree, diagonal, discriminant, dual, fixed_field,
       generators, genus_symbol, gram_matrix_of_basis, hasse_invariant,
       hermitian_lattice, intersect, involution, isdefintie, isintegral,
       islocally_isometric, ismodular, isnegative_definite,
       ispositive_definite, isrationally_equivalent, jordan_decomposition,
       local_basis_matrix, norm, pseudo_matrix, quadratic_lattice, rank,
       rational_span, rescale, scale, volume, witt_invariant, lattice

export HermLat, QuadLat

################################################################################
#
#  Types and constructors
#
################################################################################

abstract type AbsLat{S} end

mutable struct QuadLat{S, T, U} <: AbsLat{S}
  space::QuadSpace{S, T}
  pmat::U
  gram::T                        # gram matrix of the matrix part of pmat
  rational_span::QuadSpace{S, T}
  base_algebra::S
  @declare_other

  function QuadLat{S, T, U}() where {S, T, U}
    return new{S, T, U}()
  end

  function QuadLat(K::S, G::T, P::U) where {S, T, U}
    space = QuadSpace(K, G)
    z = new{S, T, U}(space, P)
    z.base_algebra = K
    return z
  end

  function QuadLat(K::S, G::T) where {S, T}
    n = nrows(G)
    M = pseudo_matrix(identity_matrix(K, n))
    return QuadLat(K, G, M)
  end
end

@doc Markdown.doc"""
    quadratic_lattice(K::NumField, B::PMat; gram_ambient_space = F) -> QuadLat

Given a number field $K$ and a pseudo-matrix $B$, returns the quadratic lattice
spanned by the pseudo-matrix $B$ inside the quadratic space over $K$ with gram
matrix $F$.

If $F$ is not supplied, the gram matrix of the ambient space will be the
identity matrix.
"""
quadratic_lattice(::NumField, ::PMat; gram_ambient_space = nothing)

# TODO: At the moment I assume that B is a pseudo-hnf (probably)
function quadratic_lattice(K::NumField, B::PMat; gram_ambient_space = nothing, gram = nothing)
  if gram_ambient_space === nothing && gram === nothing
    return QuadLat(K, identity_matrix(K, nrows(B)), pseudo_matrix(B))
  end
  if gram_ambient_space !== nothing && gram === nothing
    return QuadLat(K, gram_ambient_space, B)
  end
  if gram_ambient_space === nothing && gram !== nothing
    z = QuadLat{typeof(K), typeof(gram), typeof(B)}()
    z.pmat = B
    z.gram = gram
    z.base_algebra = K
    return z
  end
end

@doc Markdown.doc"""
    quadratic_lattice(K::NumField, B::MatElem; gram_ambient_space = F) -> QuadLat

Given a number field $K$ and a matrix $B$, returns the quadratic lattice
spanned by the rows $B$ inside the quadratic space over $K$ with gram matrix
$F$.

If $F$ is not supplied, the gram matrix of the ambient space will be the
identity matrix.
"""
quadratic_lattice(::NumField, ::MatElem; gram_ambient_space = nothing)

function quadratic_lattice(K::NumField, B::MatElem; gram_ambient_space = nothing, gram = nothing)
  if gram_ambient_space === nothing && gram === nothing
    return QuadLat(K, identity_matrix(K, nrows(B)), pseudo_matrix(B))
  end
  if gram_ambient_space !== nothing && gram === nothing
    return QuadLat(K, gram_ambient_space, pseudo_matrix(B))
  end
  if gram_ambient_space === nothing && gram !== nothing
    P = pseudo_matrix(B)
    z = QuadLat{typeof(K), typeof(B), typeof(P)}()
    z.pmat = P
    z.gram = gram
    z.base_algebra = K
    return z
  end
end

@doc Markdown.doc"""
    quadratic_lattice(V::QuadSpace, B::PMat) -> QuadLat

Given a quadratic space $V$ and a pseudo-matrix $B$, returns the quadratic lattice
spanned by the pseudo-matrix $B$ inside $V$.
"""
function lattice(V::QuadSpace, B::PMat)
  K = base_ring(V)
  z = QuadLat{typeof(K), typeof(gram_matrix(V)), typeof(B)}()
  z.pmat = B
  z.gram = gram_matrix(V, matrix(B))
  z.base_algebra = K
  z.space = V
  return z
end

@doc Markdown.doc"""
    quadratic_lattice(V::QuadSpace, B::MatElem) -> QuadLat

Given a quadratic space $V$ and a matrix $B$, returns the quadratic lattice
spanned by the rows of $B$ inside $V$.
"""
function lattice(V::QuadSpace, B::MatElem)
  K = base_ring(V)
  pmat = pseudo_matrix(B)
  z = QuadLat{typeof(K), typeof(gram_matrix(V)), typeof(pmat)}()
  z.pmat = pmat
  z.gram = gram_matrix(V, B)
  z.base_algebra = K
  z.space = V
  return z
end

# Hermitian lattices
mutable struct HermLat{S, T, U, V, W} <: AbsLat{S}
  space::HermSpace{S, T, U, W}
  pmat::V
  gram::U
  rational_span::HermSpace{S, T, U, W}
  base_algebra::S
  involution::W
  @declare_other

  function HermLat{S, T, U, V, W}() where {S, T, U, V, W}
    z = new{S, T, U, V, W}()
    return z
  end

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

    space = HermSpace(E, G)

    z = new{S, typeof(K), U, V, typeof(involution)}(space, P)
    z.base_algebra = E
    z.involution = involution
    return z
  end

  function HermLat(E::S, G::U) where {S, U}
    n = nrows(G)
    M = pseudo_matrix(identity_matrix(E, n))
    return HermLat(E, G, M)
  end
end

@doc Markdown.doc"""
    hermitian_lattice(K::NumField, B::PMat; gram_ambient_space = F) -> HermLat

Given a number field $K$ and a pseudo-matrix $B$, returns the hermitian lattice
spanned by the pseudo-matrix $B$ inside the hermitian space over $K$ with gram
matrix $F$.

If $F$ is not supplied, the gram matrix of the ambient space will be the
identity matrix.
"""
hermitian_lattice(::NumField, ::PMat; gram_ambient_space = nothing)

function hermitian_lattice(K::NumField, B::PMat; gram_ambient_space = nothing, gram = nothing)
  if gram_ambient_space === nothing && gram === nothing
    return HermLat(K, identity_matrix(K, nrows(B)), B)
  end
  if gram_ambient_space !== nothing && gram === nothing
    return HermLat(K, gram_ambient_space, B)
  end
  if gram_ambient_space === nothing && gram !== nothing
    @assert degree(K) == 2
    A = automorphisms(K)
    a = gen(K)
    if A[1](a) == a
      involution = A[2]
    else
      involution = A[1]
    end

    z = HermLat{typeof(K), typeof(base_field(K)), typeof(gram), typeof(B), morphism_type(typeof(K))}()
    z.pmat = P
    z.gram = gram
    z.involution = involution
    z.base_algebra = K
    return z
  end
end

@doc Markdown.doc"""
    hermitian_lattice(K::NumField, B::MatElem; gram_ambient_space = F) -> HermLat

Given a number field $K$ and a matrix $B$, returns the hermitian lattice
spanned by the rows $B$ inside the hermitian space over $K$ with gram matrix
$F$.

If $F$ is not supplied, the gram matrix of the ambient space will be the
identity matrix.
"""
hermitian_lattice(::NumField, ::MatElem; gram_ambient_space = nothing)

function hermitian_lattice(K::NumField, B::MatElem; gram_ambient_space = nothing, gram = nothing)
  if gram_ambient_space === nothing && gram === nothing
    return HermLat(K, identity_matrix(K, nrows(B)), pseudo_matrix(B))
  end
  if gram_ambient_space !== nothing && gram === nothing
    return HermLat(K, gram_ambient_space, pseudo_matrix(B))
  end
  if gram_ambient_space === nothing && gram !== nothing
    @assert degree(K) == 2
    A = automorphisms(K)
    a = gen(K)
    if A[1](a) == a
      involution = A[2]
    else
      involution = A[1]
    end

    P = pseudo_matrix(B)
    z = HermLat{typeof(K), typeof(base_field(K)), typeof(B), typeof(P), morphism_type(typeof(K))}()
    z.pmat = P
    z.gram = gram
    z.involution = involution
    z.base_algebra = K
    return z
  end
end

@doc Markdown.doc"""
    hermitian_lattice(V::HermSpace, B::PMat) -> HermLat

Given a hermitian space $V$ and a pseudo-matrix $B$, returns the hermitian lattice
spanned by the pseudo-matrix $B$ inside $V$.
"""
function lattice(V::HermSpace, B::PMat)
  K = base_ring(V)
  gram = gram_matrix(V, matrix(B))
  z = HermLat{typeof(K), typeof(base_field(K)), typeof(gram), typeof(B), morphism_type(typeof(K))}()
  z.pmat = B
  z.gram = gram
  z.base_algebra = base_ring(V)
  z.involution = involution(V)
  z.space = V
  return z
end

@doc Markdown.doc"""
    hermitian_lattice(V::QuadSpace, B::MatElem) -> HermLat

Given a Hermitian space $V$ and a matrix $B$, returns the Hermitian lattice
spanned by the rows of $B$ inside $V$.
"""
function lattice(V::HermSpace, B::MatElem)
  K = base_ring(V)
  gram = gram_matrix(V, B)
  pmat = pseudo_matrix(B)
  z = HermLat{typeof(K), typeof(base_field(K)), typeof(gram), typeof(pmat), morphism_type(typeof(K))}()
  z.pmat = pmat
  z.gram = gram
  z.base_algebra = base_ring(V)
  z.involution = involution(V)
  z.space = V
  return z
end

@doc Markdown.doc"""
    lattice(V::HermSpace) -> HermLat

Given a Hermitian space $V$, returns the Hermitian lattice with trivial basis
matrix.
"""
lattice(V::HermSpace) = lattice(V, identity_matrix(base_ring(V), rank(V)))

@doc Markdown.doc"""
    lattice(V::QuadSpace) -> QuadLat

Given a quadratic space $V$, returns the quadratic lattice with trivial basis
matrix.
"""
lattice(V::QuadSpace) = lattice(V, identity_matrix(base_ring(V), rank(V)))

################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, L::QuadLat)
  println(io, "Quadratic lattice of rank $(rank(L)) and degree $(degree(L))")
  println(io, "over")
  print(IOContext(io, :compact => true), base_ring(L))
end

function Base.show(io::IO, L::HermLat)
  println(io, "Hermitian lattice of rank $(rank(L)) and degree $(degree(L))")
  println(io, "over")
  print(IOContext(io, :compact => true), base_ring(L))
end

################################################################################
#
#  Ambient space
#
################################################################################

@doc Markdown.doc"""
    has_ambient_space(L::AbsLat) -> Bool

Returns wether the ambient space of $L$ is known.
"""
function has_ambient_space(L::AbsLat)
  return isdefined(L, :space)
end

@doc Markdown.doc"""
    ambient_space(L::AbsLat) -> AbsSpace

Returns the ambient space of $L$. If the ambient space is not known, an
error is raised.
"""
function ambient_space(L::AbsLat)
  if has_ambient_space(L)
    return L.space
  else
    throw(error("Ambient quadratic space not defined"))
  end
end

################################################################################
#
#  Rational span
#
################################################################################

@doc Markdown.doc"""
    rational_span(L::AbsLat) -> AbsSpace

Returns the rational span of $L$.
"""
rational_span(::AbsLat)

function rational_span(L::QuadLat)
  if isdefined(L, :rational_span)
    return L.rational_span
  else
    G = gram_matrix_of_basis(L)
    V = quadratic_space(base_field(L), G)
    L.rational_span = V
    return V
  end
end

function rational_span(L::HermLat)
  if isdefined(L, :rational_span)
    return L.rational_span
  else
    G = gram_matrix_of_basis(L)
    V = hermitian_space(base_field(L), G)
    L.rational_span = V
    return V
  end
end

################################################################################
#
#  Diagonal
#
################################################################################

@doc Markdown.doc"""
    diagonal(L::AbsLat) -> Vector

Returns the diagonal of the rational span of $L$.
"""
function diagonal(L::AbsLat)
  D, _ = _gram_schmidt(gram_matrix_of_basis(L), involution(L))
  return diagonal(D)
end

################################################################################
#
#  Module properties
#
################################################################################

@doc Markdown.doc"""
    pseudo_matrix(L::Abs) -> PMat

Returns the basis pseudo-matrix of $L$.
"""
pseudo_matrix(L::AbsLat) = L.pmat

@doc Markdown.doc"""
    coefficient_ideals(L::Abs) -> Vector{NfOrdIdl}

Returns the coefficient ideals of the pseudo-basis of $L$.
"""
coefficient_ideals(L::AbsLat) = coefficient_ideals(pseudo_matrix(L))

@doc Markdown.doc"""
    basis_matrix(L::AbsLat) -> MatElem

Returns the ??? of $L$.
"""
basis_matrix(L::AbsLat) = matrix(pseudo_matrix(L))

# I don't know if I like those names.
base_field(L::AbsLat) = L.base_algebra

base_ring(L::AbsLat) = base_ring(L.pmat)

@doc Markdown.doc"""
    fixed_field(L::AbsLat) -> NumField

Returns the fixed field of the involution of $L$.
"""
fixed_field(L::AbsLat) = fixed_field(rational_span(L))

@doc Markdown.doc"""
    involution(L::AbsLat) -> Map

Returns the involution of the rational span of $L$.
"""
involution(::AbsLat)

involution(L::QuadLat) = identity

involution(L::HermLat) = L.involution

@doc Markdown.doc"""
    rank(L::AbsLat) -> Int

Returns the rank of $L$, that is the dimension of the rational span of $L$.
"""
rank(L::AbsLat) = rank(rational_span(L))

@doc Markdown.doc"""
    degree(L::AbsLat) -> Int

Returns the rank of the ambient space of $L$.
"""
function degree(L::AbsLat)
  return dim(ambient_space(L))
end

################################################################################
#
#  Gram matrix
#
################################################################################

@doc Markdown.doc"""
    gram_matrix_of_basis(L::AbsLat) -> MatElem

Returns the gram matrix of the ?? of $L$.
"""
function gram_matrix_of_basis(L::AbsLat)
  if isdefined(L, :gram)
    return L.gram
  else
    return gram_matrix(ambient_space(L), L.pmat.matrix)
  end
end

# Check if one really needs minimal
# Steinitz form is not pretty

@doc Markdown.doc"""
    generators(L::AbsLat; minimal = false) -> Vector{Vector}

Returns a set of generators of $L$.

If `minimal == true`, the number of generators is minimal.
"""
function generators(L::AbsLat; minimal::Bool = false)
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

################################################################################
#
#  Discriminant
#
################################################################################

@doc Markdown.doc"""
    discriminant(L::AbsLat) -> NfOrdFracIdl

Returns the discriminant of $L$.
"""
function discriminant(L::AbsLat)
  d = det(gram_matrix_of_basis(L))
  v = involution(L)
  C = coefficient_ideals(L)
  I = prod(J for J in C)
  return d * I * v(I)
end

################################################################################
#
#  Rational (local) equivalence
#
################################################################################

@doc Markdown.doc"""
    hasse_invariant(L::AbsLat, p::Union{InfPlc, NfOrdIdl}) -> Int

Returns the Hasse invariant of the rational span of $L$ at $p$.
"""
function hasse_invariant(L::QuadLat, p)
  return hasse_invariant(rational_span(L), p)
end

function hasse_invariant(L::HermLat, p)
  throw(error("The lattice must be quadratic"))
end

@doc Markdown.doc"""
    witt_invariant(L::AbsLat, p::Union{InfPlc, NfOrdIdl}) -> Int

Returns the Witt invariant of the rational span of $L$ at $p$.
"""
function witt_invariant(L::QuadLat, p::NfAbsOrdIdl)
  return hasse_invariant(rational_span(L), p)
end

function witt_invariant(L::QuadLat, p::InfPlc)
  return witt_invariant(rational_span(L), p)
end

@doc Markdown.doc"""
    isrationally_equivalent(L::AbsLat, M::AbsLat, p::Union{InfPlc, NfOrdIdl})
                                                                         -> Bool

Returns whether the rational spans $L$ and $M$ are equivalent over the
completion at $\mathfrak p$.
"""
isrationally_equivalent(::AbsLat, ::AbsLat, ::NfAbsOrdIdl)

function isrationally_equivalent(L::AbsLat, M::AbsLat, p::NfAbsOrdIdl)
  return isequivalent(rational_span(L), rational_span(M), p)
end

function isrationally_equivalent(L::AbsLat, M::AbsLat, p::InfPlc)
  return isequivalent(rational_span(L), rational_span(M), p)
end

@doc Markdown.doc"""
    isrationally_equivalent(L::AbsLat, M::AbsLat, p::Union{InfPlc, NfOrdIdl})
                                                                         -> Bool

Returns whether the rational spans $L$ and $M$ are equivalent.
"""
function isrationally_equivalent(L::AbsLat, M::AbsLat)
  return isequivalent(rational_span(L), rational_span(M))
end

################################################################################
#
#  Definiteness
#
################################################################################

@doc Markdown.doc"""
    ispositive_definite(L::AbsLat) -> Bool

Returns whether the rational span of $L$ is positive definite.
"""
ispositive_definite(L::AbsLat) = ispositive_definite(rational_span(L))

@doc Markdown.doc"""
    isnegative_definite(L::AbsLat) -> Bool

Returns whether the rational span of $L$ is negative definite.
"""
isnegative_definite(L::AbsLat) = isnegative_definite(rational_span(L))

@doc Markdown.doc"""
    isdefinite(L::AbsLat) -> Bool

Returns whether the rational span of $L$ is definite.
"""
isdefinite(L::AbsLat) = isdefinite(rational_span(L))

@doc Markdown.doc"""
    can_scale_totally_positive(L::AbsLat) -> Bool, NumFieldElem

Returns whether there is totally positive rescaled lattice of $L$. If so, the
second return value is an element $a$ such that $L^a$ is totally positive.
"""
function can_scale_totally_positive(L::AbsLat)
  a = _isdefinite(rational_span(L))
  if iszero(a)
    return false, a
  else
    return true, a
  end
end

################################################################################
#
#  Addition
#
################################################################################

# Some of these assertions can be relaxed, in particular in the scaling

@doc Markdown.doc"""
    +(L::AbsLat, M::AbsLat) -> AbsLat

Returns the sum of $L$ and $M$.

The lattices $L$ and $M$ must have the same ambient space.
"""
Base.:(+)(::AbsLat, M::AbsLat)

@doc Markdown.doc"""
    intersect(L::AbsLat, M::AbsLat) -> AbsLat

Returns the intersection of $L$ and $M$.

The lattices $L$ and $M$ must have the same ambient space.
"""
intersect(L::AbsLat, M::AbsLat)

@doc Markdown.doc"""
    *(a::NumFieldElem, M::AbsLat) -> AbsLat

Returns the lattice $aM$ inside the ambient space of $M$.
"""
Base.:(*)(::NumFieldElem, ::AbsLat)

@doc Markdown.doc"""
    *(a::NfOrdIdl, M::AbsLat) -> AbsLat

Returns the lattice $aM$ inside the ambient space of $M$.
"""
Base.:(*)(::NfOrdIdl, ::AbsLat)

@doc Markdown.doc"""
    *(a::NfOrdFracIdl, M::AbsLat) -> AbsLat

Returns the lattice $aM$ inside the ambient space of $M$.
"""
Base.:(*)(::NfOrdFracIdl, ::AbsLat)

function Base.:(+)(L::QuadLat, M::QuadLat)
  @assert has_ambient_space(L) && has_ambient_space(M)
  @assert ambient_space(L) === ambient_space(M)
  m = _sum_modules(pseudo_matrix(L), pseudo_matrix(M))
  return quadratic_lattice(base_algebra(L), m, gram_ambient_space = gram_matrix(ambient_space(L)))
end

function intersect(L::QuadLat, M::QuadLat)
  @assert has_ambient_space(L) && has_ambient_space(M)
  @assert ambient_space(L) === ambient_space(M)
  m = _intersect_modules(pseudo_matrix(L), pseudo_matrix(M))
  return quadratic_lattice(base_algebra(L), m, gram_ambient_space = gram_matrix(ambient_space(L)))
end

function Base.:(*)(a, L::QuadLat)
  @assert has_ambient_space(L)
  return quadratic_lattice(base_algebra(L), _module_scale_ideal(a, pseudo_matrix(L)), gram_ambient_space = gram_matrix(ambient_space(L)))
end

function Base.:(*)(L::QuadLat, a)
  @assert has_ambient_space(L)
  return quadratic_lattice(base_algebra(L), _module_scale_ideal(a, pseudo_matrix(L)), gram_ambient_space = gram_matrix(ambient_space(L)))
end

function Base.:(+)(L::HermLat, M::HermLat)
  @assert has_ambient_space(L) && has_ambient_space(M)
  @assert ambient_space(L) === ambient_space(M)
  m = _sum_modules(pseudo_matrix(L), pseudo_matrix(M))
  return hermitian_lattice(base_algebra(L), m, gram_ambient_space = gram_matrix(ambient_space(L)))
end

function intersect(L::HermLat, M::HermLat)
  @assert has_ambient_space(L) && has_ambient_space(M)
  @assert ambient_space(L) === ambient_space(M)
  m = _intersect_modules(pseudo_matrix(L), pseudo_matrix(M))
  return hermitian_lattice(base_algebra(L), m, gram_ambient_space = gram_matrix(ambient_space(L)))
end

function Base.:(*)(a, L::HermLat)
  @assert has_ambient_space(L)
  return hermitian_lattice(base_algebra(L), _module_scale_ideal(a, pseudo_matrix(L)), gram_ambient_space = gram_matrix(ambient_space(L)))
end

function Base.:(*)(L::HermLat, a)
  @assert has_ambient_space(L)
  return hermitian_lattice(base_algebra(L), _module_scale_ideal(a, pseudo_matrix(L)), gram_ambient_space = gram_matrix(ambient_space(L)))
end

################################################################################
#
#  Absolute basis
#
################################################################################

# TODO: Write this:
# Call absolute_basis on the ideals
@doc Markdown.doc"""
    absolute_basis(L::AbsLat) -> Vector

Returns a $\mathbf{Z}$-basis of $L$.
"""
function absolute_basis(L::AbsLat)
  throw(NotImplemented())
end

@doc Markdown.doc"""
    absolute_basis_matrix(L::AbsLat) -> MatElem

Returns a $\mathbf{Z}$-basis matrix of $L$.
"""
function absolute_basis_matrix(L::AbsLat)
  throw(NotImplemented())
end

################################################################################
#
#  Norm
#
################################################################################

# cache this
@doc Markdown.doc"""
    norm(L::AbsLat) -> NfOrdFracIdl

Returns the norm of $L$. This is a fractional ideal of the fixed field of $L$.
"""
norm(::AbsLat)

function norm(L::QuadLat)
  G = gram_matrix_of_basis(L)
  C = coefficient_ideals(L)
  K = nf(order(C[1]))
  return sum(G[i, i] * C[i]^2 for i in 1:length(C)) + K(2) * scale(L)
end

# TODO: Be careful with the +, ideal_trace gives fmpq and then this must be gcd
function norm(L::HermLat)
  G = gram_matrix_of_basis(L)
  v = involution(L)
  K = base_ring(G)
  R = base_ring(L)
  C = coefficient_ideals(L)
  to_sum = sum(G[i, i] * C[i] * v(C[i]) for i in 1:length(C))
  to_sum = to_sum + R * reduce(+, [ideal_trace(C[i] * G[i, j] * v(C[j])) for j in 1:length(C) for i in 1:(j-1)])
  return minimum(numerator(to_sum))//denominator(to_sum)
end

################################################################################
#
#  Scale
#
################################################################################

# cache this

@doc Markdown.doc"""
    scale(L::AbsLat) -> NfOrdFracIdl

Returns the scale of $L$.
"""
scale(L::AbsLat)

function scale(L::QuadLat)
  G = gram_matrix_of_basis(L)
  C = coefficient_ideals(L)
  to_sum = [ G[i, j] * C[i] * involution(L)(C[j]) for j in 1:length(C) for i in 1:j]
  return sum(to_sum)
end

function scale(L::HermLat)
  G = gram_matrix_of_basis(L)
  C = coefficient_ideals(L)
  to_sum = [ G[i, j] * C[i] * involution(L)(C[j]) for j in 1:length(C) for i in 1:j ]
  d = length(to_sum)
  for i in 1:d
    push!(to_sum, involution(L)(to_sum[i]))
  end
  return sum(to_sum)
end

################################################################################
#
#  Rescale
#
################################################################################

@doc Markdown.doc"""
    rescale(L::AbsLat, a::NumFieldElem) -> AbsLat

Returns the rescaled lattice $L^a$. Note that this has a different ambient
space then $L$.
"""
rescale(::AbsLat, ::NumFieldElem)

function rescale(L::QuadLat, a)
  if isone(a)
    return L
  end
  K = fixed_field(L)
  b = K(a)
  return quadratic_lattice(base_field(L), pseudo_matrix(L), gram_ambient_space = b * gram_matrix(ambient_space(L)))
end

function rescale(L::HermLat, a)
  if isone(a)
    return L
  end
  K = fixed_field(L)
  b = base_field(L)(K(a))
  return hermitian_lattice(base_field(L), pseudo_matrix(L), gram_ambient_space = b * gram_matrix(ambient_space(L)))
end

################################################################################
#
#  Is integral?
#
################################################################################

@doc Markdown.doc"""
    isintegral(L::AbsLat) -> Bool

Returns whether the lattice $L$ is integral.
"""
function isintegral(L::AbsLat)
  return isintegral(scale(L))
end

################################################################################
#
#  Dual
#
################################################################################

@doc Markdown.doc"""
    dual(L::AbsLat) -> AbsLat

Returns the dual lattice of $L$.
"""
dual(::AbsLat)

function dual(L::QuadLat)
  G, B = _gram_schmidt(gram_matrix_of_basis(L), involution(L))
  C = coefficient_ideals(L)
  Gi = inv(G)
  new_bmat = Gi * B
  return quadratic_lattice(base_field(L), pseudo_matrix(new_bmat, [inv(c) for c in C]), gram_ambient_space = gram_matrix(ambient_space(L)))
end

function dual(L::HermLat)
  G, B = _gram_schmidt(gram_matrix_of_basis(L), involution(L))
  C = coefficient_ideals(L)
  Gi = inv(G)
  new_bmat = Gi * B
  return hermitian_lattice(base_field(L), pseudo_matrix(new_bmat, [inv(induce_image(c, involution(L))) for c in C]), gram_ambient_space = gram_matrix(ambient_space(L)))
end

################################################################################
#
#  Volume
#
################################################################################

@doc Markdown.doc"""
    volume(L::AbsLat) -> NfOrdFracIdl

Returns the volume of $L$.
"""
function volume(L::AbsLat)
  return discriminant(L)
end

################################################################################
#
#  Modularity
#
################################################################################

@doc Markdown.doc"""
    ismodular(L::AbsLat) -> Bool, NfOrdFracIdl

Returns whether $L$ is modular. In this case, the second return value is a
fractional ideal $\mathfrak a$ such that $\mathfrak a L^\perp = L$, where
$L^\perp$ is the dual of $L$.
"""
function ismodular(L::AbsLat)
  a = scale(L)
  if volume(L) == a^rank(L)
    return true, a
  else
    return false, a
  end
end

@doc Markdown.doc"""
    ismodular(L::AbsLat, p::NfOrdIdl) -> Bool, Int

Returns whether $L_{\mathfrak{p}}$ is modular. In this case the second return
value is an integer $v$ such that $L_{\mathfrak{p}}$ is
$\mathfrak{p}^v$-modular.
"""
function ismodular(L::AbsLat, p)
  a = scale(L)
  v = valuation(a, p)
  if v * rank(L) == valuation(volume(L), p)
    return true, v
  else
    return false, 0
  end
end

################################################################################
#
#  Bad primes
#
################################################################################

@doc Markdown.doc"""
    bad_primes(L::AbsLat; even = false) -> Vector{NfOrdIdl}

Returns the prime ideals dividing the scale and volume of $L$. If `even == true`
also the prime ideals dividing $2$ are included.
"""
function bad_primes(L::AbsLat; even::Bool = false)
  s = scale(L)
  f = factor(norm(scale(L)))
  ff = factor(norm(volume(L)))
  for (p, e) in ff
    f[p] = 0
  end
  if even
    for p in prime_decomposition(s, 2)
      f[p] = 0
    end
  end
  return collect(keys(f))
end

################################################################################
#
#  Local basis matrix
#
################################################################################

@doc Markdown.doc"""
    local_basis_matrix(L::AbsLat, p::NfOrdIdl; type = :any) -> MatElem

Given a prime ideal $\mathfrak p$ and a lattice $L$, this functions returns
a basis matrix of lattice $M$ such that $M_{\mathfrak{p}} = L_{\mathfrak{p}}$.

- If `type == :submodule`, the lattice $L$ will be a sublattice of $M$.
- If `type == :supermodule`, the lattice $L$ will be a superlattice of $M$.
- If `type == :any`, there may not be any containment relation between $M$ and
  $L$.
"""
function local_basis_matrix(L::AbsLat, p; type::Symbol = :any)
  R = base_ring(L)
  S = order(p)
  if R === S
    if type == :any
      return _local_basis_matrix(pseudo_matrix(L), p)
    elseif type == :submodule
      return _local_basis_submodule_matrix(pseudo_matrix(L), p)
    elseif type == :supermodule
      return _local_basis_supermodule_matrix(pseudo_matrix(L), p)
    else
      throw(error("""Invalid :type keyword :$(type).
                     Must be either :any, :submodule, or :supermodule"""))
    end
  elseif S === base_ring(R)
    if type == :any
      return _local_basis_matrix_prime_below(pseudo_matrix(L), p)
    else
      throw(error("""Invalid :type keyword :$(type).
                     Must be either :any, :submodule, or :supermodule"""))
    end
  end
end

################################################################################
#
#  Jordan decomposition
#
################################################################################

@doc Markdown.doc"""
    jordan_decomposition(L::AbsLat, p::NfOrdIdl)
                                -> Vector{MatElem}, Vector{MatElem}, Vector{Int}

Returns a Jordan decomposition of the completition of $L$ at $\mathfrak p$.

The return value consists of three lists $(M_i)_i$, $(G_i)_i$ and $(s_i)_i$ of
the same length $r$. The completions of the row spans of the matrices $M_i$
yield a Jordan decomposition of $L_{\mathfrak{p}}$ into modular sublattices
$L_i$ with gram matrices $G_i$ and scale of $\mathfrak{p}$-adic valuation $s_i$.
"""
jordan_decomposition(L::AbsLat, p::NfOrdIdl)

function jordan_decomposition(L::QuadLat, p)
  F = gram_matrix(ambient_space(L))
  even = 2 in p
  if even
    pi = elem_in_nf(uniformizer(p))
  else
    pi = zero(nf(order(p)))
  end

  oldval = PosInf()
  blocks = Int[]
  exponents = Int[]
  S = local_basis_matrix(L, p)
  n = ncols(S)
  k = 1
  while k <= n
    G = S * F * transpose(S)
    X = Union{Int, PosInf}[ valuation(G[i, i], p) for i in k:n]
    m, ii = findmin(X)
    ii = ii + (k - 1)
    pair = (ii, ii)

    for i in k:n
      for j in (i + 1):n
        tmp = iszero(G[i, j]) ? inf : valuation(G[i, j], p)
        if tmp < m
          m = temp
          pair = (i, j)
        end
      end
    end

    if m != oldval
      push!(blocks, k)
      oldval = m
      push!(exponents, m)
    end

    if even && pair[1] != pair[2]
      swap_rows!(S, pair[1], k)
      swap_rows!(S, pair[2], k +1)

      T12 = (sub(S, k:k, 1:ncols(S)) * F * transpose(sub(S, k+1:k+1, 1:ncols(S))))[1, 1]
      for l in 1:ncols(S)
        S[k, l] = S[k, l] * pi^valuation(T12, p)//T12
      end

      T = (i, j) -> (sub(S, i:i, 1:ncols(S)) * F * transpose(sub(S, j:j, 1:ncols(S))))[1, 1]
      T11 = T(k, k)
      T22 = T(k + 1, k + 1)
      T12 = T(k, k + 1)
      d = T11*T22 - T12^2
      for l in (k + 2):n
        tl = T12 * T(k + 1, l) - T22 * T(k, l)
        ul = T12 * T(k, l) - T11 * T(k + 1, l)
        for u in 1:ncols(S)
          S[l, u] = (tl//d) * S[k, l] + (ul//d) * S[k + 1, u]
        end
      end
      k = k + 2
    else
      if pair[1] == pair[2]
        swap_rows!(S, pair[1], k)
      else
        for u in 1:ncols(S)
          S[pair[1], u] = S[pair[1], u] + S[pair[2], u]
          swap_rows!(S, pair[1], k)
        end
      end
      nrm = (sub(S, k:k, 1:ncols(S)) * F * transpose(sub(S, k:k, 1:ncols(S))))[1, 1]
      XX = sub(S, k:k, 1:ncols(S)) * F * transpose(S)
      for l in k+1:n
        for u in 1:ncols(S)
          S[l, u] = S[l, u] - XX[1,l]//nrm * S[k, u]
        end
      end
      k = k + 1
    end
  end

  push!(blocks, n+1)
  matrices = typeof(F)[ sub(S, blocks[i]:(blocks[i+1] - 1), 1:ncols(S)) for i in 1:(length(blocks) - 1)]
  return matrices, typeof(F)[ m * F * transpose(m) for m in matrices], exponents
end

_contains_2(p) = 2 in p

_contains_2(p::fmpz) = p == 2

function jordan_decomposition(L::HermLat, p)
  R = base_ring(L)
  aut = involution(L)
  even = _contains_2(p)

  S = local_basis_matrix(L, p)

  D = prime_decomposition(R, p)
  split = length(D) == 2
  ram = D[1][2] == 2
  n = rank(L)

  P = D[1][1]

  if split
    # I need a p-uniformizer
    pi = elem_in_nf(p_uniformizer(P))
    @assert valuation(pi, D[2][1]) == 0
  elseif ram
    pi = elem_in_nf(uniformizer(P))
  else
    pi = base_field(L)(elem_in_nf(uniformizer(p)))
    su = even ? _special_unit(P, p) : one(nf(order(P)))
  end

  oldval = inf
  blocks = []
  exponents = []

  F = gram_matrix(ambient_space(L))

  k = 1
  while k <= n
    G = S * F * transpose(_map(S, aut))
    X = Union{Int, PosInf}[ valuation(G[i, i], P) for i in k:n]
    m, ii = findmin(X)
    ii = ii + (k - 1)
    pair = (ii, ii)
    for i in k:n
      for j in k:n
        tmp = iszero(G[i, j]) ? inf : valuation(G[i, j], P)
        if tmp < m
          m = tmp
          pair = (i, j)
        end
      end
    end
    if m != oldval
      push!(blocks, k)
      oldval = m
      push!(exponents, m)
    end
    i, j = pair[1], pair[2]
    if (i != j) && !(ram && (even || isodd(m)))
      a = G[i, j]
      if split
        lambda = valuation(pi * a, P) == m ? pi : aut(pi)
      elseif ram
        @assert iseven(m)
        lambda = norm(pi)^(div(m ,2))//a
      else
        lambda = pi^m//a * su
      end
      for l in 1:ncols(S)
        S[i, l] = S[i, l] + aut(lambda) * S[j, l]
      end
      G = S * F * transpose(_map(S, aut))
      @assert valuation(G[i, i], P) == m
      j = i
    end

    if i != j
      swap_rows!(S, i, k)
      swap_rows!(S, j, k + 1)
      SF = S * F
      X1 = SF * transpose(_map(view(S, k:k, 1:ncols(S)), aut))
      X2 = SF * transpose(_map(view(S, (k + 1):(k + 1), 1:ncols(S)), aut))
      for l in k+2:n
        den = norm(X2[k, 1]) - X1[k, 1] * X2[k + 1, 1]
        for o in 1:ncols(S)
          S[l, o] = S[l, o] - (X2[l, 1] * X1[k + 1, 1] - X1[l, 1] * X2[k + 1, 1])//den * S[k, o] +
                    (X1[l, 1] * X2[k, 1] - X2[l, 1] * X1[k, 1])//den * S[k + 1, o]
        end
      end
      k = k + 2
    else
      swap_rows!(S, i, k)
      X1 = S * F * transpose(_map(view(S, k:k, 1:ncols(S)), aut))
      for l in (k + 1):n
        for o in 1:ncols(S)
          S[l, o] = S[l, o] - X1[l, 1]//X1[k, 1] * S[k, o]
        end
      end
      k = k + 1
    end
  end

  if !ram
    G = S * F * transpose(_map(S, aut))
    @assert isdiagonal(G)
  end

  push!(blocks, n + 1)

  matrices = typeof(F)[ sub(S, blocks[i]:(blocks[i+1] - 1), 1:ncols(S)) for i in 1:(length(blocks) - 1)]
  return matrices, typeof(F)[ m * F * transpose(_map(m, aut)) for m in matrices], exponents
end

################################################################################
#
#  Genus symbol
#
################################################################################

mutable struct LocalGenusSymbol{S}
  P
  data
  x
  iseven::Bool
  E
  isramified
  non_norm
end

prime(G::LocalGenusSymbol) = G.P

uniformizer(G::LocalGenusSymbol{QuadLat}) = G.x

data(G::LocalGenusSymbol) = G.data

base_field(G::LocalGenusSymbol) = G.E

function Base.show(io::IO, G::LocalGenusSymbol)
  print(io, "Local genus symbol at\n")
  print(IOContext(io, :compact => true), G.P)
  compact = get(io, :compact, false)
  if !compact
    print(io, "\nwith base field\n")
    print(io, base_field(G))
  end
  println(io, "\nWith data ", data(G))
  !G.iseven ? println(io, "and unifomizer\n", G.x) : nothing
end

# TODO: I have to redo this
function _genus_symbol_kirschmer(L::QuadLat, p::NfOrdIdl; uniformizer = zero(order(p)))
  O = order(p)
  nf(O) != base_field(L) && throw(error("Prime ideal must be an ideal of the base field of the lattice"))
  # If you pull from cache, you might have to adjust the symbol according
  # to the uniformizer flag

  J, G, E = jordan_decomposition(L, p)
  if !iszero(uniformizer)
    unif = uniformizer
    if valuation(unif, p) != 1
      throw(error("Wrong uniformizer"))
    end
  else
    unif = elem_in_nf(Hecke.uniformizer(p))
  end

  if minimum(p) != 2
    _, _h = ResidueField(O, p)
    h = extend(_h, nf(O))
    Gs = [ h(prod(diagonal(G[i]))//unif^(E[i] * nrows(J[i]))) for i in 1:length(J)]
    @assert !(0 in Gs)
    x  = [ (nrows(J[i]), E[i], issquare(Gs[i])[1] ? 1 : -1) for i in 1:length(J)]
    return LocalGenusSymbol{QuadLat}(p, x, unif, false, base_field(L), nothing, nothing)
  else
    t = length(G)
    sL = [ minimum(iszero(g[i, j]) ? inf : valuation(g[i, j], p) for j in 1:ncols(g) for i in 1:j) for g in G]
    @assert sL == E
    e = ramification_index(p)
    aL = []
    uL = []
    wL = []
    for i in 1:t
      GG = diagonal_matrix([ j < i ? unif^(2*(sL[i] - sL[j])) * G[j] : G[j] for j in 1:t])
      D = diagonal(GG)
      m, pos = findmin([valuation(d, p) for d in D])
      if e + sL[i] <= m
        push!(aL, unif^(e + sL[i]))
      else
        push!(aL, D[pos])
      end
      push!(uL, valuation(aL[i], p))
      push!(wL, min(e + sL[i], minimum(uL[i] + quadratic_defect(d//aL[i], p) for d in D)))
    end
    fL = []
    for k in 1:(t - 1)
      exp = uL[k] + uL[k + 1]
      push!(fL, (isodd(exp) ? exp : min(quadratic_defect(aL[k] * aL[k + 1], p), uL[k] + wL[k + 1], uL[k + 1], wL[k], e + div(exp, 2) + sL[k])) - 2*sL[k])
    end
    return LocalGenusSymbol{QuadLat}(p, ([nrows(G[k]) for k in 1:t], sL, wL, aL, fL, G), unif, true, base_field(L), nothing, nothing)
  end
end

function Base.:(==)(G1::LocalGenusSymbol{QuadLat}, G2::LocalGenusSymbol{QuadLat})
  if uniformizer(G1) != uniformizer(G2)
    error("Uniformizers of the genus symbols must be equal")
  end
  return data(G1) == data(G2)
end

################################################################################
#
#  Local genus symbol
#
################################################################################

mutable struct LocalGenusSymbolHerm
  E                # Field
  p                # prime of base_field(E)
  data             # data
  norm_val         # additional norm valuation (for the dyadic case)
  isdyadic::Bool   # 2 in p
  isramified::Bool # p ramified in E
  non_norm_rep     # u in K*\N(E*)
  ni::Vector{Int}  # ni for the ramified, dyadic case

  function LocalGenusSymbolHerm()
    z = new()
    return z
  end
end

function Base.show(io::IO, ::MIME"text/plain", G::LocalGenusSymbolHerm)
#function Base.show(io::IO, G::LocalGenusSymbolHerm)
  compact = get(io, :compact, false)
  if !compact
    print(io, "Local genus symbol at\n")
    print(io, prime(G))
    print(io, "\n")
  end
  if isdyadic(G) && isramified(G)
    for i in 1:length(G)
      print(io, "(", scale(G, i), ", ", rank(G, i), ", ", det(G, i) == 1 ? "+" : "-", ", ", norm(G, i), ")")
    end
  else
    for i in 1:length(G)
      print(io, "(", scale(G, i), ", ", rank(G, i), ", ", det(G, i) == 1 ? "+" : "-",  ")")
    end
  end
end

function Base.show(io::IO, G::LocalGenusSymbolHerm)
  if isdyadic(G) && isramified(G)
    for i in 1:length(G)
      print(io, "(", scale(G, i), ", ", rank(G, i), ", ", det(G, i) == 1 ? "+" : "-", ", ", norm(G, i), ")")
      if i < length(G)
        print(io, " ")
      end
    end
  else
    for i in 1:length(G)
      print(io, "(", scale(G, i), ", ", rank(G, i), ", ", det(G, i) == 1 ? "+" : "-",  ")")
      if i < length(G)
        print(io, " ")
      end
    end
  end
end

# Basic properties

scale(G::LocalGenusSymbolHerm, i::Int) = G.data[i][1]

rank(G::LocalGenusSymbolHerm, i::Int) = G.data[i][2]

det(G::LocalGenusSymbolHerm, i::Int) = G.data[i][3]

norm(G::LocalGenusSymbolHerm, i::Int) = begin @assert isdyadic(G); G.norm_val[i] end # this only works if it is dyadic

isramified(G::LocalGenusSymbolHerm) = G.isramified

isdyadic(G::LocalGenusSymbolHerm) = G.isdyadic

data(G::LocalGenusSymbolHerm) = G.data

length(G::LocalGenusSymbolHerm) = length(G.data)

base_field(G::LocalGenusSymbolHerm) = G.E

prime(G::LocalGenusSymbolHerm) = G.p

# Get the "ni" for the ramified dyadic case
function _get_ni_from_genus_symbol(G::LocalGenusSymbolHerm)
  @assert isramified(G)
  @assert isdyadic(G)
  z = data(G)
  t = length(z)
  z = Vector{Int}(undef, t)
  for i in 1:t
    ni = minimum(2 * max(0, scale(G, i) - scale(G, j)) + 2 * norm(G, j) for j in 1:t)
    z[i] = ni
  end
  return z
end

function det(G::LocalGenusSymbolHerm)
  return prod(det(G, i) for i in 1:length(G))
end

@doc Markdown.doc"""
    det_representative(G::LocalGenusSymbolHerm) -> NumFieldElem

Return a representative for the norm class of the determinant of $G$.
"""
function det_representative(G::LocalGenusSymbolHerm)
  z = G.data
  d = prod(b[3] for b in z)
  v = sum(b[1] * b[2] for b in z)
  if isramified(maximal_order(G.E), G.P)
    v = div(v, 2)
  end
  if d == 1
    u = base_field(base_field(G))(1)
  else
    @assert isramified(G)
    u = _non_norm(G)
  end
  return u * uniformizer(G)^v
end

function rank(G::LocalGenusSymbolHerm)
  return sum(rank(G, i) for i in 1:length(G))
end

################################################################################
#
#  Constructor
#
################################################################################

function genus_symbol(::Type{HermLat}, E, p, data)
  z = LocalGenusSymbolHerm()
  z.E = E
  z.p = p
  z.isdyadic = _contains_2(p)
  z.isramified = isramified(maximal_order(E), p)
  if isramified(z) && isdyadic(z)
    z.data = Tuple{Int, Int, Int}[Base.front(v) for v in data]
    z.norm_val = Int[v[end] for v in data]
    z.ni = _get_ni_from_genus_symbol(z)
  else
    z.data = data
  end
  return z
end

################################################################################
#
#  Genus symbol of a lattice
#
################################################################################

# TODO: caching
# TODO: better documentation

@doc Markdown.doc"""
    genus_symbol(L::HermLat, p::NfOrdIdl) -> LocalGenusSymbolHerm

Returns the genus symbol of $L$ at the prime ideal $\mathfrak{p}$.

See [Kir16, Definition 8.3.1].
"""
function genus_symbol(L::HermLat, p)
  sym = _genus_symbol(L, p)
  G = genus_symbol(HermLat, nf(base_ring(L)), p, sym)
  # Just for debugging 
  if isdyadic(G) && isramified(G)
    GG = _genus_symbol_kirschmer(L, p)
    for i in 1:length(G)
      @assert GG[i][4] == G.ni[i]
    end
    #
  end
  return G
end

################################################################################
#
#  Equality
#
################################################################################

function ==(G1::LocalGenusSymbolHerm, G2::LocalGenusSymbolHerm)
  if base_field(G1) != base_field(G2)
    return false
  end

  if prime(G1) != prime(G2)
    return false
  end

  if length(G1) != length(G2)
    return false
  end

  t = length(G1)

  p = prime(G1)

  # We now check the Jordan type

  if any(i -> scale(G1, i) != scale(G2, i), 1:t)
    return false
  end

  if any(i -> (rank(G1, i) != rank(G2, i)), 1:t)
    return false
  end

  if det(G1) != det(G2) # rational spans must be isometric
    return false
  end

  if any(i -> (rank(G1, i) != rank(G2, i)), 1:t)
    return false
  end

  if !isramified(G1) # split or unramified
    return true
    # Everything is normal and the Jordan decomposition types agree
    #return all(det(G1, i) == det(G2, i) for i in 1:t)
  end

  if isramified(G1) && !isdyadic(G1) # ramified, but not dyadic
    # If s(L_i) is odd, then L_i = H(s(L_i))^(rk(L_i)/2) = H(s(L_i'))^(rk(L_i')/2) = L_i'
    # So all L_i, L_i' are locally isometric, in particular L_i is normal if and only if L_i' is normal
    # If s(L_i) = s(L_i') is even, then both L_i and L_i' have orthgonal bases, so they are
    # in particular normal.

    # Thus we only have to check Theorem 3.3.6 4.
    return all(i -> det(G1, i) == det(G2, i), 1:t)
    # TODO: If think I only have to do something if the scale is even. Check this!
  end

  # Dyadic ramified case

  # First check if L_i is normal if and only if L_i' is normal, i.e.,
  # that the Jordan decompositions agree
  for i in 1:t
    if (scale(G1, i) == 2 * norm(G1, i)) != (scale(G2, i) == 2 * norm(G2, i))
      return false
    end
  end

  if any(i -> G1.ni[i] != G2.ni[i], 1:t)
    return false
  end

  E = base_field(G1)
  lQ = prime_decomposition(maximal_order(E), p)
  @assert length(lQ) == 1 && lQ[1][2] == 2
  Q = lQ[1][1]

  e = valuation(different(maximal_order(E)), Q)

  for i in 1:(t - 1)
    dL1prod = prod(det(G1, j) for j in 1:i)
    dL2prod = prod(det(G2, j) for j in 1:i)

    d = dL1prod * dL2prod

    if d != 1
      if 2 * (e - 1) < G1.ni[i] + G1.ni[i + 1] - 2 * scale(G1, i)
        return false
      end
    end
  end

  return true
end

function _genus_symbol(L::HermLat, p)
  @assert order(p) == base_ring(base_ring(L))
  B, G, S = jordan_decomposition(L, p)
  R = base_ring(L)
  E = nf(R)
  K = base_field(E)
  if !_contains_2(p) || !isramified(R, p)
    sym = Tuple{Int, Int, Int}[ (nrows(B[i]), S[i], islocal_norm(E, coeff(det(G[i]), 0), p) ? 1 : -1) for i in 1:length(B)]
  else
    P = prime_decomposition(R, p)[1][1]
    pi = E(K(Hecke.uniformizer(p)))
    sym = Tuple{Int, Int, Int, Int}[]
    for i in 1:length(B)
      normal = _get_norm_valuation_from_gram_matrix(G[i], P) == S[i]
      GG = diagonal_matrix([pi^(max(0, S[i] - S[j])) * G[j] for j in 1:length(B)])
      v = _get_norm_valuation_from_gram_matrix(GG, P)
      @assert v == valuation(R * norm(lattice(hermitian_space(E, GG), identity_matrix(E, nrows(GG)))), P)
      r = nrows(B[i]) # rank
      s = S[i] # P-valuation of scale(L_i)
      det_class = islocal_norm(E, coeff(det(G[i]), 0), p) ? 1 : -1  # Norm class of determinant
      normi = _get_norm_valuation_from_gram_matrix(G[i], P) # P-valuation of norm(L_i)
      @assert mod(normi, 2) == 0 # I only want p-valuation
      push!(sym, (r, s, det_class, div(normi, 2)))
    end
  end
  return sym
end



# This is the "Magma" Genus symbol
function _genus_symbol_kirschmer(L::HermLat, p; uniformizer = zero(order(p)))
  @assert order(p) == base_ring(base_ring(L))

  B, G, S = jordan_decomposition(L, p)
  R = base_ring(L)
  E = nf(R)
  K = base_field(E)
  if !_contains_2(p) || !isramified(R, p)
    sym = [ (nrows(B[i]), S[i], islocal_norm(E, coeff(det(G[i]), 0), p)) for i in 1:length(B)]
  else
    P = prime_decomposition(R, p)[1][1]
    pi = E(K(Hecke.uniformizer(p)))
    sym = []
    for i in 1:length(B)
      normal = _get_norm_valuation_from_gram_matrix(G[i], P) == S[i]
      GG = diagonal_matrix([pi^(max(0, S[i] - S[j])) * G[j] for j in 1:length(B)])
      v = _get_norm_valuation_from_gram_matrix(GG, P)
      @assert v == valuation(R * norm(lattice(hermitian_space(E, GG), identity_matrix(E, nrows(GG)))), P)
      s = (nrows(B[i]), S[i], normal, v, coeff(det(diagonal_matrix([G[j] for j in 1:i])), 0))
      push!(sym, s)
    end
  end
  return sym
end

################################################################################
#
#  Local isometry
#
################################################################################

# base case for order(p) == base_ring(base_ring(L1))
function islocally_isometric(L1::HermLat, L2::HermLat, p)
  # Test first rational equivalence
  return genus_symbol(L1, p) == genus_symbol(L2, p)
end

function _islocally_isometric_kirschmer(L1::HermLat, L2::HermLat, p)
  R = base_ring(L1)
  E = nf(R)
  S1 = _genus_symbol(L1, p)
  S2 = _genus_symbol(L2, p)
  if !_contains_2(p) || !isramified(R, p)
    return S1 == S2
  end

  t = length(S1)
  if t != length(S2)
    return false
  end
  for i in 1:t
    for k in 1:4
      if S1[i][k] != S2[i][k]
        return false
      end
    end
  end

  if !islocal_norm(E, S1[t][5]//S2[t][5], p)
    return false
  end

  for i in 1:(t-1)
    @assert valuation(S1[i][5], p) == valuation(S2[i][5], p)
    x = S1[i][5]//S2[i][5]
    n = 2 * normic_defect(E, x, p)
    if n < (S1[i][4] + S1[i + 1][4]) - 2 * S1[i][2]
      return false
    end
  end
  return true
end

################################################################################
#
#  Global genus symbol
#
################################################################################

mutable struct GlobalGenusSymbol{S}
  E
  primes::Vector
  LGS::Vector
  rank::Int
  signatures

  function GlobalGenusSymbol{S}(LGS::Vector, signatures) where {S}
    @assert !isempty(LGS)
    @assert all(N >= 0 for (_,N) in signatures)
    if !_check_global_genus_symbol(LGS, signatures)
      throw(error("Invariants violate the product formula."))
    end
    g = first(LGS)
    E = base_field(g)
    r = rank(g)
    primes = Vector(undef, length(LGS))


    for i in 1:length(LGS)
      primes[i] = prime(LGS[i])
      @assert r == rank(LGS[i])
    end
    z = new{S}(E, primes, LGS, r, signatures)
    return z
  end
end

function _check_global_genus_symbol(LGS, signatures)
  _non_norm = _non_norm_primes(LGS)
  P = length(_non_norm)
  I = length([(s, N) for (s, N) in signatures if mod(N, 2) == 1])
  if mod(P + I, 2) == 1
    return false
  end
  return true
end

function _non_norm_primes(LGS::Vector)
  z = []
  for g in LGS
    p = prime(g)
    d = det(g)
    if d != 1
      push!(z, g)
    end
  end
  return z
end

function Base.getindex(G::GlobalGenusSymbol, P)
  i = findfirst(isequal(P), G.primes)
  if i === nothing
    throw(error("No local genus symbol at $P"))
  end
  return G.LGS[i]
end

################################################################################
#
#  Change the uniformizer of a Genus symbol
#
################################################################################

@doc Markdown.doc"""
    change_uniformizer(G::LocalGenusSymbol, a::NfOrdElem) -> LocalGenusSymbol

Returns an equivalent? genus symbol with uniformizer $a$.
"""
function change_uniformizer(G::LocalGenusSymbol{QuadLat}, unif::NfOrdElem)
  if unif == uniformizer(G)
    return G
  end
  P = prime(G)
  @assert isodd(minimum(P))
  @assert valuation(unif, P) == 1
  _, mF = ResidueField(order(P), P)
  mFF = extend(mF, nf(order(P)))
  b,_ = issquare(mFF(unif//uniformizer(G)))
  if b
    return LocalGenusSymbol{QuadLat}(P, G.data, unif, G.iseven, G.E, nothing, nothing)
  else
    e = G.data[1]
    return LocalGenusSymbol{QuadLat}(P, (e[1], e[2], isodd(e[1] * e[2]) ? -e[3] : e[3]), unif, G.iseven, G.E, nothing, nothing)
  end
end

################################################################################
#
#  Local isometry
#
################################################################################

@doc Markdown.doc"""
    islocally_isometric(L::AbsLat, M::AbsLat, p::NfOrdIdl) -> Bool

Returns whether the completions of $L$ and $M$ at the prime ideal
$\mathfrak{p}$ are locally isometric.
"""
islocally_isometric(::AbsLat, ::AbsLat, ::NfOrdIdl)

function islocally_isometric(L::QuadLat, M::QuadLat, p::NfOrdIdl)
  R = base_ring(L)
  base_ring(L) != base_ring(M) && throw(error("Lattices must have the same base ring"))
  order(p) != R && throw(error("Ideal must be in the base ring of the lattices"))
  d = rank(L)
  if d != rank(M)
    return false
  elseif d == 0
    return true
  end

  if minimum(p) != 2
    SL = _genus_symbol_kirschmer(L, p)
    SM = _genus_symbol_kirschmer(M, p, uniformizer = uniformizer(SL))
    return SL == SM
  end

  if !isrationally_equivalent(L, M, p)
    return false
  end

  dimL1, sL1, wL1, aL1, fL1, G1 = data(genus_symbol(L, p))
  dimL2, sL2, wL2, aL2, fL2, G2 = data(genus_symbol(M, p))

  if (dimL1 != dimL2) || (sL1 != sL2) || (wL1 != wL2)
    return false
  end

  uL1 = [valuation(aL1[k], p) for k in 1:length(aL1)]
  uL2 = [valuation(aL2[k], p) for k in 1:length(aL2)]
  if uL1 != uL2
    return false
  end

  bL = [aL1[k]//aL2[k] for k in 1:length(aL1)];
  qL = [quadratic_defect(bL[k], p) for k in 1:length(bL)]

  if reduce((x, y) -> (x || y), qL[k] < wL1[k] - uL2[k] for k in 1:length(qL))
    return false
  end

  e = ramification_index(p)
  # GL, GM: Gram matrix
  d1 = [ diagonal_matrix([G1[i] for i in 1:t]) for t in 1:length(G1)]
  d2 = [ diagonal_matrix([G2[i] for i in 1:t]) for t in 1:length(G2)]

  # This cannot work, what is going on here
  for i in 1:length(fL1)
    detquot = determinant(d1[i])//determinant(d2[i])
    if valuation(detquot, p) != 0
      return false
    end
    if quadratic_defect(detquot, p) < fL1[i]
      return false
    end
    if (fL1[i] > 2*e + uL1[i+1] - wL2[i+1]) && !(my_little_helper(d1[i], diagonal_join(d2[i], matrix(base_ring(d2[i]), 1, 1, [aL2[i+1]])), p))
      return false
    end
    if (fL1[i] > 2*e + uL1[i  ] - wL2[i  ]) && !(my_little_helper(d1[i], diagonal_joint(d2[i], matrix(base_ring(d2[i]), 1, 1, [aL2[i]])), p))
      return false
    end
  end

  return true
end

################################################################################
#
#  Compute representatives of genera
#
################################################################################

function _hermitian_form_with_invariants(E, dim, P, N)
  K = base_field(E)
  R = maximal_order(K)
#  require forall{n: n in N | n in {0..dim}}: "Number of negative entries is impossible";
  infinite_pl = [ p for p in real_places(K) if _decomposition_number(E, p) == 1 ]
  length(N) != length(infinite_pl) && error("Wrong number of real places")
  S = maximal_order(E)
  prim = [ p for p in P if length(prime_decomposition(S, p)) == 1 ] # only take non-split primes
  I = [ p for p in keys(N) if isodd(N[p]) ]
  !iseven(length(I) + length(P)) && error("Invariants do not satisfy the product formula")
  e = gen(E)
  x = 2 * e - trace(e)
  b = coeff(x^2, 0) # b = K(x^2)
  a = _find_quaternion_algebra(b, prim, I)
  D = elem_type(E)[]
  for i in 1:(dim - 1)
    if length(I) == 0
      push!(D, one(E))
    else
      push!(D, E(_weak_approximation(infinite_pl, [N[p] >= i ? -1 : 1 for p in infinite_pl])))
    end
  end
  push!(D, a * prod(D))
  Dmat = diagonal_matrix(D)
  dim0, P0, N0 = _hermitian_form_invariants(Dmat)
  @assert dim == dim0
  @assert P == P0
  @assert N == N0
  return Dmat
end

function _hermitian_form_invariants(M)
  E = base_ring(M)
  K = base_field(E)
  @assert degree(E) == 2
  A = automorphisms(E)
  a = gen(E)
  v = A[1](a) == a ? A[2] : A[1]

  @assert M == transpose(_map(M, v))
  d = coeff(det(M), 0) # K(det(M))
  P = Dict()
  for p in keys(factor(d * maximal_order(K)))
    if islocal_norm(E, d, p)
      continue
    end
    P[p] = true
  end
  for p in keys(factor(discriminant(maximal_order(E))))
    if islocal_norm(E, d, p)
      continue
    end
    P[p] = true
  end
  D = diagonal(_gram_schmidt(M, v)[1])
  I = Dict([ p=>length([coeff(d, 0) for d in D if isnegative(coeff(d, 0), p)]) for p in real_places(K) if _decomposition_number(E, p) == 1])
  return ncols(M), collect(keys(P)), I
end

################################################################################
#
#  Enumeration of local genera
#
################################################################################

function _local_genera_symbols(E, p, rank, det_val, max_scale, is_ramified)
  if is_ramified
    # the valuation is with respect to p
    # but the scale is with respect to P
    # in the ramified case p = P**2 and thus
    # the determinant of a block is
    # P^(scale*rank) = p^(scale*rank/2)
    det_val *= 2
  end

  K = number_field(order(p))

  scales_rks = [] # possible scales and ranks

  for rkseq in _integer_lists(rank, max_scale + 1)
    d = 0
    pgensymbol = []
    for i in 0:(max_scale + 1) - 1
      d += i * rkseq[i + 1]
      if rkseq[i + 1] != 0
        push!(pgensymbol, (i, rkseq[i + 1]))
      end
    end
    if d == det_val
        push!(scales_rks, pgensymbol)
    end
  end

  if !is_ramified
    return [ genus_symbol(HermLat, E,p, [(b..., 1) for b in g]) for g in scales_rks]
  end

  scales_rks = [g for g in scales_rks if all((mod(b[1]*b[2], 2) == 0) for b in g)]

  symbols = []
  hyperbolic_det = hilbert_symbol(K(-1), gen(K)^2//4 - 1, p)
  if !_contains_2(p) # non-dyadic
    for g in scales_rks
      n = length(g)
      dets = []
      for b in g
        if mod(b[1], 2) == 0
          push!(dets, [1, -1])
        end
        if mod(b[1], 2) == 1
          push!(dets, [hyperbolic_det^(div(b[2], 2))])
        end
      end

      for d in Iterators.product(dets...)
        g1 = copy(g)
        for k in 1:n
          # this is wrong
          push!(symbols, genus_symbol(HermLat, E, p, (g1[k]..., d[k])))
        end
      end
    end
    return symbols
  end

  # Ramified case
  lp = prime_decomposition(maximal_order(E), p)
  @assert length(lp) == 1 && lp[1][2] == 2
  P = lp[1][1]
  
  e = valuation(different(maximal_order(E)), P)
  # only for debugging
  scales_rks = reverse(scales_rks)

  for g in scales_rks
    n = length(g)
    det_norms = []
    #println(" === g: $g")
    for b in g
      #println(" ======== b: $b")
      if mod(b[2], 2) == 1
        @assert iseven(b[1])
        push!(det_norms, [[1, div(b[1], 2)], [-1, div(b[1], 2)]])
      end
      if mod(b[2], 2) == 0
        dn = []
        i = b[1]
        # (i + e) // 2 => k >= i/2
        for k in (ceil(Int, Int(i)//2)):(div(Int(i + e), 2) - 1)
          push!(dn, [1, k])
          push!(dn, [-1, k])
        end
        push!(dn, [hyperbolic_det^(div(b[2], 2)), div(i + e, 2)])
        if mod(i + e, 2) == 1
          push!(dn, [-hyperbolic_det^(div(b[2], 2)), div(i + e, 2)])
        end
        push!(det_norms, dn)
      end
    end
    #println("================ det_norms: $det_norms")
    for dn in Iterators.product(det_norms...)
      g1 = deepcopy(g)
      #println("g1 before: $g1")
      for k in 1:n
        g1[k] = (g1[k]..., dn[k]...)
      end
      h = genus_symbol(HermLat, E, p, g1)
      if !(h in symbols)
        push!(symbols, h)
      end
    end
  end
  return symbols
end

function hermitian_genera(E, rank, signatures, determinant; max_scale = nothing)
  K = base_field(E)
  OE = maximal_order(E)
  if max_scale === nothing
    _max_scale = determinant
  else
    _max_scale = max_scale
  end

  primes = support(discriminant(OE))
  for p in support(norm(determinant))
    if !(p in primes)
      push!(primes, p)
    end
  end

  local_symbols = []

  ms = norm(_max_scale)
  ds = norm(determinant)
  for p in primes
    det_val = valuation(ds, p)
    mscale_val = valuation(ms, p)
    det_val = div(det_val, 2)
    is_ram = isramified(OE, p)
    if !is_ram
      mscale_val = div(mscale_val, 2)
    end
    push!(local_symbols, _local_genera_symbols(E, p, rank, det_val, mscale_val, is_ram))
  end

  res = []
  it = Iterators.product(local_symbols...)
  for gs in it
    c = collect(gs)
    b = _check_global_genus_symbol(c, signatures)
    if b
      push!(res, GlobalGenusSymbol{HermLat}(c, signatures))
    end
  end

  return res
end

function _non_norm_rep(G::LocalGenusSymbolHerm)
  if isdefined(G, :non_norm_rep)
    return G.non_norm_rep
  end
  E = base_field(G)
  K = base_field(E)
  if isramified(G)
    if !isdyadic(G)
      U, mU = unit_group(maximal_order(K))
      local u
      for i in 1:ngens(U)
        u = mU(U[i])
        if !islocal_norm(E, u, prime(G))
          G.non_norm_rep = u
          return u
          break
        end
      end
    else
      lP = prime_decomposition(maximal_order(E), prime(G))
      @assert length(lP) == 1 && lP[1][2] == 2
      Q = lP[1][1]
      e = valuation(different(maximal_order(E)), Q)
      local u
      U, mU = unit_group(maximal_order(K))
      for i in 1:ngens(U)
        u = mU(U[i])
        if !islocal_norm(E, elem_in_nf(u), prime(G)) && (valuation(u - 1, prime(G)) == e - 1)
          G.non_norm_rep = u
          return u
          break
        end
      end
    end
  else
    error("This does not make any sense!")
  end
end

function uniformizer(G::LocalGenusSymbol{HermLat})
  E = base_field(G)
  K = base_field(E)
  if isramified(G)
    lP = prime_decomposition(maximal_order(E), prime(G))
    @assert length(lP) == 1 && lP[1][2] == 2
    Q = lP[1][1]
    pi = uniformizer(Q)
    A = automorphisms(E)
    uni = A[1](elem_in_nf(pi)) * A[2](elem_in_nf(pi))
    @assert iszero(coeff(uni, 1))
    @assert islocal_norm(E, coeff(uni , 0), prime(G))
    return coeff(uni, 0)
  else
    return uniformizer(prime(G))
  end
end

@doc Markdown.doc"""
    det(G::LocalGenusSymbol) -> NumFieldElem

Return the norm class of the determinant of $G$.
"""
function det(G::LocalGenusSymbol{HermLat})
  z = G.data
  d = prod(b[3] for b in z)
  v = sum(b[1] * b[2] for b in z)
  if isramified(maximal_order(G.E), G.P)
    v = div(v, 2)
  end
  if d == 1
    u = base_field(G.E)(1)
  else
    @assert isramified(G)
    u = _non_norm(G)
  end
  return u * uniformizer(G)^v
end

function rank(G::LocalGenusSymbol{HermLat})
  z = G.data
  return sum(b[2] for b in z)::Int
end

################################################################################
#
#  Helper
#
################################################################################

function _sum_modules(a::PMat, b::PMat)
  c = vcat(a, b)
  H = pseudo_hnf(H, :lowerleft)
  r = 0
  for i in 1:nrows(H)
    if !iszero_row(matrix(H), i)
      r = i
    end
  end
  @assert r != 0
  return sub(H, r:nrows(H), 1:cols(H))
end

function _intersect_modules(a::PMat, b::PMat)
  M1 = hcat(a, deepcopy(a))
  z = zero_matrix(base_ring(matrix(a)), d, d)
  M2 = hcat(pseudo_matrix(z, b.coeffs), b)
  M = vcat(M1, M2)
  H = sub(pseudo_hnf(M, :lowerleft), 1:d, 1:d)
end

function _modules_equality(a::PMat, b::PMat)
  _spans_subset_of_pseudohnf(a, b, :lowerleft) && _spans_subset_of_pseudohnf(b, a, :lowerleft)
end

function _module_scale_ideal(a::NfAbsOrdIdl, b::PMat)
  return pseudo_matrix(matrix(b), [ a * c for c in coefficient_ideals(b)])
end

_module_scale_ideal(a::PMat, b::NfAbsOrdIdl) = _module_scale_ideal(b, a)

function _module_scale_ideal(a::NfOrdFracIdl, b::PMat)
  return pseudo_matrix(matrix(b), a .* coefficient_ideals(b))
end

_module_scale_ideal(a::PMat, b::NfOrdFracIdl) = _module_scale_ideal(b, a)

function _module_scale_ideal(a::NfRelOrdIdl, b::PMat)
  return pseudo_matrix(matrix(b), a .* coefficient_ideals(b))
end

_module_scale_ideal(a::PMat, b::NfRelOrdIdl) = _module_scale_ideal(b, a)

function _module_scale_ideal(a::NfRelOrdFracIdl, b::PMat)
  return pseudo_matrix(matrix(b), a .* coefficient_ideals(b))
end

_module_scale_ideal(a::PMat, b::NfRelOrdFracIdl) = _module_scale_ideal(b, a)

function _local_basis_matrix(a::PMat, p::NfOrdIdl)
  @assert base_ring(a) == order(p)
  uni = uniformizer(p)
  z = zero_matrix(base_ring(matrix(a)), nrows(a), ncols(a))
  for i in 1:nrows(a)
    c = coefficient_ideals(a)[i]
    x = uni^valuation(c, p)
    for j in 1:ncols(a)
      z[i, j] = x * matrix(a)[i, j]
    end
  end
  return z
end

function _local_basis_matrix_prime_below(a::PMat, p)
  @assert base_ring(base_ring(a)) == order(p)
  R = base_ring(a)
  D = prime_decomposition(R, p)
  unis = [p_uniformizer(q[1]) for q in D]
  @assert all(valuation(unis[i], D[i][1]) == 1 for i in 1:length(D))
  @assert all(sum(valuation(unis[i], D[j][1]) for j in 1:length(D)) == 1 for i in 1:length(D))
  z = zero_matrix(base_ring(matrix(a)), nrows(a), ncols(a))
  for i in 1:nrows(a)
    c = coefficient_ideals(a)[i]
    x = unis[1]^valuation(c, D[1][1])
    for k in 2:length(D)
      x = x * unis[k]^valuation(c, D[k][1])
    end
    for j in 1:ncols(a)
      z[i, j] = x * matrix(a)[i, j]
    end
  end
  return z
end

function _local_basis_submodule_matrix(a::PMat, p::NfOrdIdl)
  z = zero_matrix(base_ring(matrix(a)), nrows(a), ncols(a))
  for i in 1:nrows(a)
    c = coefficient_ideals(a)[i]
    vpc = valuation(c, p)
    found = false
    local x
    for b in basis(c)
      if valuation(b, p) == vpc
        found = true
        x = b
        break
      end
    end
    @assert found
    for j in 1:ncols(a)
      z[i, j] = x * matrix(a)[i, j]
    end
  end
  return z
end

function _local_basis_supermodule_matrix(a::PMat, p::NfOrdIdl)
  z = zero_matrix(base_ring(matrix(a)), nrows(a), ncols(a))
  for i in 1:nrows(a)
    # need to do an approximate or approximate_simple
    for j in 1:ncols(a)
      z[i, j] = x * matrix(a)[i, j]
    end
  end
  return z
end

function image(S::T, A::NfOrdFracIdl) where {T <: Map}
  return S(numerator(A))//denominator(A)
end

function ideal_trace(I)
  E = nf(order(I))
  K = base_field(E)
  return fractional_ideal(maximal_order(K), [trace(b) for b in absolute_basis(I)])
end

function ideal_trace(I::NfOrdFracIdl)
  E = nf(order(I))
  K = base_field(E)
  return reduce(gcd, [trace(b) for b in basis(I)]; init = fmpq(0))
end

function isintegral(I::NfOrdFracIdl)
  @assert ismaximal(order(I))
  simplify(I)
  return denominator(I) == 1
end

# TODO: The scaling of pseudo-matrices with an element scales the ideals and not the matrix ...

@doc Markdown.doc"""
    islocal_norm(L::NumField, a::NumFieldElem, P)

Given a number field $L/K$, an element $a \in K$ and a prime ideal $P$ of $K$,
returns whether $a$ is a local norm at $P$.

The number field $L/K$ must be a simple extension of degree 2.
"""
islocal_norm(::NumField, ::NumFieldElem, ::Any)

function islocal_norm(K::AnticNumberField, a::fmpq, p::fmpz)
  degree(K) != 2 && error("Degree of number field must be 2")
  x = gen(K)
  b = (2 * x - tr(x))^2
  @assert degree(minpoly(b)) == 1
  bQ = coeff(b, 0)
  return hilbert_symbol(a, bQ, p) == 1
end

function islocal_norm(K::AnticNumberField, a::fmpq, P::NfOrdIdl)
  p = minimum(P)
  return islocal_norm(K, a, P)
end

function islocal_norm(K::AnticNumberField, a::RingElement, P::NfOrdIdl)
  return islocal_norm(K, FlintQQ(a), P)
end

function islocal_norm(K::AnticNumberField, a::RingElement, p::fmpz)
  return islocal_norm(K, FlintQQ(a), p)
end

function islocal_norm(K::AnticNumberField, a::RingElement, p::Integer)
  return islocal_norm(K, FlintQQ(a), fmpz(p))
end

function islocal_norm(K::NfRel{T}, a::T, P) where {T} # ideal of parent(a)
  nf(order(P)) != parent(a) && error("Prime ideal must have the same base field as the second argument")
  degree(K) != 2 && error("Degree of number field must be 2")
  x = gen(K)
  b = (2 * x - tr(x))^2
  @assert degree(minpoly(b)) == 1
  bQ = coeff(b, 0)
  return hilbert_symbol(a, bQ, P) == 1
end

# Return a local unit u (that is, valuation(u, P) = 0) with trace zero.
# P must be even and inert (P is lying over p)
function _special_unit(P, p)
  @assert ramification_index(P) == 1
  @assert 2 in p
  R = order(P)
  E = nf(R)
  @assert degree(E) == 2
  x = gen(E)
  x = x - trace(x)//2
  a = coeff(x^2, 0)
  K = base_field(E)
  pi = E(elem_in_nf(uniformizer(p)))
  v = valuation(a, p)
  if v != 0
    @assert iseven(v)
    a = a//pi^v
    x = x//pi^(div(v, 2))
  end
  k, h = ResidueField(order(p), p)
  hex = extend(h, K)
  t = hex \ sqrt(hex(a))
  a = a//t^2
  x = x//t
  w = valuation(a - 1, p)
  e = valuation(order(p)(2), p)
  while w < 2*e
    @assert iseven(w)
    s = sqrt(h((a - 1)//pi^w))
    t = 1 + (hex \ s) * pi^(div(w, 2))
    a = a//t^2
    x = x//t
    w = valuation(a - 1, p)
  end
  @assert w == 2 * e
  u = (1 + x)//2
  @assert trace(u) == 1
  @assert valuation(u, P) == 0
  return u
end

function sqrt(a::fq)
  Rt, t = PolynomialRing(parent(a), "t", cached = false)
  r = roots(t^2 - a)
  if length(r) > 0
    return r[1]
  else
    error("not root")
  end
end

ramification_index(P) = P.splitting_type[1]

# L is a list of (integral) number field elements
# and p a prime ideal of the maximal.
# Return v(tr(<L>), P).
function trace_ideal_valuation(L, p)
  R = order(p)
  v = valuation(different(R), p)
  V = unique!(valuation(l, p) for l in L if !iszero(l))
  X = Int[ 2 *div(l + v, 2) for l in V]
  if length(X) == 0
    return inf
  else
    minimum(X)
  end
end

function _get_norm_valuation_from_gram_matrix(G, P)
  n = ncols(G)
  R = order(P)
  L = nf(R)
  K = base_field(L)
  trrr = R * (ideal_trace(fractional_ideal(order(P), [G[i, j] for i in 1:n for j in i+1:n])))
  if iszero(trrr)
    T = inf
  else
    T = valuation(trrr, P)
  end
  #T = trace_ideal_valuation((G[i, j] for i in 1:n for j in i+1:n), P)
  diag = minimum(valuation(G[i, i], P) for i in 1:n)
  if T isa PosInf
    return diag
  else
    return min(T, diag)
  end
end

#
#function GetNorm(G, P)
#  n:= Ncols(G);
#  T:= TraceIdeal([ G[i,j]: j in [i+1..n], i in [1..n] ], P);
#  Diag:= Min([ Valuation(G[i,i], P) : i in [1..n] ]);
#  return Type(T) eq Infty select Diag else Min( Diag, T );
#end function;

function absolute_basis(I::NfOrdFracIdl)
  return basis(I)
end

function absolute_basis(I::NfRelOrdFracIdl)
  res = elem_type(nf(order(I)))[]
  pb = pseudo_basis(I)
  for (e, I) in pb
    for b in absolute_basis(I)
      push!(res, e * b)
    end
  end
  return res
end

order(::fmpz) = FlintZZ

uniformizer(p::fmpz) = p

function isramified(R, p)
  D = prime_decomposition(R, p)
  for (_, e) in D
    if e > 1
      return true
    end
  end
  return false
end

function normic_defect(E, a, p)
  R = maximal_order(E)
  if iszero(a) || islocal_norm(E, a, p)
    inf
  end
  return valuation(a, p) + valuation(discriminant(R), p) - 1
end

function _decomposition_number(E::NfRel{nf_elem}, p::InfPlc)
  f = defining_polynomial(E)
  prec = 32
  while true
    g = change_base_ring(f, x -> evaluate(x, p, 32))
    @assert all(i -> isreal(coeff(g, i)), 0:degree(g))
    try
      rts = roots(g, isolate_real = true)
      no_real = 0
      for r in rts
        if isreal(r)
          no_real += 1
        end
      end
      @assert mod(degree(f) - no_real, 2) == 0
      no_complex = div(degree(f) - no_real, 2)
      return no_real + no_complex
    catch e
      if e isa ErrorException
        prec = 2 * prec
        continue
      end
    end
  end
end

function _sign(x::arb) 
  if ispositive(x)
    return 1
  elseif isnegative(x)
    return -1
  else
    error("Could not determine sign")
  end
end

function _sign(x::acb) 
  if isreal(x)
    return _sign(real(x))
  else
    error("Element is not real")
  end
end

#// Given an element b in a number field K and sets of finite and infinite 
#// places P and I of K, return an element a in K such that 
#// { v: (a,b)_v = -1 } = P \cup I
#// Note that the function coputes the unit and class groups of K!

function _find_quaternion_algebra(b, P, I)
  @assert iseven(length(I) + length(P))
  @assert all(p -> !islocal_square(b, p), P)
  @assert all(p -> isnegative(evaluate(b, p)), I)

  K = parent(b)
  R = maximal_order(K)
  n = length(P)
  m = length(I)

  _J = b * R
  _P = Dict{}()
  for p in keys(factor(_J))
    _P[p] = true
  end
  for p in prime_decomposition(R, 2)
    _P[p[1]] = true
  end
  for p in real_places(K)
    if !(p in I) && isnegative(b, p)
      push!(I, p)
    end
  end
  F = Nemo.GF(2)
  target = matrix(F, 1, length(_P) + length(I), vcat(fill(1, n), fill(0, length(_P) - n), fill(1, m), fill(0, length(I) - m)))
  if iszero(target)
    return one(K)
  end

  __P = convert(Vector{NfOrdIdl}, collect(keys(_P)))

  found = false
  U, h = unit_group(R)
  sign_vector = g -> begin
    return matrix(F, 1, length(_P) + length(I),
                 vcat([div(1 - hilbert_symbol(K(g), b, p), 2) for p in __P ], [ div(1 - _sign(evaluate(g, p)), 2) for p in I]))
  end


  L, f = sunit_group(__P)
  M = zero_matrix(F, 0, length(_P) + length(I))
  elts = []

  for i in 1:ngens(L)
    v = sign_vector(f(L[i]))
    if rank(M) == rank(vcat(M, v))
      continue
    end
    M = vcat(M, v)
    push!(elts, f(L[i])) # cache
    fl, w = can_solve(M, target, side = :left)
    if fl 
      found = true
      break
    end
  end

  if !found
    Cl, mCl = class_group(R)
    A = DiagonalGroup(fill(0, length(_lP)))
    hh = hom(A, Cl, [mCl\(p) for p in _lP])
    S, mS = image(hh)
    Q, mQ = quo(Cl, [mS(S[i]) for i in 1:ngens(S)])

    p = 2
    while !found
      p = next_prime(p)
      for (q, e) in prime_decomposition(R, p)
        if haskey(_P, q)
          continue
        end
        o = order(mQ(mCl\(q)))
        c = -(hh\(o * (mCl\(q))))
        fl, x = isprincipal(q * prod(_lP[i]^Int(c.coeff[i]) for i in 1:length(_lP)))
        @assert fl
        v = sign_vector(x)
        if rank(M) == rank(vcat(M, v + target))
          found = true
          M = vcat(M, v)
          push!(elts, x)
          break
        end
      end
    end
  end
  fl, v = can_solve(M, target, side = :left)
  @assert fl
  #@show v
  z = evaluate(FacElem(Dict(elts[i] => Int(lift(v[1, i])) for i in 1:ncols(v))))
  @assert sign_vector(z) == target
  return z
end

function _weak_approximation(I::Vector{InfPlc}, val::Vector{Int})
  K = number_field(first(I))
  OK = maximal_order(K)
  A, exp, log = infinite_primes_map(OK, I, 1 * OK)
  uni = infinite_places_uniformizers(K)
  target_signs = zeros(Int, ngens(A))

  for P in I
    v = log(uni[P])
    for i in 1:ngens(A)
      if v.coeff[i] == 1
        target_signs[i] = val[i] == -1 ? 1 : 0
      end
      break
    end
  end

  return K(exp(A(target_signs)))
end

# Compute all decreasing non-negative integer sequenes of length len with sum
# equal to sum.
# This is not optimized.
function _integer_lists(sum::Int, len::Int)
  if sum == 0
    return [fill(0, len)]
  end
  if len == 1
    return [Int[sum]]
  end
  res = Vector{Vector{Int}}()
  for i in 0:sum
    rec = _integer_lists(sum - i, len - 1)
    if isempty(rec)
      push!(res, append!(Int[i], fill(0, len - 1)))
    else
      for v in rec
        push!(res, append!(Int[i], v))
      end
    end
  end
  return res
end

function support(I::NfAbsOrdIdl)
  lp = factor(I)
  return collect(keys(lp))
end

function support(I::NfOrdFracIdl)
  lp = factor(I)
  return collect(keys(lp))
end

function support(I::NfRelOrdIdl)
  lp = factor(I)
  return collect(keys(lp))
end

function support(I::NfRelOrdFracIdl)
  lp = factor(I)
  return collect(keys(lp))
end

function support(a::NumFieldElem)
  return support(a * maximal_order(parent(a)))
end

p_uniformizer(P::NfOrdIdl) = uniformizer(P)
