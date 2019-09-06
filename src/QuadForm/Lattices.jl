export *, +, absolute_basis, absolute_basis_matrix, ambient_space, bad_primes,
       basis_matrix, can_scale_totally_positive, change_uniformizer,
       coefficient_ideal, degree, diagonal, discriminant, dual, fixed_field,
       generators, genus_symbol, gram_matrix_of_basis, hasse_invariant,
       hermitian_lattice, intersect, involution, isdefintie, isintegral,
       islocally_isometric, ismodular, isnegative_definite,
       ispositive_definite, isrationally_equivalent, jordan_decomposition,
       local_basis_matrix, norm, pseudo_matrix, quadratic_lattice, rank,
       rational_span, rescale, scale, volume, witt_invariant

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
identity matrix
"""
quadratic_lattice(::NumField, B::PMat; gram_ambient_space = nothing)

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
    z.pmat = P
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
identity matrix
"""
quadratic_lattice(::NumField, B::MatElem; gram_ambient_space = nothing)

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
identity matrix
"""
hermitian_lattice(::NumField, B::PMat; gram_ambient_space = nothing)

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
identity matrix
"""
hermitian_lattice(::NumField, B::MatElem; gram_ambient_space = nothing)

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

################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, L::QuadLat)
  println(io, "Quadratic lattice of rank $(rank(L)) and degree $(degree(L))")
  println(io, "over")
  print(io, base_algebra(L))
end

function Base.show(io::IO, L::HermLat)
  println(io, "Hermitian lattice of rank $(rank(L)) and degree $(degree(L))")
  println(io, "over")
  print(io, base_algebra(L))
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

Returns the ambient space of $L$. If the ambient space is not know, an
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
#  Module invariants
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

base_algebra(L::AbsLat) = L.base_algebra

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

Returns the witt invariant of the rational span of $L$ at $p$.
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
  C = coefficient_ideals(L)
  to_sum = sum(G[i, i] * C[i] * v(C[i]) for i in 1:length(C))
  to_sum = to_sum + K(reduce(gcd, [ideal_trace(C[i] * G[i, j] * v(C[j])) for j in 1:length(C) for i in 1:(j-1)]; init = fmpq(0)) ) * order(to_sum)
  return minimum(to_sum)
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
  f = factor(scale(L))
  ff = factor(volume(L))
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

function jordan_decomposition(L::HermLat, p)
  throw(NotImplemented())
end

################################################################################
#
#  Genus symbol
#
################################################################################

mutable struct GenusSymbol{T}
  P::T
  data
  x
  isodd::Bool
end

prime(G::GenusSymbol) = G.P

uniformizer(G::GenusSymbol) = G.x

data(G::GenusSymbol) = G.data

function Base.show(io::IO, G::GenusSymbol)
  print(io, "Genus Symbol at\n")
  print(IOContext(io, :compact => true), G.P)
  println(io, "\nWith data\n", data(G))
  G.isodd ? println(io, "and unifomizer\n", G.x) : nothing
end

# TODO: caching

@doc Markdown.doc"""
    genus_symbol(L::AbsLat, p::NfOrdIdl; uniformizer = uniformizer(p))
                                                                  -> GenusSymbol

Returns the genus symbol of $L$ at the prime ideal $\mathfrak{p}}$. One can
specify which uniformizer to choose using the `uniformizer` keyword.
"""
genus_symbol(::AbsLat, ::NfOrdIdl; uniformizer::Any = 0)

function genus_symbol(L::QuadLat, p::NfOrdIdl; uniformizer = zero(order(p)))
  O = order(p)
  nf(O) != base_field(L) && throw(error("Prime ideal must be an ideal of the base field of the lattice"))
  # If you pull from cache, you might have to adjust the symbol accoring
  # to the uniformizer flag

  J, G, E = jordan_decomposition(L, p)
  if !iszero(uniformizer)
    unif = uniformizer
    if valuation(unif, p) != 1
      throw(error("Wrong uniformizer"))
    end
  else
    unif = Hecke.uniformizer(p)
  end

  if minimum(p) != 2
    _, _h = ResidueField(O, p)
    h = extend(_h, nf(O))
    Gs = [ h(prod(diagonal(G[i]))//unif^(E[i] * nrows(J[i]))) for i in 1:length(J)]
    @assert !(0 in Gs)
    x  = [ (nrows(J[i]), E[i], issquare(Gs[i])[1] ? 1 : -1) for i in 1:length(J)]
    return GenusSymbol(p, x, unif, true)
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
    return GenusSymbol(p, ([nrows(G[k]) for k in 1:t], sL, wL, aL, fL, G), unif, false)
  end
end

function genus_symbol(L::HermLat, p::NfOrdIdl; uniformizer = zero(order(p)))
  throw(NotImplemented())
end

function Base.:(==)(G1::GenusSymbol, G2::GenusSymbol)
  if uniformizer(G1) != uniformizer(G2)
    error("Uniformizers of the genus symbols must be equal")
  end
  return data(G1) == data(G2)
end

################################################################################
#
#  Change the uniformizer of a Genus symbol
#
################################################################################

@doc Markdown.doc"""
    change_uniformizer(G::GenusSymbol, a::NfOrdElem) -> GenusSymbol

Returns an equivalent? genus symbol with uniformizer `a`.
"""
function change_uniformizer(G::GenusSymbol, unif::NfOrdElem)
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
    return GenusSymbol(P, G.data, unif)
  else
    e = G.data[1]
    return GenusSymbol(P, (e[1], e[2], isodd(e[1] * e[2]) ? -e[3] : e[3]), unif)
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
    SL = genus_symbol(L, p)
    SM = genus_symbol(M, p, uniformizer = uniformizer(SL))
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

function islocally_isometric(L::HermLat, M::HermLat, p::NfOrdIdl)
  throw(NotImplemented())
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
  return frac_ideal(maximal_order(K), [trace(b) for b in Basis(I)])
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

