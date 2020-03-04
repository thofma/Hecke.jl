export *, +, absolute_basis, absolute_basis_matrix, ambient_space, bad_primes,
       basis_matrix, can_scale_totally_positive, 
       coefficient_ideal, degree, diagonal, discriminant, dual, fixed_field,
       generators, gram_matrix_of_basis, hasse_invariant,
       hermitian_lattice, intersect, involution, isdefinite, isintegral,
       islocally_isometric, ismodular, isnegative_definite,
       ispositive_definite, isrationally_equivalent, jordan_decomposition,
       local_basis_matrix, norm, pseudo_matrix, quadratic_lattice, rank,
       rational_span, rescale, scale, volume, witt_invariant, lattice, Zlattice,
       automorphism_group_generators, automorphism_group_order, isisometric, islocal_norm, normic_defect

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
  automorphism_group_generators::Vector{T}
  automorphism_group_order::fmpz
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
    lattice(V::QuadSpace, B::PMat) -> QuadLat

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
    lattice(V::QuadSpace, B::MatElem) -> QuadLat

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
  automorphism_group_generators::Vector{U}
  automorphism_group_order::fmpz
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
    lattice(V::HermSpace, B::PMat) -> HermLat

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
    lattice(V::QuadSpace, B::MatElem) -> HermLat

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

Returns whether the ambient space of $L$ is known.
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
    throw(error("Ambient space not defined"))
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
    pseudo_matrix(L::AbsLat) -> PMat

Returns the basis pseudo-matrix of $L$.
"""
pseudo_matrix(L::AbsLat) = L.pmat

@doc Markdown.doc"""
    pseudo_basis(L::AbsLat) -> Vector{Tuple{Vector, Ideal}}

Returns the pseudo-basis of $L$.
"""
function pseudo_basis(L::AbsLat)
  M = matrix(pseudo_matrix(L))
  LpM = pseudo_matrix(L)
  z = Vector{Tuple{Vector{elem_type(base_ring(M))}, eltype(coefficient_ideals(LpM))}}(undef, nrows(M))
  for i in 1:nrows(M)
    z[i] = (elem_type(base_ring(M))[ M[i, j] for j in 1:ncols(M) ], coefficient_ideals(LpM)[i])
  end
  return z
end

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
  K = nf(base_ring(L))
  T = elem_type(K)
  v = Vector{T}[]
  for i in 1:(d - 1)
    #@assert isprincipal(coefficient_ideals(St)[i])[1]
    push!(v, T[matrix(St)[i, j] for j in 1:d])
  end

  I = numerator(coefficient_ideals(St)[d])
  den = denominator(coefficient_ideals(St)[d])
  if minimal && base_ring(L) isa NfOrd
    b, a = isprincipal(I)
    if b
      push!(v, T[K(a)//den * matrix(St)[n, j] for j in 1:d])
    end
    return v
  end

  if base_ring(L) isa NfOrd
    _assure_weakly_normal_presentation(I)
    push!(v, T[K(I.gen_one)//den * matrix(St)[n, j] for j in 1:d])
    push!(v, T[K(I.gen_two)//den * matrix(St)[n, j] for j in 1:d])
  else
    for g in absolute_basis(I)
      push!(v, T[K(g)//den * matrix(St)[n, j] for j in 1:d])
    end
  end

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
  return lattice(ambient_space(L), _module_scale_ideal(a, pseudo_matrix(L)))
end

function Base.:(*)(L::HermLat, a)
  @assert has_ambient_space(L)
  return lattice(ambient_space(L), _module_scale_ideal(a, pseudo_matrix(L)))
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
  pb = pseudo_basis(L)
  z = Vector{typeof(pb[1][1])}()
  for (v, a) in pb
    for w in absolute_basis(a)
      push!(z, w .* v)
    end
  end
  @assert length(z) == absolute_degree(base_field(L)) * rank(L)
  return z
end

@doc Markdown.doc"""
    absolute_basis_matrix(L::AbsLat) -> MatElem

Returns a $\mathbf{Z}$-basis matrix of $L$.
"""
function absolute_basis_matrix(L::AbsLat)
  pb = pseudo_basis(L)
  E = base_field(L)
  c = ncols(matrix(pseudo_matrix(L)))
  z = zero_matrix(E, rank(L) * absolute_degree(E), c)
  k = 1
  for (v, a) in pb
    for w in absolute_basis(a)
      for j in 1:c
        z[k, j] = w * v[j]
      end
      k += 1
    end
  end
  return z
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
fractional ideal $\mathfrak a$ such that $\mathfrak a L^\# = L$, where
$L^\#$ is the dual of $L$.
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
  if base_ring(L) == order(p)
    v = valuation(a, p)
    if v * rank(L) == valuation(volume(L), p)
      return true, v
    else
      return false, 0
    end
  else
    @assert base_ring(base_ring(L)) == order(p)
    q = prime_decomposition(base_ring(L), p)[1][1]
    v = valuation(a, q)
    if v * rank(L) == valuation(volume(L), q)
      return true, v
    else
      return false, 0
    end
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

# The docstring is confusing.
# If p is a prime ideal of base_ring(L), then it actually does
# local_basis_matrix(L, minimum(p),...)
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
    return local_basis_matrix(L, minimum(p), type = type)
    #if type == :any
    #  return _local_basis_matrix(pseudo_matrix(L), p)
    #elseif type == :submodule
    #  return _local_basis_submodule_matrix(pseudo_matrix(L), p)
    #elseif type == :supermodule
    #  return _local_basis_supermodule_matrix(pseudo_matrix(L), p)
    #else
    #  throw(error("""Invalid :type keyword :$(type).
    #                 Must be either :any, :submodule, or :supermodule"""))
    #end
  elseif S === base_ring(R)
    if type == :any
      return _local_basis_matrix_prime_below(pseudo_matrix(L), p)
    elseif type == :submodule
      return _local_basis_matrix_prime_below_submodule(pseudo_matrix(L), p)
    elseif type == :supermodule
      throw(NotImplemented())
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

function jordan_decomposition(L::HermLat, p)
  R = base_ring(L)
  aut = involution(L)
  even = isdyadic(p)

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
    X = Union{Int, PosInf}[ iszero(G[i, i]) ? inf : valuation(G[i, i], P) for i in k:n]
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
      @assert i < j
      swap_rows!(S, i, k)
      swap_rows!(S, j, k + 1)
      SF = S * F
      X1 = SF * transpose(_map(view(S, k:k, 1:ncols(S)), aut))
      X2 = SF * transpose(_map(view(S, (k + 1):(k + 1), 1:ncols(S)), aut))
      for l in k+2:n
        den = norm(X2[k, 1]) - X1[k, 1] * X2[k + 1, 1]
        t1 = (X2[l, 1] * X1[k + 1, 1] - X1[l, 1] * X2[k + 1, 1])//den 
        t2 = (X1[l, 1] * X2[k, 1] - X2[l, 1] * X1[k, 1])//den 

        for o in 1:ncols(S)
          S[l, o] = S[l, o] - (t1 * S[k, o] + t2 * S[k + 1, o])
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
#  Local isometry
#
################################################################################

# base case for order(p) == base_ring(base_ring(L1))
function islocally_isometric(L1::HermLat, L2::HermLat, p)
  # Test first rational equivalence
  return genus(L1, p) == genus(L2, p)
end

function _islocally_isometric_kirschmer(L1::HermLat, L2::HermLat, p)
  R = base_ring(L1)
  E = nf(R)
  S1 = _genus_symbol_kirschmer(L1, p)
  S2 = _genus_symbol_kirschmer(L2, p)
  if !isdyadic(p) || !isramified(R, p)
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
#  Isotropy
#
################################################################################

isisotropic(L::AbsLat, p) = isisotropic(rational_span(L), p)

################################################################################
#
#  Maximal integral lattices
#
################################################################################

#{Checks whether L is p-maximal integral. If not, a minimal integral over-lattice at p is returned}

function _ismaximal_integral(L::AbsLat, p)
  R = base_ring(L)
  E = nf(R)
  D = prime_decomposition(R, p)
  e = valuation(discriminant(R), p)
  if e == 0
    s = one(E)
  else
    s = elem_in_nf(p_uniformizer(D[1][1]))^e
  end
  @assert valuation(s, D[1][1]) == valuation(discriminant(R), p)

  M = local_basis_matrix(L, p, type = :submodule)
  G = gram_matrix(ambient_space(L), M)
  F, h = ResidueField(R, D[1][1])
  hext = extend(h, E)
  sGmodp = map_entries(hext, s * G)
  Vnullity, V = kernel(sGmodp, side = :left)
  if Vnullity == 0
    return true, L
  end

  hprim = u -> elem_in_nf((h\u))

  for x in _enumerate_lines(F, nrows(V))
    v = map_entries(hprim, matrix(F, 1, nrows(V), x) * V)
    res = v * M
    resvec = [res[1, i] for i in 1:ncols(res)]
    t = inner_product(ambient_space(L), resvec, resvec)
    valv = iszero(t) ? inf : valuation(t, D[1][1])
    if valv >= 2
      # I don't want to compute the generators
      X = [ iszero(inner_product(ambient_space(L), resvec, g)) ? inf : valuation(inner_product(ambient_space(L), resvec, g), D[1][1]) for g in generators(L) ]
      @assert minimum(X) >= 1 - e
      return false, v * M
    end
  end
  return true, L
end

  #// Check if L is max. integral at p. If not, return either:
  #// - a minimal integral overlattice at p (minimal flag set)
  #// - a maximal integral overlattice at p (minimal flag not set).
function _maximal_integral_lattice(L::AbsLat, p, minimal = true)
  R = base_ring(L)
  # already maximal?
  if valuation(norm(volume(L)), p) == 0 && !isramified(R, p)
    return true, L
  end

  B, G, S = jordan_decomposition(L, p)
  D = prime_decomposition(R, p)
  P = D[1][1]
  is_max = true

  if length(D) == 2 # split
    @assert S[end] != 0
    if minimal
      max = 1
      M = pseudo_matrix(matrix(nf(R), 1, ncols(B[1]), elem_type(nf(R))[B[length(S)][1, i] for i in 1:ncols(B[1])]), [inv(P)])
    else
      max = S[end]
      coeff_ideals = fractional_ideal_type(R)[]
      _matrix = zero_matrix(nf(R), 0, ncols(B[1]))
      for i in 1:length(B)
        if S[i] == 0
          continue
        end
        _matrix = vcat(_matrix, B[i])
        for k in 1:nrows(B[i])
          push!(coeff_ideals, inv(P)^(S[i]))
        end
      end
      M = pseudo_matrix(_matrix, coeff_ideals)
    end
    _new_pmat = _sum_modules(pseudo_matrix(L), M)
    _new_pmat = _intersect_modules(_new_pmat, inv(P)^(max) * pseudo_matrix(L))
    return false, lattice(ambient_space(L), _new_pmat)
  elseif D[1][2] == 1 # The inert case
    if S[end] >= 2
      if minimal
        max = 1
        M = pseudo_matrix(matrix(nf(R), 1, ncols(B[1]), elem_type(nf(R))[B[length(S)][1, i] for i in 1:ncols(B[1])]), inv(P)^(div(S[end], 2)))
      else
        max = S[end]
        coeff_ideals = fractional_ideal_type(R)[]
        _matrix = zero_matrix(nf(R), 0, ncols(B[1]))
        for i in 1:length(B)
          if !(S[i] >= 2)
            continue
          end
          _matrix = vcat(_matrix, B[i])
          for k in 1:nrows(B[i])
            push!(coeff_ideals, inv(P)^(div(S[i], 2)))
          end
        end
        M = pseudo_matrix(_matrix, coeff_ideals)
      end
      _new_pmat = _sum_modules(pseudo_matrix(L), M)
      _new_pmat = _intersect_modules(_new_pmat, inv(P)^(max) * pseudo_matrix(L))
      L = lattice(ambient_space(L), _new_pmat)
      if minimal
        return false, L
      end
      B, G, S = jordan_decomposition(L, p)
      is_max = false
    end
    # new we look for zeros of ax^2 + by^2
    kk, h = ResidueField(R, D[1][1])
    while sum(S[i] * nrows(B[i]) for i in 1:length(B)) > 1
      k = findfirst(i -> S[i] == 1, 1:length(S))
      @assert (k !== nothing) k && nrows(B[k]) >= 2
      r = h\rand(kk)
      # The following might throw ...
      while valuation(G[k][1, 1] + G[k][2, 2] * elem_in_nf(norm(r)), D[1][1]) < 2
        r = h\rand(kk)
      end
      M = pseudo_matrix(matrix(nf(R), 1, ncols(B[k]), [B[k][1, j] + r * B[k][2, j] for j in 1:ncols(B[k])]), [inv(P)])
      _new_pmat = _sum_modules(pseudo_matrix(L), M)
      _new_pmat = _intersect_modules(_new_pmat, inv(P) * pseudo_matrix(L))
      L = lattice(ambient_space(L), _new_pmat)
      if minimal
        return false, L
      end
      is_max = false
      B, G, S = jordan_decomposition(L, p)
      @assert S[1] >= 0
    end
    return is_max, L
  else # ramified case
    if S[end] >= 2
      if minimal
        max = 1
        M = pseudo_matrix(matrix(nf(R), 1, ncols(B[1]), elem_type(nf(R))[B[length(S)][1, i] for i in 1:ncols(B[1])]), [inv(P)^(div(S[end], 2))])
      else
        max = S[end]
        coeff_ideals = fractional_ideal_type(R)[]
        _matrix = zero_matrix(nf(R), 0, ncols(B[1]))
        for i in 1:length(B)
          if !(S[i] >= 2)
            continue
          end
          _matrix = vcat(_matrix, B[i])
          for k in 1:nrows(B[i])
            push!(coeff_ideals, inv(P)^(div(S[i], 2)))
          end
        end
        M = pseudo_matrix(_matrix, coeff_ideals)
      end
      _new_pmat = _sum_modules(pseudo_matrix(L), M)
      _new_pmat = _intersect_modules(_new_pmat, inv(P)^(max) * pseudo_matrix(L))
      L = lattice(ambient_space(L), _new_pmat)
      if minimal
        return false, L
      end
      B, G, S = jordan_decomposition(L, p)
    end
    v = valuation(volume(L), P)
    ok, x = _ismaximal_integral(L, p)
    while !ok
      LL = L
      L = lattice(ambient_space(L), _sum_modules(pseudo_matrix(L), pseudo_matrix(x, [inv(P)])))
      v = v - 2
      @assert v == valuation(volume(L), P)
      @assert valuation(norm(L), p) >= 0
      if minimal
        return false, L
      end
      is_max = false
      ok, x = _ismaximal_integral(L, p)
    end
    @assert iseven(v)
    v = div(v, 2)
    m = rank(L)
    e = valuation(discriminant(R), p)
    if isodd(m)
      valmax = - div(m - 1, 2) * e
    else
      valmax = -div(m, 2) * e
      disc = discriminant(ambient_space(L))
      if !islocal_norm(nf(R), disc, p)
        valmax += 1
      end
    end
    @assert v == valmax
    return is_max, L
  end
end

#{Checks whether L is p-maximal integral. If not, a minimal integral over-lattice at p is returned}
function ismaximal_integral(L::HermLat, p)
  valuation(norm(L), p) < 0 && error("The lattice must be integral at the prime ideal")
  return _maximal_integral_lattice(L, p, true)
end

#{Checks whether L is maximal integral. If not, a minimal integral over-lattice is returned}
function ismaximal_integral(L::HermLat) 
  !isintegral(norm(L)) && throw(error("The lattice is not integral"))
  S = base_ring(L)
  f = factor(discriminant(S))
  ff = factor(norm(volume(L)))
  for (p, e) in ff
    f[p] = 0
  end
  bad = collect(keys(f))
  for p in bad 
    ok, LL = _maximal_integral_lattice(L, p, true)
    if !ok
      return false, LL
    end
  end
  return true, L
end

#{Checks if L_p is Norm(L_p)-maximal}
function ismaximal(L::HermLat, p)
  iszero(L) && error("The lattice must be non-zero")
  v = valuation(norm(L), p)
  x = elem_in_nf(p_uniformizer(p))^(-v)
  b, LL = ismaximal_integral(rescale(L, x), p)
  if b
    return b, L
  else
    return lattice(ambient_space(L), pseudo_matrix(LL))
  end
end

#{A maximal integral lattice containing L}
function maximal_integral_lattice(L::HermLat)
  !isintegral(norm(L)) && throw(error("The lattice is not integral"))
  S = base_ring(L)
  f = factor(discriminant(S))
  ff = factor(norm(volume(L)))
  for (p, e) in ff
    f[p] = 0
  end
  bad = collect(keys(f))
  for p in bad
    _, L = _maximal_integral_lattice(L, p, false)
  end
  return L
end

#{A p-maximal integral lattice over L}
function maximal_integral_lattice(L::HermLat, p)
  valuation(norm(L), p) < 0 && throw(error("Lattice is not locally integral"))
  _, L = _maximal_integral_lattice(L, p, false)
  return L
end

function maximal_integral_lattice(V::HermSpace)
  L = lattice(V, identity_matrix(base_ring(V), rank(V)))
  fac = collect(factor(scale(L)))
  S = base_ring(L)
  s = one(nf(S)) * S
  while length(fac) > 0
    nrm = norm(fac[1][1])
    i = findfirst(i -> norm(fac[i][1]) == nrm, 2:length(fac))
    if i !== nothing
      i = i + 1 # findfirst gives the index and not the element
      @assert fac[i][2] == fac[1][2]
      s = s * fractional_ideal(S, fac[1][1])^fac[1][2]
      deleteat!(fac, i)
    else
      s = s * inv(fac[1][1])^(div(fac[1][2], 2))
    end
    deleteat!(fac, 1)
  end
  if !isone(s)
    L = s * L
  end
  return maximal_integral_lattice(L)
end

################################################################################
#
#  Find a given lattice locally
#
################################################################################
# {Constructs a sublattice X of M such that X_p is isometrix to L_p and X_q =
# M_q for all other primes q}
#

function find_lattice(M::HermLat, L::HermLat, p)
  E = nf(base_ring(M))
  @assert base_ring(M) == base_ring(L)
  #@show p
  #@show pseudo_matrix(M)
  #@show pseudo_matrix(L)
  @assert isrationally_equivalent(M, L, p)
  @assert ismaximal_integral(M, p)[1]
  D = prime_decomposition(base_ring(L), p)
  #@show D
  #@show length(D)
  P = D[1][1]
  #@assert isintegral(L, P)
  if length(D) == 2 # split case
    pi = p_uniformizer(P)
    BM, _, SM = jordan_decomposition(M, p)
    BL, _, SL = jordan_decomposition(L, p)
    SMall = reduce(vcat, [ [SM[i] for j in 1:nrows(BM[i])] for i in 1:length(BM)])
    SLall = reduce(vcat, [ [SL[i] for j in 1:nrows(BL[i])] for i in 1:length(BL)])
    BMall = reduce(vcat, BM)
    E = [ SLall[i] - SMall[i] for i in 1:nrows(BMall) ]
    @assert nrows(BMall) == rank(M)
    for i in 1:nrows(BMall)
      multiply_row!(BMall, pi^E[i], i)
    end
    _new_pmat = _sum_modules(pseudo_matrix(BMall), fractional_ideal(order(P), P)^maximum(E) * pseudo_matrix(M))
    _new_pmat = _intersect_modules(_new_pmat, P^minimum(E) * pseudo_matrix(M))
    LL = lattice(ambient_space(M), _new_pmat)
  elseif length(D) == 1 && D[1][2] == 1 # inert case
    #@show "================= intert"
    genL = genus(L, p)
    r0 = 0
    for i in 1:length(genL)
      if iseven(scale(genL, i))
        r0 += rank(genL, i)
      end
    end
    #r0 = sum( rank(genL, i) for i in 1:length(genL) if iseven(scale(genL, i)))
    if isdyadic(p)
      nsn = zero(nf(base_ring(L)))
    else
      nsn = elem_in_nf(_non_square_norm(P))
    end

    B, G, S = jordan_decomposition(M, p)
    @assert all(s in [0, 1] for s in S)
    if S[1] == 0
      BB = [ B[1][i, :] for i in 1:nrows(B[1])]
      m = div(length(BB) - r0, 2)
      k, h = ResidueField(base_ring(base_ring(L)), p)
      hext = extend(h, nf(base_ring(base_ring(L))))
      Y = [ BB[i] for i in (2*m + 1):length(BB) ]
      for i in 1:m
        # transform <BB[2i-1], BB[2i]> into H(0). Then go from there.
        el = coeff(-G[1][2*i, 2*i]//G[1][2*i - 1, 2*i - 1], 0)
        b, s = issquare(hext(el))
        if b
          push!(Y, BB[2*i] + nf(base_ring(L))(hext\s)*BB[2*i - 1])
        else
          el = coeff(-G[1][2*i, 2*i]//G[1][2*i - 1, 2*i - 1], 0) * norm(nsn)
          b, s = issquare(hext(el))
          @assert b
          push!(Y, nsn * BB[2*i] + nf(base_ring(L))(hext\s) * BB[2*i - 1])
        end
      end
      if length(B) == 2
        Y = vcat(reduce(vcat, Y), B[2])
      else
        Y = reduce(vcat, Y)
      end
      _new_pmat = _sum_modules(pseudo_matrix(Y), _module_scale_ideal(P, pseudo_matrix(M)))
      _new_pmat = _intersect_modules(_new_pmat, pseudo_matrix(M))
      LL = lattice(ambient_space(M), _new_pmat)
    else
      LL = M
    end
    B, _, _ = jordan_decomposition(LL, p)
    Y = reduce(vcat, B)
#    // Now Y generates the Gerstein reduction of L_p locally.
#    // So we simply rescale the generators in Y appropriately and assemble
#    // the global solution. 
    pi = elem_in_nf(p_uniformizer(p))
    i = 1
    j = r0 + 1
    for l in 1:length(genL)
      s = pi^div(scale(genL, l), 2)
      if iseven(scale(genL, l))
        for k in 1:rank(genL, l)
          multiply_row!(Y, s, i)
          i = i + 1
        end
      else
        for k in 1:rank(genL, l)
          multiply_row!(Y, s, j)
          j = j + 1
        end
      end
    end
    max = scale(genL, length(genL))
    _new_pmat = _sum_modules(pseudo_matrix(Y), _module_scale_ideal(P^max, pseudo_matrix(M)))
    _new_pmat = _intersect_modules(_new_pmat, pseudo_matrix(M))
    LL = lattice(ambient_space(M), _new_pmat)
  elseif !isdyadic(p) # odd ramified
#   // C contains the genus symbols of all Gerstein reduced lattices above L_p.
    c = genus(L, p)
    C = [ c ]
    while scale(c, length(c)) >= 2
      c0 = genus(HermLat, nf(base_ring(L)), p, [(scale(c, i), rank(c, i), det(c, i)) for i in 1:length(c) if scale(c, i) in [0, 2]])
      if length(c0) == 2
        c0 = genus(HermLat, E, p, [(0, rank(c0, 1) + rank(c0, 2), det(c0, 1) == det(c0, 2) ? 1 : -1)])
      elseif length(c0) == 1
        c0 = genus(HermLat, E, p, [(0, rank(c0, 1), det(c0, 1))])
      end
      c1 = genus(HermLat, E, p, Tuple{Int, Int, Int}[(scale(c, i), rank(c, i), det(c, i)) for i in 1:length(c) if scale(c, i) in [1, 3]])
      if length(c1) == 2
        c1 = genus(HermLat, E, p, Tuple{Int, Int, Int}[(1, rank(c1, 1) + rank(c1, 2), det(c1, 1) == det(c1, 2) ? 1 : -1)])
      elseif length(c1) == 1
        c1 = genus(HermLat, E, p, Tuple{Int, Int, Int}[(1, rank(c1, 1), det(c1, 1))])
      end
      c = genus(HermLat, E, p, 
            vcat(Tuple{Int, Int, Int}[(scale(c0, i), rank(c0, i), det(c0, i)) for i in 1:length(c0)],
                 Tuple{Int, Int, Int}[(scale(c1, i), rank(c1, i), det(c1, i)) for i in 1:length(c1)],
                 Tuple{Int, Int, Int}[(scale(c, i) - 2, rank(c, i), det(c, i)) for i in 1:length(c) if scale(c, i) >= 4]))
      push!(C, c)
    end
    B, G, S = jordan_decomposition(M, p)
    @assert all(s in [-1, 0] for s in S)
    B0 = S[end] == 0 ? [ B[end][i, :] for i in 1:nrows(B[end]) ] : []
    B1 = S[1] == -1 ? [ B[1][i, :] for i in 1:nrows(B[1]) ] : []
    r0 = scale(c, 1) == 0 ? rank(c, 1) : 0
    for i in 1:div(r0 - length(B0), 2)
      push!(B0, B1[2*i - 1])
    end
    if length(B0) == 0
      LL = lattice(ambient_space(M), _module_scale_ideal(P, pseudo_matrix(M)))
    else
      _new_pmat = _sum_modules(pseudo_matrix(reduce(vcat, B0)), _module_scale_ideal(P, pseudo_matrix(M)))
      _new_pmat = _intersect_modules(_new_pmat, pseudo_matrix(M))
      LL = lattice(ambient_space(M), _new_pmat)
    end
    @assert genus(LL, p) == c

    E = nf(base_ring(M))
    K = base_field(E)
    k, h = ResidueField(order(p), p)
    hext = extend(h, K)
    for j in length(C)-1:-1:1
      c = C[j]
      if all(!(scale(c, i) in [0, 1]) for i in 1:length(c))
        @assert scale(C[1], 1) - valuation(scale(LL), P) >= 0
        s = div(scale(C[1], 1) - valuation(scale(LL), P), 2)
        LL = lattice(ambient_space(LL), P^s * pseudo_matrix(LL))
        break
      end
      B, G, S = jordan_decomposition(LL, p)
      r = findfirst(i -> scale(c, i) == 1, 1:length(c))
      if r !== nothing
        r = rank(c, r)
        i = findfirst(j -> j == 1, S)
        @assert i !== nothing
        Y1 = [ B[i][j,:] for j in 1:r] 
      else
        Y1 = []
      end
      Y0 = []
      r = findfirst(i -> scale(c, i) == 0, 1:length(c))
      if r !== nothing
        r = rank(c, r)
        @assert S[1] == 0
        B = [ B[1][j, :] for j in 1:nrows(B[1]) ]
        n = length(B)
        G = G[1]
        NN = [ i for i in 1:n if !(issquare(hext(coeff(G[i, i], 0)))[1])]
        if length(NN) == 0 && det(c, 1) == -1
          while true
            s = hext\rand(k)
            tmp = hext(coeff(G[n - 1, n - 1] + s^2 * G[n, n], 0))
            if !iszero(tmp) && issquare(tmp)[1]
              break
            end
          end
          Y0 = vcat(B[1:r-1], [B[n - 1] + s * B[n]])
        else
          SS = [ i for i in 1:n if !(i in NN)]
          if det(c, 1) == 1
            Y0 = []
          else
            Y0 = [ NN[1] ]
            popfirst!(NN)
          end
          if isodd(r- length(Y0))
            if length(SS) == 0
              while true
                s = hext\rand(k)
                tmp = hext(coeff(G[n - 1, n - 1] + s^2 * G[n, n], 0))
                if !iszero(tmp) && issquare(tmp)[1]
                  break
                end
              end
              v = B[n - 1]
              B[n - 1] = B[n - 1] + E(s) * B[n]
              B[n] = B[n] - s * G[n, n]//G[n - 1, n - 1] * v
              NN = [i for i in NN if i < n - 1]
              SS = [n - 1, n]
            end
            push!(Y0, SS[1])
            popfirst!(SS)
          end
          Y0 = vcat(Y0, NN[1:2*div(length(NN), 2)], SS)
          Y0 = B[Y0[1:r]]
        end
      end
      _new_pmat = _sum_modules(pseudo_matrix(reduce(vcat, vcat(Y0, Y1))), _module_scale_ideal(P, pseudo_matrix(LL)))
      _new_pmat = _intersect_modules(_new_pmat, pseudo_matrix(LL))
      LL = lattice(ambient_space(M), _new_pmat)
      @assert genus(LL, p) == c
    end
  else
#  // The even ramified case
#  // The approach below is VERY lame.
#  // What we should do is the following:
#  // 1. Find an (suffiently good approximation of an) isometry between the ambient spaces of M_p and L_p.
#  // 2. Let Y_p be the image of L_p under this map. If it is good enough, then Y_p \isom L_p.
#  // 3. Contsruct a lattice X in the space of M such that X_p = Y_p and X_q = M_q for all q \ne p.
#  else
    k, h = ResidueField(order(P), P)
    m = rank(M)
    chain = [ L ]
    ok, LL = ismaximal_integral(L, p)
    E = nf(order(P))
    while !ok
      push!(chain, LL)
      ok, LL = ismaximal_integral(LL, p)
    end
    pop!(chain)
    LL = M
    reverse!(chain)
    for X in chain 
      BM = local_basis_matrix(LL, P, type = :submodule)
      pM = fractional_ideal(order(P), P) * pseudo_matrix(LL)
      while true
        v = [ rand(k) for i in 1:m ]
        while all(i -> iszero(v[i]), 1:m)
          v = [ rand(k) for i in 1:m ]
        end
        _, KM = kernel(matrix(k, length(v), 1, v), side = :left)
        KM = map_entries(x -> E(h\x), KM)
        _new_pmat = _sum_modules(pseudo_matrix(KM * BM), pM)
        LL = lattice(ambient_space(M), _new_pmat)
        #@show "trying $LL"
        #@show ambient_space(LL)
        #@show coefficient_ideals(pseudo_matrix(LL))
        #@show matrix(pseudo_matrix(LL))
        #@show genus(X, p)
        #@show genus(LL, p)
        if islocally_isometric(X, LL, p)
          break
        end
      end
    end
  end
  #@show p, LL
  @assert islocally_isometric(L, LL, p)
  return LL
end

################################################################################
#
#  Helper
#
################################################################################

function _sum_modules(a::PMat, b::PMat)
  H = vcat(a, b)
  H = pseudo_hnf(H, :lowerleft)
  r = 0
  for i in 1:nrows(H)
    if !iszero_row(matrix(H), i)
      r = i
      break
    end
  end
  @assert r != 0
  return sub(H, r:nrows(H), 1:ncols(H))
end

function _intersect_modules(a::PMat, b::PMat)
  M1 = hcat(a, deepcopy(a))
  d = ncols(b)
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
  return pseudo_matrix(matrix(b), Ref(a) .* coefficient_ideals(b))
end

_module_scale_ideal(a::PMat, b::NfOrdFracIdl) = _module_scale_ideal(b, a)

function _module_scale_ideal(a::NfRelOrdIdl, b::PMat)
  return pseudo_matrix(matrix(b), Ref(a) .* coefficient_ideals(b))
end

_module_scale_ideal(a::PMat, b::NfRelOrdIdl) = _module_scale_ideal(b, a)

function _module_scale_ideal(a::NfRelOrdFracIdl, b::PMat)
  return pseudo_matrix(matrix(b), Ref(a) .* coefficient_ideals(b))
end

_module_scale_ideal(a::PMat, b::NfRelOrdFracIdl) = _module_scale_ideal(b, a)

*(a::NfRelOrdFracIdl, b::PMat) = _module_scale_ideal(a, b)

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

function _local_basis_matrix_prime_below_submodule(a::PMat, p)
  @assert base_ring(base_ring(a)) == order(p)
  R = base_ring(a)
  D = prime_decomposition(R, p)
#  unis = [p_uniformizer(q[1]) for q in D]
#  @assert all(valuation(unis[i], D[i][1]) == 1 for i in 1:length(D))
#  @assert all(sum(valuation(unis[i], D[j][1]) for j in 1:length(D)) == 1 for i in 1:length(D))
  z = zero_matrix(base_ring(matrix(a)), nrows(a), ncols(a))
  for i in 1:nrows(a)
    c = coefficient_ideals(a)[i]
    f = factor(c)
    if length(f) == 0
      x = one(nf(R))
    else
      for Q in D
        if !(haskey(f, Q[1]))
          f[Q[1]] = 0
        end
      end
      x = approximate([e for (_, e) in f], [p for (p, _) in f])
      @assert all(valuation(x, p) == e for (p, e) in f)
    end
    @assert valuation(x, D[1][1]) == valuation(c, D[1][1])
    #x = unis[1]^valuation(c, D[1][1])
    #for k in 2:length(D)
    #  x = x * unis[k]^valuation(c, D[k][1])
    #end
    for j in 1:ncols(a)
      z[i, j] = x * matrix(a)[i, j]
    end
  end
  if true
    _z = pseudo_matrix(z, [one(nf(R)) * R for i in 1:nrows(z)])
    @assert _spans_subset_of_pseudohnf(_z, a, :lowerleft)
    @assert valuation(det(_z), D[1][1]) == valuation(det(a), D[1][1])
  end
  return z
end

function _local_basis_submodule_matrix(a::PMat, p)
  #@assert base_ring(base_ring(a)) == order(p)
  z = zero_matrix(base_ring(matrix(a)), nrows(a), ncols(a))
  for i in 1:nrows(a)
    c = coefficient_ideals(a)[i]
    vpc = valuation(c, p)
    found = false
    local x
    for b in absolute_basis(c) # could use generators here
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
  throw(NotImplemented())
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
  diag = minimum(iszero(G[i, i]) ? inf : valuation(G[i, i], P) for i in 1:n)
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
  for i in 1:length(pb)
    (e, I) = pb[i]
    for b in absolute_basis(I)
      push!(res, e * b)
    end
  end
  return res
end

function absolute_basis(I::NfRelOrdIdl)
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
    g = map_coeffs(x -> evaluate(x, p, 32), f)
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

# Given an element b in a number field K and sets of finite and infinite 
# places P and I of K, return an element a in K such that 
# { v: (a,b)_v = -1 } = P \cup I
# Note that the function computes the unit and class groups of K!
# TODO: use factored elements
function _find_quaternion_algebra(b, P, I)
  @assert iseven(length(I) + length(P))
  @assert all(p -> !islocal_square(b, p), P)
  @assert all(p -> isnegative(evaluate(b, p)), I)

  K = parent(b)
  R = maximal_order(K)
  n = length(P)
  m = length(I)

  _J = b * R
  #_P = Dict{}()
  __P = copy(P)
  #for p in P
  #  _P[p] = true
  #end
  for p in keys(factor(_J))
    if !(p in __P)
      push!(__P, p)
    end
      #_P[p] = true
  end
  for p in prime_decomposition(R, 2)
    if !(p[1] in __P)
      push!(__P, p[1])
    end
  end
  for p in real_places(K)
    if !(p in I) && isnegative(b, p)
      push!(I, p)
    end
  end

  F = Nemo.GF(2)

  target = matrix(F, 1, length(__P) + length(I), vcat(fill(1, n), fill(0, length(__P) - n), fill(1, m), fill(0, length(I) - m)))
  if iszero(target)
    return one(K)
  end

  #__P = convert(Vector{NfOrdIdl}, collect(keys(_P)))

  found = false
  U, h = unit_group(R)
  sign_vector = g -> begin
    return matrix(F, 1, length(__P) + length(I),
                 vcat([div(1 - hilbert_symbol(K(g), b, p), 2) for p in __P ], [ div(1 - _sign(evaluate(g, p)), 2) for p in I]))
  end


  L, f = sunit_group(__P)
  M = zero_matrix(F, 0, length(__P) + length(I))
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
        if q in __P
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
        break
      end
    end
  end
  c = K(exp(A(target_signs)))
  for i in 1:length(I)
    @assert sign(c, I[i]) == val[i]
  end
  return c
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

isdyadic(p) = order(p)(2) in p

isdyadic(p::fmpz) = p == 2

# find an element of K, which is not a local norm at p
# p must be ramified
# See [Kir16, Corollary 3.3.17]
function _non_norm_rep(E, K, p)
  K = base_field(E)
  if isramified(maximal_order(E), p)
    if !isdyadic(p)
      U, mU = unit_group(maximal_order(K))
      for i in 1:ngens(U)
        u = mU(U[i])
        if !islocal_norm(E, elem_in_nf(u), p)
          return elem_in_nf(u)
        end
      end
      B = elem_in_nf.(basis(p))
      k = 0
      while true
        if k > 10000
          throw(error("Something wrong in non_norm_rep"))
        end
        y = rand(K, -5:5)
        if iszero(y)
          continue
        end
        if !islocal_norm(E, y, p)
          return y
        end
        k += 1
      end
    else
      lP = prime_decomposition(maximal_order(E), p)
      @assert length(lP) == 1 && lP[1][2] == 2
      Q = lP[1][1]
      e = valuation(different(maximal_order(E)), Q)
      U, mU = unit_group(maximal_order(K))
      for i in 1:ngens(U)
        u = mU(U[i])
        if !islocal_norm(E, elem_in_nf(u), p) && (valuation(u - 1, p) == e - 1)
          return elem_in_nf(u)
        end
      end
      # We look for a local unit u such that v_p(u - 1) = e - 1 and
      # u not a local norm
      tu = elem_in_nf(mU(U[1]))
      tuo = order(U[1])
      B = elem_in_nf.(basis(p^(e - 1)))
      k = 0
      while true
        if k > 10000
          throw(error("Something wrong in non_norm_rep"))
        end
        y = (1 + rand(B, -1:1)) * tu^(rand(1:tuo))
        @assert valuation(y, p) == 0
        if !islocal_norm(E, y, p) && valuation(y - 1, p) == e - 1
          return y
        end
        k += 1
      end
    end
    throw(error("This should not happen ..."))
  else
    lP = prime_decomposition(maximal_order(E), p)
    if length(lP) == 2
      error("This dosses not make any sense!")
    else
      return elem_in_nf(p_uniformizer(p))
     end
  end
end

function _enumerate_lines(K, n)
  if n == 1
    return Vector{elem_type(K)}[elem_type(K)[one(K)]]
  end
  _all_nminusone = Iterators.product([K for i in 1:n-1]...)
  res = Vector{elem_type(K)}[]
  for w in _all_nminusone
    v = elem_type(K)[one(K)]
    append!(v, collect(w))
    push!(res, v)
  end
  _all_rest = _enumerate_lines(K, n - 1)
  for w in _all_rest
    v = elem_type(K)[zero(K)]
    append!(v, w)
    push!(res, v)
  end
  return res
end

function ^(A::NfRelOrdFracIdl, a::Int)
  if a == 0
    B = one(nf(order(A))) * order(A)
    return B
  end

  if a == 1
    return A # copy?
  end

  if a < 0
    return inv(A^(-a))
  end

  if a == 2
    return A*A
  end

  if mod(a, 2) == 0
    return (A^div(a, 2))^2
  else
    return A * A^(a - 1)
  end
end

# P must be inert and odd
function _non_square_norm(P)
  @assert !isdyadic(P)
  #@assert isinert(P)
  R = order(P)
  p = minimum(P)
  k, h = ResidueField(order(P), P)
  kp, hp = ResidueField(order(p), p)
  local u
  while true
    r = rand(k)
    u = h\r
    if !iszero(r) && !issquare(hp(norm(u)))[1]
      break
    end
  end
  return u
end

################################################################################
#
#  Restrict scalars
#
################################################################################

mutable struct ZLat <: AbsLat{FlintRationalField}
  space::QuadSpace{FlintRationalField, fmpq_mat}  
  rational_span::QuadSpace{FlintRationalField, fmpq_mat}  
  basis_matrix::fmpq_mat
  gram_matrix::fmpq_mat
  aut_grp_gen::fmpq_mat
  aut_grp_ord::fmpz
  automorphism_group_generators::Vector{fmpz_mat}
  automorphism_group_order::fmpz
  minimum::fmpq

  function ZLat(V::QuadSpace{FlintRationalField, fmpq_mat}, B::fmpq_mat)
    z = new()
    z.space = V
    z.basis_matrix = B
    return z
  end
end

basis_matrix(L::ZLat) = L.basis_matrix

ambient_space(L::ZLat) = L.space

base_ring(L::ZLat) = FlintZZ

function gram_matrix(L::ZLat)
  b = basis_matrix(L)
  return b * gram_matrix(ambient_space(L)) * transpose(b)
end

gram_matrix_of_basis(L::ZLat) = gram_matrix(L)

function restrict_scalars(L::AbsLat)
  V = ambient_space(L)
  Vabs, f, g = restrict_scalars(V)
  Babs = absolute_basis(L)
  Mabs = zero_matrix(FlintQQ, length(Babs), rank(Vabs))
  for i in 1:length(Babs)
    v = g(Babs[i])
    for j in 1:length(v)
      Mabs[i, j] = v[j]
    end
  end
  return ZLat(Vabs, Mabs)
end

function lattice(V::QuadSpace{FlintRationalField, fmpq_mat}, B::MatElem)
  Gc = change_base_ring(FlintQQ, B)
  if typeof(Gc) !== fmpq_mat
    throw(error("Cannot convert entries of the matrix to the rationals"))
  end
  return ZLat(V, Gc)
end

function rational_span(L::ZLat)
  if isdefined(L, :rational_span)
    return L.rational_span
  else
    G = gram_matrix(L)
    V = quadratic_space(FlintQQ, G)
    L.rational_span = V
    return V
  end
end

function Zlattice(B::fmpq_mat; gram = identity_matrix(FlintQQ, ncols(B)))
  V = quadratic_space(FlintQQ, gram)
  return lattice(V, B)
end


function Zlattice(B::fmpz_mat; gram = identity_matrix(ncols(B)))
  V = quadratic_space(FlintQQ, gram)
  return lattice(V, B)
end
function Zlattice(;gram)
  n = nrows(gram)
  return lattice(quadratic_space(FlintQQ, gram), identity_matrix(FlintQQ, n))
end

# if ambient_representation = true, they are given with respect to the ambient space
function Base.show(io::IO, L::ZLat)
  print(io, "Quadratic lattice of rank ", rank(L),
            " and degree ", degree(L), " over the rationals")
end

function assert_has_automorphisms(L::ZLat)
  if isdefined(L, :automorphism_group_generators)
    return nothing
  end

  V = ambient_space(L)
  GL = gram_matrix(L)
  d = denominator(GL)
  res = fmpz_mat[change_base_ring(FlintZZ, d * GL)]
  # So the first one is either positive definite or negative definite
  # Make it positive definite. This does not change the automorphisms.
  if res[1][1, 1] < 0
    res[1] = -res[1]
  end
  Glll, T = lll_gram_with_transform(res[1])
  Ttr = transpose(T)
  res_orig = copy(res)
  res[1] = Glll

  bm = basis_matrix(L)

  # Make the Gram matrix small
  
  C = ZLatAutoCtx(res)
  init(C)
  auto(C)
  gens, order = _get_generators(C)

  # Now translate back
  Tinv = inv(T)
  for i in 1:length(gens)
    gens[i] = Tinv * gens[i] * T
  end
  
  # Now gens are with respect to the absolute basis of L
  @assert all( gens[i] * res_orig[j] * transpose(gens[i]) == res_orig[j] for i in 1:length(gens), j in 1:length(res))

  # Now translate to get the automorphisms with respect to basis_matrix(L)
  
  L.automorphism_group_generators = gens
  L.automorphism_group_order = order

  return nothing
end

# natural action = action on ambient_space

@doc Markdown.doc"""
    automorphism_group_generators(L::ZLat; check::Bool = true,
                                           ambient_representation::Bool = false)

Returns generators of the automorphism group of $L$. By default, the
automorphisms are acting on the coordinate vectors of lattice elements.
If `ambient_representation = true`, the automorphisms act on elements in the
ambient space of `L`.
"""
function automorphism_group_generators(L::ZLat; check::Bool = true,
                                                ambient_representation::Bool = true)

  assert_has_automorphisms(L)

  gens = L.automorphism_group_generators
  if !ambient_representation
    return fmpq_mat[ change_base_ring(FlintQQ, g) for g in gens]
  else
    # Now translate to get the automorphisms with respect to basis_matrix(L)
    bm = basis_matrix(L)
    bminv = inv(bm)
    gens = L.automorphism_group_generators
    V = ambient_space(L)
    if rank(L) == rank(V)
      res = fmpq_mat[bminv * change_base_ring(FlintQQ, g) * bm for g in gens]
    else
      # Extend trivially to the orthogonal complement of the rational span
      !isregular(V) &&
        throw(error(
          """Can compute ambient representation only if ambient space is
             regular"""))
      C = orthogonal_complement(V, basis_matrix(L))
      C = vcat(basis_matrix(L), C)
      Cinv = inv(C)
      D = identity_matrix(FlintQQ, rank(V) - rank(L))
      res = fmpq_mat[Cinv * diagonal_matrix(change_base_ring(FlintQQ, g), D) * C for g in gens]
    end
    if check
      for g in res
        @assert g * gram_matrix(V) * g' == gram_matrix(V)
      end
    end
    return res
  end
end

function automorphism_group_order(L::ZLat)
  assert_has_automorphisms(L)
  return L.automorphism_group_order
end

@doc Markdown.doc"""
    isisometric(L::ZLat, M::ZLat; ambient_representation::Bool = true
                                  check::Bool = true)
        -> (Bool, MatElem)

Tests if $L$ and $M$ are isometric. If this is the case, the second return value
is an isometriy $T$ from $L$ to $M$.

By default, that isometry is represented with respect to the bases of the
ambient spaces, that is, $T V_M T^t = V_L$ where $V_L$ and $V_M$ are the gram
matrices of the ambient spaces of $L$ and $M$ respectively. If
`ambient_representation = true`, then the isometry is represented with respect
to the bases of $L$ and $M$, that is, $T G_M T^t = G_L$ where $G_M$ and $G_L$ are
the gram matrices of $L$ and $M$ respectively.
"""
function isisometric(L::ZLat, M::ZLat; ambient_representation::Bool = true,
                                       check::Bool = true)
  GL = gram_matrix(L)
  dL = denominator(GL)
  GLint = change_base_ring(FlintZZ, dL * GL)
  cL = content(GLint)
  GLint = divexact(GLint, cL)

  GM = gram_matrix(M)
  dM = denominator(GM)
  GMint = change_base_ring(FlintZZ, dM * GM)
  cM = content(GMint)
  GMint = divexact(GMint, cM)

  # GLint, GMint are integral, primitive scalings of GL and GM
  # If they are isometric, then the scalars must be identitcal.
  if dL//cL != dM//cM
    return false, zero_matrix(FlintQQ, 0, 0)
  end
 
  # Now compute LLL reduces gram matrices

  GLlll, TL = lll_gram_with_transform(GLint)
  @assert TL * change_base_ring(FlintZZ, GL) * TL' * dL == GLlll * cL
  GMlll, TM = lll_gram_with_transform(GMint)
  @assert TM * change_base_ring(FlintZZ, GM) * TM' * dM == GMlll * cM

  # Setup for Plesken--Souvignier
  CL, CM = _iso_setup(fmpz_mat[GLlll], fmpz_mat[GMlll])
  # Call Plesken Souvignier
  b, T = isometry(CL, CM)

  if b
    T = change_base_ring(FlintQQ, inv(TL)*T*TM)
    if !ambient_representation
      if check
        @assert T * gram_matrix(M) * T' == gram_matrix(L)
      end
      return true, T
    else
      V = ambient_space(L)
      W = ambient_space(L)
      if rank(L) == rank(V)
        T = inv(basis_matrix(L)) * T * basis_matrix(M)
      else
        (!isregular(V) || !isregular(W)) &&
          throw(error(
            """Can compute ambient representation only if ambient space is
               regular"""))
          (rank(V) != rank(W)) &&
          throw(error(
            """Can compute ambient representation only if ambient spaces
            have the same dimension."""))

        CV = orthogonal_complement(V, basis_matrix(L))
        CV = vcat(basis_matrix(L), CV)
        CW = orthogonal_complement(V, basis_matrix(M))
        CW = vcat(basis_matrix(M), CW)
        D = identity_matrix(FlintQQ, rank(V) - rank(L))
        T = inv(CV) * diagonal_matrix(T, D) * CW
      end
      if check
        @assert T * gram_matrix(ambient_space(M))  * T' ==
                  gram_matrix(ambient_space(L))
      end
      return true, T
    end
  else
    return false, zero_matrix(FlintQQ, 0, 0)
  end
end

################################################################################
#
#  Automorphism group
#
################################################################################

_eltseq(M::MatElem) = [M[i, j] for i in 1:nrows(M) for j in 1:ncols(M)]

# Compute the automorphism group of the lattice
# per default, the are given with respect to the basis of the ambient space
# if ambient_representation = true, they are given with respect to the coordinate
# space/ambient space
function assert_has_automorphisms(L::AbsLat; check::Bool = true,
                                             redo::Bool = false)

  if !redo && isdefined(L, :automorphism_group_generators)
    return nothing
  end

  E = base_ring(ambient_space(L))

  ZgramL, scalarsL, BabsmatL, generatorsL = Zforms(L)
  @assert isone(generatorsL[1])
  # So the first one is either positive definite or negative definite
  # Make it positive definite. This does not change the automorphisms.
  if ZgramL[1][1, 1] < 0
    ZgramL[1] = -ZgramL[1]
  end

  # Make the Gram matrix small
  Glll, T = lll_gram_with_transform(ZgramL[1])
  Ttr = transpose(T)
  ZgramLorig = ZgramL
  ZgramL = copy(ZgramL)
  for i in 1:length(ZgramL)
    ZgramL[i] = T * ZgramL[i] * Ttr
  end
  CC = ZLatAutoCtx(ZgramLorig)
  init(CC)
  auto(CC)
  gens, order = _get_generators(CC)
  if check
    for g in gens
      for i in 1:length(ZgramLorig)
        @assert g * ZgramLorig[i] * g' == ZgramLorig[i]
      end
    end
  end

  # Create the automorphism context and compute generators as well as orders
  C = ZLatAutoCtx(ZgramL)
  init(C)
  auto(C)
  gens, order = _get_generators(C)

  if check
    for g in gens
      for i in 1:length(ZgramL)
        @assert g * ZgramL[i] * g' == ZgramL[i]
      end
    end
  end

  # Now undo the LLL transformation
  Tinv = inv(T)
  for i in 1:length(gens)
    gens[i] = Tinv * gens[i] * T
  end
  
  # Now gens are with respect to the absolute basis of L
  if check
    all(gens[i] * ZgramLorig[j] * transpose(gens[i]) == ZgramLorig[j] for i in 1:length(gens), j in 1:length(ZgramL))
  end

  # Now translate to get the automorphisms with respect to basis_matrix(L)
  BmatL = basis_matrix(L)

  b1, s1 = can_solve(BabsmatL, BmatL, side = :left)
  b2, s2 = can_solve(BmatL, BabsmatL, side = :left)

  t_gens = Vector{typeof(BmatL)}(undef, length(gens))

  for i in 1:length(gens)
    t_gens[i] = s1 * change_base_ring(E, gens[i]) * s2
  end


  if check
    G = gram_matrix_of_basis(L)
    @assert all(g * G * _map(transpose(g), involution(L)) == G
                  for g in t_gens)
    pm = pseudo_matrix(L)
    C = coefficient_ideals(pm)

    for g in t_gens
      @assert all(g[i, j] in C[j] * inv(C[i])
                    for i in 1:nrows(g), j in 1:nrows(g))
    end
  end

  # Now set the generators and the order

  L.automorphism_group_generators = t_gens
  L.automorphism_group_order = order
  return nothing
end

function automorphism_group_generators(L::AbsLat; check::Bool = true,
                                                  ambient_representation::Bool = true)

  assert_has_automorphisms(L)

  gens = L.automorphism_group_generators

  if !ambient_representation
    if check
      Grel = gram_matrix(rational_span(L))
      for g in gens
        @assert g * Grel * _map(transpose(g), involution(L)) == Grel
      end
    end
    return copy(gens)
  else
    bm = basis_matrix(L)
    bminv = inv(bm)
    gens = typeof(bm)[bminv * g * bm for g in gens]
    if check
      Gamb = gram_matrix(ambient_space(L))
      for g in gens
        @assert g * Gamb * _map(transpose(g), involution(L)) == Gamb
      end
    end
    return gens
  end
end

function automorphism_group_order(L::AbsLat; redo::Bool = false)
  assert_has_automorphisms(L, redo = redo)
  return L.automorphism_group_order
end

################################################################################
#
#  Isometry
#
################################################################################

function matrix(K, R::Vector{<:Vector})
  if length(R) == 0
    return zero_matrix(K, 0, 0)
  else
    n = length(R)
    m = length(R[1])
    z = zero_matrix(K, n, m)
    for i in 1:n
      @assert length(R[i]) == m
      for j in 1:m
        z[i, j] = R[i][j]
      end
    end
    return z
  end
end

function orthogonal_complement(V::AbsSpace, M::MatElem)
  N = gram_matrix(V) * _map(transpose(M), involution(V))
  r, K = left_kernel(N)
  @assert r == nrows(K)
  return K
end

function Zforms(L::AbsLat)
  E = base_ring(ambient_space(L))
  Eabs, EabsToE = absolute_field(E)
  generators = elem_type(E)[E(1), absolute_primitive_element(E)]
  return _Zforms(L, generators)
end

function absolute_primitive_element(K::NumField)
  B = basis(K)
  for i in 1:length(B)
    if degree(absolute_minpoly(B[i])) == absolute_degree(K)
      return B[i]
    end
  end
end

absolute_minpoly(a::nf_elem) = minpoly(a)

function _Zforms(L::AbsLat, generators::Vector)
  V = ambient_space(L)
  E = base_ring(V)
  Babs = absolute_basis(L)
  Babsmat = matrix(E, Babs)
  forms = fmpz_mat[]
  scalars = fmpq[]
  for b in generators
    Vres, VresToV, VtoVres = restrict_scalars(V, FlintQQ, b)
    G = gram_matrix(Vres, VtoVres.(Babs))
    d = denominator(G)
    Gint = change_base_ring(FlintZZ, d * G)
    c = content(Gint)
    G = divexact(Gint, c)
    push!(forms, G)
    push!(scalars, d//c)
  end
  return forms, scalars, Babsmat, generators
end

function isisometric(L::AbsLat, M::AbsLat; ambient_representation::Bool = true, check::Bool = true)
  V = ambient_space(L)
  W = ambient_space(M)
  E = base_ring(V)
  K = base_field(E)
  @assert base_ring(V) == base_ring(W)
  @assert base_ring(L) == base_ring(M)

  ZgramL, scalarsL, BabsmatL, generatorsL = Zforms(L)
  ZgramM, scalarsM, BabsmatM, generatorsM = Zforms(M)
  @assert generatorsL == generatorsM
  if scalarsL != scalarsM
    return false, zero_matrix(E, 0, 0)
  end

  # So the first one is either positive definite or negative definite
  # Make it positive definite. This does not change the automorphisms.
  if ZgramL[1][1, 1] < 0
    ZgramL[1] = -ZgramL[1]
    ZgramM[1] = -ZgramM[1]
  end

  ZgramLsmall = copy(ZgramL)
  ZgramMsmall = copy(ZgramM)

  # Make the Gram matrix small
  _, TL = lll_gram_with_transform(ZgramL[1])
  _, TM = lll_gram_with_transform(ZgramM[1])
  TLtr = transpose(TL)
  TMtr = transpose(TM)
  for i in 1:length(ZgramL)
    ZgramLsmall[i] = TL * ZgramL[i] * TLtr
    ZgramMsmall[i] = TM * ZgramM[i] * TMtr
  end

  CL, CM = _iso_setup(ZgramLsmall, ZgramMsmall)
  b, T = isometry(CL, CM)
  if b
    T = change_base_ring(FlintQQ, inv(TL)*T*TM)
    fl, s1 = can_solve(BabsmatL, basis_matrix(L), side = :left)
    fl, s2 = can_solve(basis_matrix(M), BabsmatM, side = :left)
    T = s1 * change_base_ring(E, T) * s2
    if check
      @assert T * gram_matrix(rational_span(M)) * _map(transpose(T), involution(L)) == gram_matrix(rational_span(L))
    end
    if !ambient_representation
      return true, T
    else
      T = inv(basis_matrix(L)) * T * basis_matrix(M)
      @assert T * gram_matrix(ambient_space(M)) * _map(transpose(T), involution(L)) == gram_matrix(ambient_space(L))
      return true, T
    end
  else
    return false, zero_matrix(E, 0, 0)
  end
end

  #pm = pseudo_matrix(L)
  #C = coefficient_ideals(pm)

  #if check
  #  @assert all(g * G * _map(transpose(g), involution(L)) == G for g in translate_gens)
  #  for g in translate_gens
  #    @assert all(g[i, j] in C[j] * inv(C[i]) for i in 1:nrows(g), j in 1:nrows(g))
  #  end
  #end

################################################################################
#
#  Root lattice
#
################################################################################

function root_lattice(R::Symbol, n::Int)
  if R === :A
    return Zlattice(gram = _root_lattice_A(n))
  end
end

function _root_lattice_A(n::Int)
  z = zero_matrix(FlintQQ, n, n)
  for i in 1:n
    z[i, i] = 2
    if i > 1 
      z[i, i - 1] = -1
    end
    if i < n
      z[i, i + 1] = -1
    end
  end
  return z
end

################################################################################
#
#  Conversion to Magma
#
################################################################################

function to_magma(L::HermLat, target = "L")
  return to_magma(stdout, L, target = target)
end

function to_magma_string(L::HermLat; target = "L")
  b = IOBuffer()
  to_magma(b, L, target = target)
  return String(take!(b))
end

function to_magma(io::IO, L::HermLat; target = "L")
  E = nf(base_ring(L))
  K = base_field(E)
  println(io, "Qx<x> := PolynomialRing(Rationals());")
  f = defining_polynomial(K)
  pol = replace(string(f), "//" => "/")
  pol = replace(pol, string(var(parent(f))) => "x")
  println(io, "f := ", pol, ";")
  println(io, "K<a> := NumberField(f);")
  println(io, "Kt<t> := PolynomialRing(K);")
  f = defining_polynomial(E)
  pol = replace(string(f), "//" => "/")
  pol = replace(pol, string(var(parent(f))) => "t")
  println(io, "g := ", pol, ";")
  println(io, "E<b> := NumberField(g);")
  F = gram_matrix(ambient_space(L))
  Fst = "[" * split(string([F[i, j] for i in 1:nrows(F) for j in 1:ncols(F)]), '[')[2]
  println(io, "F := Matrix(E, ", nrows(F), ", ", ncols(F), ", ", Fst, ");")
  pm = pseudo_matrix(L)
  M = matrix(pm)
  Mst = "[" * split(string([M[i, j] for i in 1:nrows(M) for j in 1:ncols(M)]), '[')[2]
  Mst = replace(Mst, "//" => "/")
  println(io, "M := Matrix(E, ", nrows(M), ", ", ncols(M), ", ", Mst, ");")
  println(io, "OE := MaximalOrder(E);")
  print(io, "C := [ ")
  for (i, I) in enumerate(coefficient_ideals(pm))
    print(io, "ideal< OE | ")
    bas = "[" * split(string(absolute_basis(I)), '[')[2]
    bas = replace(bas, string(var(K)) => "a")
    bas = replace(bas, string(var(E)) => "b")
    bas = replace(bas, "//" => "/")
    if i < length(coefficient_ideals(pm))
      print(io, bas, ">, ")
    else
      println(io, bas, ">];")
    end
  end
  println(io, "M := Module(PseudoMatrix(C, M));")
  println(io, "$target := HermitianLattice(M, F);")
end

function var(E::NfRel)
  return E.S
end
