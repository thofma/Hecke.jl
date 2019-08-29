export quadratic_lattice, rational_span, has_ambient_space, hermitian_lattice

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

function has_ambient_space(L::AbsLat)
  return isdefined(L, :space)
end

function ambient_space(L::AbsLat)
  if has_ambient_space(L)
    return L.space
  else
    throw(error("Ambient quadratic space not defined"))
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
    @show z
    z.pmat = P
    z.gram = gram
    z.involution = involution
    z.base_algebra = K
    return z
  end
end

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
    @show z
    z.pmat = P
    z.gram = gram
    z.involution = involution
    z.base_algebra = K
    return z
  end
end

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

function diagonal(L::AbsLat)
  D, _ = _gram_schmidt(gram_matrix_of_basis(L), involution(L))
  return diagonal(D)
end

pseudo_matrix(L::AbsLat) = L.pmat

coefficient_ideals(L::AbsLat) = coefficient_ideals(pseudo_matrix(L))

basis_matrix(L::AbsLat) = matrix(pseudo_matrix(L))

base_field(L::AbsLat) = L.base_algebra

base_algebra(L::AbsLat) = L.base_algebra

involution(L::QuadLat) = identity

involution(L::HermLat) = L.involution

rank(L::AbsLat) = rank(rational_span(L))

function gram_matrix_of_basis(L::AbsLat)
  if isdefined(L, :gram)
    return L.gram
  else
    return gram_matrix(ambient_space(L), L.pmat.matrix)
  end
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
  return d * I * induce_image(I, v)
end

################################################################################
#
#  Rational (local) equivalence
#
################################################################################

function hasse_invariant(L::QuadLat, p)
  return hasse_invariant(rational_span(L), p)
end

function hasse_invariant(L::HermLat, p)
  throw(error("The lattice must be quadratic"))
end

function witt_invariant(L::QuadLat, p::NfAbsOrdIdl)
  return hasse_invariant(rational_span(L), p)
end

function witt_invariant(L::QuadLat, p::InfPlc)
  return witt_invariant(rational_span(L), p)
end

function isrationally_equivalent(L::QuadLat, M::QuadLat, p::NfAbsOrdIdl)
  return isequivalent(rational_span(L), rational_span(M), p)
end

function isrationally_equivalent(L::QuadLat, M::QuadLat, p::InfPlc)
  return isequivalent(rational_span(L), rational_span(M), p)
end

function isrationally_equivalent(L::QuadLat, M::QuadLat)
  return isequivalent(rational_span(L), rational_span(M))
end

################################################################################
#
#  Definiteness
#
################################################################################

ispositive_definite(L::AbsLat) = ispositive_definite(rational_span(L))

isnegative_definite(L::AbsLat) = isnegative_definite(rational_span(L))

isdefinite(L::AbsLat) = isdefinite(rational_span(L))

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

Return a $\mathbf{Z}$-basis of $L$.
"""
function absolute_basis(L::AbsLat)
end

@doc Markdown.doc"""
    absolute_basis_matrix(L::AbsLat) -> MatElem

Return a $\mathbf{Z}$-basis matrix of $L$.
"""
function absolute_basis_matrix(L::AbsLat)
end

################################################################################
#
#  Local basis matrix
#
################################################################################

function local_basis_matrix(L::AbsLat, p, type::Symbol = :any)
  if type == :any
    return _local_basis_matrix(pseudo_matrix(L), p)
  elseif type == :submodule
    return _local_basis_submodule_matrix(pseudo_matrix(L), p)
  elseif type == :supermodule
    return _local_basis_supermodule_matrix(pseudo_matrix(L), p)
  else
    throw(error("Invalid type keyword :$(type).\nMust be either :any, :submodule, or :supermodule"))
  end
end

################################################################################
#
#  Norm
#
################################################################################

# cache this
function norm(L::QuadLat)
  G = gram_matrix_of_basis(L)
  C = coefficient_ideals(L)
  return sum(G[i, i] * C[i]^2 for i in 1:length(C)) + nf(order(C[1]))(2) * scale(L)
end

# TODO: Be careful with the +, trace_ideal gives fmpq and then this must be gcd
function norm(L::HermLat)
  G = gram_matrix_of_basis(L)
  K = base_ring(G)
  C = coefficient_ideals(L)
  to_sum = sum(G[i, i] * C[i] * induce_image(C[i], involution(L)) for i in 1:length(C))
  to_sum = to_sum + K(reduce(gcd, [ideal_trace(C[i] * G[i, j] * induce_image(C[j], involution(L))) for j in 1:length(C) for i in 1:(j-1)]; init = fmpq(0)) )* order(to_sum)
  return to_sum
end

################################################################################
#
#  Scale
#
################################################################################

# cache this
function scale(L::QuadLat)
  G = gram_matrix_of_basis(L)
  C = coefficient_ideals(L)
  to_sum = [ G[i, j] * C[i] * involution(L)(C[j]) for j in 1:length(C) for i in 1:j]
  return sum(to_sum)
end

function scale(L::HermLat)
  G = gram_matrix_of_basis(L)
  C = coefficient_ideals(L)
  to_sum = [ G[i, j] * C[i] * induce_image(C[j], involution(L)) for j in 1:length(C) for i in 1:j ]
  d = length(to_sum)
  for i in 1:d
    push!(to_sum, induce_image(to_sum[i], involution(L)))
  end
  return sum(to_sum)
end

################################################################################
#
#  Rescale
#
################################################################################

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

fixed_field(L::AbsLat) = base_field(base_algebra(L))

################################################################################
#
#  Is integral?
#
################################################################################

function isintegral(L::AbsLat)
  return isintegral(scale(L))
end

function isintegral(I::NfOrdFracIdl)
  @assert ismaximal(order(I))
  simplify(I)
  return denominator(I) == 1
end

################################################################################
#
#  Dual
#
################################################################################

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

function volume(L::AbsLat)
  return discriminant(L)
end

################################################################################
#
#  Modularity
#
################################################################################

function ismodular(L::AbsLat)
  a = scale(L)
  if volume(L) == a^rank(L)
    return true, a
  else
    return false, a
  end
end

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

function induce_image(A::NfOrdFracIdl, S::Map)
  return induce_image(numerator(A), S)//denominator(A)
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

# TODO: The scaling of pseudo-matrices with an element scales the ideals and not the matrix ...
