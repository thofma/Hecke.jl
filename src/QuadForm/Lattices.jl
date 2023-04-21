export *, +, absolute_basis, absolute_basis_matrix, ambient_space,
       automorphism_group_generators, automorphism_group_order, bad_primes,
       basis_matrix, basis_matrix_of_rational_span, can_scale_totally_positive,
       coefficient_ideals, degree, diagonal, diagonal_of_rational_span,
       discriminant, dual, fixed_field, fixed_ring, generators, gram_matrix_of_generators,
       gram_matrix_of_rational_span, hasse_invariant, hermitian_lattice, intersect,
       involution, is_definite, is_integral, is_isometric, is_local_norm, is_locally_isometric,
       is_modular, is_negative_definite, is_positive_definite, is_rationally_isometric,
       is_sublattice, is_sublattice_with_relations, jordan_decomposition, lattice,
       local_basis_matrix, norm, normic_defect, pseudo_matrix, quadratic_lattice,
       rank, rational_span, rescale, restrict_scalars, restrict_scalars_with_map, scale,
       volume, witt_invariant, Zlattice, trace_lattice_with_isometry,
       trace_lattice_with_isometry_and_transfer_data, hermitian_structure,
       hermitian_structure_with_transfer_data


export HermLat, QuadLat

# aliases for deprecation
is_equivalent(U::AbstractLat, V::AbstractLat) = is_isometric(U, V)
is_equivalent(U::AbstractLat, V::AbstractLat, p) = is_isometric(U, V, p)
is_rationally_equivalent(U::AbstractLat, V::AbstractLat) = is_rationally_isometric(U, V)
is_rationally_equivalent(U::AbstractLat, V::AbstractLat, p) = is_rationally_isometric(U, V, p)
is_equivalent(U::AbstractSpace, V::AbstractSpace) = is_isometric(U, V)
is_equivalent(U::AbstractSpace, V::AbstractSpace, p) = is_isometric(U, V, p)
is_equivalent_with_isometry(U::AbstractLat, V::AbstractLat) = is_isometric_with_isometry(U, V)
is_equivalent_with_isometry(U::AbstractSpace, V::AbstractSpace) = is_isometric_with_isometry(U, V)

################################################################################
#
#  Verbosity and assertion scopes
#
################################################################################

add_verbosity_scope(:Lattice)

add_assertion_scope(:Lattice)

################################################################################
#
#  Ambient space
#
################################################################################

@doc raw"""
    has_ambient_space(L::AbstractLat) -> Bool

Return whether the ambient space of the lattice `L` is set.
"""
function has_ambient_space(L::AbstractLat)
  return isdefined(L, :space)
end

@doc raw"""
    ambient_space(L::AbstractLat) -> AbstractSpace

Return the ambient space of the lattice `L`. If the ambient space is not known, an
error is raised.
"""
function ambient_space(L::AbstractLat)
  if !has_ambient_space(L)
    B = matrix(pseudo_matrix(L))
    @assert isone(B)
    L.space = rational_span(L)
  end
  return L.space
end

################################################################################
#
#  Rational span
#
################################################################################

@doc raw"""
    rational_span(L::AbstractLat) -> AbstractSpace

Return the rational span of the lattice `L`.
"""
rational_span(::AbstractLat)

################################################################################
#
#  Diagonal
#
################################################################################

@doc raw"""
    diagonal_of_rational_span(L::AbstractLat) -> Vector

Return the diagonal of the rational span of the lattice `L`.
"""
function diagonal_of_rational_span(L::AbstractLat)
  D, _ = _gram_schmidt(gram_matrix_of_rational_span(L), involution(L))
  return diagonal(D)
end

################################################################################
#
#  Module properties
#
################################################################################

@doc raw"""
    pseudo_matrix(L::AbstractLat) -> PMat

Return a basis pseudo-matrix of the lattice `L`.
"""
pseudo_matrix(L::AbstractLat) = L.pmat

@doc raw"""
    pseudo_basis(L::AbstractLat) -> Vector{Tuple{Vector, Ideal}}

Return a pseudo-basis of the lattice `L`.
"""
function pseudo_basis(L::AbstractLat)
  M = matrix(pseudo_matrix(L))
  LpM = pseudo_matrix(L)
  O = base_ring(LpM)
  z = Vector{Tuple{Vector{elem_type(nf(O))}, fractional_ideal_type(O)}}(undef, nrows(M))
  for i in 1:nrows(M)
    z[i] = (elem_type(base_ring(M))[ M[i, j] for j in 1:ncols(M) ],
            coefficient_ideals(LpM)[i])
  end
  return z
end

@doc raw"""
    coefficient_ideals(L::AbstractLat) -> Vector{NfOrdIdl}

Return the coefficient ideals of a pseudo-basis of the lattice `L`.
"""
coefficient_ideals(L::AbstractLat) = coefficient_ideals(pseudo_matrix(L))

@doc raw"""
    basis_matrix_of_rational_span(L::AbstractLat) -> MatElem

Return a basis matrix of the rational span of the lattice `L`.
"""
basis_matrix_of_rational_span(L::AbstractLat) = matrix(pseudo_matrix(L))

@doc raw"""
    base_field(L::AbstractLat) -> Field

Return the algebra over which the rational span of the lattice `L` is defined.
"""
base_field(L::AbstractLat) = L.base_algebra

@doc raw"""
    base_ring(L::AbstractLat) -> Ring

Return the order over which the lattice `L` is defined.
"""
base_ring(L::AbstractLat) = base_ring(L.pmat)

@doc raw"""
    fixed_field(L::AbstractLat) -> Field

Returns the fixed field of the involution of the lattice `L`.
"""
fixed_field(L::AbstractLat) = fixed_field(rational_span(L))

@doc raw"""
    fixed_ring(L::AbstractLat) -> Ring

Return the maximal order in the fixed field of the lattice `L`.
"""
fixed_ring(L::AbstractLat) = maximal_order(fixed_field(L))

@doc raw"""
    involution(L::AbstractLat) -> Map

Return the involution of the rational span of the lattice `L`.
"""
involution(::AbstractLat)

@doc raw"""
    rank(L::AbstractLat) -> Int

Return the rank of the underlying module of the lattice `L`.
"""
rank(L::AbstractLat) = dim(rational_span(L))

@doc raw"""
    degree(L::AbstractLat) -> Int

Return the dimension of the ambient space of the lattice `L`.
"""
function degree(L::AbstractLat)
  if isdefined(L, :space)
    return dim(L.space)
  else
    return ncols(L.pmat.matrix)
  end
end

@doc raw"""
    is_sublattice(L::AbstractLat, M::AbstractLat) -> Bool

Return whether `M` is a sublattice of the lattice `L`.
"""
function is_sublattice(L::AbstractLat, M::AbstractLat)
  if L === M
    return true
  end

  if ambient_space(L) != ambient_space(M)
    return false
  end

  return _spans_subset_of_pseudohnf(pseudo_matrix(M), _pseudo_hnf(L), :lowerleft)
end

@doc raw"""
    issubset(M::AbstractLat, L::AbstractLat) -> Bool

Return whether `M` is a subset of the lattice `L`.
"""
Base.issubset(M::AbstractLat, L::AbstractLat) = is_sublattice(L, M)

################################################################################
#
#  Pseudo-HNF
#
################################################################################

# Return a lowerleft pseudo hnf
function _pseudo_hnf(L::AbstractLat)
  get_attribute!(L, :pseudo_hnf) do
    pseudo_hnf(pseudo_matrix(L), :lowerleft)
  end::typeof(L.pmat)
end

################################################################################
#
#  Equality
#
################################################################################

function Base.:(==)(L::AbstractLat, M::AbstractLat)
  if L === M
    return true
  end
  if ambient_space(L) != ambient_space(M)
    return false
  end
  return _modules_equality(_pseudo_hnf(L),
                           _pseudo_hnf(M))
end

################################################################################
#
#  Gram matrix
#
################################################################################

@doc raw"""
    gram_matrix_of_rational_span(L::AbstractLat) -> MatElem

Return the Gram matrix of the rational span of the lattice `L`.
"""
function gram_matrix_of_rational_span(L::AbstractLat)
  if isdefined(L, :gram)
    return L.gram
  else
    return gram_matrix(ambient_space(L), L.pmat.matrix)
  end
end

################################################################################
#
#  Generators
#
################################################################################

# Check if one really needs minimal
# Steinitz form is not pretty

@doc raw"""
    generators(L::AbstractLat; minimal = false) -> Vector{Vector}

Return a set of generators of the lattice `L` over the base ring of `L`.

If `minimal == true`, the number of generators is minimal. Note that computing
minimal generators is expensive.
"""
function generators(L::AbstractLat; minimal::Bool = false)
  K = nf(base_ring(L))
  T = elem_type(K)
  if !minimal
    if isdefined(L, :generators)
      return L.generators::Vector{Vector{T}}
    end
    v = Vector{T}[]
    St = pseudo_matrix(L)
    d = ncols(St)
    for i in 1:nrows(St)
      if base_ring(L) isa NfOrd
        I = numerator(St.coeffs[i])
        den = denominator(St.coeffs[i])
        _assure_weakly_normal_presentation(I)
        push!(v, T[K(I.gen_one)//den * matrix(St)[i, j] for j in 1:d])
        push!(v, T[K(I.gen_two)//den * matrix(St)[i, j] for j in 1:d])
      else
        I = numerator(coefficient_ideals(St)[i])
        den = denominator(coefficient_ideals(St)[i])
        for g in absolute_basis(I)
          push!(v, T[K(g)//den * matrix(St)[i, j] for j in 1:d])
        end
      end
    end
    L.generators = v
    return v
  else # minimal
    if isdefined(L, :minimal_generators)
      return L.minimal_generators::Vector{Vector{T}}
    end
    St = _steinitz_form(pseudo_matrix(L), Val{false})
    d = nrows(St)
    n = degree(L)
    v = Vector{T}[]
    for i in 1:(d - 1)
      #@assert is_principal(coefficient_ideals(St)[i])[1]
      push!(v, T[matrix(St)[i, j] for j in 1:d])
    end

    I = numerator(coefficient_ideals(St)[d])
    den = denominator(coefficient_ideals(St)[d])
    if minimal && base_ring(L) isa NfOrd
      b, a = is_principal(I)
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
  end

  L.minimal_generators = v

  return v
end

###############################################################################
#
# Constructors
#
###############################################################################

@doc raw"""
    lattice(V::AbstractSpace, B::PMat ; check::Bool = true) -> AbstractLat

Given an ambient space `V` and a pseudo-matrix `B`, return the lattice spanned
by the pseudo-matrix `B` inside `V`. If `V` is hermitian (resp. quadratic) then
the output is a hermitian (resp. quadratic) lattice.

By default, `B` is checked to be of full rank. This test can be disabled by setting
`check` to false.
"""
lattice(V::AbstractSpace, B::PMat ; check::Bool = true)

@doc raw"""
    lattice(V::AbstractSpace, basis::MatElem ; check::Bool = true) -> AbstractLat

Given an ambient space `V` and a matrix `basis`, return the lattice spanned
by the rows of `basis` inside `V`. If `V` is hermitian (resp. quadratic) then
the output is a hermitian (resp. quadratic) lattice.

By default, `basis` is checked to be of full rank. This test can be disabled by setting
`check` to false.
"""
lattice(V::AbstractSpace, basis::MatElem ; check::Bool = true) = lattice(V, pseudo_matrix(basis), check = check)

@doc raw"""
    lattice(V::AbstractSpace, gens::Vector) -> AbstractLat

Given an ambient space `V` and a list of generators `gens`, return the lattice
spanned by `gens` in `V`. If `V` is hermitian (resp. quadratic) then the output
is a hermitian (resp. quadratic) lattice.

If `gens` is empty, the function returns the zero lattice in `V`.
"""
function lattice(V::Hecke.AbstractSpace, gens::Vector)
  if length(gens) == 0
    pm = pseudo_matrix(matrix(base_ring(V), 0, dim(V), []))
    return lattice(V, pm, check = false)
  end
  @assert length(gens[1]) > 0
  @req all(v -> length(v) == length(gens[1]), gens) "All vectors in gens must be of the same length"
  @req length(gens[1]) == dim(V) "Incompatible arguments: the length of the elements of gens must correspond to the dimension of V"
  F = base_ring(V)
  gens = [map(F, v) for v in gens]
  M = zero_matrix(F, length(gens), length(gens[1]))
  for i=1:nrows(M)
    for j=1:ncols(M)
      M[i,j] = gens[i][j]
    end
  end
  pm = pseudo_hnf(pseudo_matrix(M), :lowerleft)
  i = 1
  while is_zero_row(pm.matrix, i)
    i += 1
  end
  pm = sub(pm, i:nrows(pm), 1:ncols(pm))
  L = lattice(V, pm, check = false)
  L.generators = gens
  return L
end

@doc raw"""
    lattice(V::AbstractSpace) -> AbstractLat

Given an ambient space `V`, return the lattice with the standard basis
matrix. If `V` is hermitian (resp. quadratic) then the output is a hermitian
(resp. quadratic) lattice.
"""
lattice(V::AbstractSpace) = lattice(V, identity_matrix(base_ring(V), rank(V)), check = false)

################################################################################
#
#  Gram matrix of generators
#
################################################################################

@doc raw"""
    gram_matrix_of_generators(L::AbstractLat; minimal::Bool = false) -> MatElem

Return the Gram matrix of a generating set of the lattice `L`.

If `minimal == true`, then a minimal generating set is used. Note that computing
minimal generators is expensive.
"""
function gram_matrix_of_generators(L::AbstractLat; minimal::Bool = false)
  m = generators(L, minimal = minimal)
  M = matrix(nf(base_ring(L)), m)
  return gram_matrix(ambient_space(L), M)
end

################################################################################
#
#  Discriminant
#
################################################################################

@doc raw"""
    discriminant(L::AbstractLat) -> NfOrdFracIdl

Return the discriminant of the lattice `L`, that is, the generalized index ideal
$[L^\# : L]$.
"""
function discriminant(L::AbstractLat)
  d = det(gram_matrix_of_rational_span(L))
  v = involution(L)
  C = coefficient_ideals(L)
  I = prod(J for J in C)
  return d * I * v(I)
end

################################################################################
#
#  Rational (local) isometry
#
################################################################################

@doc raw"""
    hasse_invariant(L::AbstractLat, p::Union{InfPlc, NfOrdIdl}) -> Int

Return the Hasse invariant of the rational span of the lattice `L` at the place `p`.
The lattice must be quadratic.
"""
hasse_invariant(L::AbstractLat, p)

@doc raw"""
    witt_invariant(L::AbstractLat, p::Union{InfPlc, NfOrdIdl}) -> Int

Return the Witt invariant of the rational span of the lattice `L` at the place `p`.
The lattice must be quadratic.
"""
witt_invariant(L::AbstractLat, p)

################################################################################
#
#  Rational isometry
#
################################################################################

@doc raw"""
    is_rationally_isometric(L::AbstractLat, M::AbstractLat, p::Union{InfPlc, NfAbsOrdIdl})
                                                                         -> Bool

Return whether the rational spans of the lattices `L` and `M` are isometric over
the completion at the place `p`.
"""
is_rationally_isometric(::AbstractLat, ::AbstractLat, ::NfAbsOrdIdl)

function is_rationally_isometric(L::AbstractLat, M::AbstractLat, p::NfAbsOrdIdl)
  return is_isometric(rational_span(L), rational_span(M), p)
end

function is_rationally_isometric(L::AbstractLat, M::AbstractLat, p::InfPlc)
  return is_isometric(rational_span(L), rational_span(M), p)
end

@doc raw"""
    is_rationally_isometric(L::AbstractLat, M::AbstractLat) -> Bool

Return whether the rational spans of the lattices `L` and `M` are isometric.
"""
function is_rationally_isometric(L::AbstractLat, M::AbstractLat)
  return is_isometric(rational_span(L), rational_span(M))
end

################################################################################
#
#  Definiteness
#
################################################################################

@doc raw"""
    is_positive_definite(L::AbstractLat) -> Bool

Return whether the rational span of the lattice `L` is positive definite.
"""
is_positive_definite(L::AbstractLat) = is_positive_definite(rational_span(L))

@doc raw"""
    is_negative_definite(L::AbstractLat) -> Bool

Return whether the rational span of the lattice `L` is negative definite.
"""
is_negative_definite(L::AbstractLat) = is_negative_definite(rational_span(L))

@doc raw"""
    is_definite(L::AbstractLat) -> Bool

Return whether the rational span of the lattice `L` is definite.
"""
@attr Bool is_definite(L::AbstractLat) = is_definite(rational_span(L))

@doc raw"""
    can_scale_totally_positive(L::AbstractLat) -> Bool, NumFieldElem

Return whether there is a totally positive rescaled lattice of the lattice `L`.
If so, the second returned value is an element $a$ such that $L^a$ is totally positive.
"""
function can_scale_totally_positive(L::AbstractLat)
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

@doc raw"""
    +(L::AbstractLat, M::AbstractLat) -> AbstractLat

Return the sum of the lattices `L` and `M`.

The lattices `L` and `M` must have the same ambient space.
"""
Base.:(+)(::AbstractLat, ::AbstractLat)

function Base.:(+)(L::T, M::T) where {T <: AbstractLat}
  @assert has_ambient_space(L) && has_ambient_space(M)
  @assert ambient_space(L) === ambient_space(M)
  V = ambient_space(L)
  fr = nrows(pseudo_matrix(L)) == dim(V) || nrows(pseudo_matrix(M)) == dim(V)
  m = _sum_modules(L, pseudo_matrix(L), pseudo_matrix(M), fr)
  return lattice_in_same_ambient_space(L, m)
end

################################################################################
#
#  Intersection
#
################################################################################

@doc raw"""
    intersect(L::AbstractLat, M::AbstractLat) -> AbstractLat

Return the intersection of the lattices `L` and `M`.

The lattices `L` and `M` must have the same ambient space.
"""
intersect(::AbstractLat, ::AbstractLat)

function intersect(L::T, M::T) where T <: AbstractLat
  @assert has_ambient_space(L) && has_ambient_space(M)
  @req ambient_space(L) === ambient_space(M) "Lattices must be in the same ambient space"
  V = ambient_space(L)
  fr = nrows(pseudo_matrix(L)) == dim(V) && nrows(pseudo_matrix(M)) == dim(V)
  if !fr
    return _intersect_via_restriction_of_scalars(L, M)
  end
  m = _intersect_modules(L, pseudo_matrix(L), pseudo_matrix(M), fr)
  return lattice_in_same_ambient_space(L, m)
end

function _intersect_via_restriction_of_scalars(L::AbstractLat, M::AbstractLat)
  @assert has_ambient_space(L) && has_ambient_space(M)
  @assert ambient_space(L) === ambient_space(M)
  @assert !(L isa ZLat)
  Lres, f = restrict_scalars_with_map(L, FlintQQ)
  Mres = restrict_scalars(M, f)
  Nres = intersect(Lres, Mres)
  Bres = basis_matrix(Nres)
  gens = [f(vec(collect(Bres[i,:]))) for i in 1:nrows(Bres)]
  return lattice(ambient_space(L), gens)
end

################################################################################
#
#  Scalar multiplication
#
################################################################################

@doc raw"""
    *(a::NumFieldElem, L::AbstractLat) -> AbstractLat

Return the lattice $aL$ inside the ambient space of the lattice `L`.
"""
function Base.:(*)(a::NumFieldElem, L::AbstractLat)
  @assert has_ambient_space(L)
  O = maximal_order(parent(a))
  m = _module_scale_ideal(a*O, pseudo_matrix(L))
  return lattice_in_same_ambient_space(L, m)
end

function Base.:(*)(L::QuadLat, a)
  return a * L
end

@doc raw"""
    *(a::NumFieldOrdIdl, L::AbstractLat) -> AbstractLat

Return the lattice $aL$ inside the ambient space of the lattice `L`.
"""
Base.:(*)(::NumFieldOrdIdl, ::AbstractLat)

function Base.:(*)(a::Union{NfRelOrdIdl, NfAbsOrdIdl}, L::AbstractLat)
  @assert has_ambient_space(L)
  m = _module_scale_ideal(a, pseudo_matrix(L))
  return lattice_in_same_ambient_space(L, m)
end

@doc raw"""
    *(a::NumFieldOrdFracIdl, L::AbstractLat) -> AbstractLat

Return the lattice $aL$ inside the ambient space of the lattice `L`.
"""
Base.:(*)(::NumFieldOrdFracIdl, ::AbstractLat)

function Base.:(*)(a::Union{NfRelOrdFracIdl, NfAbsOrdFracIdl}, L::AbstractLat)
  @assert has_ambient_space(L)
  m = _module_scale_ideal(a, pseudo_matrix(L))
  return lattice_in_same_ambient_space(L, m)
end

################################################################################
#
#  Absolute basis
#
################################################################################

@doc raw"""
    absolute_basis(L::AbstractLat) -> Vector

Return a $\mathbf{Z}$-basis of the lattice `L`.
"""
function absolute_basis(L::AbstractLat)
  pb = pseudo_basis(L)
  z = Vector{Vector{elem_type(base_field(L))}}()
  for (v, a) in pb
    for w in absolute_basis(a)
      push!(z, w .* v)
    end
  end
  @assert length(z) == absolute_degree(base_field(L)) * rank(L)
  return z
end

################################################################################
#
#  Absolute basis matrix
#
################################################################################

@doc raw"""
    absolute_basis_matrix(L::AbstractLat) -> MatElem

Return a $\mathbf{Z}$-basis matrix of the lattice `L`.
"""
function absolute_basis_matrix(L::AbstractLat)
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

@doc raw"""
    norm(L::AbstractLat) -> NfOrdFracIdl

Return the norm of the lattice `L`. This is a fractional ideal of the fixed field
of `L`.
"""
norm(::AbstractLat)

################################################################################
#
#  Scale
#
################################################################################

@doc raw"""
    scale(L::AbstractLat) -> NfOrdFracIdl

Return the scale of the lattice `L`.
"""
scale(L::AbstractLat)

################################################################################
#
#  Rescale
#
################################################################################

@doc raw"""
    rescale(L::AbstractLat, a::NumFieldElem) -> AbstractLat

Return the rescaled lattice $L^a$. Note that this has a different ambient
space than the lattice `L`.
"""
rescale(::AbstractLat, ::NumFieldElem)

Base.:(^)(L::AbstractLat, a::RingElement) = rescale(L, a)

################################################################################
#
#  Is integral
#
################################################################################

@doc raw"""
    is_integral(L::AbstractLat) -> Bool

Return whether the lattice `L` is integral.
"""
function is_integral(L::AbstractLat)
  return is_integral(scale(L))
end

################################################################################
#
#  Dual lattice
#
################################################################################

@doc raw"""
    dual(L::AbstractLat) -> AbstractLat

Return the dual lattice of the lattice `L`.
"""
dual(::AbstractLat)

################################################################################
#
#  Volume
#
################################################################################

@doc raw"""
    volume(L::AbstractLat) -> NfOrdFracIdl

Return the volume of the lattice `L`.
"""
function volume(L::AbstractLat)
  return discriminant(L)
end

################################################################################
#
#  Modularity
#
################################################################################

@doc raw"""
    is_modular(L::AbstractLat) -> Bool, NfOrdFracIdl

Return whether the lattice `L` is modular. In this case, the second returned value
is a fractional ideal $\mathfrak a$ of the base algebra of `L` such that
$\mathfrak a L^\# = L$, where $L^\#$ is the dual of `L`.
"""
function is_modular(L::AbstractLat)
  a = scale(L)
  if volume(L) == a^rank(L)
    return true, a
  else
    return false, a
  end
end

@doc raw"""
    is_modular(L::AbstractLat, p::NfOrdIdl) -> Bool, Int

Return whether the completion $L_{p}$ of the lattice `L` at the prime ideal `p`
is modular. If it is the case the second returned value is an integer `v` such
that $L_{p}$ is $p^v$-modular.
"""
is_modular(::AbstractLat, p)

function is_modular(L::AbstractLat{<: NumField}, p)
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
#  Local basis matrix
#
################################################################################

@doc raw"""
    local_basis_matrix(L::AbstractLat, p::NfOrdIdl; type = :any) -> MatElem

Given a prime ideal `p` and a lattice `L`, return a basis matrix of a lattice
`M` such that $M_{p} = L_{p}$. Note that if `p` is an ideal in the base ring of
`L`, the completions are taken at the minimum of `p` (which is an ideal in the
base ring of the order of `p`).

- If `type == :submodule`, the lattice `M` will be a sublattice of `L`.
- If `type == :supermodule`, the lattice `M` will be a superlattice of `L`.
- If `type == :any`, there may not be any containment relation between `M` and
  `L`.
"""
function local_basis_matrix(L::AbstractLat, p; type::Symbol = :any)
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
    #  error("""Invalid :type keyword :$(type).
    #           Must be either :any, :submodule, or :supermodule""")
    #end
  elseif S === base_ring(R)
    if type == :any
      return _local_basis_matrix_prime_below(pseudo_matrix(L), p)
    elseif type == :submodule
      return _local_basis_matrix_prime_below_submodule(pseudo_matrix(L), p)
    elseif type == :supermodule
      throw(NotImplemented())
    else
      error("""Invalid :type keyword :$(type).
               Must be either :any, :submodule, or :supermodule""")
    end
  else
    error("Something wrong")
  end
end

################################################################################
#
#  Jordan decomposition
#
################################################################################

@doc raw"""
    jordan_decomposition(L::AbstractLat, p::NfOrdIdl)
                                -> Vector{MatElem}, Vector{MatElem}, Vector{Int}

Return a Jordan decomposition of the completion of the lattice `L` at a prime
ideal `p`.

The returned value consists of three lists $(M_i)_i$, $(G_i)_i$ and $(s_i)_i$ of
the same length $r$. The completions of the row spans of the matrices $M_i$
yield a Jordan decomposition of $L_{p}$ into modular sublattices
$L_i$ with Gram matrices $G_i$ and scale of $p$-adic valuation $s_i$.
"""
jordan_decomposition(L::AbstractLat, p::NfOrdIdl)

################################################################################
#
#  Local isometry
#
################################################################################

@doc raw"""
    is_locally_isometric(L::AbstractLat, M::AbstractLat, p::NfOrdIdl) -> Bool

Return whether the completions of the lattices `L` and `M` at the prime ideal
`p` are isometric.
"""
is_locally_isometric(::AbstractLat, ::AbstractLat, ::NfOrdIdl)

################################################################################
#
#  Isotropy
#
################################################################################

@doc raw"""
    is_isotropic(L::AbstractLat, p::Union{NfOrdIdl, InfPlc}) -> Bool

Return whether the completion of the lattice `L` at the place `p` is
isotropic.
"""
is_isotropic(L::AbstractLat, p) = is_isotropic(rational_span(L), p)

################################################################################
#
#  Restrict scalars
#
################################################################################

@doc raw"""
    restrict_scalars(L::AbstractLat, K::QQField,
                                     alpha::FieldElem = one(base_field(L))) -> ZLat

Given a lattice `L` in a space $(V, \Phi)$, return the $\mathcal O_K$-lattice
obtained by restricting the scalars of $(V, \alpha\Phi)$ to the number field `K`.
The rescaling factor $\alpha$ is set to 1 by default.

Note that for now one can only restrict scalars to $\mathbb Q$.
"""
function restrict_scalars(L::AbstractLat, K::QQField,
                                          alpha::FieldElem = one(base_field(L)))
  V = ambient_space(L)
  Vabs, f = restrict_scalars(V, K, alpha)
  Babs = absolute_basis(L)
  Mabs = zero_matrix(FlintQQ, length(Babs), rank(Vabs))
  for i in 1:length(Babs)
    v = f\(Babs[i])
    for j in 1:length(v)
      Mabs[i, j] = v[j]
    end
  end
  return ZLat(Vabs, Mabs)
end

@doc raw"""
    restrict_scalars_with_map(L::AbstractLat, K::QQField,
                                              alpha::FieldElem = one(base_field(L)))
                                                        -> Tuple{ZLat, AbstractSpaceRes}

Given a lattice `L` in a space $(V, \Phi)$, return the $\mathcal O_K$-lattice
obtained by restricting the scalars of $(V, \alpha\Phi)$ to the number field `K`,
together with the map `f` for extending scalars back.
The rescaling factor $\alpha$ is set to 1 by default.

Note that for now one can only restrict scalars to $\mathbb Q$.
"""
function restrict_scalars_with_map(L::AbstractLat, K::QQField,
                                                   alpha::FieldElem = one(base_field(L)))
  V = ambient_space(L)
  Vabs, f = restrict_scalars(V, K, alpha)
  Babs = absolute_basis(L)
  Mabs = zero_matrix(FlintQQ, length(Babs), rank(Vabs))
  for i in 1:length(Babs)
    v = f\(Babs[i])
    for j in 1:length(v)
      Mabs[i, j] = v[j]
    end
  end
  return ZLat(Vabs, Mabs), f
end

@doc raw"""
    restrict_scalars(L::AbstractLat, f::AbstractSpaceRes) -> ZLat

Given a lattice `L` in a space $(V, \Phi)$ and a map `f` for restricting the
scalars of $(V, \alpha\Phi)$ to a number field `K`, where $\alpha$ is in the
base algebra of `L`, return the associated $\mathcal O_K$-lattice obtained from
`L` with respect to `f`.

Note that for now one can only restrict scalars to $\mathbb Q$.
"""
function restrict_scalars(L::AbstractLat, f::AbstractSpaceRes)
  @req ambient_space(L) === codomain(f) "Incompatible arguments: ambient space of L must be the same as the codomain of f"
  Vabs = domain(f)
  Babs = absolute_basis(L)
  Mabs = zero_matrix(FlintQQ, length(Babs), rank(Vabs))
  for i in 1:length(Babs)
    v = f\(Babs[i])
    for j in 1:length(v)
      Mabs[i, j] = v[j]
    end
  end
  return ZLat(Vabs, Mabs)
end

################################################################################
#
#  Trace equivalence
#
################################################################################

# TODO: add jldoctest
@doc raw"""
    trace_lattice_with_isometry(H::AbstractLat{T}; alpha::FieldElem = one(base_field(H)),
                                                   beta::FieldElem = gen(base_field(H)),
                                                   order::Integer = 2) where T
                                                                       -> ZLat, QQMatrix

Given a lattice `H` which is either:

   - a $\mathbb Z$-lattice (i.e. of type `ZLat`);
   - a hermitian lattice over a CM-extension $E/K$, where $E/\mathbb{Q}$ is defined
     by an irreducible monic polynomial $p$ with $p(0) = 1$

return the pair $(L, f)$ where $L$ is a $\mathbb{Z}$-lattice obtained as the trace
lattice of $H$ [`restrict_scalars(::AbstractLat)`](@ref)) and $f$ is an isometry
of $L$ given by:

   - the identity if $H$ is a `ZLat` and `order == 1`;
   - the opposite of the identity if $H$ is a `ZLat` and `order == 2`;
   - given by the multiplication by an element `beta` of norm 1 in $E$
     otherwise.

Note that the optional argument `order` has no effect if `H` is not a
$\mathbb Z$-lattice.

The choice of `alpha` corresponds to the choice of a rescaling of the form on $H$
for the trace construction using [`restrict_scalars`](@ref).

The choice of `beta` corresponds to the choice of an element of norm 1 in the
base field of $H$, in the hermitian case, used to construct the isometry `f`.

Note that the isometry `f` computed is given by its action on the ambient space of the
trace lattice of `H`.
"""
function trace_lattice_with_isometry(H::AbstractLat{T}; alpha::FieldElem = one(base_field(H)),
                                                        beta::FieldElem = gen(base_field(H)),
                                                        order::Integer = 2) where T

  return trace_lattice_with_isometry_and_transfer_data(H, alpha=alpha, beta=beta, order=order)[1:2]
end

# TODO: add jldoctest
@doc raw"""
    trace_lattice_with_isometry_and_transfer_data(H::AbstractLat{T}; alpha::FieldElem = one(base_field(H)),
                                                                     beta::FieldElem = gen(base_field(H)),
                                                                     order::Integer = 2) where T
                                                                        -> ZLat, QQMatrix, AbstractSpaceRes

Return the trace lattice of `H` together with the associated isometry corresponding
to multiplication by `beta` (see [`trace_lattice(::AbstractLat)`](@ref)) and with
the map of change of scalars associated to the underlying trace construction.
"""
function trace_lattice_with_isometry_and_transfer_data(H::AbstractLat{T}; alpha::FieldElem = one(base_field(H)),
                                                                          beta::FieldElem = gen(base_field(H)),
                                                                          order::Integer = 2) where T
  E = base_field(H)

  # We only consider full rank lattices for simplicity
  @req degree(H) == rank(H) "Lattice must be of full rank"
  @req parent(beta) === E "beta must be an element of the base algebra of H"
  @req (beta == QQ(1) || norm(beta) == 1) "beta must be of norm 1"
  @req !is_zero(alpha) "alpha must be non zero"

  n = degree(H)

  # will be useful to shorten code of lattices with isometry on Oscar
  if E == QQ
    @req order in [1,2] "For ZLat the order must be 1 or 2"
    V = ambient_space(H)
    if order == 1
      f = identity_matrix(E, n)
    else
      f = -identity_matrix(E, n)
    end
    return H, f, AbstractSpaceRes(V, V, identity_matrix(E, n), identity_matrix(E, n))
  end

  @req (degree(E) == 2) && (is_totally_complex(E)) && (is_totally_real(base_field(E))) "The base field of H must be CM"
  @req maximal_order(E) == equation_order(E) "Equation order and maximal order must coincide"

  # This function perform the trace construction on the level of the
  # ambient spaces - we just need to transport the lattice
  Lres, res = restrict_scalars_with_map(H, QQ, alpha)

  # This will correspond to multiplication by beta along the transfer
  iso = zero_matrix(QQ, 0, degree(Lres))

  v = vec(zeros(QQ, 1, degree(Lres)))

  for i in 1:degree(Lres)
    v[i] = one(QQ)
    v2 = res(v)
    v2 = beta.*v2
    v3 = (res\v2)
    iso = vcat(iso, transpose(matrix(v3)))
    v[i] = zero(QQ)
  end

  @hassert :Lattice 2 iso*gram_matrix(ambient_space(Lres))*transpose(iso) == gram_matrix(ambient_space(Lres))

  return Lres, iso, res
end

# TODO: add jldoctest
@doc raw"""
    trace_lattice_with_isometry(H::HermLat, res::AbstractSpaceRes) where T
                                                       -> ZLat, QQMatrix, AbstractSpaceRes

Return the trace lattice of `H` together with the associated isometry (see
[`trace_lattice(::AbstractLat)`](@ref)) with respect to the given map of change of scalars
`res`.
"""
function trace_lattice_with_isometry(H::HermLat, res::AbstractSpaceRes; beta::FieldElem = gen(base_field(H)))
  E = base_field(H)

  @req codomain(res) === ambient_space(H) "f must be a map of restriction of scalars associated to the ambient space of H"
  @req degree(H) == rank(H) "Lattice must be of full rank"
  @req parent(beta) === E "beta must be an element of the base algebra of H"
  @req (beta == QQ(1) || norm(beta) == 1) "beta must be of norm 1"

  @req (degree(E) == 2) && (is_totally_complex(E)) && (is_totally_real(base_field(E))) "The base field of H must be CM"
  @req maximal_order(E) == equation_order(E) "Equation order and maximal order must coincide"

  Lres = restrict_scalars(H, res)
  iso = zero_matrix(QQ, 0, degree(Lres))
  v = vec(zeros(QQ, 1, degree(Lres)))

  for i in 1:degree(Lres)
    v[i] = one(QQ)
    v2 = res(v)
    v2 = beta.*v2
    v3 = (res\v2)
    iso = vcat(iso, transpose(matrix(v3)))
    v[i] = zero(QQ)
  end

  @hassert :Lattice 2 iso*gram_matrix(ambient_space(Lres))*transpose(iso) == gram_matrix(ambient_space(Lres))

  return Lres, iso
end

# If the minpoly of f is irreducible, return a basis of the QQ-vector space
# on which f acts such that, after extension of scalars to a vector space
# over the parent of b, the associated f-action is given by multiplication
# by b. This function requires f to be invertible, b to be have norm 1,
# b and f must have the same (absolute) minimal polynomial and the number
# of rows of f should be divisible by the absolute degree of the parent of b
function _admissible_basis(f::QQMatrix, b::NfRelElem; check::Bool = true)
  chi = absolute_minpoly(b)

  if check
    @assert norm(b) == 1
    chi_f = minpoly(parent(chi), f)
    @assert chi == chi_f
    @assert divides(ncols(f), degree(chi))[1]
  end

  m = divexact(ncols(f), degree(chi))
  _mb = absolute_representation_matrix(b)

  # we look for a basis on which f acts blockwise
  # as mutliplication by b along extension of scalars
  mb = block_diagonal_matrix([_mb for i in 1:m])
  bca = Hecke._basis_of_commutator_algebra(f, _mb)
  @assert !is_empty(bca)

  # l will be our new basis, it is made of several blocks,
  # m blocks to be exact.
  l = zero_matrix(QQ, 0, ncols(f))
  while rank(l) != ncols(f)
    _m = popfirst!(bca)
    _l = vcat(l, _m)
    if rank(_l) > rank(l)
      l = _l
    end
  end

  @assert det(l) != 0
  @assert l*f == mb*l
  return l
end

#TODO: add jldoctest
@doc raw"""
    hermitian_structure(L::ZLat, f::QQMatrix; check::Bool = true
                                              ambient_representation::Bool = true)
                                                                     -> HermLat

Given a $\mathbb{Z}$-lattice `L` together with an isometry `f` with irreducible minimal polynomial,
return the associated hermitian structure on `(L, f)`.

Note that `f` must be of infinite order or of order at least 3. In which case, the rank of the lattice `L`
should be divisible by the degree of the minimal polynomial of `f`.

If `L` is not of full rank, then the associated map of change of scalars is defined on the rational
span of `L` (see [`rational_span(::ZLat)`](@ref)), since only the action on the rational span of the lattice
matters for the trace equivalence. If `L` is of full rank, we use its ambient space as rational span since both
are isometric (see [`ambient_space(::ZLat)`](@ref))

If `ambient_representation` is set to true, then the isometry `f` is seen as an isometry of the ambient space of `L`.
If `check == true`, then the function checks whether the minimal polynomial of the action of `f` on the rational
span of `L` is irreducible.
"""
function hermitian_structure(L::ZLat, f::QQMatrix; check::Bool = true,
                                                   ambient_representation::Bool = true,
                                                   res = nothing,
                                                   E = nothing)

  return hermitian_structure_with_transfer_data(L, f, check=check,
                                                      ambient_representation = ambient_representation,
                                                      res = res,
                                                      E = E)[1]
end

# TODO: add jldoctest
@doc raw"""
    hermitian_structure_with_transfer_data(L::ZLat, f::QQMatrix; check::Bool = true,
                                                                 ambient_representation::Bool = true)
                                                                              -> HermLat, AbstractSpaceRes

Given a $\mathbb{Z}$-lattice `L` together with an isometry `f` with irreducible minimal polynomial,
return the associated hermitian structure on `(L, f)` together with the map of change of scalars.

Note that `f` must be of infinite order or of order at least 3. In which case, the rank of the lattice `L`
should be divisible by the degree of the minimal polynomial of `f`.

If `L` is not of full rank, then the associated map of change of scalars is defined on the rational
span of `L` (see [`rational_span(::ZLat)`](@ref)), since only the action on the rational span of the lattice
matters for the trace equivalence. If `L` is of full rank, we use its ambient space as rational span since both
are isometric (see [`ambient_space(::ZLat)`](@ref))

If `ambient_representation` is set to true, then the isometry `f` is seen as an isometry of the ambient space of `L`.
If `check == true`, then the function checks whether the minimal polynomial of the action of `f` on the rational
span of `L` is irreducible.
"""
function hermitian_structure_with_transfer_data(_L::ZLat, f::QQMatrix; check::Bool = true,
                                                                       ambient_representation::Bool = true,
                                                                       res = nothing,
                                                                       E = nothing)

  # Since the minimal polynomial of f might not be irreducible, but the one
  # of its restriction to _L is, we are only concerned about _L inside
  # its rational span. So if _L is not of full rank, we consider its
  # "full rank version". Otherwise, we keep it as is and consider f as
  # acting on the ambient space (which is isometric to the rational span of _L)
  if rank(_L) != degree(_L)
    L = Zlattice(gram = gram_matrix(_L))
    if ambient_representation
      ok, f = can_solve_with_solution(basis_matrix(_L), basis_matrix(_L)*f, side=:left)
      @req ok "Isometry does not restrict to L"
    end
  else
    L = _L
    if !ambient_representation
      B = basis_matrix(_L)
      f = inv(B)*f*B
    end
  end

  n = multiplicative_order(f)

  n2 = degree(minpoly(f))

  @req !is_finite(n) || n > 2 "Isometry must have infinite order or order bigger than 2"

  if check
    G = gram_matrix(ambient_space(L))
    @req is_irreducible(minpoly(f)) "The minimal polynomial of f must be irreducible"
    @req f*G*transpose(f) == G "f does not define an isometry of the space of L"
    @req divides(rank(L), n2)[1] "The degree of the minimal polynomial of f must divide the rank of L"
  end

  # for regular users, `res` and `E` will always be `nothing`
  if res !== nothing
    @assert domain(res) === ambient_space(L)
    b = gen(base_ring(codomain(res)))
  elseif E === nothing
    if is_finite(n)
      E, b = cyclotomic_field_as_cm_extension(n)
    else
      Etemp, btemp = number_field(minpoly(f))
      K, a = number_field(minpoly(btemp + inv(btemp)), "a", cached=false)
      Kt, t = K["t"]
      E, b = number_field(t^2-a*t+1, "b", cached=false)
    end
  else
    @req E isa NfRel "E must be a relative number field"
    @req (degree(E) == 2) && (is_totally_complex(E)) && (is_totally_real(base_field(E))) "E must be a CM-field"
    b = gen(E)
    chi = absolute_minpoly(b)
    R = parent(chi)
    @req minpoly(R, f) == chi "The absolute defining polynomial of E should be the same as the minimal polynomial of f"
  end

  m = divexact(rank(L), n2)
  _mb = absolute_representation_matrix(b)
  mb = block_diagonal_matrix([_mb for j in 1:m])

  # regular users should not have to care about this.
  # If res is specified and f is compatible, in the sense of
  # "_admissible_basis", then we transfer the lattice along this map
  if res !== nothing
    W = codomain(res)
    l = res.btop
    @assert l*f == mb*l
    BL = basis_matrix(L)
    gene = Vector{elem_type(base_ring(W))}[res(vec(collect(BL[i, :]))) for i in 1:degree(L)]
    Lh = lattice(W, gene)
    return Lh, res
  end

  # here we get an "admissible basis", i.e. a nice basis on which
  # f acts as multiplication by b after extending scalars
  l = _admissible_basis(f, b, check=false)

  # we construct the gram matrix of the hermitian space in which to extend the scalars.
  # For this we change the basis of the ambient space/rational span of L and
  # we use the transfer formula to revert the trace construction (this is
  # where we actually need a basis on which the isometry is given by mutliplication
  # by `b`.
  gram = matrix(zeros(E, m, m))
  s = involution(E)
  G = l*gram_matrix(ambient_space(L))*transpose(l)
  v = zero_matrix(QQ, 1, rank(L))
  bs = absolute_basis(E)
  trace_mat = zero_matrix(QQ, n2, n2)
  for i in 1:n2
    for j in 0:n2-1
      trace_mat[i, j+1] = trace(b^j*bs[i], QQ)
    end
  end

  for i=1:m
    for j=1:m
      vi = deepcopy(v)
      vi[1,1+(i-1)*euler_phi(n)] = one(QQ)
      vj = deepcopy(v)
      vj[1,1+(j-1)*euler_phi(n)] = one(QQ)
      a = matrix(QQ, 1, n2, [(vi*mb^k*G*transpose(vj))[1] for k in 0:n2-1])
      co = solve_left(trace_mat, a)
      gram[i,j] = (co*bs)[1]
    end
  end

  @assert transpose(map_entries(s, gram)) == gram

  W = hermitian_space(E, gram)

  # we create the map for extending/restricting scalars
  # considering our "nice" basis keeping track of the action of the isometry
  # on the ambient space. This will be needed for the hermitian Miranda-Morrison
  # theory.
  res = AbstractSpaceRes(ambient_space(L), W, l, identity_matrix(E, m))

  # once we have the map between the ambient spaces, it just remain to transfer
  # the lattice
  BL = basis_matrix(L)
  gene = Vector{elem_type(E)}[res(vec(collect(BL[i, :]))) for i in 1:degree(L)]

  Lh = lattice(W, gene)
  return Lh, res
end

################################################################################
#
#  Automorphism group
#
################################################################################

# Determine the gram matrices of the bilinear forms
# V x V -> Q, (x, y) -> Tr_K/Q(a*B(x, y))
# with respect to an absolute basis of L, for all a in generators.
function Zforms(L::AbstractLat{<: NumField}, generators)
  return _Zforms(L, generators)
end

function Zforms(L::AbstractLat{<: NumField})
  E = base_ring(ambient_space(L))
  if degree(E) > 1
    generators = elem_type(E)[E(1), absolute_primitive_element(E)]
  else
    generators = elem_type(E)[E(1)]
  end
  return _Zforms(L, generators)
end

function _Zforms(L::AbstractLat{<: NumField}, generators::Vector)
  V = ambient_space(L)
  E = base_ring(V)
  Babs = absolute_basis(L)
  Babsmat = matrix(E, Babs)
  forms = ZZMatrix[]
  scalars = QQFieldElem[]
  for b in generators
    Vres, VresToV = restrict_scalars(V, FlintQQ, b)
    G = gram_matrix(Vres, map(t -> preimage(VresToV, t), Babs))
    d = denominator(G)
    Gint = change_base_ring(FlintZZ, d * G)
    c = content(Gint)
    G = divexact(Gint, c)
    push!(forms, G)
    push!(scalars, d//c)
  end
  return forms, scalars, Babsmat, generators
end

# Compute the automorphism group of the lattice
# per default, the are given with respect to the basis of the ambient space
# if ambient_representation = true, they are given with respect to the coordinate
# space/ambient space
function assert_has_automorphisms(L::AbstractLat{<: NumField}; redo::Bool = false)

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

  # Create the automorphism context and compute generators as well as orders

  C = ZLatAutoCtx(ZgramL)
  fl, Csmall = try_init_small(C)
  if fl
    auto(Csmall)
    _gens, order = _get_generators(Csmall)
    gens = ZZMatrix[matrix(ZZ, g) for g in _gens]
  else
    init(C)
    auto(C)
    gens, order = _get_generators(C)
  end

  @hassert :Lattice 1 begin
    flag = true
    for g in gens
      gt = transpose(g)
      for i in 1:length(ZgramL)
        if g * ZgramL[i] * transpose(g) != ZgramL[i]
          flag = false
        end
      end
    end
    flag
  end

  # Now undo the LLL transformation
  Tinv = inv(T)
  for i in 1:length(gens)
    gens[i] = Tinv * gens[i] * T
  end

  # Now gens are with respect to the absolute basis of L
  @hassert :Lattice 1 begin
    flag = true
    for j in 1:length(ZgramL)
      for i in 1:length(gens)
        if gens[i] * ZgramLorig[j] * transpose(gens[i]) != ZgramLorig[j]
          flag = false
        end
      end
    end
    flag
  end

  # Now translate to get the automorphisms with respect to basis_matrix(L)
  BmatL = basis_matrix_of_rational_span(L)

  b1, s1 = can_solve_with_solution(BabsmatL, BmatL, side = :left)
  b2, s2 = can_solve_with_solution(BmatL, BabsmatL, side = :left)

  t_gens = Vector{typeof(BmatL)}(undef, length(gens))

  for i in 1:length(gens)
    t_gens[i] = s1 * change_base_ring(E, gens[i]) * s2
  end

  G = gram_matrix_of_rational_span(L)
  @hassert :Lattice 1 all(g * G * _map(transpose(g), involution(L)) == G
                            for g in t_gens)

  pm = pseudo_matrix(L)
  C = coefficient_ideals(pm)

  for g in t_gens
    @hassert :Lattice 1 all(g[i, j] in C[j] * inv(C[i])
                              for i in 1:nrows(g), j in 1:nrows(g))
  end

  # Now set the generators and the order

  L.automorphism_group_generators = t_gens
  L.automorphism_group_order = order
  return nothing
end

################################################################################
#
#  Automorphism group generators
#
################################################################################

@doc raw"""
    automorphism_group_generators(L::AbstractLat; ambient_representation::Bool = true)
                                                          -> Vector{MatElem}

Given a definite lattice `L`, return generators for the automorphism group of `L`.
If `ambient_representation == true` (the default), the transformations are represented
with respect to the ambient space of `L`. Otherwise, the transformations are represented
with respect to the (pseudo-)basis of `L`.
"""
automorphism_group_generators(L::AbstractLat; ambient_representation::Bool = true)

function automorphism_group_generators(L::AbstractLat; ambient_representation::Bool = true, check = false)

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
    bm = basis_matrix_of_rational_span(L)
    bminv = inv(bm)
    gens = typeof(bm)[bminv * g * bm for g in gens]
    @hassert :Lattice 1 begin
      flag = true
      Gamb = gram_matrix(ambient_space(L))
      for g in gens
        if g * Gamb * _map(transpose(g), involution(L)) != Gamb
          flag = false
        end
      end
      flag
    end
    return gens
  end
end

################################################################################
#
#  Automorphism group order
#
################################################################################

@doc raw"""
    automorphism_group_order(L::AbstractLat) -> Int

Given a definite lattice `L`, return the order of the automorphism group of `L`.
"""
automorphism_group_order(L::AbstractLat; redo::Bool = false)

function automorphism_group_order(L::AbstractLat; redo::Bool = false)
  assert_has_automorphisms(L, redo = redo)
  return L.automorphism_group_order
end

################################################################################
#
#  Isometry
#
################################################################################

@doc raw"""
    is_isometric(L::AbstractLat, M::AbstractLat) -> Bool

Return whether the lattices `L` and `M` are isometric.
"""
is_isometric(L::AbstractLat, M::AbstractLat) = is_isometric_with_isometry(L, M, ambient_representation=false)[1]


@doc raw"""
    is_isometric_with_isometry(L::AbstractLat, M::AbstractLat; ambient_representation::Bool = true)
                                                              -> (Bool, MatElem)

Return whether the lattices `L` and `M` are isometric. If this is the case, the
second returned value is an isometry `T` from `L` to `M`.

By default, that isometry is represented with respect to the bases of the
ambient spaces, that is, $T V_M T^t = V_L$ where $V_L$ and $V_M$ are the Gram
matrices of the ambient spaces of `L` and `M` respectively. If
`ambient_representation == false`, then the isometry is represented with respect
to the (pseudo-)bases of `L` and `M`, that is, $T G_M T^t = G_L$ where $G_M$
and $G_L$ are the Gram matrices of the (pseudo-)bases of `L` and `M`
respectively.
"""
is_isometric_with_isometry(L::AbstractLat, M::AbstractLat; ambient_representation::Bool = true) = throw(NotImplemented())


function is_isometric_with_isometry(L::AbstractLat{<: NumField}, M::AbstractLat{<: NumField};
                                            ambient_representation::Bool = true)
  V = ambient_space(L)
  W = ambient_space(M)
  E = base_ring(V)
  K = base_field(E)
  @assert base_ring(V) == base_ring(W)
  @assert base_ring(L) == base_ring(M)

  ZgramL, scalarsL, BabsmatL, generatorsL = Zforms(L)
  ZgramM, scalarsM, BabsmatM, generatorsM = Zforms(M, generatorsL)
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

  fl, CLsmall, CMsmall = _try_iso_setup_small(ZgramLsmall, ZgramMsmall)
  if fl
    b, _T = isometry(CLsmall, CMsmall)
    T = matrix(FlintZZ, _T)
  else
    CL, CM = _iso_setup(ZgramLsmall, ZgramMsmall)
    b, T = isometry(CL, CM)
  end

  if b
    T = change_base_ring(FlintQQ, inv(TL)*T*TM)
    fl, s1 = can_solve_with_solution(BabsmatL, basis_matrix_of_rational_span(L), side = :left)
    fl, s2 = can_solve_with_solution(basis_matrix_of_rational_span(M), BabsmatM, side = :left)
    T = s1 * change_base_ring(E, T) * s2
    @hassert :Lattice 1 T * gram_matrix(rational_span(M)) *
                            _map(transpose(T), involution(L)) ==
                                gram_matrix(rational_span(L))
    if !ambient_representation
      return true, T
    else
      T = inv(basis_matrix_of_rational_span(L)) * T *
                 basis_matrix_of_rational_span(M)

      @hassert :Lattice 1 T * gram_matrix(ambient_space(M)) *
                              _map(transpose(T), involution(L)) ==
                                  gram_matrix(ambient_space(L))
      return true, T
    end
  else
    return false, zero_matrix(E, 0, 0)
  end
end

################################################################################
#
#  Maximal sublattices
#
################################################################################

function maximal_sublattices(L::AbstractLat, p; use_auto::Bool = false,
                                           callback = false, max = inf)
  @req base_ring(L) == order(p) "Incompatible arguments: p must be an ideal in the base ring of L"

  B = local_basis_matrix(L, p, type = :submodule)
  full_rank = rank(matrix(L.pmat)) == Hecke.max(nrows(L.pmat), ncols(L.pmat))
  n = nrows(B)
  R = base_ring(L)
  K = nf(R)
  k, h = residue_field(R, p)
  hext = extend(h, K)
  use_auto = (is_definite(L) && full_rank) ? use_auto : false

  if use_auto
    G = automorphism_group_generators(L)
    Binv = inv(B)
    adjust_gens = [transpose(B*g*Binv) for g in G]
    adjust_gens_mod_p = [map_entries(hext, g) for g in adjust_gens]
    adjust_gens_mod_p = [g for g in adjust_gens_mod_p if !is_diagonal(g)]
    use_auto = length(adjust_gens_mod_p) >= 1
  end

  if use_auto
    Ls = line_orbits(adjust_gens_mod_p)
  else
    Ls = maximal_subspaces(k, n)
  end

  pML = p * pseudo_matrix(L)
  result = typeof(L)[]
  keep = true
  cont = true
  E = Int[]
  for i in 1:length(Ls)
    if use_auto
      m = map_entries(y -> hext\y, (kernel(matrix(Ls[i][1]), side = :left)[2]))
    else
      m = map_entries(y -> hext\y, Ls[i])
    end
    LL = lattice(ambient_space(L), _sum_modules(L, pseudo_matrix(m * B), pML))
    if !(callback isa Bool)
      keep, cont = callback(result, LL)::Tuple{Bool, Bool}
    end
    if keep
      push!(result, LL)
      push!(E, use_auto ? Ls[i][2] : 1)
    end
    if !cont
      break
    end
    if length(result) >= max
      break
    end
  end
  return result, E
end

################################################################################
#
#  Minimal superlattices
#
################################################################################

function minimal_superlattices(L::AbstractLat, p; use_auto::Bool = false,
                                             callback = false, max = inf)
  @req base_ring(L) == order(p) "Incompatible arguments: p must be an ideal in the base ring of L"

  B = local_basis_matrix(L, p, type = :submodule)
  full_rank = rank(matrix(L.pmat)) == Hecke.max(nrows(L.pmat), ncols(L.pmat))
  n = nrows(B)
  R = base_ring(L)
  K = nf(R)
  k, h = residue_field(R, p)
  hext = extend(h, K)
  use_auto = (is_definite(L) && full_rank) ? use_auto : false

  if use_auto
    G = automorphism_group_generators(L)
    Binv = inv(B)
    adjust_gens = [B*g*Binv for g in G]
    adjust_gens_mod_p = [map_entries(hext, g) for g in adjust_gens]
    adjust_gens_mod_p = [g for g in adjust_gens_mod_p if !is_diagonal(g)]
    use_auto = length(adjust_gens_mod_p) >= 1
  end

  if use_auto
    Ls = line_orbits(adjust_gens_mod_p)
  else
    Ls = enumerate_lines(k, n)
  end

  pinv = inv(p)
  ML = pseudo_matrix(L)
  result = typeof(L)[]
  keep = true
  cont = true
  E = Int[]
  for v in Ls
    l = use_auto ? transpose(matrix(v[1])) : transpose(matrix(v))
    m = map_entries(y -> hext\y, l)
    ppm = pseudo_matrix(m*B, [pinv])
    LL = lattice(ambient_space(L), _sum_modules(L, ML, ppm))
    if !(callback isa Bool)
      keep, cont = callback(result, LL)
    end
    if keep
      push!(result, LL)
      push!(E, use_auto ? v[2] : 1)
    end
    if !cont
      break
    end
    if length(result) >= max
      break
    end
  end
  return result, E
end

################################################################################
#
#  Direct sums/direct products/biproducts
#
################################################################################

@doc raw"""
    direct_sum(x::Vararg{T}) where T <: AbstractLat -> T, Vector{AbstractSpaceMor}
    direct_sum(x::Vector{T}) where T <: AbstractLat -> T, Vector{AbstractSpaceMor}

Given a collection of quadratic or hermitian lattices $L_1, \ldots, L_n$,
return their direct sum $L := L_1 \oplus \ldots \oplus L_n$, together with
the injections $L_i \to L$ (seen as maps between the corresponding ambient spaces).

For objects of type `AbstractLat`, finite direct sums and finite direct
products agree and they are therefore called biproducts.
If one wants to obtain `L` as a direct product with the projections $L \to L_i$,
one should call `direct_product(x)`.
If one wants to obtain `L` as a biproduct with the injections $L_i \to L$ and the
projections $L \to L_i$, one should call `biproduct(x)`.
"""
function direct_sum(x::Vector{T}) where T <: AbstractLat
  @req length(x) >= 2 "Input must consist of at least two lattices"
  W, inj = direct_sum(ambient_space.(x))
  H = _biproduct(x)
  return lattice(W, H), inj
end

direct_sum(x::Vararg{AbstractLat}) = direct_sum(collect(x))

@doc raw"""
    direct_product(x::Vararg{T}) where T <: AbstractLat -> T, Vector{AbstractSpaceMor}
    direct_product(x::Vector{T}) where T <: AbstractLat -> T, Vector{AbstractSpaceMor}

Given a collection of quadratic or hermitian lattices $L_1, \ldots, L_n$,
return their direct product $L := L_1 \times \ldots \times L_n$, together with
the projections $L \to L_i$ (seen as maps between the corresponding ambient spaces).

For objects of type `AbstractLat`, finite direct sums and finite direct
products agree and they are therefore called biproducts.
If one wants to obtain `L` as a direct sum with the injections $L_i \to L$,
one should call `direct_sum(x)`.
If one wants to obtain `L` as a biproduct with the injections $L_i \to L$ and the
projections $L \to L_i$, one should call `biproduct(x)`.
"""
function direct_product(x::Vector{T}) where T <: AbstractLat
  @req length(x) >= 2 "Input must consist of at least two lattices"
  W, proj = direct_product(ambient_space.(x))
  H = _biproduct(x)
  return lattice(W, H), proj
end

direct_product(x::Vararg{AbstractLat}) = direct_product(collect(x))

@doc raw"""
    biproduct(x::Vararg{T}) where T <: AbstractLat -> T, Vector{AbstractSpaceMor}, Vector{AbstractSpaceMor}
    biproduct(x::Vector{T}) where T <: AbstractLat -> T, Vector{AbstractSpaceMor}, Vector{AbstractSpaceMor}

Given a collection of quadratic or hermitian lattices $L_1, \ldots, L_n$,
return their biproduct $L := L_1 \oplus \ldots \oplus L_n$, together with
the injections $L_i \toL$ and the projections $L \to L_i$ (seen as maps
between the corresponding ambient spaces).

For objects of type `AbstractLat`, finite direct sums and finite direct
products agree and they are therefore called biproducts.
If one wants to obtain `L` as a direct sum with the injections $L_i \to L$,
one should call `direct_sum(x)`.
If one wants to obtain `L` as a direct product with the projections $L \to L_i$,
one should call `direct_product(x)`.
"""
function biproduct(x::Vector{T}) where T <: AbstractLat
  @req length(x) >= 2 "Input must consist of at least two lattices"
  W, inj, proj = biproduct(ambient_space.(x))
  H = _biproduct(x)
  return lattice(W, H), inj, proj
end

biproduct(x::Vararg{AbstractLat}) = biproduct(collect(x))

function _biproduct(x::Vector{T}) where T <: AbstractLat
  px = pseudo_matrix.(x)
  Mpx = matrix.(px)
  H = pseudo_matrix(diagonal_matrix(Mpx),
                    reduce(vcat, coefficient_ideals.(px)))
  return H
end

################################################################################
#
#  Orthogonal complement
#
################################################################################

@doc raw"""
    orthogonal_submodule(L::AbstractLat, M::AbstractLat) -> AbstractLat

Return the largest submodule of `L` orthogonal to `M`.
"""
function orthogonal_submodule(L::AbstractLat, M::AbstractLat)
  @req ambient_space(M) == ambient_space(L) "Lattices must be in the same ambient space"
  V = ambient_space(L)
  EM = basis_matrix_of_rational_span(M)
  Morth = orthogonal_complement(V, EM)
  N = lattice(V, Morth)
  N = intersect(L, N)
  return primitive_closure(L, N)
end

# does not seem to work either
function _orthogonal_complement(v::Vector, L::AbstractLat)
  V = ambient_space(L)
  M = matrix(base_ring(V), 1, length(v), v)
  ge = generators(L)
  ge_or = copy(ge)
    for i in 1:length(ge)
    # <v, v> = 1
    ge_or[i] = ge[i] - inner_product(V, ge[i], v) .* v
    @assert inner_product(V, ge_or[i], v) == 0
  end
  pm = pseudo_hnf_kb(pseudo_matrix(transpose(matrix(ge_or))), :lowerleft)
  i = 1
  while is_zero_row(pm.matrix, i)
    i += 1
  end

  pm = sub(pm, i:nrows(pm), 1:ncols(pm))

  return lattice(V, pm)
end

################################################################################
#
#  Maximal integral lattices
#
################################################################################

@doc raw"""
    is_maximal_integral(L::AbstractLat, p::NfOrdIdl) -> Bool, AbstractLat

Given a lattice `L` and a prime ideal `p` of the fixed ring $\mathcal O_K$ of
`L`, return whether the completion of `L` at `p` is maximal integral. If it is
not the case, the second returned value is a lattice in the ambient space of `L`
whose completion at `p` is a minimal overlattice of $L_p$.
"""
is_maximal_integral(::AbstractLat, p)

@doc raw"""
    is_maximal_integral(L::AbstractLat) -> Bool, AbstractLat

Given a lattice `L`, return whether `L` is maximal integral. If it is not,
the second returned value is a minimal overlattice of `L` with integral norm.
"""
is_maximal_integral(::AbstractLat)

@doc raw"""
    is_maximal(L::AbstractLat, p::NfOrdIdl) -> Bool, AbstractLat

Given a lattice `L` and a prime ideal `p` in the fixed ring $\mathcal O_K$ of
`L`, check whether the norm of $L_p$ is integral and return whether `L` is maximal
at `p`. If it is locally integral but not locally maximal, the second returned value
is a lattice in the same ambient space of `L` whose completion at `p` has integral norm
and is a proper overlattice of $L_p$.
"""
is_maximal(::AbstractLat, p)

@doc raw"""
    maximal_integral_lattice(L::AbstractLat, p::NfOrdIdl) -> AbstractLat

Given a lattice `L` and a prime ideal `p` of the fixed ring $\mathcal O_K$ of
`L`, return a lattice `M` in the ambient space of `L` which is maximal integral
at `p` and which agrees with `L` locally at all the places different from `p`.
"""
maximal_integral_lattice(::AbstractLat, p)

@doc raw"""
    maximal_integral_lattice(L::AbstractLat) -> AbstractLat

Given a lattice `L`, return a lattice `M` in the ambient space of `L` which
is maximal integral and which contains `L`.
"""
maximal_integral_lattice(::AbstractLat)

@doc raw"""
    maximal_integral_lattice(V::AbstractSpace) -> AbstractLat

Given a space `V`, return a lattice in `V` with integral norm
and which is maximal in `V` satisfying this property.
"""
maximal_integral_lattice(::AbstractSpace)

################################################################################
#
#  Primitive closure
#
################################################################################

@doc raw"""
    primitive_closure(M::AbstractLat, N::AbstractLat) -> AbstractLat

Given two lattices `M` and `N` defined over a number field `E`, with
$N \subseteq E\otimes M$, return the primitive closure $M \cap E\otimes N$
of `N` in `M`.

One can also use the alias `saturate(L, M)`.
"""
function primitive_closure(M::AbstractLat, N::AbstractLat)
  @assert has_ambient_space(N) && has_ambient_space(M)
  @req ambient_space(N) === ambient_space(M) "Lattices must be in the same ambient space"
  Mres, f = restrict_scalars_with_map(M, FlintQQ)
  Nres = restrict_scalars(N, f)
  Lres = primitive_closure(Mres, Nres)
  B = basis_matrix(Lres)
  B2 = [f(vec(collect(B[i,:]))) for i in 1:nrows(B)]
  return lattice(ambient_space(M), B2)
end

@doc raw"""
    saturate(L::AbstractLat, M::AbstractLat) -> AbstractLat

Alias for `primitive_closure`.
"""
saturate(L::AbstractLat, M::AbstractLat) = primitive_closure(L::AbstractLat, M::AbstractLat)
