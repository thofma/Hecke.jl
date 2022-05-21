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
       rank, rational_span, rescale, scale, volume, witt_invariant, Zlattice
      

export HermLat, QuadLat

# aliases for deprecation
is_equivalent(U::AbsLat, V::AbsLat) = is_isometric(U, V)
is_equivalent(U::AbsLat, V::AbsLat, p) = is_isometric(U, V, p)
is_rationally_equivalent(U::AbsLat, V::AbsLat) = is_rationally_isometric(U, V)
is_rationally_equivalent(U::AbsLat, V::AbsLat, p) = is_rationally_isometric(U, V, p)
is_equivalent(U::AbsSpace, V::AbsSpace) = is_isometric(U, V)
is_equivalent(U::AbsSpace, V::AbsSpace, p) = is_isometric(U, V, p)
is_equivalent_with_isometry(U::AbsLat, V::AbsLat) = is_isometric_with_isometry(U, V)
is_equivalent_with_isometry(U::AbsSpace, V::AbsSpace) = is_isometric_with_isometry(U, V)

################################################################################
#
#  Verbose and assert scopes
#
################################################################################

add_verbose_scope(:Lattice)

add_assert_scope(:Lattice)

################################################################################
#
#  Ambient space
#
################################################################################

@doc Markdown.doc"""
    has_ambient_space(L::AbsLat) -> Bool

Return whether the ambient space of the lattice `L` is set.
"""
function has_ambient_space(L::AbsLat)
  return isdefined(L, :space)
end

@doc Markdown.doc"""
    ambient_space(L::AbsLat) -> AbsSpace

Return the ambient space of the lattice `L`. If the ambient space is not known, an
error is raised.
"""
function ambient_space(L::AbsLat)
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

@doc Markdown.doc"""
    rational_span(L::AbsLat) -> AbsSpace

Return the rational span of the lattice `L`.
"""
rational_span(::AbsLat)

################################################################################
#
#  Diagonal
#
################################################################################

@doc Markdown.doc"""
    diagonal_of_rational_span(L::AbsLat) -> Vector

Return the diagonal of the rational span of the lattice `L`.
"""
function diagonal_of_rational_span(L::AbsLat)
  D, _ = _gram_schmidt(gram_matrix_of_rational_span(L), involution(L))
  return diagonal(D)
end

################################################################################
#
#  Module properties
#
################################################################################

@doc Markdown.doc"""
    pseudo_matrix(L::AbsLat) -> PMat

Return a basis pseudo-matrix of the lattice `L`.
"""
pseudo_matrix(L::AbsLat) = L.pmat

@doc Markdown.doc"""
    pseudo_basis(L::AbsLat) -> Vector{Tuple{Vector, Ideal}}

Return a pseudo-basis of the lattice `L`.
"""
function pseudo_basis(L::AbsLat)
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

@doc Markdown.doc"""
    coefficient_ideals(L::AbsLat) -> Vector{NfOrdIdl}

Return the coefficient ideals of a pseudo-basis of the lattice `L`.
"""
coefficient_ideals(L::AbsLat) = coefficient_ideals(pseudo_matrix(L))

@doc Markdown.doc"""
    basis_matrix_of_rational_span(L::AbsLat) -> MatElem

Return a basis matrix of the rational span of the lattice `L`.
"""
basis_matrix_of_rational_span(L::AbsLat) = matrix(pseudo_matrix(L))

@doc Markdown.doc"""
    base_field(L::AbsLat) -> Field

Return the algebra over which the rational span of the lattice `L` is defined.
"""
base_field(L::AbsLat) = L.base_algebra

@doc Markdown.doc"""
    base_ring(L::AbsLat) -> Ring

Return the order over which the lattice `L` is defined.
"""
base_ring(L::AbsLat) = base_ring(L.pmat)

@doc Markdown.doc"""
    fixed_field(L::AbsLat) -> Field

Returns the fixed field of the involution of the lattice `L`.
"""
fixed_field(L::AbsLat) = fixed_field(rational_span(L))

@doc Markdown.doc"""
    fixed_ring(L::AbsLat) -> Ring

Return the maximal order in the fixed field of the lattice `L`.
"""
fixed_ring(L::AbsLat) = maximal_order(fixed_field(L))

@doc Markdown.doc"""
    involution(L::AbsLat) -> Map

Return the involution of the rational span of the lattice `L`.
"""
involution(::AbsLat)

@doc Markdown.doc"""
    rank(L::AbsLat) -> Int

Return the rank of the underlying module of the lattice `L`.
"""
rank(L::AbsLat) = dim(rational_span(L))

@doc Markdown.doc"""
    degree(L::AbsLat) -> Int

Return the dimension of the ambient space of the lattice `L`.
"""
function degree(L::AbsLat)
  if isdefined(L, :space) 
    return dim(L.space)
  else
    return ncols(L.pmat.matrix)
  end
end

@doc Markdown.doc"""
    is_sublattice(L::AbsLat, M::AbsLat) -> Bool

Return whether `M` is a sublattice of the lattice `L`.
"""
function is_sublattice(L::AbsLat, M::AbsLat)
  if L === M
    return true
  end

  if ambient_space(L) != ambient_space(M)
    return false
  end

  return _spans_subset_of_pseudohnf(pseudo_matrix(M), _pseudo_hnf(L), :lowerleft)
end

@doc Markdown.doc"""
    issubset(M::AbsLat, L::AbsLat) -> Bool

Return whether `M` is a subset of the lattice `L`.
"""
Base.issubset(M::AbsLat, L::AbsLat) = is_sublattice(L, M)

################################################################################
#
#  Pseudo-HNF
#
################################################################################

# Return a lowerleft pseudo hnf
function _pseudo_hnf(L::AbsLat)
  get_attribute!(L, :pseudo_hnf) do
    pseudo_hnf(pseudo_matrix(L), :lowerleft)
  end::typeof(L.pmat)
end

################################################################################
#
#  Equality
#
################################################################################

function Base.:(==)(L::AbsLat, M::AbsLat)
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

@doc Markdown.doc"""
    gram_matrix_of_rational_span(L::AbsLat) -> MatElem

Return the Gram matrix of the rational span of the lattice `L`.
"""
function gram_matrix_of_rational_span(L::AbsLat)
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

@doc Markdown.doc"""
    generators(L::AbsLat; minimal = false) -> Vector{Vector}

Return a set of generators of the lattice `L` over the base ring of `L`.

If `minimal == true`, the number of generators is minimal. Note that computing
minimal generators is expensive.
"""
function generators(L::AbsLat; minimal::Bool = false)
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

@doc Markdown.doc"""
    lattice(V::AbsSpace, B::PMat ; check::Bool = true) -> AbsLat

Given an ambient space `V` and a pseudo-matrix `B`, return the lattice spanned
by the pseudo-matrix `B` inside `V`. If `V` is hermitian (resp. quadratic) then
the output is a hermitian (resp. quadratic) lattice.

By default, `B` is checked to be of full rank. This test can be disabled by setting
`check` to false.
"""
lattice(V::AbsSpace, B::PMat ; check::Bool = true)

@doc Markdown.doc"""
    lattice(V::AbsSpace, basis::MatElem ; check::Bool = true) -> AbsLat

Given an ambient space `V` and a matrix `basis`, return the lattice spanned
by the rows of `basis` inside `V`. If `V` is hermitian (resp. quadratic) then
the output is a hermitian (resp. quadratic) lattice.

By default, `basis` is checked to be of full rank. This test can be disabled by setting
`check` to false.
"""
lattice(V::AbsSpace, basis::MatElem ; check::Bool = true) = lattice(V, pseudo_matrix(basis), check = check)

@doc Markdown.doc"""
    lattice(V::AbsSpace, gens::Vector) -> AbsLat

Given an ambient space `V` and a list of generators `gens`, return the lattice
spanned by `gens` in `V`. If `V` is hermitian (resp. quadratic) then the output
is a hermitian (resp. quadratic) lattice.

If `gens` is empty, the function returns the zero lattice in `V`.
"""
function lattice(V::Hecke.AbsSpace, gens::Vector)
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

@doc Markdown.doc"""
    lattice(V::AbsSpace) -> AbsLat

Given an ambient space `V`, return the lattice with the standard basis
matrix. If `V` is hermitian (resp. quadratic) then the output is a hermitian
(resp. quadratic) lattice.
"""
lattice(V::AbsSpace) = lattice(V, identity_matrix(base_ring(V), rank(V)), check = false)

################################################################################
#
#  Gram matrix of generators
#
################################################################################

@doc Markdown.doc"""
    gram_matrix_of_generators(L::AbsLat; minimal::Bool = false) -> MatElem

Return the Gram matrix of a generating set of the lattice `L`.

If `minimal == true`, then a minimal generating set is used. Note that computing
minimal generators is expensive.
"""
function gram_matrix_of_generators(L::AbsLat; minimal::Bool = false)
  m = generators(L, minimal = minimal)
  M = matrix(nf(base_ring(L)), m)
  return gram_matrix(ambient_space(L), M)
end

################################################################################
#
#  Discriminant
#
################################################################################

@doc Markdown.doc"""
    discriminant(L::AbsLat) -> NfOrdFracIdl

Return the discriminant of the lattice `L`, that is, the generalized index ideal
$[L^\# : L]$.
"""
function discriminant(L::AbsLat)
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

@doc Markdown.doc"""
    hasse_invariant(L::AbsLat, p::Union{InfPlc, NfOrdIdl}) -> Int

Return the Hasse invariant of the rational span of the lattice `L` at the place `p`.
The lattice must be quadratic.
"""
hasse_invariant(L::AbsLat, p)

@doc Markdown.doc"""
    witt_invariant(L::AbsLat, p::Union{InfPlc, NfOrdIdl}) -> Int

Return the Witt invariant of the rational span of the lattice `L` at the place `p`.
The lattice must be quadratic.
"""
witt_invariant(L::AbsLat, p)

################################################################################
#
#  Rational isometry
#
################################################################################

@doc Markdown.doc"""
    is_rationally_isometric(L::AbsLat, M::AbsLat, p::Union{InfPlc, NfAbsOrdIdl})
                                                                         -> Bool

Return whether the rational spans of the lattices `L` and `M` are isometric over
the completion at the place `p`.
"""
is_rationally_isometric(::AbsLat, ::AbsLat, ::NfAbsOrdIdl)

function is_rationally_isometric(L::AbsLat, M::AbsLat, p::NfAbsOrdIdl)
  return is_isometric(rational_span(L), rational_span(M), p)
end

function is_rationally_isometric(L::AbsLat, M::AbsLat, p::InfPlc)
  return is_isometric(rational_span(L), rational_span(M), p)
end

@doc Markdown.doc"""
    is_rationally_isometric(L::AbsLat, M::AbsLat) -> Bool

Return whether the rational spans of the lattices `L` and `M` are isometric.
"""
function is_rationally_isometric(L::AbsLat, M::AbsLat)
  return is_isometric(rational_span(L), rational_span(M))
end

################################################################################
#
#  Definiteness
#
################################################################################

@doc Markdown.doc"""
    is_positive_definite(L::AbsLat) -> Bool

Return whether the rational span of the lattice `L` is positive definite.
"""
is_positive_definite(L::AbsLat) = is_positive_definite(rational_span(L))

@doc Markdown.doc"""
    is_negative_definite(L::AbsLat) -> Bool

Return whether the rational span of the lattice `L` is negative definite.
"""
is_negative_definite(L::AbsLat) = is_negative_definite(rational_span(L))

@doc Markdown.doc"""
    is_definite(L::AbsLat) -> Bool

Return whether the rational span of the lattice `L` is definite.
"""
is_definite(L::AbsLat) = is_definite(rational_span(L))

@doc Markdown.doc"""
    can_scale_totally_positive(L::AbsLat) -> Bool, NumFieldElem

Return whether there is a totally positive rescaled lattice of the lattice `L`.
If so, the second returned value is an element $a$ such that $L^a$ is totally positive.
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

Return the sum of the lattices `L` and `M`.

The lattices `L` and `M` must have the same ambient space.
"""
Base.:(+)(::AbsLat, ::AbsLat)

function Base.:(+)(L::T, M::T) where {T <: AbsLat}
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

@doc Markdown.doc"""
    intersect(L::AbsLat, M::AbsLat) -> AbsLat

Return the intersection of the lattices `L` and `M`.

The lattices `L` and `M` must have the same ambient space.
"""
intersect(::AbsLat, ::AbsLat)

function intersect(L::T, M::T) where {T <: AbsLat}
  @assert has_ambient_space(L) && has_ambient_space(M)
  @assert ambient_space(L) === ambient_space(M)
  V = ambient_space(L)
  fr = nrows(pseudo_matrix(L)) == dim(V) || nrows(pseudo_matrix(M)) == dim(V)
  if !fr
    error("Only implemented for lattices of full rank")
  end
  m = _intersect_modules(L, pseudo_matrix(L), pseudo_matrix(M), fr)
  return lattice_in_same_ambient_space(L, m)
end

################################################################################
#
#  Scalar multiplication
#
################################################################################

@doc Markdown.doc"""
    *(a::NumFieldElem, L::AbsLat) -> AbsLat

Return the lattice $aL$ inside the ambient space of the lattice `L`.
"""
function Base.:(*)(a::NumFieldElem, L::AbsLat)
  @assert has_ambient_space(L)
  O = maximal_order(parent(a))
  m = _module_scale_ideal(a*O, pseudo_matrix(L))
  return lattice_in_same_ambient_space(L, m)
end

function Base.:(*)(L::QuadLat, a)
  return a * L
end

@doc Markdown.doc"""
    *(a::NumFieldOrdIdl, L::AbsLat) -> AbsLat

Return the lattice $aL$ inside the ambient space of the lattice `L`.
"""
Base.:(*)(::NumFieldOrdIdl, ::AbsLat)

function Base.:(*)(a::Union{NfRelOrdIdl, NfAbsOrdIdl}, L::AbsLat)
  @assert has_ambient_space(L)
  m = _module_scale_ideal(a, pseudo_matrix(L))
  return lattice_in_same_ambient_space(L, m)
end

@doc Markdown.doc"""
    *(a::NumFieldOrdFracIdl, L::AbsLat) -> AbsLat

Return the lattice $aL$ inside the ambient space of the lattice `L`.
"""
Base.:(*)(::NumFieldOrdFracIdl, ::AbsLat)

function Base.:(*)(a::Union{NfRelOrdFracIdl, NfAbsOrdFracIdl}, L::AbsLat)
  @assert has_ambient_space(L)
  m = _module_scale_ideal(a, pseudo_matrix(L))
  return lattice_in_same_ambient_space(L, m)
end

################################################################################
#
#  Absolute basis
#
################################################################################

@doc Markdown.doc"""
    absolute_basis(L::AbsLat) -> Vector

Return a $\mathbf{Z}$-basis of the lattice `L`.
"""
function absolute_basis(L::AbsLat)
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

@doc Markdown.doc"""
    absolute_basis_matrix(L::AbsLat) -> MatElem

Return a $\mathbf{Z}$-basis matrix of the lattice `L`.
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

@doc Markdown.doc"""
    norm(L::AbsLat) -> NfOrdFracIdl

Return the norm of the lattice `L`. This is a fractional ideal of the fixed field
of `L`.
"""
norm(::AbsLat)

################################################################################
#
#  Scale
#
################################################################################

@doc Markdown.doc"""
    scale(L::AbsLat) -> NfOrdFracIdl

Return the scale of the lattice `L`.
"""
scale(L::AbsLat)

################################################################################
#
#  Rescale
#
################################################################################

@doc Markdown.doc"""
    rescale(L::AbsLat, a::NumFieldElem) -> AbsLat

Return the rescaled lattice $L^a$. Note that this has a different ambient
space than the lattice `L`.
"""
rescale(::AbsLat, ::NumFieldElem)

Base.:(^)(L::AbsLat, a::RingElement) = rescale(L, a)

################################################################################
#
#  Is integral
#
################################################################################

@doc Markdown.doc"""
    is_integral(L::AbsLat) -> Bool

Return whether the lattice `L` is integral.
"""
function is_integral(L::AbsLat)
  return is_integral(scale(L))
end

################################################################################
#
#  Dual lattice
#
################################################################################

@doc Markdown.doc"""
    dual(L::AbsLat) -> AbsLat

Return the dual lattice of the lattice `L`.
"""
dual(::AbsLat)

################################################################################
#
#  Volume
#
################################################################################

@doc Markdown.doc"""
    volume(L::AbsLat) -> NfOrdFracIdl

Return the volume of the lattice `L`.
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
    is_modular(L::AbsLat) -> Bool, NfOrdFracIdl

Return whether the lattice `L` is modular. In this case, the second returned value
is a fractional ideal $\mathfrak a$ of the base algebra of `L` such that
$\mathfrak a L^\# = L$, where $L^\#$ is the dual of `L`.
"""
function is_modular(L::AbsLat)
  a = scale(L)
  if volume(L) == a^rank(L)
    return true, a
  else
    return false, a
  end
end

@doc Markdown.doc"""
    is_modular(L::AbsLat, p::NfOrdIdl) -> Bool, Int

Return whether the completion $L_{p}$ of the lattice `L` at the prime ideal `p`
is modular. If it is the case the second returned value is an integer `v` such
that $L_{p}$ is $p^v$-modular.
"""
is_modular(::AbsLat, p)

function is_modular(L::AbsLat{<: NumField}, p)
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

@doc Markdown.doc"""
    local_basis_matrix(L::AbsLat, p::NfOrdIdl; type = :any) -> MatElem

Given a prime ideal `p` and a lattice `L`, return a basis matrix of a lattice
`M` such that $M_{p} = L_{p}$. Note that if `p` is an ideal in the base ring of
`L`, the completions are taken at the minimum of `p` (which is an ideal in the
base ring of the order of `p`).

- If `type == :submodule`, the lattice `L` will be a sublattice of `M`.
- If `type == :supermodule`, the lattice `L` will be a superlattice of `M`.
- If `type == :any`, there may not be any containment relation between `M` and
  `L`.
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

@doc Markdown.doc"""
    jordan_decomposition(L::AbsLat, p::NfOrdIdl)
                                -> Vector{MatElem}, Vector{MatElem}, Vector{Int}

Return a Jordan decomposition of the completion of the lattice `L` at a prime
ideal `p`.

The returned value consists of three lists $(M_i)_i$, $(G_i)_i$ and $(s_i)_i$ of
the same length $r$. The completions of the row spans of the matrices $M_i$
yield a Jordan decomposition of $L_{p}$ into modular sublattices
$L_i$ with Gram matrices $G_i$ and scale of $p$-adic valuation $s_i$.
"""
jordan_decomposition(L::AbsLat, p::NfOrdIdl)

################################################################################
#
#  Local isometry
#
################################################################################

@doc Markdown.doc"""
    is_locally_isometric(L::AbsLat, M::AbsLat, p::NfOrdIdl) -> Bool

Return whether the completions of the lattices `L` and `M` at the prime ideal
`p` are isometric.
"""
is_locally_isometric(::AbsLat, ::AbsLat, ::NfOrdIdl)

################################################################################
#
#  Isotropy
#
################################################################################

@doc Markdown.doc"""
    is_isotropic(L::AbsLat, p::Union{NfOrdIdl, InfPlc}) -> Bool

Return whether the completion of the lattice `L` at the place `p` is
isotropic.
"""
is_isotropic(L::AbsLat, p) = is_isotropic(rational_span(L), p)

################################################################################
#
#  Restrict scalars
#
################################################################################

function restrict_scalars(L::AbsLat)
  V = ambient_space(L)
  Vabs, f = restrict_scalars(V, FlintQQ)
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
#  Automorphism group
#
################################################################################

# Determine the gram matrices of the bilinear forms
# V x V -> Q, (x, y) -> Tr_K/Q(a*B(x, y))
# with respect to an absolute basis of L, for all a in generators.
function Zforms(L::AbsLat{<: NumField}, generators)
  return _Zforms(L, generators)
end

function Zforms(L::AbsLat{<: NumField})
  E = base_ring(ambient_space(L))
  if degree(E) > 1
    generators = elem_type(E)[E(1), absolute_primitive_element(E)]
  else
    generators = elem_type(E)[E(1)]
  end
  return _Zforms(L, generators)
end

function _Zforms(L::AbsLat{<: NumField}, generators::Vector)
  V = ambient_space(L)
  E = base_ring(V)
  Babs = absolute_basis(L)
  Babsmat = matrix(E, Babs)
  forms = fmpz_mat[]
  scalars = fmpq[]
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
function assert_has_automorphisms(L::AbsLat{<: NumField}; redo::Bool = false)

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
    gens = fmpz_mat[matrix(ZZ, g) for g in _gens]
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

@doc Markdown.doc"""
    automorphism_group_generators(L::AbsLat; ambient_representation::Bool = true)
                                                          -> Vector{MatElem}

Given a definite lattice `L`, return generators for the automorphism group of `L`.
If `ambient_representation == true` (the default), the transformations are represented
with respect to the ambient space of `L`. Otherwise, the transformations are represented
with respect to the (pseudo-)basis of `L`.
"""
automorphism_group_generators(L::AbsLat; ambient_representation::Bool = true)

function automorphism_group_generators(L::AbsLat; ambient_representation::Bool = true, check = false)

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

@doc Markdown.doc"""
    automorphism_group_order(L::AbsLat) -> Int

Given a definite lattice `L`, return the order of the automorphism group of `L`.
"""
automorphism_group_order(L::AbsLat; redo::Bool = false)

function automorphism_group_order(L::AbsLat; redo::Bool = false)
  assert_has_automorphisms(L, redo = redo)
  return L.automorphism_group_order
end

################################################################################
#
#  Isometry
#
################################################################################

@doc Markdown.doc"""
    is_isometric(L::AbsLat, M::AbsLat; ambient_representation::Bool = true)
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
is_isometric(L::AbsLat, M::AbsLat; ambient_representation::Bool = true)

function is_isometric(L::AbsLat{<: NumField}, M::AbsLat{<: NumField};
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

function maximal_sublattices(L::AbsLat, p; use_auto::Bool = false,
                                           callback = false, max = inf)
  @req base_ring(L) == order(p) "Incompatible arguments: p must be an ideal in the base ring of L"

  B = local_basis_matrix(L, p, type = :submodule)
  full_rank = rank(matrix(L.pmat)) == Hecke.max(nrows(L.pmat), ncols(L.pmat))
  n = nrows(B)
  R = base_ring(L)
  K = nf(R)
  k, h = ResidueField(R, p)
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

function minimal_superlattices(L::AbsLat, p; use_auto::Bool = false,
                                             callback = false, max = inf)
  @req base_ring(L) == order(p) "Incompatible arguments: p must be an ideal in the base ring of L"

  B = local_basis_matrix(L, p, type = :submodule)
  full_rank = rank(matrix(L.pmat)) == Hecke.max(nrows(L.pmat), ncols(L.pmat))
  n = nrows(B)
  R = base_ring(L)
  K = nf(R)
  k, h = ResidueField(R, p)
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
#  Orthogonal sum
#
################################################################################

# TODO: Make this a proper coproduct with injections?
function orthogonal_sum(M::T, N::T) where {T <: AbsLat}
  @req base_ring(M) === base_ring(N) "Base rings must be equal"
  U = ambient_space(M)
  V = ambient_space(N)
  W, f1, f2 = orthogonal_sum(U, V)
  rU = rank(U)
  rV = rank(V)
  rW = rank(W)
  pM = pseudo_matrix(M)
  pN = pseudo_matrix(N)
  MpM = matrix(pM)
  MpN = matrix(pN)
  H = pseudo_matrix(diagonal_matrix(MpM, MpN),
                    vcat(coefficient_ideals(pM), coefficient_ideals(pN)))
  return lattice(W, H), f1, f2
end

################################################################################
#
#  Orthogonal complement
#
################################################################################

# bugged needs intersections of non-full modules to work first
@doc Markdown.doc"""
    _orthogonal_complement(M::AbsLat, L::AbsLat) -> AbsLat

Return the orthogonal complement of the lattice `L` inside the lattice `M`.
"""
function _orthogonal_complement(M::AbsLat, L::AbsLat)
  @req ambient_space(M) == ambient_space(L) "lattices must be in the same ambient space"
  V = ambient_space(L)
  M = basis_matrix_of_rational_span(M)
  Morth = orthogonal_complement(V, M)
  # Now intersect KM with L
  pm = _intersection_modules(pseudo_matrix(Morth), pseudo_matrix(L))
  return lattice(V, pm)
end

# does not seem to work either
function _orthogonal_complement(v::Vector, L::AbsLat)
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

@doc Markdown.doc"""
    is_maximal_integral(L::AbsLat, p::NfOrdIdl) -> Bool, AbsLat

Given a lattice `L` and a prime ideal `p` of the fixed ring $\mathcal O_K$ of
`L`, return whether the completion of `L` at `p` is maximal integral. If it is
not the case, the second returned value is a lattice in the ambient space of `L`
whose completion at `p` is a minimal overlattice of $L_p$.
"""
is_maximal_integral(::AbsLat, p)

@doc Markdown.doc"""
    is_maximal_integral(L::AbsLat) -> Bool, AbsLat

Given a lattice `L`, return whether `L` is maximal integral. If it is not,
the second returned value is a minimal overlattice of `L` with integral norm.
"""
is_maximal_integral(::AbsLat)

@doc Markdown.doc"""
    is_maximal(L::AbsLat, p::NfOrdIdl) -> Bool, AbsLat

Given a lattice `L` and a prime ideal `p` in the fixed ring $\mathcal O_K$ of
`L`, check whether the norm of $L_p$ is integral and return whether `L` is maximal
at `p`. If it is locally integral but not locally maximal, the second returned value
is a lattice in the same ambient space of `L` whose completion at `p` has integral norm
and is a proper overlattice of $L_p$.
"""
is_maximal(::AbsLat, p)

@doc Markdown.doc"""
    maximal_integral_lattice(L::AbsLat, p::NfOrdIdl) -> AbsLat

Given a lattice `L` and a prime ideal `p` of the fixed ring $\mathcal O_K$ of
`L`, return a lattice `M` in the ambient space of `L` which is maximal integral
at `p` and which agrees with `L` locally at all the places different from `p`.
"""
maximal_integral_lattice(::AbsLat, p)

@doc Markdown.doc"""
    maximal_integral_lattice(L::AbsLat) -> AbsLat

Given a lattice `L`, return a lattice `M` in the ambient space of `L` which
is maximal integral and which contains `L`.
"""
maximal_integral_lattice(::AbsLat)

@doc Markdown.doc"""
    maximal_integral_lattice(V::AbsSpace) -> AbsLat

Given a space `V`, return a lattice in `V` with integral norm
and which is maximal in `V` satisfying this property.
"""
maximal_integral_lattice(::AbsSpace)

