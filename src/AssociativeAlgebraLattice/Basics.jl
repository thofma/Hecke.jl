################################################################################
#
#  Embedded module interface
#
################################################################################

function _map_to_ambient(x::AbstractAssociativeAlgebraElem, M::EmbeddedModule)
  @assert parent(x) === M.overstructure
  t = _tmp_mat_overring(M, 1)
  elem_to_mat_row!(t, 1, x)
  return t
end

function _map_to_ambient(x::Vector{<:AbstractAssociativeAlgebraElem}, M::EmbeddedModule)
  return coordinates!(_tmp_mat_overring(M, length(x)), x)
end

function pseudo_basis(M::EmbeddedModule{_PID}, A::AbstractAssociativeAlgebra)
  return [_pseudo_element(x, ring(M)) for x in basis(M, A)]
end

function pseudo_basis(M::EmbeddedModule{_DD}, A::AbstractAssociativeAlgebra)
  pm = basis_matrix(M) # pseudo-matrix
  pmmat = matrix(pm)
  pmc = coefficient_ideals(pm)
  res = PseudoElement{elem_type(A), fractional_ideal_type(ring(M))}[]
  for i in 1:nrows(pmmat)
    push!(res, _pseudo_element(elem_from_mat_row(A, pmmat, i), pmc[i]))
  end
  return res
end

function basis(M::EmbeddedModule, A::AbstractAssociativeAlgebra)
  bmat = basis_matrix(M)
  res = elem_type(A)[]
  for i in 1:nrows(bmat)
    push!(res, elem_from_mat_row(A, bmat, i))
  end
  return res
end

################################################################################
#
#  Coordinates
#
################################################################################

function coordinates(A::AbstractAssociativeAlgebra, v::Vector{<:AbstractAssociativeAlgebraElem{T}}) where {T}
  n = length(v)
  M = zero_matrix(base_ring(A), n, dim(A))
  return coordinates!(M, v)
end

function coordinates!(M::MatrixElem{T}, A::Vector{<:AbstractAssociativeAlgebraElem{T}}) where T
  n = length(A)
  @assert nrows(M) == n
  d = ncols(M)
  K = base_ring(M)

  for i = 1:n
    elem_to_mat_row!(M, i, A[i])
    #for j = 1:d
    #  M[i, j] = deepcopy(coefficients(A[i], copy = false)[j])
    #end
  end
  return M
end

coordinates(A::Vector{<:AbstractAssociativeAlgebraElem}) = basis_matrix(A)

function coordinates(A::Vector{<:PseudoElement}, R::Ring)
  return coordinates(A, R, _ring_type(R))
end

function coordinates(A::Vector{<:PseudoElement}, R::Ring, ::Type{_PID})
  return coordinates(element.(A))
end

function coordinates(A::Vector{<:PseudoElement}, R::Ring, ::Type{_DD})
  M = coordinates(element.(A))
  coeff = fractional_ideal.(A)
  return pseudo_matrix(R, M, coeff)
end

################################################################################
#
#  Accessors and construction
#
################################################################################

_underlying_module_type(::Type{AssociativeAlgebraLattice{S, T}}) where {S, T} = _embedded_module_type(T, base_ring_type(S))

underlying_module(L::AssociativeAlgebraLattice) = L.M::_underlying_module_type(typeof(L))

algebra(L::AssociativeAlgebraLattice) = L.algebra

base_ring(L::AssociativeAlgebraLattice) = L.base_ring

base_ring_type(::Type{AssociativeAlgebraLattice{S, T}}) where {S, T} = T

algebra_type(::Type{AssociativeAlgebraLattice{S, T}}) where {S, T} = S

function _lattice(A::AbstractAssociativeAlgebra, R::Ring, M::EmbeddedModule)
  @req ring(M) === R "Coefficient rings do not agree"
  @req overring(M) === base_ring(A) "Scalar rings do not agree"
  @req overstructure(M) === A "Ambient algebras do not agree"
  @req ambient_rank(M) == dim(A) "The module has the wrong ambient rank"
  return AssociativeAlgebraLattice(A, R, M)
end

lattice(A::AbstractAssociativeAlgebra, R::Ring, M::EmbeddedModule) = _lattice(A, R, M)

function _lattice_module(A::AbstractAssociativeAlgebra, R::Ring, M::MatElem, ::Type{_PID}; is_basis_matrix::Bool = false)
  return embedded_module(R, base_ring(A), M; overstructure = A, is_basis_matrix)
end

function _lattice_module(A::AbstractAssociativeAlgebra, R::Ring, M::MatElem, ::Type{_DD}; is_basis_matrix::Bool = false)
  C = [fractional_ideal(R, one(R)) for _ in 1:nrows(M)]
  PM = pseudo_matrix(R, M, C)
  return embedded_module(R, base_ring(A), PM; overstructure = A, is_basis_matrix)
end

function lattice(A::AbstractAssociativeAlgebra, R::Ring, M::MatElem; is_basis_matrix::Bool = false)
  @req base_ring(M) === base_ring(A) "The matrix and algebra have different base rings"
  @req ncols(M) == dim(A) "The matrix has the wrong number of columns"
  N = _lattice_module(A, R, M, _ring_type(R); is_basis_matrix)
  return _lattice(A, R, N)
end

function lattice(A::AbstractAssociativeAlgebra, R::Ring, M::PMat; is_basis_matrix::Bool = false)
  @req _ring_type(R) === _DD "Pseudo-matrices are only supported over Dedekind domains"
  @req base_ring(M) === R "The pseudo-matrix and lattice have different base rings"
  @req base_ring(matrix(M)) === base_ring(A) "The pseudo-matrix and algebra have different scalar rings"
  @req ncols(M) == dim(A) "The pseudo-matrix has the wrong number of columns"
  N = embedded_module(R, base_ring(A), M; overstructure = A, is_basis_matrix)
  return _lattice(A, R, N)
end

function lattice(A::AbstractAssociativeAlgebra, R::Ring, elts::Vector{<:AbstractAssociativeAlgebraElem})
  @req all(x -> parent(x) === A, elts) "The elements must belong to the ambient algebra"
  M = coordinates(A, elts)
  return lattice(A, R, M)
end

function lattice(A::AbstractAssociativeAlgebra, R::Ring, elts::Vector{<:PseudoElement})
  @req all(x -> parent(element(x)) === A, elts) "The elements must belong to the ambient algebra"
  @req _ring_type(R) === _DD "Pseudo-elements are only supported over Dedekind domains"
  return lattice(A, R, coordinates(elts, R))
end

function zero_lattice(A::AbstractAssociativeAlgebra, R::Ring)
  return lattice(A, R, zero_matrix(base_ring(A), 0, dim(A)))
end

################################################################################
#
#  Basis and rank
#
################################################################################

function basis_matrix(L::AssociativeAlgebraLattice; copy::Bool = true)
  M = basis_matrix(underlying_module(L))
  return copy ? deepcopy(M) : M
end

function pseudo_basis(L::AssociativeAlgebraLattice; copy::Bool = true)
  B = pseudo_basis(underlying_module(L), algebra(L))
  return copy ? deepcopy(B) : B
end

@doc raw"""
    basis(L::AssociativeAlgebraLattice; copy::Bool = true)

For PID coefficients, return a basis of `L` as ambient algebra elements.
The basis is cached; return a shallow copy of the vector if `copy` is `true`.
"""
function basis(L::AssociativeAlgebraLattice; copy::Bool = true)
  @req _ring_type(base_ring(L)) === _PID "Use pseudo_basis for lattices over Dedekind domains"
  if !isdefined(L, :basis)
    L.basis = basis(underlying_module(L), algebra(L))
  end
  B = L.basis::Vector{elem_type(algebra(L))}
  return copy ? Base.copy(B) : B
end

rank(L::AssociativeAlgebraLattice) = rank(underlying_module(L))

ambient_rank(L::AssociativeAlgebraLattice) = ambient_rank(underlying_module(L))

is_full_lattice(L::AssociativeAlgebraLattice) = has_full_rank(underlying_module(L))

is_full_rank(L::AssociativeAlgebraLattice) = is_full_lattice(L)

iszero(L::AssociativeAlgebraLattice) = iszero(rank(L))

function is_compatible(L::AssociativeAlgebraLattice, M::AssociativeAlgebraLattice)
  algebra(L) === algebra(M) || return false
  return base_ring(L) === base_ring(M)
end

function _check_compatible(L::AssociativeAlgebraLattice, M::AssociativeAlgebraLattice)
  @req is_compatible(L, M) "The lattices have different ambient modules"
  return nothing
end

################################################################################
#
#  Containment and equality
#
################################################################################

function in(x::AbstractAssociativeAlgebraElem, L::AssociativeAlgebraLattice)
  @req parent(x) === algebra(L) "The element and lattice have different ambient algebras"
  return in(x, underlying_module(L))
end

function in(x::PseudoElement, L::AssociativeAlgebraLattice)
  @req parent(element(x)) === algebra(L) "The element and lattice have different ambient algebras"
  return in(x, underlying_module(L))
end

function in(x::AssociativeAlgebraLatticeElem, L::AssociativeAlgebraLattice)
  return elem_in_algebra(x) in L
end

function issubset(L::AssociativeAlgebraLattice, M::AssociativeAlgebraLattice)
  @req is_compatible(L, M) "The lattices have different ambient modules"
  return issubset(underlying_module(L), underlying_module(M))
end

@doc raw"""
    module_index(N::AssociativeAlgebraLattice, L::AssociativeAlgebraLattice; check = true)

For PID coefficients, return the index ideal of `N` in `L` in `base_ring(L)`
using the underlying embedded modules. If `check` is `true`, require compatible
lattices with the same rank and `N` contained in `L`. Use `gen` to obtain a
normalized generator of the index ideal.
"""
function module_index(N::AssociativeAlgebraLattice, L::AssociativeAlgebraLattice; check = true)
  return module_index(underlying_module(N), underlying_module(L); check)
end

function ==(L::AssociativeAlgebraLattice, M::AssociativeAlgebraLattice)
  L === M && return true
  return underlying_module(L) == underlying_module(M)
end

function Base.hash(L::AssociativeAlgebraLattice, h::UInt)
  return hash(underlying_module(L), h)
end

################################################################################
#
#  Printing
#
################################################################################

function show(io::IO, L::AssociativeAlgebraLattice)
  print(io, "Lattice of rank ", rank(L), " in ")
  show(io, algebra(L))
end
