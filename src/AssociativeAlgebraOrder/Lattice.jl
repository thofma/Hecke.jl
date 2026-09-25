################################################################################
#
#  Accessors and construction
#
################################################################################

_module(L::AssociativeAlgebraLattice{S, T}) where {S, T} = L.M::_embedded_module_type(T, base_ring_type(S))

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

lattice(O::AssociativeAlgebraOrder) = lattice(algebra(O), base_ring(O), _underlying_module(O))

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
  M = basis_matrix(_module(L))
  return copy ? deepcopy(M) : M
end

function pseudo_basis(L::AssociativeAlgebraLattice; copy::Bool = true)
  B = pseudo_basis(_module(L), algebra(L))
  return copy ? deepcopy(B) : B
end

function basis(L::AssociativeAlgebraLattice; copy::Bool = true)
  @req _ring_type(base_ring(L)) === _PID "Use pseudo_basis for lattices over Dedekind domains"
  B = basis(_module(L), algebra(L))
  return copy ? deepcopy(B) : B
end

rank(L::AssociativeAlgebraLattice) = rank(_module(L))

ambient_rank(L::AssociativeAlgebraLattice) = ambient_rank(_module(L))

is_full_lattice(L::AssociativeAlgebraLattice) = has_full_rank(_module(L))

is_full_rank(L::AssociativeAlgebraLattice) = is_full_lattice(L)

iszero(L::AssociativeAlgebraLattice) = iszero(rank(L))

################################################################################
#
#  Containment and equality
#
################################################################################

function in(x::AbstractAssociativeAlgebraElem, L::AssociativeAlgebraLattice)
  @req parent(x) === algebra(L) "The element and lattice have different ambient algebras"
  return in(x, _module(L))
end

function in(x::PseudoElement, L::AssociativeAlgebraLattice)
  @req parent(element(x)) === algebra(L) "The element and lattice have different ambient algebras"
  return in(x, _module(L))
end

function is_compatible(L::AssociativeAlgebraLattice, M::AssociativeAlgebraLattice)
  algebra(L) === algebra(M) || return false
  return base_ring(L) === base_ring(M)
end

function issubset(L::AssociativeAlgebraLattice, M::AssociativeAlgebraLattice)
  @req is_compatible(L, M) "The lattices have different ambient modules"
  return issubset(_module(L), _module(M))
end

function ==(L::AssociativeAlgebraLattice, M::AssociativeAlgebraLattice)
  L === M && return true
  return _module(L) == _module(M)
end

function Base.hash(L::AssociativeAlgebraLattice, h::UInt)
  return hash(_module(L), h)
end

################################################################################
#
#  Arithmetic
#
################################################################################

function _check_compatible(L::AssociativeAlgebraLattice, M::AssociativeAlgebraLattice)
  @req is_compatible(L, M) "The lattices have different ambient modules"
  return nothing
end

function +(L::AssociativeAlgebraLattice, M::AssociativeAlgebraLattice)
  _check_compatible(L, M)
  return lattice(algebra(L), base_ring(L), _module(L) + _module(M))
end

function intersect(L::AssociativeAlgebraLattice, M::AssociativeAlgebraLattice)
  _check_compatible(L, M)
  return lattice(algebra(L), base_ring(L), intersect(_module(L), _module(M)))
end

function _product(L::AssociativeAlgebraLattice, M::AssociativeAlgebraLattice, ::Type{_PID})
  if iszero(L) || iszero(M)
    return zero_lattice(algebra(L), base_ring(L))
  end
  B = [x*y for x in basis(L, copy = false) for y in basis(M, copy = false)]
  return lattice(algebra(L), base_ring(L), B)
end

function _product(L::AssociativeAlgebraLattice, M::AssociativeAlgebraLattice, ::Type{_DD})
  if iszero(L) || iszero(M)
    return zero_lattice(algebra(L), base_ring(L))
  end
  B = [x*y for x in pseudo_basis(L, copy = false) for y in pseudo_basis(M, copy = false)]
  return lattice(algebra(L), base_ring(L), B)
end

function *(L::AssociativeAlgebraLattice, M::AssociativeAlgebraLattice)
  _check_compatible(L, M)
  return _product(L, M, _ring_type(base_ring(L)))
end

function _multiply(L::AssociativeAlgebraLattice, x::AbstractAssociativeAlgebraElem, ::Type{_PID}, action::Symbol)
  if iszero(L)
    return zero_lattice(algebra(L), base_ring(L))
  end
  B = if action === :left
    [x*y for y in basis(L, copy = false)]
  else
    [y*x for y in basis(L, copy = false)]
  end
  return lattice(algebra(L), base_ring(L), B)
end

function _multiply(L::AssociativeAlgebraLattice, x::AbstractAssociativeAlgebraElem, ::Type{_DD}, action::Symbol)
  if iszero(L)
    return zero_lattice(algebra(L), base_ring(L))
  end
  B = if action === :left
    [_pseudo_element(x*element(y), deepcopy(fractional_ideal(y))) for y in pseudo_basis(L, copy = false)]
  else
    [_pseudo_element(element(y)*x, deepcopy(fractional_ideal(y))) for y in pseudo_basis(L, copy = false)]
  end
  return lattice(algebra(L), base_ring(L), B)
end

function *(x::AbstractAssociativeAlgebraElem, L::AssociativeAlgebraLattice)
  @req parent(x) === algebra(L) "The element and lattice have different ambient algebras"
  return _multiply(L, x, _ring_type(base_ring(L)), :left)
end

function *(L::AssociativeAlgebraLattice, x::AbstractAssociativeAlgebraElem)
  @req parent(x) === algebra(L) "The element and lattice have different ambient algebras"
  return _multiply(L, x, _ring_type(base_ring(L)), :right)
end

function _scale_lattice(x, L::AssociativeAlgebraLattice)
  if iszero(x)
    return zero_lattice(algebra(L), base_ring(L))
  end
  B = x*basis_matrix(L, copy = false)
  return lattice(algebra(L), base_ring(L), B)
end

function *(x::IntegerUnion, L::AssociativeAlgebraLattice)
  return _scale_lattice(base_ring(algebra(L))(x), L)
end

function *(x::RingElem, L::AssociativeAlgebraLattice)
  R = base_ring(L)
  K = base_ring(algebra(L))
  @req parent(x) === R || parent(x) === K "The scalar does not belong to the coefficient ring or its fraction field"
  y = parent(x) === R ? image(fraction_map(_module(L)), x) : x
  return _scale_lattice(y, L)
end

*(L::AssociativeAlgebraLattice, x::Union{IntegerUnion, RingElem}) = x*L

Base.copy(L::AssociativeAlgebraLattice) = L

################################################################################
#
#  Printing
#
################################################################################

function show(io::IO, L::AssociativeAlgebraLattice)
  print(io, "Lattice of rank ", rank(L), " in ")
  show(io, algebra(L))
end
