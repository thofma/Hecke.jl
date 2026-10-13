################################################################################
#
#  Arithmetic
#
################################################################################

function +(L::AssociativeAlgebraLattice, M::AssociativeAlgebraLattice)
  _check_compatible(L, M)
  return lattice(algebra(L), base_ring(L), underlying_module(L) + underlying_module(M))
end

function intersect(L::AssociativeAlgebraLattice, M::AssociativeAlgebraLattice)
  _check_compatible(L, M)
  return lattice(algebra(L), base_ring(L), intersect(underlying_module(L), underlying_module(M)))
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
  y = parent(x) === R ? image(fraction_map(underlying_module(L)), x) : x
  return _scale_lattice(y, L)
end

*(L::AssociativeAlgebraLattice, x::Union{IntegerUnion, RingElem}) = x*L
