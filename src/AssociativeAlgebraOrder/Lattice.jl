_module(O::AssociativeAlgebraLattice{S, T}) where {S, T} = O.M::_embedded_module_type(T, base_ring_type(S))

function lattice(A::AbstractAssociativeAlgebra, R::Ring, elts::Vector)
  return AssociativeAlgebraLattice(A, R, coordinates(A, elts))
end
