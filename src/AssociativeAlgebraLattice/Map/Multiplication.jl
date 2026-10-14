@doc raw"""
    multiplication_map(L::AssociativeAlgebraLattice, N::AssociativeAlgebraLattice, a; side)
    multiplication_map(L::AssociativeAlgebraLattice, a; side)

Return the linear map from `L` to `N` given by `x -> a*x` for `side = :left`
or `x -> x*a` for `side = :right`. The coefficient ring must be a PID, the
ambient algebras must agree, and all images must belong to `N`. The multiplier
`a` may be a lattice element or an ambient algebra element. The second form
takes `N = L`.
"""
function multiplication_map(L::AssociativeAlgebraLattice, N::AssociativeAlgebraLattice,
                            a::AbstractAssociativeAlgebraElem; side::Symbol)
  _check_compatible(L, N)
  @req parent(a) === algebra(L) "The element and lattices have different ambient algebras"
  @req side === :left || side === :right "The side must be :left or :right"
  # TODO: Speed this up using the representation matrix of a.
  B = basis(L; copy = false)
  images = side === :left ? [a*b for b in B] : [b*a for b in B]
  return hom(L, N, images)
end

multiplication_map(L::AssociativeAlgebraLattice, N::AssociativeAlgebraLattice,
                   a::AssociativeAlgebraLatticeElem; side::Symbol) =
  multiplication_map(L, N, elem_in_algebra(a); side)

multiplication_map(L::AssociativeAlgebraLattice,
                   a::Union{AbstractAssociativeAlgebraElem, AssociativeAlgebraLatticeElem};
                   side::Symbol) = multiplication_map(L, L, a; side)
