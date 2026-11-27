@doc raw"""
    multiplication_map(L::AssociativeAlgebraLattice, N::AssociativeAlgebraLattice, a; side)
    multiplication_map(L::AssociativeAlgebraLattice, a; side)

Return the linear map from `L` to `N` given by `x -> a*x` for `side = :left`
or `x -> x*a` for `side = :right`. The coefficient ring may be a PID or a
supported maximal Dedekind order. The ambient algebras must agree, and all
images must belong to `N`. The multiplier `a` may be a lattice element or an
ambient algebra element. The second form takes `N = L`.
"""
function multiplication_map(L::AssociativeAlgebraLattice, N::AssociativeAlgebraLattice,
                            a::AbstractAssociativeAlgebraElem; side::Symbol)
  _check_compatible(L, N)
  @req parent(a) === algebra(L) "The element and lattices have different ambient algebras"
  @req side === :left || side === :right "The side must be :left or :right"
  f = EmbeddedModules._hom_from_ambient_matrix(underlying_module(L),
        underlying_module(N), representation_matrix(a, side))
  return AssociativeAlgebraLatticeMap(L, N, f)
end

multiplication_map(L::AssociativeAlgebraLattice, N::AssociativeAlgebraLattice,
                   a::AssociativeAlgebraLatticeElem; side::Symbol) =
  multiplication_map(L, N, elem_in_algebra(a); side)

multiplication_map(L::AssociativeAlgebraLattice,
                   a::Union{AbstractAssociativeAlgebraElem, AssociativeAlgebraLatticeElem};
                   side::Symbol) = multiplication_map(L, L, a; side)
