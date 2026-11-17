@doc raw"""
    inclusion_map(L::AssociativeAlgebraLattice, N::AssociativeAlgebraLattice)

Return the inclusion of `L` into `N`, requiring `L` to be contained in `N`.
This works over PIDs and Dedekind domains.
"""
function inclusion_map(L::AssociativeAlgebraLattice, N::AssociativeAlgebraLattice)
  f = EmbeddedModules.inclusion_map(underlying_module(L), underlying_module(N))
  return AssociativeAlgebraLatticeMap(L, N, f)
end

id_hom(L::AssociativeAlgebraLattice) = inclusion_map(L, L)
