@doc raw"""
    compose(f::AssociativeAlgebraLatticeMap, g::AssociativeAlgebraLatticeMap)

Return the composite `h` with `h(x) == g(f(x))`. The intermediate lattice must
be the same parent object: `codomain(f) === domain(g)`.
"""
function compose(f::AssociativeAlgebraLatticeMap, g::AssociativeAlgebraLatticeMap)
  @req codomain(f) === domain(g) "Composition: Maps are not compatible"
  if !(codomain(g) isa Union{AssociativeAlgebraLattice, EmbeddedModule})
    return invoke(compose, Tuple{Map, Map}, f, g)
  end
  h = compose(underlying_map(f), underlying_map(g))
  return AssociativeAlgebraLatticeMap(domain(f), codomain(g), h)
end
