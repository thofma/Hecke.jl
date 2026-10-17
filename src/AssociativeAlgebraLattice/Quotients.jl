@doc raw"""
    quo(L::AssociativeAlgebraLattice, N::AssociativeAlgebraLattice)

For PID coefficients and compatible lattices with `N` contained in `L`, return
`(Q, f)` representing the module quotient `L/N` and its projection. The quotient
may have torsion. The map accepts elements of `L`; its preimages are elements
of `L`, and its kernel is a lattice in the ambient algebra of `L`.
"""
function quo(L::AssociativeAlgebraLattice, N::AssociativeAlgebraLattice)
  Q, f = quo(underlying_module(L), underlying_module(N))
  return Q, AssociativeAlgebraLatticeMap(L, Q, f)
end

function quotient_vector_space(L::AssociativeAlgebraLattice, p::RingElem)
  V, f = quotient_vector_space(underlying_module(L), p)
  return V, AssociativeAlgebraLatticeMap(L, V, f)
end

function quotient_vector_space(L::AssociativeAlgebraLattice, N::AssociativeAlgebraLattice,
                               p::RingElem)
  V, f = quotient_vector_space(underlying_module(L), underlying_module(N), p)
  return V, AssociativeAlgebraLatticeMap(L, V, f)
end
