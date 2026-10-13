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

@doc raw"""
    quotient_vector_space(L::AssociativeAlgebraLattice, p::RingElem)
    quotient_vector_space(L::AssociativeAlgebraLattice, N::AssociativeAlgebraLattice, p::RingElem)

For PID coefficients, return `(V, f, RtoF)` for `L/pL` or `L/N` over the
residue field `F = R/(p)`, where `R = base_ring(L)` and `p` is prime in `R`.
The second form requires compatible lattices with `pL` contained in `N` and `N`
contained in `L`. The projection accepts elements of `L`, preimages belong to
`L`, and its kernel is a lattice in the ambient algebra of `L`.
"""
function quotient_vector_space(L::AssociativeAlgebraLattice, p::RingElem)
  V, f, RtoF = quotient_vector_space(underlying_module(L), p)
  return V, AssociativeAlgebraLatticeMap(L, V, f), RtoF
end

function quotient_vector_space(L::AssociativeAlgebraLattice, N::AssociativeAlgebraLattice,
                               p::RingElem)
  V, f, RtoF = quotient_vector_space(underlying_module(L), underlying_module(N), p)
  return V, AssociativeAlgebraLatticeMap(L, V, f), RtoF
end
