@doc raw"""
    mod(x::AssociativeAlgebraLatticeElem, N::AssociativeAlgebraLattice)

Return the representative of `x + N` obtained by normal-form reduction in the
underlying embedded modules. Require `N` to be compatible with and contained
in `parent(x)`. The result has the same parent as `x`.
"""
function mod(x::AssociativeAlgebraLatticeElem, N::AssociativeAlgebraLattice)
  m = mod(elem_in_module(x), underlying_module(N))
  return AssociativeAlgebraLatticeElem(parent(x), m)
end

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
