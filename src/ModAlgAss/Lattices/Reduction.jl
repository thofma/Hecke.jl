################################################################################
#
#  Reduction
#
################################################################################

@doc raw"""
    reduction(L::ModAlgAssLat, p::IntegerUnion) -> ModAlgAss

Given an $L$ over an $\mathbf{Z}$-order and a prime $p$, return the module $L/pL$
over the field $\mathbf{F}_p$.

Note that the module will be defined without algebra and the action will be
given by $\rank(O)$ many generators. To obtain a module for the
$\mathbf{F}_p$-algebra $O/pO$, the algebra first has to be constructed using
`reduction(O, p)`.

See also `change_coefficient_ring`.
"""
function reduction(L::ModAlgAssLat, p::IntegerUnion)
  @req base_ring((L.base_ring)) isa ZZRing "Order must be a Z-order"
  F = Native.GF(p, cached = false)
  a = action_of_basis(L)
  amodp = map(m -> change_base_ring(F, m), a)
  return Amodule(amodp)
end

@doc raw"""
    change_coefficient_ring(R::Ring, L::ModAlgAssLat{ZZRing}) -> ModAlgAss

Given a lattice $L$ over an $\mathbf{Z}$-order $L$, return the $L \otimes R$
over the ring $R$.

Note that the module will be defined without algebra and the action will be
given by $\rank(O)$ many generators.
"""
function change_coefficient_ring(R::Ring, L::ModAlgAssLat)
  @req base_ring((L.base_ring)) isa ZZRing "Order must be a Z-order"
  a = action_of_basis(L)
  aR = map(m -> change_base_ring(R, m), a)
  return Amodule(aR)
end
