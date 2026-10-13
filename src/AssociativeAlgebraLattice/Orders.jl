################################################################################
#
#  Multiplier modules
#
################################################################################

@doc raw"""
    _left_order_module(L::AssociativeAlgebraLattice)

For a full PID lattice `L` in a unital algebra `A`, return the embedded module
`{x in A | x*L ⊆ L}`. The result is cached on `L`.
"""
function _left_order_module(L::AssociativeAlgebraLattice)
  return get_attribute!(L, :left_order_module) do
    _colon_module(L, L; side = :left)
  end::_underlying_module_type(typeof(L))
end

@doc raw"""
    _right_order_module(L::AssociativeAlgebraLattice)

For a full PID lattice `L` in a unital algebra `A`, return the embedded module
`{x in A | L*x ⊆ L}`. The result is cached on `L`.
"""
function _right_order_module(L::AssociativeAlgebraLattice)
  return get_attribute!(L, :right_order_module) do
    _colon_module(L, L; side = :right)
  end::_underlying_module_type(typeof(L))
end
