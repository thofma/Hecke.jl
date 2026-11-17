@attr order_type(typeof(L)) function left_order(L::AssociativeAlgebraLattice)
  M = _left_order_module(L)
  return order(lattice(algebra(L), base_ring(L), M); check = false)
end

@attr order_type(typeof(L)) function right_order(L::AssociativeAlgebraLattice)
  M = _right_order_module(L)
  return order(lattice(algebra(L), base_ring(L), M); check = false)
end
