@attributes mutable struct AssociativeAlgebraOrder{BaseRingType, RingKind <: _RingType, AlgType} <: NCRing
  algebra::AlgType
  lattice::AssociativeAlgebraLattice{AlgType, BaseRingType}

  function AssociativeAlgebraOrder(L::AssociativeAlgebraLattice{A, R};
                                  check::Bool = true) where {A, R}
    @req !check || defines_order(L) "The lattice does not define an order"
    return new{R, _ring_type(R), A}(algebra(L), L)
  end
end

mutable struct AssociativeAlgebraOrderElem{OrderType, LatticeElemType} <: NCRingElem
  parent::OrderType
  elem_in_lattice::LatticeElemType

  function AssociativeAlgebraOrderElem(O::AssociativeAlgebraOrder,
                                      x::AssociativeAlgebraLatticeElem)
    @req parent(x) === underlying_lattice(O) "The element belongs to a different lattice"
    return new{typeof(O), typeof(x)}(O, x)
  end
end
