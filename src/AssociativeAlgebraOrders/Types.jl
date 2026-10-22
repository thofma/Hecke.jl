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

@attributes mutable struct AssociativeAlgebraOrderIdeal{
    OrderType <: AssociativeAlgebraOrder,
    LatticeType <: AssociativeAlgebraLattice}
  order::OrderType
  lattice::LatticeType

  function AssociativeAlgebraOrderIdeal(O::AssociativeAlgebraOrder,
                                       L::AssociativeAlgebraLattice;
                                       side::Symbol, check::Bool = true)
    _check_ideal_side(side)
    Lo = underlying_lattice(O)
    @req is_compatible(Lo, L) "The order and lattice are incompatible"
    @req issubset(L, Lo) "The lattice is not contained in the order"
    I = new{typeof(O), typeof(L)}(O, L)
    if check
      @req _test_ideal_sidedness(I, side) "The lattice has incorrect sidedness"
    end
    _set_ideal_side!(I, side)
    return I
  end
end
