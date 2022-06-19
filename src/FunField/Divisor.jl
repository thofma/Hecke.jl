using Hecke
using Hecke.GenericRound2

export Divisor

export finite_maximal_order, infinite_maximal_order

mutable struct Divisor
  finite_order::GenericRound2.Order
  infinite_order::GenericRound2.Order
  finite_ideal::FfOrdlIdl
  infinite_ideal::FfOrdIdl

  function Divisor(I::FfOrdIdl, J::FfOrdIdl)
    r = new()
    return r
  end

end


function finite_maximal_order(K::FunctionField)
  get_attribute!(K, :finite_maximal_order) do
    return _finite_maximal_order(K)
  end
end

function _finite_maximal_order(K::FunctionField)
  return integral_closure(base_ring(K))
end

function infinite_maximal_order(K::FunctionField)
  get_attribute!(K, :infinite_maximal_order) do
    return _infinite_maximal_order(K)
  end
end

function _infinite_maximal_order(K::FunctionField)
  R = Localization(base_ring(F),degree)
  Oinfi = integral_closure(R,F)
  return Oinfi
end

