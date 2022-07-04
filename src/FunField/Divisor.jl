using Hecke

export Divisor

export finite_maximal_order, infinite_maximal_order, function_field, field_of_fractions

mutable struct Divisor
  function_field::AbstractAlgebra.Generic.FunctionField
  finite_ideal::FfOrdFracIdl
  infinite_ideal::FfOrdFracIdl

  function Divisor(I::FfOrdFracIdl, J::FfOrdFracIdl)
    r = new()
    
    O = order(I)
    Oinf = order(J)
    K = function_field(O)
    
    @req K == function_field(Oinf) "Ideals need to belong to orders of the same function field."
    @req isa(O, PolyRing) "First ideal needs to be an ideal over the finite order"
    @req isa(base_ring(Oinf), KInftyRing) "Second ideal needs to be an ideal over the infinite order"
    
    r.function_field = K
    r.finite_ideal = I
    r.infinite_ideal = J
    
    return r
  end
  
  function Divisor(I::FfOrdIdl, J::FfOrdIdl)
    return Divisor(FfOrdFracIdl(I), FfOrdFracIdl(J))
  end

end

@attributes AbstractAlgebra.Generic.FunctionField

function function_field(D::Divisor)
  return D.function_field
end

function ideals(D)

  return D.finite_ideal, D.infinite_ideal

end

function field_of_fractions(O::GenOrd)
  return O.F
end

function function_field(O::GenOrd)
  return O.F
end

function constant_field(K::AbstractAlgebra.Generic.FunctionField)
  return base_ring(base_ring(K))
end

function finite_maximal_order(K::AbstractAlgebra.Generic.FunctionField)
  get_attribute!(K, :finite_maximal_order) do
    return _finite_maximal_order(K)
  end
end

function _finite_maximal_order(K::AbstractAlgebra.Generic.FunctionField)
  kx = parent(numerator(gen(base_ring(K))))
  return integral_closure(kx, K)
end

function infinite_maximal_order(K::AbstractAlgebra.Generic.FunctionField)
  get_attribute!(K, :infinite_maximal_order) do
    return _infinite_maximal_order(K)
  end
end

function _infinite_maximal_order(K::AbstractAlgebra.Generic.FunctionField)
  R = Localization(base_ring(K),degree)
  Oinf = integral_closure(R, K)
  return Oinf
end

function Base.:+(D1::Divisor, D2::Divisor)
  return Divisor(finite_ideal(D1) * finite_ideal(D2), infinite_ideal(D1) * infinite_ideal(D2))
end

function Base.:-(D1::Divisor, D2::Divisor)
  return Divisor(finite_ideal(D1) // finite_ideal(D2), infinite_ideal(D1) // infinite_ideal(D2))
end

function Base.:*(n::Int, D1::Divisor)
  return Divisor(finite_ideal(D1)^n, infinite_ideal(D1)^n)
end

Base.:*(D::Divisor, n::Int) = n * D

#=function RiemannRochSpace(D::Divisor)
  OS, O_S = ideals(D)
  V = colon(FfOrdIdl(O, one(O)), OS)
  B = colon(FfOrdIdl(O, one(O)), O_S)
end
=#

