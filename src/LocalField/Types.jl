abstract type LocalFieldParameter end
abstract type EisensteinLocalField <: LocalFieldParameter end
abstract type UnramifiedLocalField <: LocalFieldParameter end
abstract type GenericLocalField <: LocalFieldParameter end

mutable struct LocalField{S, T} <: Field
  defining_polynomial::Generic.Poly{S}
  S::Symbol
  precision::Int
  traces_basis::Vector{S}
  ramification_index::Int
  inertia_degree::Int
  uniformizer::Generic.Poly{S}

  function LocalField{S, T}(f::Generic.Poly{S}, s::Symbol) where {S <: FieldElem, T <: LocalFieldParameter}
    z = new{S, T}()
    z.defining_polynomial = f
    z.S = s
    z.precision = precision(f)
    z.ramification_index = -1
    z.inertia_degree = -1
    return z
  end
end

mutable struct LocalFieldElem{S, T} <: FieldElem
  parent::LocalField{S, T}
  data::Generic.Poly{S}
  precision::Int
end

