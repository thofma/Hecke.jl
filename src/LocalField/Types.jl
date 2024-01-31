abstract type LocalFieldParameter end
abstract type EisensteinLocalField <: LocalFieldParameter end
abstract type UnramifiedLocalField <: LocalFieldParameter end
abstract type GenericLocalField <: LocalFieldParameter end

@attributes mutable struct LocalField{S, T} <: NonArchLocalField
  def_poly::Function #Int -> Poly at prec n
  def_poly_cache::Dict{Int, Generic.Poly{S}}
  S::Symbol
  precision::Int #only used for exact to ring
  traces_basis::Dict{Int, Vector{S}}
  ramification_index::Int
  inertia_degree::Int
  uniformizer::Generic.Poly{S}
  residue_field_map

  function LocalField{S, T}(f::Generic.Poly{S}, s::Symbol) where {S <: FieldElem, T <: LocalFieldParameter}
    z = new{S, T}()
    z.def_poly = n -> setprecision(f, n)
    z.def_poly_cache = Dict{Int, Generic.Poly{S}}(precision(f) => f)
    z.traces_basis = Dict{Int, Vector{S}}()
    z.S = s
    z.precision = precision(f)
    z.ramification_index = -1
    z.inertia_degree = -1
    return z
  end
end

mutable struct LocalFieldElem{S, T} <: NonArchLocalFieldElem
  parent::LocalField{S, T}
  data::Generic.Poly{S}
  precision::Int
end

mutable struct CompletionMap{S, T} <: Map{AbsSimpleNumField, S, HeckeMap, CompletionMap{S, T}}
  header::MapHeader{AbsSimpleNumField, S}
  P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}
  prim_img::T
  inv_img::Tuple{AbsSimpleNumFieldElem, AbsSimpleNumFieldElem}
  precision::Int

  function CompletionMap(K::AbsSimpleNumField, L::LocalField{QadicFieldElem, EisensteinLocalField},
                          img::LocalFieldElem{QadicFieldElem, EisensteinLocalField},
                          inv_img::Tuple{AbsSimpleNumFieldElem, AbsSimpleNumFieldElem}, precision::Int)
    z = new{LocalField{QadicFieldElem, EisensteinLocalField}, LocalFieldElem{QadicFieldElem, EisensteinLocalField}}()
    z.header = MapHeader(K, L)
    z.prim_img = img
    z.inv_img = inv_img
    z.precision = precision
    return z
  end

  function CompletionMap(K::AbsSimpleNumField, L::LocalField{PadicFieldElem, EisensteinLocalField},
                          img::LocalFieldElem{PadicFieldElem, EisensteinLocalField},
                          inv_img::AbsSimpleNumFieldElem, precision::Int)
    z = new{LocalField{PadicFieldElem, EisensteinLocalField}, LocalFieldElem{PadicFieldElem, EisensteinLocalField}}()
    z.header = MapHeader(K, L)
    z.prim_img = img
    z.inv_img = (zero(K), inv_img)
    z.precision = precision
    return z
  end

  function CompletionMap(K::AbsSimpleNumField, L::QadicField,
                          img::QadicFieldElem,
                          inv_img::AbsSimpleNumFieldElem, precision::Int)
    z = new{QadicField, QadicFieldElem}()
    z.header = MapHeader(K, L)
    z.prim_img = img
    z.inv_img = (inv_img, zero(K))
    z.precision = precision
    return z
  end
end
