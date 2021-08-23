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
  residue_field_map

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

mutable struct CompletionMap{S, T} <: Map{AnticNumberField, S, HeckeMap, CompletionMap{S, T}}
  header::MapHeader{AnticNumberField, S}
  P::NfOrdIdl
  prim_img::T
  inv_img::Tuple{nf_elem, nf_elem}
  precision::Int

  function CompletionMap(K::AnticNumberField, L::LocalField{qadic, EisensteinLocalField},
                          img::LocalFieldElem{qadic, EisensteinLocalField},
                          inv_img::Tuple{nf_elem, nf_elem}, precision::Int)
    z = new{LocalField{qadic, EisensteinLocalField}, LocalFieldElem{qadic, EisensteinLocalField}}()
    z.header = MapHeader(K, L)
    z.prim_img = img
    z.inv_img = inv_img
    z.precision = precision
    return z
  end

  function CompletionMap(K::AnticNumberField, L::LocalField{padic, EisensteinLocalField},
                          img::LocalFieldElem{padic, EisensteinLocalField},
                          inv_img::nf_elem, precision::Int)
    z = new{LocalField{padic, EisensteinLocalField}, LocalFieldElem{padic, EisensteinLocalField}}()
    z.header = MapHeader(K, L)
    z.prim_img = img
    z.inv_img = (zero(K), inv_img)
    z.precision = precision
    return z
  end

  function CompletionMap(K::AnticNumberField, L::FlintQadicField,
                          img::qadic,
                          inv_img::nf_elem, precision::Int)
    z = new{FlintQadicField, qadic}()
    z.header = MapHeader(K, L)
    z.prim_img = img
    z.inv_img = (inv_img, zero(K))
    z.precision = precision
    return z
  end
end