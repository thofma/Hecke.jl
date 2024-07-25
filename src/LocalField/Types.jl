################################################################################
#
#  LocalField
#
################################################################################

abstract type LocalFieldParameter end
abstract type EisensteinLocalField <: LocalFieldParameter end
abstract type UnramifiedLocalField <: LocalFieldParameter end
abstract type GenericLocalField <: LocalFieldParameter end

@attributes mutable struct LocalField{S, T} <: NonArchLocalField
  def_poly::Function #Int -> Poly at prec n
  def_poly_cache::Dict{Int, Generic.Poly{S}}
  S::Symbol
  precision_base::Int #only used for exact to ring
  precision_times_ramification_index::Int #only used for exact to ring
  traces_basis::Dict{Int, Vector{S}}
  ramification_index::Int
  absolute_ramification_index::Int
  inertia_degree::Int
  uniformizer::Generic.Poly{S}
  residue_field_map

  function LocalField{S, T}(f::Generic.Poly{S}, s::Symbol) where {S <: FieldElem, T <: LocalFieldParameter}
    z = new{S, T}()
    z.def_poly = n -> setprecision(f, n)
    z.def_poly_cache = Dict{Int, Generic.Poly{S}}(precision(f) => f)
    z.traces_basis = Dict{Int, Vector{S}}()
    z.S = s
    z.precision_base = precision(f)
    z.precision_times_ramification_index = -1
    z.ramification_index = -1
    z.absolute_ramification_index = -1
    z.inertia_degree = -1
    return z
  end
end

mutable struct LocalFieldElem{S, T} <: NonArchLocalFieldElem
  parent::LocalField{S, T}
  data::Generic.Poly{S}
  precision::Int
end

################################################################################
#
#  CompletionMap
#
################################################################################

mutable struct CompletionMap{S, T} <: Map{AbsSimpleNumField, S, HeckeMap, CompletionMap{S, T}}
  header::MapHeader{AbsSimpleNumField, S}
  P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}
  prim_img::T
  inv_img::Tuple{AbsSimpleNumFieldElem, AbsSimpleNumFieldElem}
  precision::Int
  lift_data::Tuple{Int, ZZMatrix, AbstractAlgebra.Solve.SolveCtx{QQFieldElem, AbstractAlgebra.Solve.RREFTrait, QQMatrix, QQMatrix, QQMatrix}}

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

################################################################################
#
#  Valuation ring
#
################################################################################

@attributes mutable struct LocalFieldValuationRing{S, T} <: Generic.Ring
  Q::S #The corresponding local field
  basis::Vector{T} #The OK-basis of the ring, where OK is
                   #the maximal order of the base field of Q
  function LocalFieldValuationRing{S, T}(x::S) where {S <: Union{LocalField, QadicField, PadicField}, T}
    z = new{S, T}()
    z.Q = x
    return z
  end

end

mutable struct LocalFieldValuationRingElem{S, T} <: RingElem
  P::LocalFieldValuationRing{S, T}
  x::T
  function LocalFieldValuationRingElem(P::LocalFieldValuationRing{S, T}, a::T) where {S, T}
    r = new{S, T}(P, a)
  end
end

################################################################################
#
#  Residue ring
#
################################################################################

# Type for O/m^k where O is the valuation ring of the field F and m the maximal
# ideal
@attributes mutable struct LocalFieldValuationRingResidueRing{S <: NonArchLocalField, T <: NonArchLocalFieldElem} <: Ring
  R::LocalFieldValuationRing{S, T}
  k::Int

  function LocalFieldValuationRingResidueRing(R::LocalFieldValuationRing{S, T}, k::Int) where {S, T}
    return new{S, T}(R, k)
  end
end

mutable struct LocalFieldValuationRingResidueRingElem{S <: NonArchLocalField, T <: NonArchLocalFieldElem} <: RingElem
  a::T
  parent::LocalFieldValuationRingResidueRing{S, T}

  function LocalFieldValuationRingResidueRingElem(a::T, R::LocalFieldValuationRingResidueRing{S, T}) where {S, T}
    return new{S, T}(a, R)
  end
end
