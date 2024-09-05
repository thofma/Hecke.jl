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
  precision_base::Int # precision of the defining polynomial
  precision_times_ramification_index::Int # precision_base * ramification index,
                                          # this is the precision that is used
                                          # for "exact input"
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

const NonArchLocalFieldTypes = Union{PadicField, QadicField, LocalField, Generic.LaurentSeriesField{<: FinFieldElem}}
const NonArchLocalFieldElemTypes = Union{PadicFieldElem, QadicFieldElem, LocalFieldElem, Generic.LaurentSeriesFieldElem{<: FinFieldElem}}

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

abstract type NonArchLocalFieldValuationRing <: Ring end
abstract type NonArchLocalFieldValuationRingElem <: RingElem end

@attributes mutable struct LocalFieldValuationRing{S, T} <: NonArchLocalFieldValuationRing
  Q::S #The corresponding local field
  basis::Vector{T} #The OK-basis of the ring, where OK is
                   #the maximal order of the base field of Q
  function LocalFieldValuationRing{S, T}(x::S) where {S <: NonArchLocalField, T}
    z = new{S, T}()
    z.Q = x
    return z
  end

end

mutable struct LocalFieldValuationRingElem{S, T} <: NonArchLocalFieldValuationRingElem
  P::LocalFieldValuationRing{S, T}
  x::T
  function LocalFieldValuationRingElem(P::LocalFieldValuationRing{S, T}, a::T) where {S, T}
    r = new{S, T}(P, a)
  end
end

# Wrap PowerSeriesRing as a dedicated "valuation ring" type

@attributes mutable struct LaurentSeriesFieldValuationRing{FieldType, RingType, RingElemType} <: NonArchLocalFieldValuationRing
  K::FieldType # the Laurent series field
  R::RingType # the power series ring

  function LaurentSeriesFieldValuationRing(K::Generic.LaurentSeriesField{<:FinFieldElem})
    R, _ = power_series_ring(base_ring(K), max_precision(K), var(K), cached = false)
    return new{typeof(K), typeof(R), elem_type(R)}(K, R)
  end
end

mutable struct LaurentSeriesFieldValuationRingElem{FieldType, SeriesRingType, SeriesType} <: NonArchLocalFieldValuationRingElem
  parent::LaurentSeriesFieldValuationRing{FieldType, SeriesRingType, SeriesType}
  a::SeriesType # a power series

  function LaurentSeriesFieldValuationRingElem(R::LaurentSeriesFieldValuationRing{S, T, U}, a::U) where {S, T, U}
    return new{S, T, U}(R, a)
  end
end

################################################################################
#
#  Residue ring
#
################################################################################

# Type for O/m^k where O is a valuation ring and m the maximal ideal
# TODO: Should this be called NonArchLocalFieldValuationRingResidueRing?
@attributes mutable struct LocalFieldValuationRingResidueRing{S <: NonArchLocalFieldValuationRing, T <: NonArchLocalFieldValuationRingElem} <: Ring
  R::S
  k::Int

  function LocalFieldValuationRingResidueRing(R::S, k::Int) where S
    return new{S, elem_type(S)}(R, k)
  end
end

mutable struct LocalFieldValuationRingResidueRingElem{S <: NonArchLocalFieldValuationRing, T <: NonArchLocalFieldValuationRingElem} <: RingElem
  a::T
  parent::LocalFieldValuationRingResidueRing{S, T}

  function LocalFieldValuationRingResidueRingElem(a::T, R::LocalFieldValuationRingResidueRing{S, T}) where {S, T}
    return new{S, T}(a, R)
  end
end
