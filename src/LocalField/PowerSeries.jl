################################################################################
#
# Power series wrapped as valuation rings
#
################################################################################

################################################################################
#
#  Parent type etc
#
################################################################################

parent_type(::Type{LaurentSeriesFieldValuationRingElem{S, T, U}}) where {S, T, U} = LaurentSeriesFieldValuationRing{S, T, U}
elem_type(::Type{LaurentSeriesFieldValuationRing{S, T, U}}) where {S, T, U} = LaurentSeriesFieldValuationRingElem{S, T, U}
is_domain_type(::Type{<: LaurentSeriesFieldValuationRingElem}) = true
is_exact_type(::Type{<: LaurentSeriesFieldValuationRingElem}) = false

################################################################################
#
#  Field access
#
################################################################################

_field(R::LaurentSeriesFieldValuationRing) = R.K
data(R::LaurentSeriesFieldValuationRing) = R.R

base_ring(R::LaurentSeriesFieldValuationRing) = Union{}
base_ring_type(::Type{<: LaurentSeriesFieldValuationRing}) = typeof(Union{})

parent(a::LaurentSeriesFieldValuationRingElem) = a.parent
data(a::LaurentSeriesFieldValuationRingElem) = a.a

################################################################################
#
#  Basic functionality
#
################################################################################

characteristic(R::LaurentSeriesFieldValuationRing) = characteristic(data(R))

function zero(Q::LaurentSeriesFieldValuationRing; precision::Int=precision(Q))
  return LaurentSeriesFieldValuationRingElem(Q, set_precision!(zero(data(Q)), precision))
end

function one(Q::LaurentSeriesFieldValuationRing; precision::Int=precision(Q))
  return LaurentSeriesFieldValuationRingElem(Q, set_precision!(one(data(Q)), precision))
end

is_zero(a::LaurentSeriesFieldValuationRingElem) = is_zero(data(a))
is_one(a::LaurentSeriesFieldValuationRingElem) = is_one(data(a))

valuation(a::LaurentSeriesFieldValuationRingElem) = valuation(data(a))
_valuation_integral(a::LaurentSeriesFieldValuationRingElem) = valuation(data(a))
uniformizer(R::LaurentSeriesFieldValuationRing) = R(uniformizer(_field(R)))

is_unit(a::LaurentSeriesFieldValuationRingElem) = !iszero(a) && valuation(a) == 0

function canonical_unit(a::LaurentSeriesFieldValuationRingElem)
  iszero(a) && return one(parent(a), precision = precision(a))
  v = valuation(a)
  pi = uniformizer(parent(a))
  return divexact(data(a), pi^v)
end

################################################################################
#
#  Precision
#
################################################################################

Base.precision(Q::LaurentSeriesFieldValuationRing) = max_precision(data(Q))
Base.precision(a::LaurentSeriesFieldValuationRingElem) = precision(data(a))

function setprecision!(Q::LaurentSeriesFieldValuationRing, n::Int)
  setprecision!(data(Q), n)
end

function Base.setprecision(a::LaurentSeriesFieldValuationRingElem, n::Int)
  return parent(a)(set_precision(data(a), n))
end

function setprecision!(a::LaurentSeriesFieldValuationRingElem, n::Int)
  a.a = set_precision!(data(a), n)
  return a
end

# TODO: Make this work (upstream)
#function with_precision(f, R::LaurentSeriesFieldValuationRing, n::Int)
#  return with_precision(f, data(R), n)
#end

################################################################################
#
#  Parent object overloading
#
################################################################################

function (Q::LaurentSeriesFieldValuationRing{S, T, U})(a::U) where {S, T, U}
  @assert parent(a) === data(Q)
  return LaurentSeriesFieldValuationRingElem(Q, a)
end

function (Q::LaurentSeriesFieldValuationRing)(a::Generic.LaurentSeriesFieldElem)
  @assert parent(a) === _field(Q)
  @req valuation(a) >= 0 "Not an element of the valuation ring"
  R = data(Q)
  c = zeros(base_ring(R), pol_length(a) * Generic.scale(a))
  for i in 0:pol_length(a) - 1
    c[Generic.scale(a) * i + 1] = polcoeff(a, i)
  end
  b = R(c, Generic.scale(a) * pol_length(a), precision(a), valuation(a))
  return Q(b)
end

(Q::LaurentSeriesFieldValuationRing)(a::LaurentSeriesFieldValuationRingElem) = LaurentSeriesFieldValuationRingElem(parent(a), data(a))

function (Q::LaurentSeriesFieldValuationRing)(a::Integer; precision::Int=precision(Q))
  aR = set_precision!(data(Q)(a), precision)
  return LaurentSeriesFieldValuationRingElem(Q, aR)
end

function (Q::LaurentSeriesFieldValuationRing)(a::ZZRingElem; precision::Int=precision(Q))
  aR = set_precision!(data(Q)(a), precision)
  return LaurentSeriesFieldValuationRingElem(Q, aR)
end

function (Q::LaurentSeriesFieldValuationRing)(; precision::Int=precision(Q))
  aR = set_precision!(data(Q)(), precision)
  return LaurentSeriesFieldValuationRingElem(Q, aR)
end

function (Q::LaurentSeriesFieldValuationRing)(a::FinFieldElem; precision::Int=precision(Q))
  @assert base_ring(data(Q)) === parent(a) "Fields don't match"
  aR = set_precision!(data(Q)(a), precision)
  return LaurentSeriesFieldValuationRingElem(Q, aR)
end

function (K::Generic.LaurentSeriesField)(a::LaurentSeriesFieldValuationRingElem)
  if _field(parent(a)) !== K
    error("Parent mismatch")
  end
  f = data(a)
  return K(
           [polcoeff(f, i) for i in 0:pol_length(f) - 1],
           pol_length(f), precision(f), valuation(f), 1
          )
end

################################################################################
#
#  Printing
#
################################################################################

function Base.show(io::IO, R::LaurentSeriesFieldValuationRing)
  @show_name(io, R)
  @show_special(io, R)

  print(pretty(io), "Valuation ring of ", Lowercase(), _field(R))
end

function Base.show(io::IO, a::LaurentSeriesFieldValuationRingElem)
  print(io, data(a))
end

function AbstractAlgebra.expressify(a::LaurentSeriesFieldValuationRingElem; context=nothing)
  return expressify(data(a); context=context)
end

################################################################################
#
#  Hashing / deepcopy
#
################################################################################

function Base.hash(a::LaurentSeriesFieldValuationRingElem, h::UInt)
  return hash(data(a), h)
end

function Base.deepcopy_internal(a::LaurentSeriesFieldValuationRingElem, dict::IdDict)
  return LaurentSeriesFieldValuationRingElem(parent(a), Base.deepcopy_internal(data(a), dict))
end

################################################################################
#
#  Comparison
#
################################################################################

==(a::LaurentSeriesFieldValuationRingElem, b::LaurentSeriesFieldValuationRingElem) = data(a) == data(b)

################################################################################
#
#  Unary operations
#
################################################################################

-(a::LaurentSeriesFieldValuationRingElem) = LaurentSeriesFieldValuationRingElem(parent(a), -data(a))

################################################################################
#
#  Binary operations
#
################################################################################

*(a::LaurentSeriesFieldValuationRingElem, b::LaurentSeriesFieldValuationRingElem) = LaurentSeriesFieldValuationRingElem(parent(a), data(a) * data(b))
+(a::LaurentSeriesFieldValuationRingElem, b::LaurentSeriesFieldValuationRingElem) = LaurentSeriesFieldValuationRingElem(parent(a), data(a) + data(b))
-(a::LaurentSeriesFieldValuationRingElem, b::LaurentSeriesFieldValuationRingElem) = LaurentSeriesFieldValuationRingElem(parent(a), data(a) - data(b))

################################################################################
#
#  Powering
#
################################################################################

function Base.:(^)(a::LaurentSeriesFieldValuationRingElem, e::Int)
  @req is_unit(a) || e >= 0 "Element is not invertible"
  return parent(a)(data(a)^e)
end

################################################################################
#
#  Divexact
#
################################################################################

function divexact(a::LaurentSeriesFieldValuationRingElem, b::LaurentSeriesFieldValuationRingElem; check::Bool=true)
  @assert !iszero(data(b))
  iszero(a) && return a
  valuation(data(a)) >= valuation(data(b)) || error("division not exact")
  return LaurentSeriesFieldValuationRingElem(parent(a), divexact(data(a), data(b)))
end

################################################################################
#
#  Divrem / gcd
#
################################################################################

function Base.divrem(a::LaurentSeriesFieldValuationRingElem, b::LaurentSeriesFieldValuationRingElem)
  @req parent(a) === parent(b) "Parents do not match"
  @req !is_zero(b) "Division by 0"
  if !is_zero(a) && valuation(data(a)) >= valuation(data(b))
    q = divexact(a, b)
    return q, a - q*b
  end
  return setprecision(parent(a)(0), precision(a)), a
end

function Base.div(a::LaurentSeriesFieldValuationRingElem, b::LaurentSeriesFieldValuationRingElem)
  if valuation(data(a)) < valuation(data(b))
    return setprecision(parent(a)(0), precision(a))
  end
  q = divexact(a, b)
  return q
end

function gcdx(a::LaurentSeriesFieldValuationRingElem, b::LaurentSeriesFieldValuationRingElem)
  if iszero(a)
    c = canonical_unit(b)
    return divexact(b, c), a, inv(c)
  end
  if iszero(b)
    c = canonical_unit(a)
    return divexact(a, c), inv(c), b
  end
  if valuation(data(a)) < valuation(data(b))
    c = canonical_unit(a)
    return divexact(a, c), inv(c), setprecision(parent(a)(0), precision(a))
  else
    c = canonical_unit(b)
    return divexact(b, c), setprecision(parent(b)(0), precision(b)), inv(c)
  end
end

################################################################################
#
#  Inverse
#
################################################################################

function inv(a::LaurentSeriesFieldValuationRingElem)
  @req is_unit(a) "Element is not invertible"
  return LaurentSeriesFieldValuationRingElem(parent(a), inv(data(a)))
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function zero!(a::LaurentSeriesFieldValuationRingElem)
  a.a = zero!(data(a))
  return a
end

function mul!(a::LaurentSeriesFieldValuationRingElem, b::LaurentSeriesFieldValuationRingElem, c::LaurentSeriesFieldValuationRingElem)
  a.a = mul!(data(a), data(b), data(c))
  return a
end

function add!(a::LaurentSeriesFieldValuationRingElem, b::LaurentSeriesFieldValuationRingElem, c::LaurentSeriesFieldValuationRingElem)
  a.a = add!(data(a), data(b), data(c))
  return a
end

################################################################################
#
#  Promotion
#
################################################################################

AbstractAlgebra.promote_rule(::Type{LaurentSeriesFieldValuationRingElem{S, T, U}}, ::Type{LaurentSeriesFieldValuationRingElem{S, T, U}}) where {S, T, U} = LaurentSeriesFieldValuationRingElem{S, T, U}

function AbstractAlgebra.promote_rule(::Type{LaurentSeriesFieldValuationRingElem{S, T, U}}, ::Type{V}) where {S, T, U, V <: RingElement}
  AbstractAlgebra.promote_rule(U, V) == U ? LaurentSeriesFieldValuationRingElem{S, T, U} : Union{}
end

################################################################################
#
#  Construction
#
################################################################################

@attr LaurentSeriesFieldValuationRing{typeof(K), relative_power_series_ring_type(T), relative_power_series_type(T)} function valuation_ring(K::Generic.LaurentSeriesField{T}) where {T <: FinFieldElem }
  return LaurentSeriesFieldValuationRing(K)
end

# TODO: move this upstream (and generalize it)
relative_power_series_type(::Type{FqFieldElem}) = FqRelPowerSeriesRingElem
relative_power_series_type(::Type{fpFieldElem}) = fpRelPowerSeriesRingElem
relative_power_series_type(::Type{FpFieldElem}) = FpRelPowerSeriesRingElem
relative_power_series_type(::Type{fqPolyRepFieldElem}) = fqPolyRepRelPowerSeriesRingElem
relative_power_series_type(::Type{FqPolyRepFieldElem}) = FqPolyRepRelPowerSeriesRingElem
relative_power_series_ring_type(T::Type{<:FinFieldElem}) = parent_type(relative_power_series_type(T))
