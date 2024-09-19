################################################################################
#
# (q/p)adic integers
#
# complete enough to support hnf
################################################################################
# CHECK precision!!!

################################################################################
#
#  Parent type etc
#
################################################################################

parent_type(::Type{LocalFieldValuationRingElem{S, T}}) where {S, T} = LocalFieldValuationRing{S, T}
elem_type(::Type{LocalFieldValuationRing{S, T}}) where {S, T} = LocalFieldValuationRingElem{S, T}
is_domain_type(::Type{<: LocalFieldValuationRingElem}) = true
is_exact_type(::Type{<: LocalFieldValuationRingElem}) = false

################################################################################
#
#  Field access
#
################################################################################

_field(R::LocalFieldValuationRing) = R.Q

base_ring(R::LocalFieldValuationRing) = Union{}
base_ring_type(::Type{<: LocalFieldValuationRing}) = typeof(Union{})

parent(a::LocalFieldValuationRingElem) = a.P
data(a::LocalFieldValuationRingElem) = a.x

################################################################################
#
#  Basic functionality
#
################################################################################

characteristic(R::LocalFieldValuationRing) = 0

function zero(Q::LocalFieldValuationRing; precision::Int=precision(Q))
  return LocalFieldValuationRingElem(Q, zero(_field(Q), precision = precision))
end

function one(Q::LocalFieldValuationRing; precision::Int=precision(Q))
  return LocalFieldValuationRingElem(Q, one(_field(Q), precision = precision))
end

is_zero(a::LocalFieldValuationRingElem) = is_zero(data(a))
is_one(a::LocalFieldValuationRingElem) = is_one(data(a))

valuation(a::LocalFieldValuationRingElem) = valuation(data(a))
_valuation_integral(a::LocalFieldValuationRingElem) = _valuation_integral(data(a))
uniformizer(R::LocalFieldValuationRing) = R(uniformizer(_field(R)))

is_unit(a::LocalFieldValuationRingElem) = !iszero(a) && valuation(a) == 0

function canonical_unit(a::LocalFieldValuationRingElem)
  iszero(data(a)) && return setprecision(parent(a)(1), precision(a))
  v = ZZ(absolute_ramification_index(_field(parent(a)))*valuation(data(a)))
  pi = uniformizer(_field(parent(a)))
  return LocalFieldValuationRingElem(parent(a), data(a)//pi^v)
end

################################################################################
#
#  Precision
#
################################################################################

Base.precision(Q::LocalFieldValuationRing) = precision(_field(Q))
Base.precision(a::LocalFieldValuationRingElem) = precision(data(a))

function setprecision!(Q::LocalFieldValuationRing, n::Int)
  setprecision!(_field(Q), n)
end

function Base.setprecision(a::LocalFieldValuationRingElem, n::Int)
  return parent(a)(setprecision(data(a), n))
end

function setprecision!(a::LocalFieldValuationRingElem, n::Int)
  a.x = setprecision!(data(a), n)
  return a
end

function Base.setprecision(a::Generic.MatSpaceElem{LocalFieldValuationRingElem{QadicFieldElem}}, n::Int)
  return map_entries(x -> setprecision(x, n), a)
end

function with_precision(f, R::LocalFieldValuationRing, n::Int)
  return with_precision(f, _field(R), n)
end

################################################################################
#
#  Coefficients
#
################################################################################

coefficient_ring(Q::LocalFieldValuationRing) = valuation_ring(base_field(_field(Q)))

function absolute_coordinates(a::LocalFieldValuationRingElem)
  v = absolute_coordinates(data(a))
  Zp = ring_of_integers(base_field(parent(data(a))))
  return Zp.(v)
end

function absolute_coordinates(Zp::LocalFieldValuationRing, a::LocalFieldValuationRingElem)
  v = absolute_coordinates(_field(Zp), data(a))
  return Zp.(v)
end

################################################################################
#
#  Parent object overloading
#
################################################################################

function (Q::LocalFieldValuationRing{S, T})(a::T; check::Bool = true) where {S, T}
  @req parent(a) === _field(Q) "Fields do not match"
  if check
    @req is_zero(a) || valuation(a) >= 0 "Not an element of the valuation ring"
  end
  return LocalFieldValuationRingElem(Q, a)
end

(Q::LocalFieldValuationRing)(a::LocalFieldValuationRingElem) = LocalFieldValuationRingElem(parent(a), data(a))

function (Q::LocalFieldValuationRing)(a::Integer; precision::Int=precision(Q))
  return LocalFieldValuationRingElem(Q, _field(Q)(a, precision = precision))
end

function (Q::LocalFieldValuationRing)(a::ZZRingElem; precision::Int=precision(Q))
  return LocalFieldValuationRingElem(Q, _field(Q)(a, precision = precision))
end

function (Q::LocalFieldValuationRing)(a::QQFieldElem; precision::Int=precision(Q))
  p = prime(_field(Q))
  if iszero(mod(denominator(a), p))
    error("The element is not in the ring!")
  end
  return LocalFieldValuationRingElem(Q, _field(Q)(a, precision = precision))
end

(Q::LocalFieldValuationRing)(; precision::Int=precision(_field(Q))) = LocalFieldValuationRingElem(Q, _field(Q)(precision = precision))

function (Q::Union{PadicField, QadicField, LocalField})(a::LocalFieldValuationRingElem)
  if _field(parent(a)) !== Q
    error("Parent mismatch")
  end
  return data(a)
end

(Q::QadicField)(a::PadicFieldElem) =  _map(Q, a) #TODO: do properly

function _map(Q::QadicField, a::PadicFieldElem)
  K = parent(a)
  @assert prime(K) == prime(Q)
  v = valuation(a)
  if v >= 0
    q = Q(lift(ZZ, a))
    return setprecision(q, a.N)
  else
    d = uniformizer(K)^-v
    n = a*d
    n1 = divexact(Q(lift(ZZ, n)), Q(lift(ZZ, d)))
    return n1
  end
end

################################################################################
#
#  Printing
#
################################################################################

function Base.show(io::IO, R::LocalFieldValuationRing)
  @show_name(io, R)
  @show_special(io, R)

  print(pretty(io), "Valuation ring of ", Lowercase(), _field(R))
end

function Base.show(io::IO, a::LocalFieldValuationRingElem)
  print(io, data(a))
end

function AbstractAlgebra.expressify(a::LocalFieldValuationRingElem; context=nothing)
  return expressify(data(a); context=context)
end

################################################################################
#
#  Hashing / deepcopy
#
################################################################################

function Base.hash(a::LocalFieldValuationRingElem, h::UInt)
  return hash(data(a), h)
end

function Base.deepcopy_internal(a::LocalFieldValuationRingElem, dict::IdDict)
  return LocalFieldValuationRingElem(parent(a), Base.deepcopy_internal(data(a), dict))
end

################################################################################
#
#  Comparison
#
################################################################################

==(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem) = data(a) == data(b)

################################################################################
#
#  Unary operations
#
################################################################################

-(a::LocalFieldValuationRingElem) = LocalFieldValuationRingElem(parent(a), -data(a))

################################################################################
#
#  Binary operations
#
################################################################################

*(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem) = LocalFieldValuationRingElem(parent(a), data(a) * data(b))
+(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem) = LocalFieldValuationRingElem(parent(a), data(a) + data(b))
-(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem) = LocalFieldValuationRingElem(parent(a), data(a) - data(b))

################################################################################
#
#  Powering
#
################################################################################

^(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem) = LocalFieldValuationRingElem(parent(a), data(a)^data(b))
^(a::T, b::LocalFieldValuationRingElem{S, T}) where {S, T} = a^data(b)

function Base.:(^)(a::LocalFieldValuationRingElem, e::Int)
  @req is_unit(a) || e >= 0 "Element is not invertible"
  return parent(a)(data(a)^e)
end

################################################################################
#
#  Divexact
#
################################################################################

function divexact(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem; check::Bool=true)
  @assert !iszero(data(b))
  iszero(a) && return a
  valuation(data(a)) >= valuation(data(b)) || error("division not exact")
  return LocalFieldValuationRingElem(parent(a), data(a)//data(b))
end

################################################################################
#
#  Divrem / gcd
#
################################################################################

function Base.divrem(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem)
  @req parent(a) === parent(b) "Parents do not match"
  @req !is_zero(b) "Division by 0"
  if !is_zero(a) && valuation(data(a)) >= valuation(data(b))
    q = divexact(a, b)
    return q, a - q*b
  end
  return setprecision(parent(a)(0), precision(a)), a
end

function Base.div(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem)
  if valuation(data(a)) < valuation(data(b))
    return setprecision(parent(a)(0), precision(a))
  end
  q = divexact(a, b)
  return q
end

function gcdx(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem)
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

function inv(a::LocalFieldValuationRingElem)
  @req is_unit(a) "Element is not invertible"
  return LocalFieldValuationRingElem(parent(a), inv(data(a)))
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function zero!(a::LocalFieldValuationRingElem)
  a.x = zero!(data(a))
  return a
end

function mul_red!(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem, c::LocalFieldValuationRingElem, f::Bool = false)
  a.x = mul_red!(data(a), data(b), data(c), f)
  return a
end

function mul!(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem, c::LocalFieldValuationRingElem)
  a.x = mul!(data(a), data(b), data(c))
  return a
end

function add!(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem, c::LocalFieldValuationRingElem)
  a.x = add!(data(a), data(b), data(c))
  return a
end

################################################################################
#
#  Promotion
#
################################################################################

AbstractAlgebra.promote_rule(::Type{LocalFieldValuationRingElem{S, T}}, ::Type{LocalFieldValuationRingElem{S, T}}) where {S, T} = LocalFieldValuationRingElem{S, T}

function AbstractAlgebra.promote_rule(::Type{LocalFieldValuationRingElem{S, T}}, ::Type{U}) where {S, T, U <: RingElement}
  AbstractAlgebra.promote_rule(T, U) == T ? LocalFieldValuationRingElem{S, T} : Union{}
end

################################################################################
#
#  Construction
#
################################################################################

@attr LocalFieldValuationRing{T, elem_type(T)} function valuation_ring(K::T) where {T <: NonArchLocalField}
  return LocalFieldValuationRing{T, elem_type(T)}(K)
end

MaximalOrder(K::NonArchLocalField) = valuation_ring(K)
