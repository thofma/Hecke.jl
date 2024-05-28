################################################################################
#
# (q/p)adic integers
#
# complete enough to support hnf
################################################################################
# CHECK precision!!!

function Base.show(io::IO, Q::LocalFieldValuationRing)
  print("Integers of ", Q.Q)
end

function MaximalOrder(Q::QadicField)
  return LocalFieldValuationRing{QadicField, QadicFieldElem}(Q)
end

function MaximalOrder(Q::PadicField)
  return LocalFieldValuationRing{PadicField, PadicFieldElem}(Q)
end
#integers(Q::QadicField) = ring_of_integers(Q)
function MaximalOrder(Q::LocalField{S, T}) where {S, T <: Union{EisensteinLocalField, UnramifiedLocalField}}
  return LocalFieldValuationRing{LocalField{S, T}, LocalFieldElem{S, T}}(Q)
end
#integers(Q::PadicField) = ring_of_integers(Q)

valuation_ring(K::NonArchLocalField) = MaximalOrder(K)

uniformizer(R::LocalFieldValuationRing) = R(uniformizer(R.Q))

function Base.show(io::IO, a::LocalFieldValuationRingElem)
  print(io, a.x)
end

*(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem) = LocalFieldValuationRingElem(a.P, a.x*b.x)
+(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem) = LocalFieldValuationRingElem(a.P, a.x+b.x)
-(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem) = LocalFieldValuationRingElem(a.P, a.x-b.x)
-(a::LocalFieldValuationRingElem) = LocalFieldValuationRingElem(a.P, -a.x)
^(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem) = LocalFieldValuationRingElem(a.P, a.x^b.x)
^(a::T, b::LocalFieldValuationRingElem{S, T}) where {S, T} = a^b.x

function inv(a::LocalFieldValuationRingElem)
  valuation(a.x) == 0 || error("The element is not invertible!")
  return LocalFieldValuationRingElem(a.P, inv(a.x))
end

==(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem) = a.x == b.x

function divexact(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem; check::Bool=true)
  @assert !iszero(b.x)
  iszero(a) && return a
  valuation(a.x) >= valuation(b.x) || error("division not exact")
  return LocalFieldValuationRingElem(a.P, a.x//b.x)
end

function Base.divrem(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem)
  if valuation(a.x) < valuation(b.x)
    return setprecision(a.P(0), precision(a)), a
  end
  q = divexact(a, b)
  return q, a-q*b
end

function Base.div(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem)
  if valuation(a.x) < valuation(b.x)
    return setprecision(a.P(0), precision(a))
  end
  q = divexact(a, b)
  return q
end

parent(a::LocalFieldValuationRingElem) = a.P
elem_type(::Type{LocalFieldValuationRing{S, T}}) where {S, T} = LocalFieldValuationRingElem{S, T}
parent_type(::Type{LocalFieldValuationRingElem{S, T}}) where {S, T} = LocalFieldValuationRing{S, T}

function zero(Q::LocalFieldValuationRing; precision::Int=precision(Q))
  return LocalFieldValuationRingElem(Q, zero(Q.Q, precision = precision))
end

function one(Q::LocalFieldValuationRing; precision::Int=precision(Q))
  return LocalFieldValuationRingElem(Q, one(Q.Q, precision = precision))
end

function (Q::LocalFieldValuationRing{S, T})(a::T) where {S, T}
  @assert parent(a) === Q.Q
  LocalFieldValuationRingElem(Q, a)
end
(Q::LocalFieldValuationRing)(a::LocalFieldValuationRingElem) = LocalFieldValuationRingElem(a.P, a.x)

function (Q::LocalFieldValuationRing)(a::Integer; precision::Int=precision(Q))
  return LocalFieldValuationRingElem(Q, Q.Q(a, precision = precision))
end

function (Q::LocalFieldValuationRing)(a::ZZRingElem; precision::Int=precision(Q))
  return LocalFieldValuationRingElem(Q, Q.Q(a, precision = precision))
end

function (Q::LocalFieldValuationRing)(a::QQFieldElem; precision::Int=precision(Q))
  p = prime(Q.Q)
  if iszero(mod(denominator(a), p))
    error("The element is not in the ring!")
  end
  return LocalFieldValuationRingElem(Q, Q.Q(a, precision = precision))
end

(Q::LocalFieldValuationRing)() = LocalFieldValuationRingElem(Q, Q.Q())

function (Q::Union{PadicField, QadicField, LocalField})(a::LocalFieldValuationRingElem)
  if parent(a).Q !== Q
    error("Parent mismatch")
  end
  return a.x
end

valuation(a::LocalFieldValuationRingElem) = valuation(a.x)
is_unit(a::LocalFieldValuationRingElem) = !iszero(a) && valuation(a) == 0
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

function Base.deepcopy_internal(a::LocalFieldValuationRingElem, dict::IdDict)
  return LocalFieldValuationRingElem(a.P, a.x)
end

function canonical_unit(a::LocalFieldValuationRingElem)
  iszero(a.x) && return setprecision(a.P(1), precision(a))
  v = valuation(a.x)
  return LocalFieldValuationRingElem(a.P, inv(a.x//prime(a.P.Q)^v))
end

function gcdx(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem)
  if iszero(a)
    c = canonical_unit(b)
    return b*c, a, c
  end
  if iszero(b)
    c = canonical_unit(a)
    return a*c, c, b
  end
  if valuation(a.x) < valuation(b.x)
    c = canonical_unit(a)
    return a*c, c, setprecision(a.P(0), precision(a))
  else
    c = canonical_unit(b)
    return b*c, setprecision(b.P(0), precision(b)), c
  end
end

function mul_red!(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem, c::LocalFieldValuationRingElem, f::Bool = false)
  return b*c
end

function mul!(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem, c::LocalFieldValuationRingElem)
  return b*c
end

function add!(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem, c::LocalFieldValuationRingElem)
  return b+c
end

function addeq!(a::LocalFieldValuationRingElem, b::LocalFieldValuationRingElem)
  return a+b
end

Base.iszero(a::LocalFieldValuationRingElem) = iszero(a.x)
Base.isone(a::LocalFieldValuationRingElem) = isone(a.x)

Base.precision(Q::LocalFieldValuationRing) = precision(Q.Q)
Base.precision(a::LocalFieldValuationRingElem) = precision(a.x)

function setprecision!(Q::LocalFieldValuationRing, n::Int)
  setprecision!(Q.Q, n)
end

function Base.setprecision(a::LocalFieldValuationRingElem, n::Int)
  return a.P(setprecision(a.x, n))
end

function setprecision!(a::LocalFieldValuationRingElem, n::Int)
  a.x = setprecision!(a.x, n)
end

function Base.setprecision(a::Generic.MatSpaceElem{LocalFieldValuationRingElem{QadicFieldElem}}, n::Int)
  return map_entries(x -> setprecision(x, n), a)
end

coefficient_ring(Q::LocalFieldValuationRing) = ring_of_integers(coefficient_ring(Q.Q))

coefficient_ring(K::LocalField) = base_field(K)

function absolute_coordinates(a::LocalFieldValuationRingElem)
  v = absolute_coordinates(a.x)
  Zp = ring_of_integers(prime_field(parent(a.x)))
  return Zp.(v)
end

function absolute_coordinates(Zp::LocalFieldValuationRing, a::LocalFieldValuationRingElem)
  v = absolute_coordinates(Zp.Q, a.x)
  return Zp.(v)
end

AbstractAlgebra.promote_rule(::Type{LocalFieldValuationRingElem{S, T}}, ::Type{LocalFieldValuationRingElem{S, T}}) where {S, T} = LocalFieldValuationRingElem{S, T}

function AbstractAlgebra.promote_rule(::Type{LocalFieldValuationRingElem{S, T}}, ::Type{U}) where {S, T, U <: RingElement}
  AbstractAlgebra.promote_rule(T, U) == T ? LocalFieldValuationRingElem{S, T} : Union{}
end
