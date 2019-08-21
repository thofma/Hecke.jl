################################################################################
#
# (q/p)adic integers
# 
# complete enough to support hnf
################################################################################
# CHECK precision!!!

struct QadicRing{T} <: Generic.Ring
  Q::T
end

function Base.show(io::IO, Q::QadicRing)
  println("Integers of ", Q.Q)
end

function MaximalOrder(Q::FlintQadicField)
  return QadicRing{FlintQadicField}(Q)
end
#integers(Q::FlintQadicField) = ring_of_integers(Q)

function MaximalOrder(Q::FlintPadicField)
  return QadicRing{FlintPadicField}(Q)
end
#integers(Q::FlintPadicField) = ring_of_integers(Q)

struct QadicRingElem{S} <: RingElem
  x::S
  P::QadicRing
  function QadicRingElem(a::qadic, P::QadicRing)
    r = new{qadic}(a, P)
  end
  function QadicRingElem(a::padic, P::QadicRing)
    r = new{padic}(a, P)
  end
end

function Base.show(io::IO, a::QadicRingElem)
  print(io, a.x)
end
  
*(a::QadicRingElem, b::QadicRingElem) = QadicRingElem(a.x*b.x, a.P)
+(a::QadicRingElem, b::QadicRingElem) = QadicRingElem(a.x+b.x, a.P)
-(a::QadicRingElem, b::QadicRingElem) = QadicRingElem(a.x-b.x, a.P)
-(a::QadicRingElem) = QadicRingElem(-a.x, a.P)
^(a::QadicRingElem, b::QadicRingElem) = QadicRingElem(a.x^b.x, a.P)
^(a::T, b::QadicRingElem{T}) where {T} = a^b.x

function inv(a::QadicRingElem) 
  valuation(a.x) == 0 || error("non unit")
  return QadicRingElem(inv(a.x), a.P)
end

==(a::QadicRingElem, b::QadicRingElem) = a.x == b.x 

function divexact(a::QadicRingElem, b::QadicRingElem)
  @assert !iszero(b.x)
  iszero(a) && return a
  valuation(a.x) >= valuation(b.x) || error("division not exact")
  return QadicRingElem(a.x//b.x, a.P)
end

function divrem(a::QadicRingElem, b::QadicRingElem)
  if valuation(a.x) < valuation(b.x)
    return setprecision(a.P(0), precision(a)), a 
  end
  q = divexact(a, b)
  return q, a-q*b
end

function Base.div(a::QadicRingElem, b::QadicRingElem)
  if valuation(a.x) < valuation(b.x)
    return setprecision(a.P(0), precision(a))
  end
  q = divexact(a, b)
  return q
end

parent(a::QadicRingElem) = a.P
elem_type(::Type{QadicRing{FlintPadicField}}) = QadicRingElem{padic}
elem_type(::Type{QadicRing{FlintQadicField}}) = QadicRingElem{qadic}
parent_type(::Type{QadicRingElem{padic}}) = QadicRing{FlintPadicField}
parent_type(::Type{QadicRingElem{qadic}}) = QadicRing{FlintQadicField}

zero(Q::QadicRing) = QadicRingElem(Q.Q(0), Q)
one(Q::QadicRing) = QadicRingElem(Q.Q(1), Q)

(Q::QadicRing)(a::qadic) = QadicRingElem(a, Q)
(Q::QadicRing)(a::padic) = QadicRingElem(a, Q)
(Q::QadicRing)(a::QadicRingElem) = QadicRingElem(a.x, a.P)
(Q::QadicRing)(a::Int) = QadicRingElem(Q.Q(a), Q)
(Q::QadicRing)() = QadicRingElem(Q.Q(), Q)
(Q::FlintQadicField)(a::QadicRingElem{qadic}) = a.x
(Q::FlintPadicField)(a::QadicRingElem{padic}) = a.x
(Q::FlintQadicField)(a::padic) = Q(lift(a)) #TODO: do properly
valuation(a::QadicRingElem) = valuation(a.x)
isunit(a::QadicRingElem) = valuation(a) == 0
function Base.deepcopy_internal(a::QadicRingElem, dict::IdDict)
  return QadicRingElem(a.x, a.P)
end
function canonical_unit(a::QadicRingElem)
  iszero(a.x) && return setprecision(a.P(1), precision(a))
  v = valuation(a.x)
  return QadicRingElem(inv(a.x//prime(a.P.Q)^v), a.P)
end

function gcdx(a::QadicRingElem, b::QadicRingElem)
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

function mul_red!(a::QadicRingElem, b::QadicRingElem, c::QadicRingElem, f::Bool = false)
  return b*c
end

function mul!(a::QadicRingElem, b::QadicRingElem, c::QadicRingElem)
  return b*c
end

function add!(a::QadicRingElem, b::QadicRingElem, c::QadicRingElem)
  return b+c
end

function addeq!(a::QadicRingElem, b::QadicRingElem)
  return a+b
end

Base.iszero(a::QadicRingElem) = iszero(a.x)
Base.isone(a::QadicRingElem) = isone(a.x)

Base.precision(Q::QadicRing) = precision(Q.Q)
Base.precision(a::QadicRingElem) = precision(a.x)
function setprecision!(Q::QadicRing, n::Int) 
  setprecision!(Q.Q, n)
end

function Base.setprecision(a::QadicRingElem, n::Int)
  return a.P(setprecision(a.x, n))
end

function setprecision!(a::QadicRingElem, n::Int)
  setprecision!(a.x, n)
end

function Base.setprecision(a::Generic.MatSpaceElem{QadicRingElem{qadic}}, n::Int)
  return matrix(map(x -> setprecision(x, n), a.entries))
end

coefficient_ring(Q::QadicRing) = integers(coefficient_ring(Q.Q))


