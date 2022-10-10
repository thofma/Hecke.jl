################################################################################
#
# (q/p)adic integers
#
# complete enough to support hnf
################################################################################
# CHECK precision!!!

mutable struct QadicRing{S, T} <: Generic.Ring
  Q::S #The corresponding local field
  basis::Vector{T} #The OK-basis of the ring, where OK is
                   #the maximal order of the base field of Q
  function QadicRing{S, T}(x::S) where {S <: Union{LocalField, FlintQadicField, FlintPadicField}, T}
    z = new{S, T}()
    z.Q = x
    return z
  end

end

function Base.show(io::IO, Q::QadicRing)
  println("Integers of ", Q.Q)
end

function MaximalOrder(Q::FlintQadicField)
  return QadicRing{FlintQadicField, qadic}(Q)
end

function MaximalOrder(Q::FlintPadicField)
  return QadicRing{FlintPadicField, padic}(Q)
end
#integers(Q::FlintQadicField) = ring_of_integers(Q)
function MaximalOrder(Q::LocalField{S, T}) where {S, T <: Union{EisensteinLocalField, UnramifiedLocalField}}
  return QadicRing{LocalField{S, T}, LocalFieldElem{S, T}}(Q)
end
#integers(Q::FlintPadicField) = ring_of_integers(Q)

mutable struct QadicRingElem{S, T} <: RingElem
  P::QadicRing{S, T}
  x::T
  function QadicRingElem(P::QadicRing{S, T}, a::T) where {S, T}
    r = new{S, T}(P, a)
  end
end

function Base.show(io::IO, a::QadicRingElem)
  print(io, a.x)
end

*(a::QadicRingElem, b::QadicRingElem) = QadicRingElem(a.P, a.x*b.x)
+(a::QadicRingElem, b::QadicRingElem) = QadicRingElem(a.P, a.x+b.x)
-(a::QadicRingElem, b::QadicRingElem) = QadicRingElem(a.P, a.x-b.x)
-(a::QadicRingElem) = QadicRingElem(a.P, -a.x)
^(a::QadicRingElem, b::QadicRingElem) = QadicRingElem(a.P, a.x^b.x)
^(a::T, b::QadicRingElem{S, T}) where {S, T} = a^b.x

function inv(a::QadicRingElem)
  valuation(a.x) == 0 || error("The element is not invertible!")
  return QadicRingElem(a.P, inv(a.x))
end

==(a::QadicRingElem, b::QadicRingElem) = a.x == b.x

function divexact(a::QadicRingElem, b::QadicRingElem)
  @assert !iszero(b.x)
  iszero(a) && return a
  valuation(a.x) >= valuation(b.x) || error("division not exact")
  return QadicRingElem(a.P, a.x//b.x)
end

function Base.divrem(a::QadicRingElem, b::QadicRingElem)
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
elem_type(::Type{QadicRing{S, T}}) where {S, T} = QadicRingElem{S, T}
parent_type(::Type{QadicRingElem{S, T}}) where {S, T} = QadicRing{S, T}

zero(Q::QadicRing) = QadicRingElem(Q, Q.Q(0))
one(Q::QadicRing) = QadicRingElem(Q, Q.Q(1))

(Q::QadicRing{S, T})(a::T) where {S, T} = QadicRingElem(Q, a)
(Q::QadicRing)(a::QadicRingElem) = QadicRingElem(a.P, a.x)
(Q::QadicRing)(a::Integer) = QadicRingElem(Q, Q.Q(a))
(Q::QadicRing)(a::fmpz) = QadicRingElem(Q, Q.Q(a))

function (Q::QadicRing)(a::fmpq)
  p = prime(Q.Q)
  if iszero(mod(denominator(a), p))
    error("The element is not in the ring!")
  end
  return QadicRingElem(Q, Q.Q(a))
end

(Q::QadicRing)() = QadicRingElem(Q, Q.Q())


(Q::LocalField{S, T})(a::QadicRingElem{S, T}) where {S, T} = a.x
(Q::FlintPadicField)(a::QadicRingElem{FlintPadicField, padic}) = a.x
(Q::FlintQadicField)(a::QadicRingElem{FlintQadicField, qadic}) = a.x


valuation(a::QadicRingElem) = valuation(a.x)
is_unit(a::QadicRingElem) = !iszero(a) && valuation(a) == 0
(Q::FlintQadicField)(a::padic) =  _map(Q, a) #TODO: do properly



function _map(Q::FlintQadicField, a::padic)
  K = parent(a)
  v = valuation(a)
  if v >= 0
    q = Q(lift(a))
    return setprecision(q, a.N)
  else
    d = uniformizer(K)^-v
    n = a*d
    n1 = divexact(Q(lift(n)), Q(lift(d)))
    return n1
  end
end

function Base.deepcopy_internal(a::QadicRingElem, dict::IdDict)
  return QadicRingElem(a.P, a.x)
end

function canonical_unit(a::QadicRingElem)
  iszero(a.x) && return setprecision(a.P(1), precision(a))
  v = valuation(a.x)
  return QadicRingElem(a.P, inv(a.x//prime(a.P.Q)^v))
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
  a.x = setprecision!(a.x, n)
end

function Base.setprecision(a::Generic.MatSpaceElem{QadicRingElem{qadic}}, n::Int)
  return map_entries(x -> setprecision(x, n), a)
end

coefficient_ring(Q::QadicRing) = integers(coefficient_ring(Q.Q))



