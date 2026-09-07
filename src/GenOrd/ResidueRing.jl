################################################################################
#
#  GenOrd/ResidueRing.jl : Quotients of generic orders
#
################################################################################

################################################################################
#
#  Field access
#
################################################################################

function elem_type(::Type{GenOrdQuoRing{S, T}}) where {S, T}
  U = elem_type(S)
  return GenOrdQuoRingElem{S, T, U}
end

base_ring(Q::GenOrdQuoRing) = Q.base_ring

base_ring_type(::Type{GenOrdQuoRing{S, T}}) where {S, T} = S

ideal(Q::GenOrdQuoRing) = Q.ideal

basis_matrix(Q::GenOrdQuoRing) = Q.basis_matrix

parent(x::GenOrdQuoRingElem) = x.parent

parent_type(::Type{GenOrdQuoRingElem{S, T, U}}) where {S, T, U} = GenOrdQuoRing{S, T}

(Q::GenOrdQuoRing)() = zero(Q)

canonical_unit(x::GenOrdQuoRingElem) = one(parent(x))

################################################################################
#
#  Hashing
#
################################################################################

hash(x::GenOrdQuoRingElem, h::UInt) = hash(parent(x), hash(x.elem, h))

################################################################################
#
#  Copying
#
################################################################################

Base.deepcopy_internal(x::GenOrdQuoRingElem, dict::IdDict) =
        GenOrdQuoRingElem(parent(x), Base.deepcopy_internal(x.elem, dict))

################################################################################
#
#  I/O
#
################################################################################

# TODO: better show function
function show(io::IO, Q::GenOrdQuoRing)
  io = pretty(io)
  print(io, "Quotient of ", Lowercase(), base_ring(Q))
end

function AbstractAlgebra.expressify(x::GenOrdQuoRingElem; context = nothing)
  return AbstractAlgebra.expressify(x.elem, context = context)
end

@enable_all_show_via_expressify GenOrdQuoRingElem

################################################################################
#
#  Parent object overloading
#
################################################################################

function (Q::GenOrdQuoRing{S, T})(x::U) where {S, T, U <: GenOrdElem}
  base_ring(Q) !== parent(x) && error("Cannot coerce element into the quotient ring")
  return GenOrdQuoRingElem(Q, x)
end

function (Q::GenOrdQuoRing{S, T})(x::GenOrdQuoRingElem) where {S, T}
  Q !== parent(x) && error("Cannot coerce element into the quotient ring")
  return x
end

function (Q::GenOrdQuoRing)(x::RingElement)
  return GenOrdQuoRingElem(Q, base_ring(Q)(x))
end

################################################################################
#
#  Quotient function
#
################################################################################

function quo(O::GenOrd, I::GenOrdIdl)
  @req order(I) === O "Ideal must be an ideal of the order"
  Q = GenOrdQuoRing(O, I)
  f = GenOrdQuoMap(O, Q)
  return Q, f
end

residue_ring(O::GenOrd, I::GenOrdIdl) = GenOrdQuoRing(O, I)

lift(a::GenOrdQuoRingElem) = a.elem

function lift(O::GenOrd, a::GenOrdQuoRingElem)
  @req base_ring(parent(a)) === O "Wrong order"
  return a.elem
end

################################################################################
#
#  Arithmetic
#
################################################################################

function +(x::GenOrdQuoRingElem{S, T, U}, y::GenOrdQuoRingElem{S, T, U}) where {S, T, U}
  check_parent(x, y)
  Q = parent(x)
  return Q(x.elem + y.elem)
end

function -(x::GenOrdQuoRingElem{S, T, U}, y::GenOrdQuoRingElem{S, T, U}) where {S, T, U}
  check_parent(x, y)
  Q = parent(x)
  return Q(x.elem - y.elem)
end

function -(x::GenOrdQuoRingElem)
  return parent(x)(-x.elem)
end

function *(x::GenOrdQuoRingElem, y::GenOrdQuoRingElem)
  check_parent(x, y)
  Q = parent(x)
  return Q(x.elem * y.elem)
end

function mul!(z::GenOrdQuoRingElem, x::GenOrdQuoRingElem, y::GenOrdQuoRingElem)
  z.elem = mod(x.elem * y.elem, ideal(parent(z)))
  return z
end

function add!(z::GenOrdQuoRingElem, x::GenOrdQuoRingElem, y::GenOrdQuoRingElem)
  z.elem = mod(x.elem + y.elem, ideal(parent(z)))
  return z
end

function sub!(z::GenOrdQuoRingElem, x::GenOrdQuoRingElem, y::GenOrdQuoRingElem)
  z.elem = mod(x.elem - y.elem, ideal(parent(z)))
  return z
end

function *(x::IntegerUnion, y::GenOrdQuoRingElem)
  Q = parent(y)
  return Q(x*y.elem)
end

*(x::GenOrdQuoRingElem, y::IntegerUnion) = y*x

function ^(a::GenOrdQuoRingElem, b::Int)
  @req b >= 0 "Negative powers are not supported"
  if b == 0
    return one(parent(a))
  elseif b == 1
    return deepcopy(a)
  end
  bit = ~((~UInt(0)) >> 1)
  while (UInt(bit) & b) == 0
    bit >>= 1
  end
  z = deepcopy(a)
  bit >>= 1
  while bit != 0
    z = z*z
    if (UInt(bit) & b) != 0
      z = z*a
    end
    bit >>= 1
  end
  return z
end

################################################################################
#
#  Special elements
#
################################################################################

iszero(x::GenOrdQuoRingElem) = iszero(x.elem)

isone(x::GenOrdQuoRingElem) = x == one(parent(x))

function one(Q::GenOrdQuoRing)
  return deepcopy(Q.one)::elem_type(Q)
end

function zero(Q::GenOrdQuoRing)
  return GenOrdQuoRingElem(Q, zero(base_ring(Q)))
end

function zero!(x::GenOrdQuoRingElem)
  x.elem = zero(base_ring(parent(x)))
  return x
end

function ConformanceTests.generate_element(R::GenOrdQuoRing)
  S = base_ring(R)
  return R(S([rand(base_ring(S), 0:10) for _ in 1:degree(S)]))
end

################################################################################
#
#  Equality
#
################################################################################

function ==(x::GenOrdQuoRingElem, y::GenOrdQuoRingElem)
  parent(x) !== parent(y) && return false
  return x.elem == y.elem
end
