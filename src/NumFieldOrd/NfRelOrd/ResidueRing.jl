################################################################################
#
#  Field access
#
################################################################################

function elem_type(::Type{RelOrdQuoRing{T1, T2, T3}}) where { T1, T2, T3 }
  S = elem_type(T1)
  return RelOrdQuoRingElem{T1, T2, T3, S}
end

base_ring(Q::RelOrdQuoRing) = Q.base_ring

base_ring_type(::Type{RelOrdQuoRing{T1, T2, T3}}) where {T1, T2, T3} = T1

ideal(Q::RelOrdQuoRing) = Q.ideal

basis_pmatrix(Q::RelOrdQuoRing) = Q.basis_pmatrix

parent(x::RelOrdQuoRingElem) = x.parent

parent_type(::Type{RelOrdQuoRingElem{T1, T2, T3, S}}) where { T1, T2, T3, S } = RelOrdQuoRing{T1, T2, T3}

################################################################################
#
#  Hashing
#
################################################################################

hash(x::RelOrdQuoRingElem, h::UInt) = hash(x.elem, h)

################################################################################
#
#  Copying
#
################################################################################

Base.deepcopy_internal(x::RelOrdQuoRingElem, dict::IdDict) =
        RelOrdQuoRingElem(parent(x), Base.deepcopy_internal(x.elem, dict))

################################################################################
#
#  Lifting
#
################################################################################

lift(x::RelOrdQuoRingElem) = x.elem

################################################################################
#
#  I/O
#
################################################################################

function show(io::IO, Q::RelOrdQuoRing)
  print(io, "Quotient of $(base_ring(Q))")
end

function show(io::IO, x::RelOrdQuoRingElem)
  print(io, "$(x.elem)")
end

################################################################################
#
#  Parent object overloading
#
################################################################################

function (Q::RelOrdQuoRing{T1, T2, T3})(x::RelOrdQuoRingElem{T1, T2, T3, S}) where { T1, T2, T3, S }
  parent(x) !== Q && error("Cannot coerce element into quotient ring")
  return x
end

function (Q::RelOrdQuoRing{T1, T2, T3})(x::S) where { T1, T2, T3, S }
  parent(x) !== base_ring(Q) && error("Cannot coerce element into the quotient ring")
  return RelOrdQuoRingElem(Q, x)
end

function (Q::RelOrdQuoRing)(x::Integer)
  return Q(base_ring(Q)(x))
end

function (Q::RelOrdQuoRing)(x::ZZRingElem)
  return Q(base_ring(Q)(x))
end

################################################################################
#
#  Quotient function
#
################################################################################

function quo(O::Union{RelNumFieldOrder, AlgAssRelOrd}, I::Union{RelNumFieldOrderIdeal, AlgAssRelOrdIdl})
  @assert order(I) === O
  # We should check that I is not zero
  Q = RelOrdQuoRing(O, I)
  f = RelOrdQuoMap(O, Q)
  return Q, f
end

Nemo.residue_ring(O::Union{RelNumFieldOrder, AlgAssRelOrd}, I::Union{RelNumFieldOrderIdeal, AlgAssRelOrdIdl}) = RelOrdQuoRing(O, I)

################################################################################
#
#  Arithmetic
#
################################################################################

function +(x::RelOrdQuoRingElem, y::RelOrdQuoRingElem)
  check_parent(x, y)
  return parent(x)(x.elem + y.elem)
end

function -(x::RelOrdQuoRingElem, y::RelOrdQuoRingElem)
  check_parent(x, y)
  return parent(x)(x.elem - y.elem)
end

function -(x::RelOrdQuoRingElem)
  return parent(x)(-x.elem)
end

function *(x::RelOrdQuoRingElem, y::RelOrdQuoRingElem)
  check_parent(x, y)
  return parent(x)(x.elem * y.elem)
end

function mul!(z::RelOrdQuoRingElem, x::RelOrdQuoRingElem, y::RelOrdQuoRingElem)
  z.elem = mul!(z.elem, x.elem, y.elem)
  z.elem = mod!(z.elem, parent(z))
  return z
end

function add!(z::RelOrdQuoRingElem, x::RelOrdQuoRingElem, y::RelOrdQuoRingElem)
  z.elem = add!(z.elem, x.elem, y.elem)
  z.elem = mod!(z.elem, parent(z))
  return z
end

function *(x::Integer, y::RelOrdQuoRingElem)
  return parent(y)(x * y.elem)
end

*(x::RelOrdQuoRingElem, y::Integer) = y*x

function *(x::ZZRingElem, y::RelOrdQuoRingElem)
  return parent(y)(x * y.elem)
end

*(x::RelOrdQuoRingElem, y::ZZRingElem) = y*x

function ^(a::RelOrdQuoRingElem, f::ZZRingElem)
  if fits(Int, f)
    return a^Int(f)
  end
  f == 0 && return one(parent(a))
  f == 1 && return deepcopy(a)
  if f < 0
    f = -f
    a = inv(a)
  end
  b = a^(div(f, 2))
  b *= b
  if isodd(f)
    b *= a
  end
  return b
end

function ^(a::RelOrdQuoRingElem, b::Int)
  if b == 0
    return one(parent(a))
  elseif b == 1
    return deepcopy(a)
  else
    if b < 0
      a = inv(a)
      b = -b
    end
    bit = ~((~UInt(0)) >> 1)
    while (UInt(bit) & b) == 0
      bit >>= 1
    end
    z = deepcopy(a)
    bit >>= 1
    while bit != 0
      z = mul!(z, z, z)
      if (UInt(bit) & b) != 0
        z = mul!(z, z, a)
      end
      bit >>= 1
    end
    return z
  end
end

################################################################################
#
#  Special elements
#
################################################################################

iszero(x::RelOrdQuoRingElem) = iszero(x.elem)

isone(x::RelOrdQuoRingElem) = isone(x.elem)

function one(Q::RelOrdQuoRing)
  return Q(one(base_ring(Q)))
end

function zero(Q::RelOrdQuoRing)
  return Q(zero(base_ring(Q)))
end

################################################################################
#
#  Equality
#
################################################################################

==(x::RelOrdQuoRingElem, y::RelOrdQuoRingElem) = parent(x) === parent(y) && x.elem == y.elem
