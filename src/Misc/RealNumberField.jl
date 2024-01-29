#TODO:
# check_parent
# hash
# elem_type  & friends
#

mutable struct RealNumberField <: Nemo.Field
  K::AbsSimpleNumField
  P::InfPlc

  function RealNumberField(K::AbsSimpleNumField, P::InfPlc)
    if !isreal(P)
      error("place is not real")
    end
    r = new()
    r.K = K
    r.P = P
    return r
  end
end

@doc raw"""
    real_number_field(K::AbsSimpleNumField, i::Int)

The real field using the $i$-th conjugate for evaluation and comparison.
$i$ has to define a real embedding.
"""
function real_number_field(K::AbsSimpleNumField, i::Int)
  r1, r2 = signature(K)
  if i > r1 || i < 1
    error("$i does not define a real embedding")
  end
  P = infinite_places(K)[i]
  return RealNumberField(K, P)
end

@doc raw"""
    real_number_field(K::AbsSimpleNumField, P::InfPlc)

The real field using the real place $P$ to define the embedding for
evaluation and comparison.
"""
function real_number_field(K::AbsSimpleNumField, P::InfPlc)
  return RealNumberField(K, P)
end

function show(io::IO, K::RealNumberField)
  println(io, "RealNumberField represented by $(K.parent.pol) and $(K.P)")
end

mutable struct RealNumberFieldElem <: Nemo.FieldElem
  data::AbsSimpleNumFieldElem
  parent::RealNumberField
  function RealNumberFieldElem(K::RealNumberField, a::AbsSimpleNumFieldElem)
    r = new()
    r.data = a
    r.parent = K
    return r
  end
end

function show(io::IO, e::RealNumberFieldElem)
  println(io, "$(e.data) = ", evaluate(e.data, e.parent.P))
end

@doc raw"""
    evaluate(a::RealNumberFieldElem, p::Int = 10)

The value of $a$ as a real number under the chosen embedding.
$p$ specifies the prescision of the result.
"""
function evaluate(a::RealNumberFieldElem, p::Int = 10)
  return evaluate(a.data, a.parent.P, p)
end

function Base.isless(a::RealNumberFieldElem, b::RealNumberFieldElem)
  return sign(a.data-b.data, b.parent.P) < 0
end

Base.isless(a::RealNumberFieldElem, b::Integer) = isless(a, a.parent(b))
Base.isless(a::RealNumberFieldElem, b::ZZRingElem) = isless(a, a.parent(b))
Base.isless(a::RealNumberFieldElem, b::QQFieldElem) = isless(a, a.parent(b))
Base.isless(a::Integer, b::RealNumberFieldElem) = isless(b.parent(a), b)
Base.isless(a::ZZRingElem, b::RealNumberFieldElem) = isless(b.parent(a), b)
Base.isless(a::QQFieldElem, b::RealNumberFieldElem) = isless(b.parent(a), b)

Base.isequal(a::RealNumberFieldElem, b::RealNumberFieldElem) = isequal(a.data, b.data)

parent(a::RealNumberFieldElem) = a.parent


==(a::RealNumberFieldElem, b::RealNumberFieldElem) = a.data == b.data
+(a::RealNumberFieldElem, b::RealNumberFieldElem) = RealNumberFieldElem(a.parent, a.data+b.data)
-(a::RealNumberFieldElem, b::RealNumberFieldElem) = RealNumberFieldElem(a.parent, a.data-b.data)
*(a::RealNumberFieldElem, b::RealNumberFieldElem) = RealNumberFieldElem(a.parent, a.data*b.data)
//(a::RealNumberFieldElem, b::RealNumberFieldElem) = RealNumberFieldElem(a.parent, a.data//b.data)
-(a::RealNumberFieldElem) = RealNumberFieldElem(a.parent, -a.data)
inv(a::RealNumberFieldElem) = RealNumberFieldElem(a.parent, inv(a.data))
*(a::Integer, b::RealNumberFieldElem) = RealNumberFieldElem(b.parent, a*b.data)
*(a::ZZRingElem, b::RealNumberFieldElem) = RealNumberFieldElem(b.parent, a*b.data)
*(a::QQFieldElem, b::RealNumberFieldElem) = RealNumberFieldElem(b.parent, a*b.data)
+(a::Integer, b::RealNumberFieldElem) = RealNumberFieldElem(b.parent, a+b.data)
+(a::ZZRingElem, b::RealNumberFieldElem) = RealNumberFieldElem(b.parent, a+b.data)
+(a::QQFieldElem, b::RealNumberFieldElem) = RealNumberFieldElem(b.parent, a+b.data)


(K::RealNumberField)(a::AbsSimpleNumFieldElem) = RealNumberFieldElem(K, a)
(K::RealNumberField)(a::Integer) = RealNumberFieldElem(K, K.parent(a))
(K::RealNumberField)(a::ZZRingElem) = RealNumberFieldElem(K, K.parent(a))
(K::RealNumberField)(a::QQFieldElem) = RealNumberFieldElem(K, K.parent(a))
(K::RealNumberField)(a::RealNumberFieldElem) = RealNumberFieldElem(K, a.data)
