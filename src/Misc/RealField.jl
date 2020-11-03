#TODO:
# check_parent
# hash
# elem_type  & friends
#

mutable struct RealField <: Nemo.Field
  K::AnticNumberField
  P::InfPlc

  function RealField(K::AnticNumberField, P::InfPlc)
    if !isreal(P)
      error("place is not real")
    end
    r = new()
    r.K = K
    r.P = P
    return r
  end
end

@doc Markdown.doc"""
    real_field(K::AnticNumberField, i::Int)

The real field using the $i$-th conjugate for evaluation and comparison.
$i$ has to define a real embedding.
"""
function real_field(K::AnticNumberField, i::Int)
  r1, r2 = signature(K)
  if i > r1 || i < 1
    error("$i does not define a real embedding")
  end
  P = infinite_places(K)[i]
  return RealField(K, P)
end

@doc Markdown.doc"""
    real_field(K::AnticNumberField, P::InfPlc)

The real field using the real place $P$ to define the embedding for
evaluation and comparison.
"""
function real_field(K::AnticNumberField, P::InfPlc)
  return RealField(K, P)
end

function show(io::IO, K::RealField)
  println(io, "RealField represented by $(K.parent.pol) and $(K.P)")
end

mutable struct RealFieldElem <: Nemo.FieldElem
  data::nf_elem
  parent::RealField
  function RealFieldElem(K::RealField, a::nf_elem)
    r = new()
    r.data = a
    r.parent = K
    return r
  end
end

function show(io::IO, e::RealFieldElem)
  println(io, "$(e.data) = ", evaluate(e.data, e.parent.P))
end

@doc Markdown.doc"""
    evaluate(a::nf_elem, P::InfPlc, p::Int = 20)

The evaluation of $a$ at the place $P$, i.e. a real or complex value.
$p$ specifies the precision to be returned.
"""
function evaluate(a::nf_elem, P::InfPlc, p::Int = 10)
  return conjugates_arb(a, p)[P.i]
end

@doc Markdown.doc"""
    evaluate(a::RealFieldElem, p::Int = 10)

The value of $a$ as a real number under the chosen embedding.
$p$ specifies the prescision of the result.
"""
function evaluate(a::RealFieldElem, p::Int = 10)
  return evaluate(a.data, a.parent.P, p)
end

function Base.isless(a::RealFieldElem, b::RealFieldElem)
  return sign(a.data-b.data, b.parent.P) < 0
end

Base.isless(a::RealFieldElem, b::Integer) = isless(a, a.parent(b))
Base.isless(a::RealFieldElem, b::fmpz) = isless(a, a.parent(b))
Base.isless(a::RealFieldElem, b::fmpq) = isless(a, a.parent(b))
Base.isless(a::Integer, b::RealFieldElem) = isless(b.parent(a), b)
Base.isless(a::fmpz, b::RealFieldElem) = isless(b.parent(a), b)
Base.isless(a::fmpq, b::RealFieldElem) = isless(b.parent(a), b)

Base.isequal(a::RealFieldElem, b::RealFieldElem) = isequal(a.data, b.data)

parent(a::RealFieldElem) = a.parent


==(a::RealFieldElem, b::RealFieldElem) = a.data == b.data
+(a::RealFieldElem, b::RealFieldElem) = RealFieldElem(a.parent, a.data+b.data)
-(a::RealFieldElem, b::RealFieldElem) = RealFieldElem(a.parent, a.data-b.data)
*(a::RealFieldElem, b::RealFieldElem) = RealFieldElem(a.parent, a.data*b.data)
//(a::RealFieldElem, b::RealFieldElem) = RealFieldElem(a.parent, a.data//b.data)
-(a::RealFieldElem) = RealFieldElem(a.parent, -a.data)
inv(a::RealFieldElem) = RealFieldElem(a.parent, inv(a.data))
*(a::Integer, b::RealFieldElem) = RealFieldElem(b.parent, a*b.data)
*(a::fmpz, b::RealFieldElem) = RealFieldElem(b.parent, a*b.data)
*(a::fmpq, b::RealFieldElem) = RealFieldElem(b.parent, a*b.data)
+(a::Integer, b::RealFieldElem) = RealFieldElem(b.parent, a+b.data)
+(a::fmpz, b::RealFieldElem) = RealFieldElem(b.parent, a+b.data)
+(a::fmpq, b::RealFieldElem) = RealFieldElem(b.parent, a+b.data)


(K::RealField)(a::nf_elem) = RealFieldElem(K, a)
(K::RealField)(a::Integer) = RealFieldElem(K, K.parent(a))
(K::RealField)(a::fmpz) = RealFieldElem(K, K.parent(a))
(K::RealField)(a::fmpq) = RealFieldElem(K, K.parent(a))
(K::RealField)(a::RealFieldElem) = RealFieldElem(K, a.data)
