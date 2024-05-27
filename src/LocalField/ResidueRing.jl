################################################################################
#
#  Parent type etc
#
################################################################################

parent_type(::Type{PadicResidueRingElem{S, T}}) where {S, T} = PadicResidueRing{T}
elem_type(::Type{PadicResidueRing{T}}) where {T} = PadicResidueRingElem{elem_type(T), T}
is_domain_type(::Type{<: PadicResidueRing}) = false
is_exact_type(::Type{<: PadicResidueRing}) = true

################################################################################
#
#  Field access
#
################################################################################

_field(R::PadicResidueRing) = R.F # TODO: how to call this?
_exponent(R::PadicResidueRing) = R.k

# TODO: implement base_ring(::PadicResidueRing)? Should this return the field or the valuation ring?
base_ring(R::PadicResidueRing) = Union{}
base_ring_type(::Type{<: PadicResidueRing}) = typeof(Union{})

parent(a::PadicResidueRingElem) = a.parent
data(a::PadicResidueRingElem) = a.a

################################################################################
#
#  Basic functionality
#
################################################################################

characteristic(R::PadicResidueRing) = prime(_field(R))^_exponent(R)

zero(R::PadicResidueRing) = R()
one(R::PadicResidueRing) = R(one(_field(R), precision = _exponent(R)), copy = false)

is_zero(a::PadicResidueRingElem) = is_zero(data(a))
is_one(a::PadicResidueRingElem) = is_one(data(a))

function is_unit(a::PadicResidueRingElem)
  is_zero(a) && return false
  return is_zero(valuation(data(a)))
end
is_zero_divisor(a::PadicResidueRingElem) = !is_unit(a)

function canonical_unit(a::PadicResidueRingElem)
  if is_unit(a)
    return a
  end
  return one(parent(a))
end

################################################################################
#
#  Parent object overloading
#
################################################################################

(R::PadicResidueRing)() = R(zero(_field(R), precision = _exponent(R)), copy = false)

function (R::PadicResidueRing)(a::Union{Integer, ZZRingElem, QQFieldElem, Rational})
  @req is_zero(a) || valuation(a, prime(_field(R))) >= 0 "Not an element of the valuation ring"
  return R(_field(R)(a, precision = _exponent(R)), copy = false)
end

function (R::PadicResidueRing)(a::PadicResidueRingElem)
  @req parent(a) === R "The given element is not an element of the ring"
  return a
end

function (R::PadicResidueRing)(a::NonArchLocalFieldElem; copy::Bool = true)
  @req parent(a) === _field(R) "Local fields don't match"
  @req precision(a) >= _exponent(R) "Insufficient precision"
  # Make sure that we have unique representatives
  if copy
    b = setprecision(a, _exponent(R))
  else
    b = setprecision!(a, _exponent(R))
  end
  return PadicResidueRingElem(b, R)
end

################################################################################
#
#  Printing
#
################################################################################

function Base.show(io::IO, mime::MIME"text/plain", R::PadicResidueRing)
  @show_name(io, R)
  @show_special(io, mime, R)

  io = pretty(io)
  println(io, "Residue ring of valuation ring of")
  println(io, Indent(), _field(R), Dedent())
  print(io, "modulo the maximal ideal to the power ", _exponent(R))
end

function Base.show(io::IO, R::PadicResidueRing)
  @show_name(io, R)
  @show_special(io, R)

  if is_terse(io)
    print(io, "Residue ring of non-archimedean local ring")
  else
    print(io, "Residue ring of ")
    print(terse(io), _field(R))
    print(io, " to the power ", _exponent(R))
  end
end

# TODO: Improve
Base.show(io::IO, a::PadicResidueRingElem) = show(io, data(a))
Base.show(io::IO, a::PadicResidueRingElem{PadicFieldElem}) = show(io, lift(ZZ, data(a)))

################################################################################
#
#  Hashing / deepcopy
#
################################################################################

function Base.deepcopy_internal(a::PadicResidueRingElem{S, T}, dict::IdDict) where {S, T}
  return PadicResidueRingElem(Base.deepcopy_internal(data(a), dict), parent(a))
end

function Base.hash(a::PadicResidueRingElem, h::UInt)
  return hash(data(a), h)
end

################################################################################
#
#  Comparison
#
################################################################################

function Base.:(==)(a::PadicResidueRingElem, b::PadicResidueRingElem)
  @req parent(a) === parent(b) "Parents do not match"
  return data(a) == data(b)
end

################################################################################
#
#  Unary operations
#
################################################################################

function Base.:(-)(a::PadicResidueRingElem)
  return parent(a)(-data(a), copy = false)
end

################################################################################
#
#  Binary operations
#
################################################################################

function Base.:(+)(a::PadicResidueRingElem, b::PadicResidueRingElem)
  @req parent(a) === parent(b) "Parents do not match"
  return parent(a)(data(a) + data(b), copy = false)
end

function Base.:(-)(a::PadicResidueRingElem, b::PadicResidueRingElem)
  @req parent(a) === parent(b) "Parents do not match"
  return parent(a)(data(a) - data(b), copy = false)
end

function Base.:(*)(a::PadicResidueRingElem, b::PadicResidueRingElem)
  @req parent(a) === parent(b) "Parents do not match"
  return parent(a)(data(a) * data(b), copy = false)
end

################################################################################
#
#  Powering
#
################################################################################

function Base.:(^)(a::PadicResidueRingElem, e::Int)
  @req is_unit(a) || e >= 0 "Element is not invertible"
  return parent(a)(data(a)^e, copy = false)
end

################################################################################
#
#  Divexact
#
################################################################################

function divexact(a::PadicResidueRingElem, b::PadicResidueRingElem)
  @req parent(a) === parent(b) "Parents do not match"
  @req valuation(data(a)) >= valuation(data(b)) "Division not possible"
  c = divexact(data(a), data(b))
  setprecision!(c, _exponent(parent(a)))
  return parent(a)(c, copy = false)
end

################################################################################
#
#  Divrem
#
################################################################################

function Base.divrem(a::PadicResidueRingElem, b::PadicResidueRingElem)
  @req parent(a) === parent(b) "Parents do not match"
  @req !is_zero(b) "Division by 0"
  if valuation(data(a)) >= valuation(data(b))
    return divexact(a, b), zero(parent(a))
  end
  return zero(parent(a)), b
end

################################################################################
#
#  Inverse
#
################################################################################

function inv(a::PadicResidueRingElem)
  @req is_unit(a) "Element is not invertible"
  return parent(a)(inv(data(a)), copy = false)
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function zero!(a::PadicResidueRingElem)
  a.a = zero!(data(a))
  return a
end

function mul!(c::PadicResidueRingElem, a::PadicResidueRingElem, b::PadicResidueRingElem)
  @req parent(a) === parent(b) === parent(c) "Parents do not match"
  c.a = mul!(data(c), data(a), data(b))
  return c
end

function add!(c::PadicResidueRingElem, a::PadicResidueRingElem, b::PadicResidueRingElem)
  @req parent(a) === parent(b) === parent(c) "Parents do not match"
  c.a = add!(data(c), data(a), data(b))
  return c
end

function addeq!(a::PadicResidueRingElem, b::PadicResidueRingElem)
  @req parent(a) === parent(b) "Parents do not match"
  a.a = addeq!(data(a), data(b))
  return a
end

################################################################################
#
#  Promotion
#
################################################################################

AbstractAlgebra.promote_rule(::Type{PadicResidueRingElem{S, T}}, ::Type{PadicResidueRingElem{S, T}}) where {S, T} = PadicResidueRingElem{S, T}

function AbstractAlgebra.promote_rule(::Type{PadicResidueRingElem{S, T}}, ::Type{U}) where {S, T, U <: RingElement}
  AbstractAlgebra.promote_rule(S, U) == S ? PadicResidueRingElem{S, T} : Union{}
end

################################################################################
#
#  Construction
#
################################################################################

# TODO: What should the user constructor be?
# * residue_ring(::Field, ::Int)
# * residue_ring(::Ring, ::Int)
# * residue_ring(::Ring, ::Ideal)
# * ?
# where Field = the local field, Ring = the valuation ring, and Ideal = the
# desired power of the maximal ideal

