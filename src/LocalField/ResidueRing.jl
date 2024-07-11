################################################################################
#
#  Parent type etc
#
################################################################################

parent_type(::Type{LocalFieldValuationRingResidueRingElem{S, T}}) where {S, T} = LocalFieldValuationRingResidueRing{S, T}
elem_type(::Type{LocalFieldValuationRingResidueRing{S, T}}) where {S, T} = LocalFieldValuationRingResidueRingElem{S, T}
is_domain_type(::Type{<: LocalFieldValuationRingResidueRingElem}) = false
is_exact_type(::Type{<: LocalFieldValuationRingResidueRingElem}) = true

################################################################################
#
#  Field access
#
################################################################################

_valuation_ring(R::LocalFieldValuationRingResidueRing) = R.R
_field(R::LocalFieldValuationRingResidueRing) = _valuation_ring(R).Q
_exponent(R::LocalFieldValuationRingResidueRing) = R.k

base_ring(R::LocalFieldValuationRingResidueRing) = Union{}
base_ring_type(::Type{<: LocalFieldValuationRingResidueRing}) = typeof(Union{})

parent(a::LocalFieldValuationRingResidueRingElem) = a.parent
data(a::LocalFieldValuationRingResidueRingElem) = a.a
lift(a::LocalFieldValuationRingResidueRingElem) = _valuation_ring(parent(a))(data(a))

################################################################################
#
#  Basic functionality
#
################################################################################

characteristic(R::LocalFieldValuationRingResidueRing) = prime(_field(R))^_exponent(R)

zero(R::LocalFieldValuationRingResidueRing) = R()
one(R::LocalFieldValuationRingResidueRing) = R(one(_valuation_ring(R), precision = _exponent(R)), copy = false)

is_zero(a::LocalFieldValuationRingResidueRingElem) = is_zero(data(a))
is_one(a::LocalFieldValuationRingResidueRingElem) = is_one(data(a))

function is_unit(a::LocalFieldValuationRingResidueRingElem)
  is_zero(a) && return false
  return is_zero(valuation(data(a)))
end
is_zero_divisor(a::LocalFieldValuationRingResidueRingElem) = !is_unit(a)

function canonical_unit(a::LocalFieldValuationRingResidueRingElem)
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

(R::LocalFieldValuationRingResidueRing)() = R(zero(_valuation_ring(R), precision = _exponent(R)), copy = false)

function (R::LocalFieldValuationRingResidueRing)(a::Union{Integer, ZZRingElem, QQFieldElem, Rational})
  return R(_valuation_ring(R)(a, precision = _exponent(R)), copy = false)
end

function (R::LocalFieldValuationRingResidueRing)(a::LocalFieldValuationRingResidueRingElem)
  @req parent(a) === R "The given element is not an element of the ring"
  return a
end

function (R::LocalFieldValuationRingResidueRing)(a::LocalFieldValuationRingElem; copy::Bool = true)
  @req parent(a) === _valuation_ring(R) "Rings don't match"
  return R(a.x, copy = copy)
end

function (R::LocalFieldValuationRingResidueRing)(a::NonArchLocalFieldElem; copy::Bool = true, check::Bool = true)
  @req parent(a) === _field(R) "Fields don't match"
  if check
    @req precision(a) >= _exponent(R) "Insufficient precision"
    @req is_zero(a) || valuation(a) >= 0 "Not an element of the valuation ring"
  end
  # Make sure that we have unique representatives
  if copy
    b = setprecision(a, _exponent(R))
  else
    b = setprecision!(a, _exponent(R))
  end
  return LocalFieldValuationRingResidueRingElem(b, R)
end

################################################################################
#
#  Printing
#
################################################################################

function Base.show(io::IO, R::LocalFieldValuationRingResidueRing)
  @show_name(io, R)
  @show_special(io, R)

  print(io, _valuation_ring(R), " modulo ", uniformizer(_field(R)), "^", _exponent(R))
end

function AbstractAlgebra.expressify(x::LocalFieldValuationRingResidueRingElem{PadicField}; context = nothing)
  p = BigInt(prime(_field(parent(x))))
  sum = Expr(:call, :+)
  v = valuation(data(x))
  u = BigInt(lift(ZZ, data(x)))
  if v > 0
    u = div(u, p^v)
  end
  d = digits(u, base=p)
  for i in 0:length(d)-1
    ppower = Expr(:call, :^, p, i + v)
    push!(sum.args, Expr(:call, :*, d[i + 1], ppower))
  end
  return sum
end

function AbstractAlgebra.expressify(a::LocalFieldValuationRingResidueRingElem{QadicField}, x = var(_field(parent(a))); context = nothing)
  b = data(a)
  K = base_field(parent(b))
  if iszero(b)
    return 0
  end
  p = BigInt(prime(K))
  sum = Expr(:call, :+)
  c = K(precision = precision(parent(b)))
  for i in degree(parent(b)):-1:0
    ccall((:padic_poly_get_coeff_padic, libflint), Nothing,
          (Ref{PadicFieldElem}, Ref{QadicFieldElem}, Int, Ref{QadicField}),
          c, b, i, parent(b))

    # expressify c (without + O(...))
    ec = Expr(:call, :+)
    v = valuation(c)
    u = BigInt(lift(ZZ, c))
    if v > 0
      u = div(u, p^v)
    end
    d = digits(u, base=p)
    for i in 0:length(d)-1
      ppower = Expr(:call, :^, p, i + v)
      push!(ec.args, Expr(:call, :*, d[i + 1], ppower))
    end

    if !iszero(c)
      if iszero(i)
        push!(sum.args, ec)
      elseif isone(i)
        push!(sum.args, Expr(:call, :*, ec, x))
      else
        push!(sum.args, Expr(:call, :*, ec, Expr(:call, :^, x, i)))
      end
    end
  end
  return sum
end

function show(io::IO, a::LocalFieldValuationRingResidueRingElem{<:Union{PadicField, QadicField}})
  print(io, AbstractAlgebra.obj_to_string(a, context = io))
end

Base.show(io::IO, a::LocalFieldValuationRingResidueRingElem) = show(io, data(a))

################################################################################
#
#  Hashing / deepcopy
#
################################################################################

function Base.deepcopy_internal(a::LocalFieldValuationRingResidueRingElem, dict::IdDict)
  return LocalFieldValuationRingResidueRingElem(Base.deepcopy_internal(data(a), dict), parent(a))
end

function Base.hash(a::LocalFieldValuationRingResidueRingElem, h::UInt)
  return hash(data(a), h)
end

################################################################################
#
#  Comparison
#
################################################################################

function Base.:(==)(a::LocalFieldValuationRingResidueRingElem, b::LocalFieldValuationRingResidueRingElem)
  @req parent(a) === parent(b) "Parents do not match"
  return data(a) == data(b)
end

################################################################################
#
#  Unary operations
#
################################################################################

function Base.:(-)(a::LocalFieldValuationRingResidueRingElem)
  return parent(a)(-data(a), copy = false, check = false)
end

################################################################################
#
#  Binary operations
#
################################################################################

function Base.:(+)(a::LocalFieldValuationRingResidueRingElem, b::LocalFieldValuationRingResidueRingElem)
  @req parent(a) === parent(b) "Parents do not match"
  return parent(a)(data(a) + data(b), copy = false, check = false)
end

function Base.:(-)(a::LocalFieldValuationRingResidueRingElem, b::LocalFieldValuationRingResidueRingElem)
  @req parent(a) === parent(b) "Parents do not match"
  return parent(a)(data(a) - data(b), copy = false, check = false)
end

function Base.:(*)(a::LocalFieldValuationRingResidueRingElem, b::LocalFieldValuationRingResidueRingElem)
  @req parent(a) === parent(b) "Parents do not match"
  return parent(a)(data(a) * data(b), copy = false, check = false)
end

################################################################################
#
#  Powering
#
################################################################################

function Base.:(^)(a::LocalFieldValuationRingResidueRingElem, e::Int)
  @req is_unit(a) || e >= 0 "Element is not invertible"
  return parent(a)(data(a)^e, copy = false, check = false)
end

################################################################################
#
#  Divexact
#
################################################################################

function divexact(a::LocalFieldValuationRingResidueRingElem, b::LocalFieldValuationRingResidueRingElem)
  @req parent(a) === parent(b) "Parents do not match"
  @req !is_zero(b) "Division by 0"
  if is_zero(a)
    return zero(parent(a))
  end
  @req valuation(data(a)) >= valuation(data(b)) "Division not possible"
  c = divexact(data(a), data(b))
  setprecision!(c, _exponent(parent(a)))
  return parent(a)(c, copy = false, check = false)
end

################################################################################
#
#  Divrem
#
################################################################################

function Base.divrem(a::LocalFieldValuationRingResidueRingElem, b::LocalFieldValuationRingResidueRingElem)
  @req parent(a) === parent(b) "Parents do not match"
  @req !is_zero(b) "Division by 0"
  if !is_zero(a) && valuation(data(a)) >= valuation(data(b))
    return divexact(a, b), zero(parent(a))
  end
  return zero(parent(a)), a
end

function _canonicalize_gcdxx(g::T, u::T, v::T, s::T, t::T) where {T <: LocalFieldValuationRingResidueRingElem}
  e = canonical_unit(g)
  is_one(e) && return g, u, v, s, t
  g = divexact(g, e)
  u = divexact(u, e)
  v = divexact(v, e)
  s *= e
  t *= e
  return g, u, v, s, t
end

# Return g, u, v, s, t with g = gcd(a, b), g = u*a + v*b, 0 = s*a + t*b and u*t - v*s = 1
function AbstractAlgebra.gcdxx(a::LocalFieldValuationRingResidueRingElem, b::LocalFieldValuationRingResidueRingElem)
  @req parent(a) === parent(b) "Parents do not match"

  R = parent(a)
  if is_zero(b)
    return _canonicalize_gcdxx(a, one(R), zero(R), zero(R), one(R))
  end
  if is_zero(a)
    return _canonicalize_gcdxx(b, zero(R), one(R), -one(R), zero(R))
  end

  if valuation(data(a)) > valuation(data(b))
    return _canonicalize_gcdxx(b, zero(R), one(R), -one(R), divexact(a, b))
  end
  return _canonicalize_gcdxx(a, one(R), zero(R), -divexact(b, a), one(R))
end

function annihilator(a::LocalFieldValuationRingResidueRingElem)
  if is_zero(a)
    return one(parent(a))
  end
  pi = uniformizer(_valuation_ring(parent(a)))
  va = absolute_ramification_index(_field(parent(a)))*valuation(data(a))
  return parent(a)(pi)^ZZ(_exponent(parent(a)) - va)
end

################################################################################
#
#  Inverse
#
################################################################################

function inv(a::LocalFieldValuationRingResidueRingElem)
  @req is_unit(a) "Element is not invertible"
  return parent(a)(inv(data(a)), copy = false, check = false)
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function zero!(a::LocalFieldValuationRingResidueRingElem)
  a.a = zero!(data(a))
  return a
end

function mul!(c::LocalFieldValuationRingResidueRingElem, a::LocalFieldValuationRingResidueRingElem, b::LocalFieldValuationRingResidueRingElem)
  @req parent(a) === parent(b) === parent(c) "Parents do not match"
  c.a = mul!(data(c), data(a), data(b))
  c.a = setprecision!(c.a, _exponent(parent(a)))
  return c
end

function add!(c::LocalFieldValuationRingResidueRingElem, a::LocalFieldValuationRingResidueRingElem, b::LocalFieldValuationRingResidueRingElem)
  @req parent(a) === parent(b) === parent(c) "Parents do not match"
  c.a = add!(data(c), data(a), data(b))
  c.a = setprecision!(c.a, _exponent(parent(a)))
  return c
end

function addeq!(a::LocalFieldValuationRingResidueRingElem, b::LocalFieldValuationRingResidueRingElem)
  @req parent(a) === parent(b) "Parents do not match"
  a.a = addeq!(data(a), data(b))
  a.a = setprecision!(a.a, _exponent(parent(a)))
  return a
end

################################################################################
#
#  Promotion
#
################################################################################

AbstractAlgebra.promote_rule(::Type{LocalFieldValuationRingResidueRingElem{S, T}}, ::Type{LocalFieldValuationRingResidueRingElem{S, T}}) where {S, T} = LocalFieldValuationRingResidueRingElem{S, T}

function AbstractAlgebra.promote_rule(::Type{LocalFieldValuationRingResidueRingElem{S, T}}, ::Type{U}) where {S, T, U <: RingElement}
  AbstractAlgebra.promote_rule(T, U) == T ? LocalFieldValuationRingResidueRingElem{S, T} : Union{}
end

################################################################################
#
#  Construction
#
################################################################################

function residue_ring(R::LocalFieldValuationRing, a::LocalFieldValuationRingElem)
  @req parent(a) === R "Rings do not match"
  k = Int(absolute_ramification_index(R.Q)*valuation(a))
  S = LocalFieldValuationRingResidueRing(R, k)
  return S, Generic.EuclideanRingResidueMap(R, S)
end
