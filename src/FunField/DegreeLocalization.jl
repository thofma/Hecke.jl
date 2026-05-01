###############################################################################
#
#  Localization of K[1/x] at (1/x), i.e. k_\infty(x) \subseteq k(x)
#
#
#  (C) 2021 William Hart
#
###############################################################################

###############################################################################
#
#   Data type and parent object methods
#
###############################################################################

elem_type(::Type{KInftyRing{T,U}}) where {T, U} = KInftyElem{T, U}

parent_type(::Type{KInftyElem{T, U}}) where {T, U} = KInftyRing{T, U}

is_domain_type(::Type{KInftyElem{T, U}}) where {T, U} = true

# return the rational function field which KInfty wraps, mostly internal use
function_field(R::KInftyRing) = R.K

parent(a::KInftyElem) = a.parent

function Base.hash(a::KInftyElem, h::UInt)
  b = 0x32ba43ad011affd1%UInt
  return xor(b, hash(data(a), h))
end

###############################################################################
#
#   Basic manipulation
#
###############################################################################

data(a::KInftyElem) = a.d

function numerator(a::KInftyElem, canonicalise::Bool=true)
  return numerator(data(a), canonicalise)
end

function denominator(a::KInftyElem, canonicalise::Bool=true)
  return denominator(data(a), canonicalise)
end

gen(R::KInftyRing) = R(inv(gen(R.K)))

characteristic(R::KInftyRing) = characteristic(R.K)

@doc raw"""
     degree(a::KInftyElem)

Return the degree of the given element, i.e.
`degree(numerator) - degree(denominator)`.
"""
degree(a::KInftyElem) = degree(numerator(a, false)) - degree(denominator(a, false))

@doc raw"""
    valuation(a::KInftyElem)

Return the degree valuation of the given element, i.e. `-degree(a)`.
"""
valuation(a::KInftyElem) = -degree(a)

zero(K::KInftyRing) = K(0)
one(K::KInftyRing)  = K(1)

is_zero(a::KInftyElem) = is_zero(data(a))
is_one(a::KInftyElem)  = is_one(data(a))

function is_unit(a::KInftyElem)
  return degree(numerator(data(a), false)) == degree(denominator(data(a), false))
end

@doc raw"""
    in(a::Generic.RationalFunctionFieldElem{T,U}, R::KInftyRing{T,U})

Return `true` if the given element of the rational function field is an
element of $k_\infty(x)$, i.e. if `degree(numerator) <= degree(denominator)`.
"""
function in(a::Generic.RationalFunctionFieldElem{T,U}, R::KInftyRing{T,U}) where {T, U}
  if parent(a) != function_field(R)
    return false
  end
  return degree(numerator(a, false)) <= degree(denominator(a, false))
end

function Base.deepcopy_internal(a::KInftyElem, dict::IdDict)
  c = Base.deepcopy_internal(data(a), dict)
  parent(a)(Base.deepcopy_internal(data(a), dict))
end

###############################################################################
#
#   AbstractString I/O
#
###############################################################################

function AbstractAlgebra.expressify(a::KInftyElem; context = nothing)
  return AbstractAlgebra.expressify(data(a), context = context)
end

function show(io::IO, a::KInftyElem)
  print(io, AbstractAlgebra.obj_to_string(a, context = io))
end

function show(io::IO, R::KInftyRing)
  print(io, "Degree localization of ", function_field(R))
end

###############################################################################
#
#   Unary operations
#
###############################################################################

function -(a::KInftyElem)
  parent(a)(-data(a), false)
end

###############################################################################
#
#   Binary operators
#
###############################################################################

function +(a::KInftyElem{T,U}, b::KInftyElem{T,U})  where {T,U}
  check_parent(a, b)
  return parent(a)(data(a) + data(b), false)
end

function -(a::KInftyElem{T,U}, b::KInftyElem{T,U})  where {T,U}
  check_parent(a, b)
  return parent(a)(data(a) - data(b), false)
end

function *(a::KInftyElem{T,U}, b::KInftyElem{T,U})  where {T,U}
  check_parent(a, b)
  return parent(a)(data(a)*data(b), false)
end

###############################################################################
#
#   Inplace
#
###############################################################################

function mul!(a::KInftyElem{T,U}, b::KInftyElem{T,U}, c::KInftyElem{T,U}) where {T,U}
  return b*c
end

###############################################################################
#
#   Comparison
#
###############################################################################

function ==(a::KInftyElem{T,U}, b::KInftyElem{T,U}) where {T,U}
  check_parent(a, b)
  return data(a) == data(b)
end

###############################################################################
#
#  Inversion
#
###############################################################################

@doc raw"""
     inv(a::KInftyElem, checked::Bool = true)
Returns the inverse element of $a$ if $a$ is a unit.
If 'checked = false' the invertibility of $a$ is not checked and the
corresponding inverse element of the rational function field is returned.
"""
function inv(a::KInftyElem, checked::Bool = true)
  b = inv(data(a))
  return parent(a)(b, checked)
end

###############################################################################
#
#  Exact division
#
###############################################################################

@doc raw"""
     divides(a::KInftyElem, b::KInftyElem, checked::Bool = true)

Returns tuple `(flag, c)` where `flag = true` if $b$ divides $a$ and $a = bc$,
otherwise `flag = false` and $c = 0$.
If `checked = false` the corresponding element of the rational function field
is returned and it is not checked whether it is an element of the given
localization.
"""
function divides(a::KInftyElem{T,U}, b::KInftyElem{T,U}, checked::Bool = true) where {T,U}
  check_parent(a, b)

  iszero(a) && return true, a
  checked && valuation(a) < valuation(b) && return false, zero(parent(a))

  return true, parent(a)(divexact(data(a), data(b)), false)
end

@doc raw"""
     divexact(a::KInftyElem, b::KInftyElem, checked::Bool = true)
Returns element 'c' of given localization such that $a = bc$ if such element
exists. If `checked = false` the corresponding element of the rational function
field is returned and it is not checked whether it is an element of the given
localization.
"""
function divexact(a::KInftyElem{T,U}, b::KInftyElem{T,U}; check::Bool = true) where {T,U}
  iszero(b) && throw(DivideError())

  flag, quo = divides(a, b, check)
  !flag && error("$a not divisible by $b in the given localization")

  return quo
end

###############################################################################
#
#  Euclidean division
#
###############################################################################

# compute the canonical representative of a modulo <b> = <1/x^n> with n = v(b)
#   this is the truncation of a power series in uniformizer 1/x to the first n terms
function mod(a::KInftyElem{T,U}, b::KInftyElem{T,U}) where {T,U}
  check_parent(a, b)
  iszero(b) && throw(DivideError())
  iszero(a) && return a

  # in a DVR, all nonzero ideals have the form (1/x^n), n >= 1
  # if v(a) >= v(b), then a is in <b>, so a mod b == 0
  if valuation(a) >= valuation(b)
    return zero(parent(a))
  end

  # For a polynomial f of degree d, the reversal reverse(f) = x^d * f(1/x)
  #   swaps the coefficient order. For a = f/g with deg(f) <= deg(g),
  #   padding f to length deg(g)+1 before reversing gives:
  # reverse(f) / reverse(g) = f(1/x) / g(1/x) = a(1/x)
  # Computing reverse(f) * reverse(g)^{-1} mod x^n gives the first n
  #   coefficients of a(1/x) as a polynomial r(x) of degree < n.
  # Note that the constant term of reverse(g) is the leading coefficient of g,
  #   which is nonzero, so reverse(g) is invertible mod x^n.
  # To substitute back: r(1/x) = reverse(r) / x^deg(r).

  numer_a, denom_a = numerator(a.d), denominator(a.d)
  len = degree(denom_a) + 1

  x = gen(parent(numer_a))
  xn = x^valuation(b)

  r = mod( mod(reverse(numer_a, len), xn) * invmod(reverse(denom_a), xn), xn )

  Qx = parent(a.d)
  return parent(a)( Qx(reverse(r)) // Qx(x)^degree(r) )
end

function div(a::KInftyElem{T,U}, b::KInftyElem{T,U}) where {T,U}
  check_parent(a, b)
  return divrem(a, b)[1]
end

function divrem(a::KInftyElem{T,U}, b::KInftyElem{T,U}) where {T,U}
  check_parent(a, b)
  iszero(b) && throw(DivideError())
  iszero(a) && return a, a

  if valuation(a) < valuation(b)
    r = mod(a, b)
    return divexact(a-r, b; check = false), r
  else
    return divexact(a, b; check = false), zero(parent(a))
  end
end

Base.rem(a::KInftyElem{T,U}, b::KInftyElem{T,U}) where {T,U} = mod(a, b)

###############################################################################
#
#  GCD
#
###############################################################################

function gcd(a::KInftyElem{T,U}, b::KInftyElem{T,U}) where {T,U}
  check_parent(a, b)
  t = gen(parent(a))

  if iszero(a)
    return iszero(b) ? a : t^valuation(b)
  elseif iszero(b)
    return t^valuation(a)
  else
    return t^min(valuation(a), valuation(b))
  end
end

function lcm(a::KInftyElem{T,U}, b::KInftyElem{T,U}) where {T,U}
  check_parent(a, b)

  if iszero(a) || iszero(b)
    return zero(parent(a))
  else
    t = gen(parent(a))
    return t^max(valuation(a), valuation(b))
  end
end

###############################################################################
#
#  GCDX
#
###############################################################################

function gcdx(a::KInftyElem{T,U}, b::KInftyElem{T,U}) where {T,U}
  check_parent(a, b)
  K = parent(a)
  t = gen(K)

  if iszero(a)
    if iszero(b)
      return zero(K), zero(K), one(K)
    else
      return t^valuation(b), zero(K), inv(canonical_unit(b))
    end
  end

  if iszero(b) || valuation(a) <= valuation(b)
    return t^valuation(a), inv(canonical_unit(a)), zero(K)
  end

  return t^valuation(b), zero(K), inv(canonical_unit(b))
end

function gcdinv(a::KInftyElem{T,U}, b::KInftyElem{T,U}) where {T,U}
  g, q, w = gcdx(a, b)
  @assert is_unit(g)
  return one(parent(a)), q*inv(g)
end

###############################################################################
#
#   Powering
#
###############################################################################

function ^(a::KInftyElem, b::Int)
  return parent(a)(data(a)^b, false)
end

###############################################################################
#
#   Random functions
#
###############################################################################

RandomExtensions.maketype(R::KInftyRing, _) = elem_type(R)

function RandomExtensions.make(S::KInftyRing, vs...)
  R = function_field(S)
  if length(vs) == 1 && elem_type(R) == Random.gentype(vs[1])
    RandomExtensions.Make(S, vs[1]) # forward to default Make constructor
  else
    RandomExtensions.Make(S, make(R, vs...))
  end
end

function rand(rng::AbstractRNG,
              sp::SamplerTrivial{<:Make2{<:RingElement, <:KInftyRing}})
  S, v = sp[][1:end]
  R = function_field(S)
  d = rand(rng, v)
  if iszero(d)
    return S(d, false)
  end
  if degree(numerator(d, false)) <= degree(denominator(d, false))
    return S(d, false)
  else
    return S(inv(d), false)
  end
end

rand(rng::AbstractRNG, S::KInftyRing, v...) =
  rand(rng, make(S, v...))

rand(S::KInftyRing, v...) = rand(GLOBAL_RNG, S, v...)

###############################################################################
#
#   Promotion rules
#
###############################################################################

AbstractAlgebra.promote_rule(::Type{KInftyElem{T,U}}, ::Type{KInftyElem{T,U}}) where {T,U} = KInftyElem{T,U}

function AbstractAlgebra.promote_rule(::Type{KInftyElem{T,U}}, ::Type{S}) where {T,U, S <: Generic.RationalFunctionFieldElem{T,U}}
  return S
end

function AbstractAlgebra.promote_rule(::Type{KInftyElem{T,U}}, ::Type{S}) where {T,U, S <: RingElem}
  promote_rule(T, U) == T ? KInftyElem{T,U} : Union{}
end

###############################################################################
#
#  Parent call overloading
#
###############################################################################

(R::KInftyRing)() = R(function_field(R)())

function (R::KInftyRing{T,U})(a::Generic.RationalFunctionFieldElem{T,U}, checked::Bool=true) where {T, U}
  checked && degree(numerator(a, false)) > degree(denominator(a, false)) &&
                                           error("Not an element of k_infty(x)")
  return KInftyElem{T,U}(a, R)
end

(R::KInftyRing{T,U})(a::RingElement) where {T, U} = R(function_field(R)(a), false)

function (R::KInftyRing{T,U})(a::KInftyElem{T,U}) where {T, U}
  parent(a) != R && error("Cannot coerce element")
  return a
end

###############################################################################
#
#  Canonical unit
#
###############################################################################

function canonical_unit(a::KInftyElem)
  iszero(a) && return one(parent(a))
  num = numerator(a, false)
  den = denominator(a, false)
  R = parent(num)
  x = gen(R)
  return parent(a)((x^(degree(den) - degree(num))*num)//den)
end

###############################################################################
#
#  Factorisation
#
###############################################################################

function factor(d::KInftyElem)
  t = gen(parent(d))
  a = degree(d)
  return Fac(canonical_unit(d), Dict(t=>-a))
end

###############################################################################
#
#  Constructors
#
###############################################################################

function residue_field(K::KInftyRing{T,U}, a::KInftyElem{T,U}) where {T,U}
  F = base_ring(K.K)
  @assert degree(a) == -1
  #TODO: can be optimized, see blurb of euc. div. above
  return F, MapFromFunc(K, F, x -> leading_coefficient(numerator(mod(x, a))), y-> K(y))
end
#TODO: residue_ring is probably "just" poly of deg < n, think about it

@doc raw"""
    localization(K::RationalFunctionField{T}, ::typeof(degree)) where T <: FieldElement

Return the localization of $k[1/x]$ at $(1/x)$ inside the rational function
field $k(x)$, i.e. the localization of the function field at the point at
infinity, i.e. the valuation ring for valuation $-$degree$(x)$. This is the ring
$k_\infty(x) = \{ f/g | \deg(f) \leq \deg(g)\}$.
"""
function localization(K::Generic.RationalFunctionField{T, U}, ::typeof(degree); cached::Bool = true) where {T, U}
  return KInftyRing{T, U}(K; cached = cached)
end
