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

elem_type(::Type{KInftyRing{T}}) where T <: FieldElement = KInftyElem{T}

parent_type(::Type{KInftyElem{T}}) where T <: FieldElement = KInftyRing{T}

is_domain_type(::Type{KInftyElem{T}}) where {T} = true

# return the rational function field which KInfty wraps, mostly internal use
function function_field(R::KInftyRing{T}) where T <: FieldElement
  return R.K::Generic.RationalFunctionField{T}
end

parent(a::KInftyElem{T}) where T <: FieldElement = a.parent

function Base.hash(a::KInftyElem, h::UInt)
  b = 0x32ba43ad011affd1%UInt
  return xor(b, hash(data(a), h))
end

###############################################################################
#
#   Basic manipulation
#
###############################################################################

data(a::KInftyElem{T}) where T <: FieldElement = a.d::Generic.RationalFunctionFieldElem{T}

function numerator(a::KInftyElem{T}, canonicalise::Bool=true) where T <: FieldElement
  return numerator(data(a), canonicalise)
end

function denominator(a::KInftyElem{T}, canonicalise::Bool=true) where T <: FieldElement
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

zero(K::KInftyRing{T}) where T <: FieldElement = K(0)

one(K::KInftyRing{T}) where T <: FieldElement = K(1)

iszero(a::KInftyElem{T}) where T <: FieldElement = iszero(data(a))

isone(a::KInftyElem{T}) where T <: FieldElement = isone(data(a))

function is_unit(a::KInftyElem{T}) where T <: FieldElement
  return degree(numerator(data(a), false)) ==
                                            degree(denominator(data(a), false))
end

@doc raw"""
    in(a::Generic.RationalFunctionFieldElem{T}, R::KInftyRing{T}) where T <: FieldElement

Return `true` if the given element of the rational function field is an
element of $k_\infty(x)$, i.e. if `degree(numerator) <= degree(denominator)`.
"""
function in(a::Generic.RationalFunctionFieldElem{T}, R::KInftyRing{T}) where T <: FieldElement
  if parent(a) != function_field(R)
    return false
  end
  return degree(numerator(a, false)) <= degree(denominator(a, false))
end

function Base.deepcopy_internal(a::KInftyElem{T}, dict::IdDict) where T <: FieldElement
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

function -(a::KInftyElem{T}) where T <: FieldElement
  parent(a)(-data(a), false)
end

###############################################################################
#
#   Binary operators
#
###############################################################################

function +(a::KInftyElem{T}, b::KInftyElem{T})  where T <: FieldElement
  check_parent(a, b)
  return parent(a)(data(a) + data(b), false)
end

function -(a::KInftyElem{T}, b::KInftyElem{T})  where T <: FieldElement
  check_parent(a, b)
  return parent(a)(data(a) - data(b), false)
end

function *(a::KInftyElem{T}, b::KInftyElem{T})  where T <: FieldElement
  check_parent(a, b)
  return parent(a)(data(a)*data(b), false)
end

###############################################################################
#
#   Inplace
#
###############################################################################

function mul!(a::KInftyElem{T}, b::KInftyElem{T}, c::KInftyElem{T}) where {T}
  return b*c
end

###############################################################################
#
#   Comparison
#
###############################################################################

function ==(a::KInftyElem{T}, b::KInftyElem{T}) where T <: FieldElement
  check_parent(a, b)
  return data(a) == data(b)
end

###############################################################################
#
#  Inversion
#
###############################################################################

@doc raw"""
     inv(a::KInftyElem{T}, checked::Bool = true)  where T <: FieldElement
Returns the inverse element of $a$ if $a$ is a unit.
If 'checked = false' the invertibility of $a$ is not checked and the
corresponding inverse element of the rational function field is returned.
"""
function inv(a::KInftyElem{T}, checked::Bool = true)  where T <: FieldElement
  b = inv(data(a))
  return parent(a)(b, checked)
end

###############################################################################
#
#  Exact division
#
###############################################################################

@doc raw"""
     divides(a::KInftyElem{T}, b::KInftyElem{T}, checked::Bool = true) where T <: FieldElement

Returns tuple `(flag, c)` where `flag = true` if $b$ divides $a$ and $a = bc$,
otherwise `flag = false` and $c = 0$.
If `checked = false` the corresponding element of the rational function field
is returned and it is not checked whether it is an element of the given
localization.
"""
function divides(a::KInftyElem{T}, b::KInftyElem{T}, checked::Bool = true) where T <: FieldElement
  check_parent(a, b)
  if iszero(a)
    return true, a
  end
  if checked && degree(a) > degree(b)
    return false, parent(a)()
  else
    elem = divexact(data(a), data(b))
    return true, parent(a)(elem, false)
  end
end

@doc raw"""
     divexact(a::KInftyElem{T}, b::KInftyElem{T}, checked::Bool = true)  where {T <: AbsSimpleNumFieldElem}
Returns element 'c' of given localization such that $a = bc$ if such element
exists. If `checked = false` the corresponding element of the rational function
field is returned and it is not checked whether it is an element of the given
localization.
"""
function divexact(a::KInftyElem{T}, b::KInftyElem{T}; check::Bool = true)  where T <: FieldElement
  iszero(b) && throw(DivideError())
  d = divides(a, b, check)
  d[1] ? d[2] : error("$a not divisible by $b in the given localization")
end

###############################################################################
#
#  Euclidean division
#
###############################################################################

#= an attempt to have a canonical rep modulo the ideal
 generated by b
 - <b> = <1/t^n>, the canonical rep
 - translate via t-> 1/t into the "normal" world
 - a rep of a/b mod t^n is ((a % t^n)*invmod(b, t^n) % t^n)
 - translate back
 The "canonical" rep should be r/t^l for deg(r) < n and l = deg(r)
 In particular, for n=1, this is a scalar.

 The translation is done using reverse:
  a-> a(1/t)*t^deg(a) = reverse(a)
  so a/b -> a(1/t)/b(1/t) and this needs to be expanded by t^max/t^max to
  make both num and den polynomials
  a/b -> reverse(a, max)//reverse(b, max)
=#

function mod(a::KInftyElem{T}, b::KInftyElem{T}, checked::Bool=true) where T <: FieldElement
  check_parent(a, b)
  iszero(b) && throw(DivideError())
  iszero(a) && return deepcopy(a)

  if degree(a) > degree(b)
    n = -degree(b)
    na = numerator(a.d)
    da = denominator(a.d)
    mx = max(degree(na), degree(da))+1
    if mx != 0
      na = reverse(na, mx)
      da = reverse(da, mx)
    end
    t = gen(parent(na))
    tn = t^n
    r = mod(mod(na, tn) * invmod(da, tn), tn)
    Qt = parent(a.d)
    return parent(a)(Qt(reverse(r))//Qt(t)^degree(r))
  else
    return zero(parent(a))
  end
end

function div(a::KInftyElem{T}, b::KInftyElem{T}, check::Bool=true) where T <: FieldElement
  check_parent(a, b)
  iszero(b) && throw(DivideError())
  iszero(a) && return a
  if degree(a) > degree(b)
    return divexact(a-mod(a, b), b, check = check)
  else
    return divexact(a, b, check = check)
  end
end

function divrem(a::KInftyElem{T}, b::KInftyElem{T}, check::Bool=true) where T <: FieldElement
  check_parent(a, b)
  iszero(b) && throw(DivideError())
  iszero(a) && return a, a

  if degree(a) > degree(b)
    r = mod(a, b)
    return divexact(a-r, b, check = check), r
  else
    return divexact(a, b, check = check), parent(a)()
  end
end

Base.rem(a::KInftyElem{T}, b::KInftyElem{T}, checked::Bool=true) where T <: FieldElement = mod(a, b, checked)

###############################################################################
#
#  GCD
#
###############################################################################

function gcd(a::KInftyElem{T}, b::KInftyElem{T}, checked::Bool=true) where T <: FieldElement
  check_parent(a, b)
  t = gen(parent(a))
  iszero(a) && iszero(b) && return a
  iszero(a) && return t^-degree(b)
  iszero(b) && return t^-degree(a)

  return t^-max(degree(a), degree(b))
end

function lcm(a::KInftyElem{T}, b::KInftyElem{T}, checked::Bool=true) where T <: FieldElement
  t = gen(parent(a))
  iszero(a) && iszero(b) && return a
  iszero(a) && return t^-degree(b)
  iszero(b) && return t^-degree(a)

  return t^-min(degree(a), degree(b))
end
###############################################################################
#
#  GCDX
#
###############################################################################

function gcdx(a::KInftyElem{T}, b::KInftyElem{T}, checked::Bool=true) where T <: FieldElement
  check_parent(a, b)
  K = parent(a)
  t = gen(K)

  if iszero(a)
    iszero(b) && a, a, one(K)
    g = t^-degree(b)
    return g, zero(K), inv(canonical_unit(b))
  end

  if iszero(b) || degree(a) >= degree(b)
    g = t^-degree(a)
    return g, inv(canonical_unit(a)), zero(K)
  end

  g = t^-degree(b)
  return g, zero(K), inv(canonical_unit(b))
end

function gcdinv(a::KInftyElem{T}, b::KInftyElem{T}) where {T}
  g, q, w = gcdx(a, b)
  @assert is_unit(g)
  return one(parent(a)), q*inv(g)
end

###############################################################################
#
#   Powering
#
###############################################################################

function ^(a::KInftyElem{T}, b::Int) where T <: FieldElement
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

AbstractAlgebra.promote_rule(::Type{KInftyElem{T}}, ::Type{KInftyElem{T}}) where T <: FieldElement = KInftyElem{T}

function AbstractAlgebra.promote_rule(::Type{KInftyElem{T}}, ::Type{U}) where {T <: FieldElement, U <: Generic.RationalFunctionFieldElem{T}}
  return KInftyElem{T}
end

function AbstractAlgebra.promote_rule(::Type{KInftyElem{T}}, ::Type{U}) where {T <: FieldElement, U <: RingElem}
  promote_rule(T, U) == T ? KInftyElem{T} : Union{}
end

###############################################################################
#
#  Parent call overloading
#
###############################################################################

(R::KInftyRing)() = R(function_field(R)())

function (R::KInftyRing{T})(a::Generic.RationalFunctionFieldElem{T}, checked::Bool=true) where T <: FieldElement
  checked && degree(numerator(a, false)) > degree(denominator(a, false)) &&
                                           error("Not an element of k_infty(x)")
  return KInftyElem{T}(a, R)
end

(R::KInftyRing)(a::RingElement) = R(function_field(R)(a), false)

function (R::KInftyRing{T})(a::KInftyElem{T}) where T <: FieldElement
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

function residue_field(K::KInftyRing{T}, a::KInftyElem{T}) where {T <: FieldElement}
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
function localization(K::Generic.RationalFunctionField{T}, ::typeof(degree); cached::Bool=true) where T <: FieldElement
  return KInftyRing{T}(K, cached)
end


