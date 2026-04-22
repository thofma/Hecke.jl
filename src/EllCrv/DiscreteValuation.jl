################################################################################
#
# Common interface for Discrete Valuations
#
# Explicit design choices:
# This is internal helper for implementing "local" algorithms in a generic way
# The goal is NOT to implement general DVR
# Currently it lives in Elliptic Curve because this is the first (and only) user
#   but when/if we need it in other places it can be moved
#
################################################################################

# DiscreteValuation acts as traits, the interface is currently as follows
#
# base_field(DiscreteValuation{T})
# the field where this valuation is defined
#
# residue_field(DiscreteValuation{T})
# the residue field of the valuation
#
# uniformizer(DiscreteValuation{T})
# uniformizer of the valuation
#
# valuation(DiscreteValuation{T}, T) -> Union{IntegerUnion, PosInf}
# computes valuation of an element
#
# reduce(DiscreteValuation{T}, T)
# maps an element of the field to the valuation's residue field
#
# lift(DiscreteValuation{T}, x)
# lifts an element of the valuation's residue field to the field
#
# norm(DiscreteValuation{T}) -> ZZRingElem
# norm of the corresponding non-archimedean place
#
# we also implement (in a generic way) the following
#
# reduce_mod(DiscreteValuation{T}, T) -> T
# canonical element y such that x = y mod p
#
# inv_mod(DiscreteValuation{T}, T) -> T
# canonical element y such that xy = 1 mod p

abstract type DiscreteValuation{T} end

function reduce_mod(v::DiscreteValuation, x)
  return lift(v, reduce(v, x))
end

function inv_mod(v::DiscreteValuation, x)
  return lift(v, inv(reduce(v, x)))
end

function norm(v::DiscreteValuation)
  return order(residue_field(v))
end

################################################################################
#
# Valuation on QQ (p-adic)
#
################################################################################

struct QQValuation <: DiscreteValuation{QQFieldElem}
  p::ZZRingElem
  F::FqField
end

function QQValuation(p_::IntegerUnion)
  p = ZZ(p_)
  F = finite_field(p; cached = false)[1]
  return QQValuation(p, F)
end

base_field(::QQValuation) = QQ
residue_field(v::QQValuation) = v.F
uniformizer(v::QQValuation) = QQ(v.p)

function valuation(v::QQValuation, x::QQFieldElem)
  return iszero(x) ? inf : valuation(x, v.p)
end

reduce(v::QQValuation, x::QQFieldElem) = v.F(x)
lift(v::QQValuation, y) = QQ(lift(ZZ, y))

################################################################################
#
# Valuation on Number Field (at a prime ideal)
#
################################################################################

struct AbsSimpleNumFieldValuation <: DiscreteValuation{AbsSimpleNumFieldElem}
  p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}
  uniformizer::AbsSimpleNumFieldElem
  red_map::NfToFinFldMor{FqField}
end

function AbsSimpleNumFieldValuation(p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  OK = order(p)
  F, mF = residue_field(OK, p)
  red = extend(mF, nf(OK))
  return AbsSimpleNumFieldValuation(p, elem_in_nf(uniformizer(p)), red)
end

base_field(v::AbsSimpleNumFieldValuation) = nf(order(v.p))
residue_field(v::AbsSimpleNumFieldValuation) = codomain(v.red_map)
uniformizer(v::AbsSimpleNumFieldValuation) = v.uniformizer

function valuation(v::AbsSimpleNumFieldValuation, x::AbsSimpleNumFieldElem)
  return iszero(x) ? inf : valuation(x, v.p)
end

reduce(v::AbsSimpleNumFieldValuation, x::AbsSimpleNumFieldElem) = v.red_map(x)
lift(v::AbsSimpleNumFieldValuation, y) = v.red_map\y

################################################################################
#
# Valuation on Rational Function Field k(t) (at an irreducible polynomial)
#
################################################################################

struct RationalFunctionFieldValuation{T, U, S} <: DiscreteValuation{AbstractAlgebra.Generic.RationalFunctionFieldElem{T, U}}
  K::AbstractAlgebra.Generic.RationalFunctionField{T, U}
  f::U
  red_map::S
end

function RationalFunctionFieldValuation(K::AbstractAlgebra.Generic.RationalFunctionField{T, U}, f::U) where {T, U <: PolyRingElem{T}}
  @req is_irreducible(f) "Polynomial must be irreducible"
  @assert parent(f) === base_ring(K.fraction_field)
  F, red_map = residue_field(parent(f), f)
  return RationalFunctionFieldValuation{T, U, typeof(red_map)}(K, f, red_map)
end

base_field(v::RationalFunctionFieldValuation) = v.K
residue_field(v::RationalFunctionFieldValuation) = codomain(v.red_map)
uniformizer(v::RationalFunctionFieldValuation) = v.K(v.f)

# for both valuation and reduce we want to allow passing polynomials (implicit denominator 1)
#   we do immediate type coercion, so anything not coercible to K is rejected.
# TODO: maybe it is worth it to explicitly provide two overloads
#   one for RationalFunctionFieldElem{T, U} and another for U (which is polynomial type).
function valuation(v::RationalFunctionFieldValuation, x_)
  x = v.K(x_)
  return iszero(x) ? inf : valuation(numerator(x), v.f) - valuation(denominator(x), v.f)
end

function reduce(v::RationalFunctionFieldValuation, x_)
  x = v.K(x_)
  return v.red_map(numerator(x)) // v.red_map(denominator(x))
end

lift(v::RationalFunctionFieldValuation, y) = v.K(v.red_map\y)

################################################################################
#
# Valuation on Rational Function Field k(t) (at the infinite place)
#
################################################################################

struct RationalFunctionFieldDegreeValuation{T, U, S} <: DiscreteValuation{AbstractAlgebra.Generic.RationalFunctionFieldElem{T, U}}
  K::AbstractAlgebra.Generic.RationalFunctionField{T, U}
  red_map::S
end

function RationalFunctionFieldDegreeValuation(K::AbstractAlgebra.Generic.RationalFunctionField{T, U}) where {T, U <: PolyRingElem{T}}
  Kinf = localization(K, degree)
  F, red_map = residue_field(Kinf, Kinf(1//gen(K)))
  return RationalFunctionFieldDegreeValuation{T, U, typeof(red_map)}(K, red_map)
end

base_field(v::RationalFunctionFieldDegreeValuation) = v.K
residue_field(v::RationalFunctionFieldDegreeValuation) = codomain(v.red_map)
uniformizer(v::RationalFunctionFieldDegreeValuation) = 1//gen(v.K)

# for both valuation and reduce we want to allow passing polynomials (implicit denominator 1)
#   we do immediate type coercion, so anything not coercible to K is rejected.
# TODO: maybe it is worth it to explicitly provide two overloads
#   one for RationalFunctionFieldElem{T, U} and another for U (which is polynomial type).
function valuation(v::RationalFunctionFieldDegreeValuation, x_)
  x = v.K(x_)
  return iszero(x) ? inf : degree(denominator(x)) - degree(numerator(x))
end

function reduce(v::RationalFunctionFieldDegreeValuation, x_)
  x = v.K(x_)
  Kl = domain(v.red_map)
  return v.red_map(Kl(x))
end

lift(v::RationalFunctionFieldDegreeValuation, y) = v.K(v.red_map\y)
