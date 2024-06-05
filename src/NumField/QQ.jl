"""
    ZZIdl

Type for ideals in ZZ. Parametrized by a generator in ZZ.
"""
struct ZZIdl <: NumFieldOrderIdeal
  gen::ZZRingElem

  function ZZIdl(x::ZZRingElem)
    if x < 0
      return new(abs(x))
    else
      return new(x)
    end
  end
end

"""
    ZZFracIdl

Type for fractional ideals in ZZ or QQ, parametrized by a generator in QQ.
"""
struct ZZFracIdl <: NumFieldOrderFractionalIdeal
  gen::QQFieldElem

  function ZZFracIdl(x::QQFieldElem)
    if x < 0
      return new(abs(x))
    else
      return new(x)
    end
  end
end

Base.hash(x::ZZIdl, h::UInt) = hash(gen(x), h)

order(::ZZIdl) = FlintZZ

order(::ZZFracIdl) = FlintZZ

# constructors
*(::ZZRing, x::IntegerUnion) = ideal(ZZ, x)

*(x::IntegerUnion, ::ZZRing) = ideal(ZZ, x)

ideal(::ZZRing, x::ZZRingElem) = ZZIdl(x)

ideal(::ZZRing, x::Integer) = ZZIdl(ZZRingElem(x))

ideal(::ZZRing, x::AbstractVector{ZZRingElem}) = ZZIdl(gcd(x))

ideal(::ZZRing, x::AbstractVector{<:Integer}) = ZZIdl(ZZRingElem(gcd(x)))

fractional_ideal(::ZZRing, x::QQFieldElem) = ZZFracIdl(x)

fractional_ideal(::ZZRing, x::RingElement) = ZZFracIdl(QQFieldElem(x))

fractional_ideal(::ZZRing, x::AbstractVector{<:RationalUnion}) = ZZFracIdl(QQFieldElem(gcd(x)))

*(x::Union{QQFieldElem, Rational{<:Integer}}, ::ZZRing) = ZZFracIdl(QQFieldElem(x))

*(::ZZRing, x::Union{QQFieldElem, Rational{<:Integer}}) = ZZFracIdl(QQFieldElem(x))

#

norm(x::ZZIdl) = gen(x)

norm(x::ZZFracIdl) = gen(x)

minimum(x::ZZIdl) = gen(x)

minimum(x::ZZFracIdl) = gen(x)

absolute_minimum(x::ZZIdl) = gen(x)

absolute_minimum(x::ZZFracIdl) = gen(x)

prime_decomposition(O::AbsSimpleNumFieldOrder, p::ZZIdl) = prime_decomposition(O, gen(p))

uniformizer(x::ZZIdl) = gen(x)

# printing
function Base.show(io::IO, x::ZZIdl)
  print(io, "$(x.gen)ZZ")
end

function Base.show(io::IO, x::ZZFracIdl)
  print(io, "Fractional ideal $(x.gen)ZZ")
end

# comparison
function ==(I::ZZIdl, J::ZZIdl)
  return I.gen == J.gen
end

function ==(I::ZZFracIdl, J::ZZFracIdl)
  return I.gen == J.gen
end

# access
gen(I::ZZIdl) = I.gen

gens(I::ZZIdl) = ZZRingElem[I.gen]


gen(I::ZZFracIdl) = I.gen
gens(I::ZZFracIdl) = QQFieldElem[I.gen]

#TODO

# arithmetic

function +(I::ZZIdl, J::ZZIdl)
  g = gcd(I.gen, J.gen)
  return ZZIdl(g)
end

function *(s::ZZRingElem, J::ZZIdl)
  return ZZIdl(s*J.gen)
end

function *(J::ZZIdl, s::ZZRingElem)
  return ZZIdl(s*J.gen)
end

# Arithmetic

*(x::ZZIdl, y::ZZIdl) = ZZIdl(x.gen * y.gen)

function intersect(x::ZZIdl, y::ZZIdl...)
  g = gen(x)
  for I in y
    g = lcm(g, gen(I))
  end
  return ZZIdl(g)
end

lcm(x::ZZIdl, y::ZZIdl) = intersect(x, y)

*(x::ZZFracIdl, y::ZZFracIdl) = ZZFracIdl(x.gen * y.gen)

# We use the great convention about the gcd of rationals
+(x::ZZFracIdl, y::ZZFracIdl) = ZZFracIdl(gcd(x.gen, y.gen))

gcd(x::ZZFracIdl, y::ZZFracIdl) = x + y

lcm(x::ZZFracIdl, y::ZZFracIdl) = intersect(x, y)

intersect(x::ZZFracIdl, y::ZZFracIdl) = ZZFracIdl(lcm(x.gen, y.gen))

# TODO

gcd(I::ZZIdl, J::ZZIdl) = ZZIdl(gcd(I.gen, J.gen))
gcd(I::ZZIdl, n::T) where T <: Union{ZZRingElem, Int} = ZZIdl(gcd(I.gen, n))
gcd(n::T, I::ZZIdl) where T <: Union{ZZRingElem, Int} = ZZIdl(gcd(I.gen, n))

isone(I::ZZIdl) = isone(I.gen)
iszero(I::ZZIdl) = iszero(gen(I))
is_maximal(I::ZZIdl) = is_prime(gen(I))
is_prime(I::ZZIdl) = is_zero(I) || is_maximal(I)
is_primary(I::ZZIdl) = is_zero(I) || is_prime_power_with_data(gen(I))[1]

is_subset(I::ZZIdl, J::ZZIdl) = is_divisible_by(gen(J), gen(I))

radical(I::ZZIdl) = iszero(I) ? I : ideal(ZZ, radical(gen(I)))
primary_decomposition(I::ZZIdl) = iszero(I) ? [ (I,I) ] :
  [ (ideal(ZZ, p^k), ideal(ZZ, p)) for (p,k) in factor(gen(I)) ]

maximal_order(::QQField) = ZZ

ideal_type(::ZZRing) = ZZIdl
order_type(::QQField) = ZZRing
ideal_type(::Type{ZZRing}) = ZZIdl
order_type(::Type{QQField}) = ZZRing
place_type(::QQField) = PosInf
place_type(::Type{QQField}) = PosInf

fractional_ideal_type(::QQField) = ZZFracIdl

elem_in_nf(x::ZZRingElem) = FlintQQ(x)

nf(::ZZRing) = FlintQQ

# Infinite places

isreal(::PosInf) = true
is_complex(::PosInf) = false

infinite_places(::QQField) = [inf]
infinite_place(::QQField) = inf

function infinite_place(::QQField, i::Int)
  i !=1 && error("Index must be 1")
  return inf
end

real_places(::QQField) = PosInf[inf]

complex_places(::QQField) = PosInf[]

function sign(x::Union{QQFieldElem, ZZRingElem, FacElem{QQFieldElem}}, p::PosInf)
  return sign(x, QQEmb())
end

function signs(a::Union{QQFieldElem, ZZRingElem, FacElem{QQFieldElem}}, l::Vector{PosInf})
  return Dict(inf => sign(a))
end

function is_positive(x::FacElem{QQFieldElem}, ::Union{PosInf, Vector{PosInf}})
  return sign(x) == 1
end

function is_totally_positive(x::Union{QQFieldElem, ZZRingElem, FacElem{QQFieldElem}}, p::Union{PosInf, Vector{PosInf}})
  return sign(x) == 0
end

function is_negative(x::FacElem{QQFieldElem}, ::Union{PosInf, Vector{PosInf}})
  return sign(x) == -1
end

number_field(::PosInf) = QQ

uniformizer(::PosInf) = QQ(-1)

infinite_places_uniformizers(::QQField) = QQFieldElem[QQ(1)]

function hilbert_symbol(a,b, p::ZZIdl)
  return hilbert_symbol(a,b, gen(p))
end

is_local_norm(K, x, p::ZZIdl) = is_local_norm(K, x, gen(p))

function quadratic_defect(q::QQFieldElem, p::ZZIdl)
  return quadratic_defect(q, gen(p))
end

################################################################################
#
#  Support
#
################################################################################

function support(a::QQFieldElem, R::ZZRing)
  return ZZIdl[p*R for (p, _) in factor(R, a)]
end

################################################################################
#
#  CRT
#
################################################################################

function crt(a::Vector{ZZRingElem}, b::Vector{ZZIdl})
  return crt(a, ZZRingElem[gen(x) for x in b])
end

################################################################################
#
#  Factoring
#
################################################################################

function factor(i::ZZIdl)
  C = [(ideal(ZZ,c[1]),c[2]) for c in collect(factor(gen(i)))]
  D = Dict{ZZIdl,Int64}(C)
  return D
end

function factor(i::ZZFracIdl)
  g = gen(i)
  f1 = factor(numerator(g))
  f2 = factor(denominator(g))
  C1 = [(ideal(ZZ,c[1]),c[2]) for c in collect(f1)]
  C2 = [(ideal(ZZ,c[1]),-c[2]) for c in collect(f2)]
  C = append!(C1, C2)
  D = Dict{ZZIdl,Int64}(C)
  return D
end


################################################################################
# S units
################################################################################

sunit_group_fac_elem(S::Vector{ZZIdl}) = sunit_group_fac_elem([gen(i) for i in S])

################################################################################
#
#  Evaluation
#
################################################################################

# Let's not turn this into an ArbFieldElem for now
# If this causes trouble, we need to change it to ArbField(p, cached = false)(x)
evaluate(x::QQFieldElem, ::PosInf, p::Int) = x


################################################################################
#
#  Residue Rings
#
################################################################################

quo(R::ZZRing, I::ZZIdl) = quo(R, gen(I))

residue_ring(R::ZZRing, I::ZZIdl) = quo(R, I)

residue_field(R::ZZRing, I::ZZIdl) = residue_field(R, gen(I))


################################################################################
#
#  Membership Test
#
################################################################################

Base.in(x, I::ZZIdl) = iszero(mod(x,gen(I)))

################################################################################
#
#  Compliance with the schemes interfaces
#
################################################################################

coordinates(x, I::ZZIdl) = [divexact(x, gen(I))]

saturated_ideal(I::ZZIdl) = I

lifted_numerator(x::ZZRingElem) = x

lifted_denominator(x::ZZRingElem) = ZZRingElem(1)

################################################################################

absolute_basis(Q::QQField) = [one(Q)]
