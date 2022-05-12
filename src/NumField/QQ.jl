struct ZZIdl <: NumFieldOrdIdl
  gen::fmpz

  function ZZIdl(x::fmpz)
    if x < 0
      return new(abs(x))
    else
      return new(x)
    end
  end
end

struct ZZFracIdl <: NumFieldOrdFracIdl
  gen::fmpq

  function ZZFracIdl(x::fmpq)
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
*(::FlintIntegerRing, x::IntegerUnion) = ideal(ZZ, x)

*(x::IntegerUnion, ::FlintIntegerRing) = ideal(ZZ, x)

ideal(::FlintIntegerRing, x::fmpz) = ZZIdl(x)

ideal(::FlintIntegerRing, x::Integer) = ZZIdl(fmpz(x))

ideal(::FlintIntegerRing, x::AbstractVector{fmpz}) = ZZIdl(gcd(x))

ideal(::FlintIntegerRing, x::AbstractVector{<:Integer}) = ZZIdl(fmpz(gcd(x)))

fractional_ideal(::FlintIntegerRing, x::fmpq) = ZZFracIdl(x)

fractional_ideal(::FlintIntegerRing, x::RingElement) = ZZFracIdl(fmpq(x))

*(x::fmpq, ::FlintIntegerRing) = ZZFracIdl(x)

*(::FlintIntegerRing, x::fmpq) = ZZFracIdl(x)

#

norm(x::ZZIdl) = gen(x)

norm(x::ZZFracIdl) = gen(x)

minimum(x::ZZIdl) = gen(x)

minimum(x::ZZFracIdl) = gen(x)

prime_decomposition(O::NfOrd, p::ZZIdl) = prime_decomposition(O, gen(p))

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

# access
gen(I::ZZIdl) = I.gen

gens(I::ZZIdl) = fmpz[I.gen]


gen(I::ZZFracIdl) = I.gen
gens(I::ZZFracIdl) = fmpq[I.gen]

#TODO

# arithmetic

function +(I::ZZIdl, J::ZZIdl)
  g = gcd(I.gen, J.gen)
  return ZZIdl(g)
end

function *(s::fmpz, J::ZZIdl)
  return ZZIdl(s*J.gen)
end

function (J::ZZIdl, s::fmpz)
  return ZZIdl(s*J.gen)
end

# TODO

gcd(I::ZZIdl, J::ZZIdl) = ZZIdl(gcd(I.gen, J.gen))
gcd(I::ZZIdl, n::T) where T <: Union{fmpz, Int} = ZZIdl(gcd(I.gen, n))
gcd(n::T, I::ZZIdl) where T <: Union{fmpz, Int} = ZZIdl(gcd(I.gen, n))

isone(I::ZZIdl) = isone(I.gen)

maximal_order(::FlintRationalField) = ZZ

ideal_type(::FlintIntegerRing) = ZZIdl
order_type(::FlintRationalField) = FlintIntegerRing
ideal_type(::Type{FlintIntegerRing}) = ZZIdl
order_type(::Type{FlintRationalField}) = FlintIntegerRing
place_type(::FlintRationalField) = PosInf
place_type(::Type{FlintRationalField}) = PosInf

fractional_ideal_type(::FlintRationalField) = ZZFracIdl

elem_in_nf(x::fmpz) = FlintQQ(x)

nf(::FlintIntegerRing) = FlintQQ
number_field(::FlintIntegerRing) = FlintQQ

# Infinite places

isreal(::PosInf) = true
is_complex(::PosInf) = false

infinite_places(::FlintRationalField) = [inf]
infinite_place(::FlintRationalField) = inf

function infinite_place(::FlintRationalField, i::Int)
  i !=1 && error("Index must be 1")
  return inf
end

real_places(::FlintRationalField) = PosInf[inf]

complex_places(::FlintRationalField) = PosInf[]

function sign(x::Union{fmpq,fmpz},p::PosInf)
  return Int(ZZ(sign(x)))
end

function signs(a::Union{fmpq,fmpz}, l::Vector{PosInf})
  return Dict((inf, sign(a)))
end

function is_positive(x::Union{fmpq,fmpz},p::PosInf)
  return x > 0
end

function is_totally_positive(x::Union{fmpq,fmpz},p::PosInf)
  return x > 0
end

function is_negative(x::Union{fmpq,fmpz},p::PosInf)
  return x < 0
end

number_field(::PosInf) = QQ

uniformizer(::PosInf) = QQ(-1)

infinite_places_uniformizers(::FlintRationalField) = fmpq[QQ(1)]

function hilbert_symbol(a,b, p::ZZIdl)
  return hilbert_symbol(a,b, gen(p))
end

is_local_norm(K, x, p::ZZIdl) = is_local_norm(K, x, gen(p))

function quadratic_defect(q::fmpq, p::ZZIdl)
  return quadratic_defect(q, gen(p))
end

################################################################################
#
#  Support
#
################################################################################

function support(a::fmpq, R::FlintIntegerRing)
  return ZZIdl[p*R for (p, _) in factor(a, R)]
end

################################################################################
#
#  CRT
#
################################################################################

function crt(a::Vector{fmpz}, b::Vector{ZZIdl})
  return crt(a, fmpz[gen(x) for x in b])
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
