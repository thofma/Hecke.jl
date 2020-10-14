export Localization, LocElem, Loc

###############################################################################

#   Declaration types
#   Loc / LocElem
#
###############################################################################

import AbstractAlgebra: base_ring, parent, check_parent, isunit, +, -, *,
      divexact, zero, Base.promote_rule, elem_type, parent_type, Base.one,
      Base.iszero, Base.isone, Base.==, Base.gcd, Base.deepcopy_internal,
      needs_parentheses, Base.show, displayed_with_minus_in_front, show_minus_one,
      Base.^, data, Base.numerator, Base.denominator, canonical_unit, Base.gcdx,
      divides, Base.lcm, Base.rand
import Nemo: prime

#prime might be product of several primes if localized at several primes, those primes are in array primes
mutable struct Loc{T} <: AbstractAlgebra.Ring
   base_ring::AbstractAlgebra.Ring
   prime::T
   primes::Array{T,1}  # in general, not set.
   comp::Bool  # false: den has to be coprime to prime
               # true:  den can ONLY use prime (and powers)

   function Loc{T}(prime::T, primes::Array{T,1}, cached::Bool = true, comp::Bool = false) where {T <: RingElem}
      length(primes) == 0 && error("No element to localize at since array of primes is empty")
      if cached && haskey(LocDict, (parent(prime), prime, comp))
         return LocDict[parent(prime), prime, comp]::Loc{T}
      else
         z = new(parent(prime), prime, primes, comp)
         if cached
            LocDict[parent(prime), prime, comp] = z
         end
         return z
      end
   end
   function Loc{T}(prime::T, cached::Bool = true, comp::Bool = false) where {T <: RingElem}
     isunit(prime) && error("no-point")
     if cached && haskey(LocDict, (parent(prime), prime, comp))
       return LocDict[parent(prime), prime, comp]::Loc{T}
     else
       r = new()
       r.base_ring = parent(prime)
       r.prime = prime
       r.comp = comp
       if cached
          LocDict[parent(prime), prime, comp] = r
       end
       return r
     end
   end
end


const LocDict = Dict{Tuple{AbstractAlgebra.Ring, RingElement, Bool}, AbstractAlgebra.Ring}()

function isin(a, L::Loc{T}) where {T <: RingElem}
  iszero(a) && return true
  L.comp || (!isone(gcd(denominator(a), prime(L))) && return false)
  L.comp && ppio(denominator(a), prime(L))[1] != denominator(a.data) && return false
  return true
end

mutable struct LocElem{T} <: AbstractAlgebra.RingElem
   data::FieldElem
   parent::Loc{T}
   function LocElem{T}(data::FracElem{T}, par::Loc, checked::Bool = true) where {T <: RingElem}
     checked && (isin(data, par) || error("illegal elt"))
     return new{T}(data,par)
   end
end

#=

Let s be an integer (start with localisations in PIDs = Z)
and S = {x | gcd(x, s) = 1} (for s = p, S = Z \setminus p)

  the localsation L = S^-1 R = {a/b | gcd(b, s) = 1}

This is euclidean under N(a/b) = gcd(a, s^infty)

a_1*s_1/b_1 : a_2*s_2/b_2

  divrem(a_1 * s_1 * b_2, s_2) = q, r  => r < s_2
  a_1 s_1 b_2 = q s_2 + r

a_1*s_1/b_1 =   q/(a_2 b_1) *  a_2 s_2/b_2 + r/(b_1 b_2)


This works....


Now the other one:
  S = { s^i : i}
  L = S^-1 R  = { a/b | gcd(b, s^infty) = b}

a_1/s_1 : a_2/s_2   N(a/s) = |a/gcd(a, s^infty)|

a_1s_2 = q a_2 + r
a_1/s_1 = q/s_1 a_2/s_2 + r/(s1 s2)

===========================================
Poly: deg(N(a/b)), rest the same

===========================================
=#
###############################################################################
#
#   Unsafe operators and functions
#
###############################################################################

# TODO (easy): Do this properly
AbstractAlgebra.add!(c::LocElem, a::LocElem, b::LocElem) = a + b

AbstractAlgebra.mul!(c::LocElem, a::LocElem, b::LocElem) = a * b

AbstractAlgebra.addeq!(a::LocElem, b::LocElem) = a + b

###############################################################################
#
#   Data type and parent object methods
#
###############################################################################

elem_type(::Type{Loc{T}}) where {T} = LocElem{T}

parent_type(::Type{LocElem{T}}) where {T} = Loc{T}

base_ring(L::Loc) = L.base_ring

base_ring(a::LocElem) = base_ring(parent(a))

parent(a::LocElem) = a.parent

function check_parent(a::LocElem{T}, b::LocElem{T})  where {T <: RingElem}
    parent(a) !== parent(b) && error("Parent objects do not match")
end


###############################################################################
#
#   Basic manipulation
#
###############################################################################

data(a::LocElem) = a.data

numerator(a::LocElem{T}) where {T <: RingElement} = numerator(data(a))

denominator(a::LocElem{T}) where {T <: RingElement} = denominator(data(a))

prime(L::Loc) = L.prime

zero(L::Loc) = L(0)

one(L::Loc) = L(1)

iszero(a::LocElem) = iszero(data(a))

isone(a::LocElem) = isone(data(a))

function isunit(a::LocElem{T})  where {T <: RingElem}
  return isin(inv(a.data), parent(a))
end

deepcopy_internal(a::LocElem, dict::IdDict) = parent(a)(deepcopy(data(a)))

###############################################################################
#
#   AbstractString I/O
#
###############################################################################

function show(io::IO, a::LocElem)
   print(io, data(a))
end

function show(io::IO, L::Loc)
   if L.comp
     print(io, "Localization of ", base_ring(L), " at complement of ", prime(L))
   else
     print(io, "Localization of ", base_ring(L), " at ", prime(L))
   end
end

needs_parentheses(x::LocElem) = needs_parentheses(data(x))

displayed_with_minus_in_front(x::LocElem) = displayed_with_minus_in_front(data(x))

show_minus_one(::Type{LocElem{T}}) where {T <: RingElement} = true
show_minus_one(::Type{LocElem{NfOrdIdl}}) = true

###############################################################################
#
#   Unary operations
#
###############################################################################

function -(a::LocElem)
   parent(a)(-data(a))
end

###############################################################################
#
#   Binary operators
#
###############################################################################

function +(a::LocElem{T}, b::LocElem) where {T}
   check_parent(a,b)
   return LocElem{T}(data(a) + data(b), parent(a), false)
end

function -(a::LocElem{T}, b::LocElem{T})  where {T}
   check_parent(a,b)
   return LocElem{T}(data(a) - data(b), parent(a), false)
end

function *(a::LocElem{T}, b::LocElem{T})  where {T}
   check_parent(a,b)
   return LocElem{T}(data(a) * data(b), parent(a), false)
end

###############################################################################
#
#   Comparison
#
###############################################################################

function ==(a::LocElem{T}, b::LocElem{T}) where {T <: RingElement}
   check_parent(a, b)
   return data(a) == data(b)
end

###############################################################################
#
#   Inversion
#
###############################################################################

@doc Markdown.doc"""
     inv(a::LocElem{T}, checked::Bool = true)  where {T <: RingElem}
Returns the inverse element of $a$ if $a$ is a unit.
If 'checked = false' the invertibility of $a$ is not checked and the corresponding inverse element
of the Fraction Field is returned.
"""
function inv(a::LocElem{T}, checked::Bool = true)  where {T}
   b = inv(a.data)
   checked && (isin(b, parent(a)) || error("no unit"))
   return LocElem{T}(b, parent(a), false)
end

###############################################################################
#
#   Exact division
#
###############################################################################

@doc Markdown.doc"""
     divides(a::LocElem{T}, b::LocElem{T}, checked::Bool = true) where {T <: RingElem}
Returns tuple (`true`,`c`) if $b$ divides $a$ where `c`*$b$ = $a$.
If 'checked = false' the corresponding element of the Fraction Field is returned and it is not
checked whether it is an element of the given localization.
"""
function divides(a::LocElem, b::LocElem, checked::Bool = true)
   check_parent(a,b)
   c = divexact(data(a), data(b))
   isin(c, parent(a)) && return true, parent(a)(c, checked)
   return false, a
end

@doc Markdown.doc"""
     divexact(a::LocElem{T}, b::LocElem{T}, checked::Bool = true)  where {T <: RingElem}
Returns element 'c' of given localization s.th. `c`*$b$ = $a$ if such element exists.
If 'checked = false' the corresponding element of the Fraction Field is returned and it is not
checked whether it is an element of the given localization.
"""
function divexact(a::LocElem, b::LocElem, checked::Bool = true)
   d = divides(a, b, checked)
   d[1] ? d[2] : error("$a not divisible by $b in the given Localization")
end

@doc Markdown.doc"""
     divrem(a::LocElem{T}, b::LocElem{T}, checked::Bool = true)  where {T <: RingElem}
In case the ring is euclidean, return a euclidean division.
"""
function Base.divrem(a::LocElem{T}, b::LocElem{T}, checked::Bool = true)  where {T <: RingElem}
  check_parent(a, b)
  L = parent(a)
  if L.comp
    a1, s1 = ppio(numerator(a.data), L.prime)
    a2, s2 = ppio(numerator(b.data), L.prime)
    b1 = denominator(a)
    b2 = denominator(b)
    q, r = divrem(a1 * s1 * b2, s2)
    return L(q//(a2*b1), checked), L(r//(b1*b2), checked)
  else
    q, r = divrem(numerator(a)*denominator(b), numerator(b))
    return L(q//denominator(a), checked), L(r//(denominator(a)*denominator(b)), checked)
  end
end

function Base.div(a::LocElem{T}, b::LocElem{T}) where {T}
  return divrem(a, b)[1]
end

function rem(a::LocElem{T}, b::LocElem{T}) where {T}
  return divrem(a, b)[2]
end

function euclid(a::LocElem{T}) where {T <: RingElem}
  L = parent(a)
  if L.comp
    return ppio(numerator(a.data), L.prime)[1]
  else
    return ppio(numerator(a.data), L.prime)[2]
  end
end

###############################################################################
#
#   GCD & LCM
#
###############################################################################

@doc Markdown.doc"""
    gcd(a::LocElem{T}, b::LocElem{T}) where {T <: RingElement}
Returns gcd of $a$ and $b$ in canonical representation.
"""
function gcd(a::LocElem{T}, b::LocElem{T}) where {T <: RingElement}
   check_parent(a,b)
   iszero(a) && return inv(canonical_unit(b)) * b
   iszero(b) && return inv(canonical_unit(a)) * a
   par = parent(a)
   if par.comp
     elem = ppio(gcd(numerator(a.data), numerator(b.data)), parent(a).prime)[2]
   else
     elem = ppio(gcd(numerator(a.data), numerator(b.data)), parent(a).prime)[1]
   end
   return par(elem)
end

@doc Markdown.doc"""
    lcm(a::LocElem{T}, b::LocElem{T}) where {T <: RingElement}
Returns lcm of $a$ and $b$ in canonical representation.
"""
function lcm(a::LocElem{T}, b::LocElem{T}) where {T <: RingElement}
   check_parent(a,b)
   par = parent(a)
   (iszero(a) || iszero(b)) && return par()
   if par.comp
     elem = ppio(lcm(numerator(a.data), numerator(b.data)), parent(a).prime)[2]
   else
     elem = ppio(lcm(numerator(a.data), numerator(b.data)), parent(a).prime)[1]
   end
   return par(elem)
end

###############################################################################
#
#   GCDX
#
###############################################################################

@doc Markdown.doc"""
    gcdx(a::LocElem{T}, b::LocElem{T}) where {T <: RingElement}
Returns tuple `(g,u,v)` s.th. `g` = gcd($a$,$b$) and `g` = `u` * $a$ + `v` * $b$.
Requires method gcdx for ring that is localized.
"""
function gcdx(a::LocElem{T}, b::LocElem{T}) where {T <: RingElement}
   check_parent(a,b)
   L = parent(a)
   g, u, v = gcdx(numerator(a.data), numerator(b.data))
   c = inv(canonical_unit(L(g)))
   return c*L(g), c*L(u*denominator(a.data)), c*L(v*denominator(b.data))
end

###############################################################################
#
#   Random Functions
#
###############################################################################

#mainly for testing
function rand(L::Loc{T}, num_scale = (1:1000), den_scale=(1:1000)) where {T <: fmpz}
   num = rand(num_scale)
   den = rand(den_scale)
   while gcd(den,prime(L)) != 1
      den = rand(den_scale)
   end
   return L(num//den)
end
###############################################################################
#
#   Powering
#
###############################################################################

function ^(a::LocElem, b::Int)
   return parent(a)(data(a)^b, parent(a), false)
end

###############################################################################
#
#   Promotion rules
#
###############################################################################

promote_rule(::Type{LocElem{T}}, ::Type{LocElem{T}}) where {T <: RingElement} = LocElem{T}


###############################################################################
#
#   Parent object call overloading
#
###############################################################################

(L::Loc{T})() where {T} = L(zero(base_ring(L)))

(L::Loc{T})(a::Integer)  where {T} = L(base_ring(L)(a))

function (L::Loc{T})(data::FracElem{T}, checked::Bool = true) where {T <: RingElem}
   return LocElem{T}(data,L,checked)
end

function (L::Loc{T})(data::Rational{<: Integer}, checked::Bool = true) where {T}
   return LocElem{T}(base_ring(L)(numerator(data)) // base_ring(L)(denominator(data)),L,checked)
end

function (L::Loc{T})(data::T, checked::Bool = false) where {T <: RingElem}
   return LocElem{T}(data // parent(data)(1),L,checked)
end

function (L::Loc{T})(a::LocElem{T}) where {T <: RingElement}
   L != parent(a) && error("No element of $L")
   return a
end

################################################################################
#
#   Valuation
#
################################################################################

@doc Markdown.doc"""
    valuation(a::LocElem{T}, p::T) where {T <: RingElement}
Returns the valuation `n` of $a$ at $p$, i.e. the integer `n` s.th $a$ = $p$^`n` * x, where x has valuation 0 at $p$.
"""
valuation(a::LocElem{T}, p::T) where {T <: RingElement} = valuation(data(a), p)

###############################################################################
#
#   Canonicalisation
#
###############################################################################

@doc Markdown.doc"""
    canonical_unit(a::LocElem{T}) where {T <: RingElem}
Returns unit `b`::LocElem{T} s.th. $a$ * `b` only consists of powers of primes localized at.
"""
function canonical_unit(a::LocElem{T}) where {T <: RingElem}
   if parent(a).comp
     b = ppio(numerator(a.data), parent(a).prime)[1]
   else
     b = ppio(numerator(a.data), parent(a).prime)[2]
   end
   return parent(a)(b//denominator(a.data))
end

###############################################################################
#
#   Constructors
#
###############################################################################

@doc Markdown.doc"""
    Localization(R::AbstractAlgebra.Ring, prime::T; cached=true, comp=false) where {T <: RingElement}
Returns the localization of the ring $R$ at the ideal generated by the ring element $prime$. Requires $R$ to
be an euclidean domain and $prime$ to be a prime element, both not checked.
If `cached == true` (the default) then the resulting
localization parent object is cached and returned for any subsequent calls
to the constructor with the same base ring $R$ and element $prime$.
"""
function Localization(R::AbstractAlgebra.Ring, prime::T; cached::Bool=true, comp::Bool = false) where {T <: RingElement}
   return Loc{elem_type(R)}(R(prime), cached, comp)
end

@doc Markdown.doc"""
     Localization(R::AbstractAlgebra.Ring, primes::Array{T,1}; cached=true) where {T <: RingElement}
Returns the localization of the ring $R$ at the union of principal ideals that are generated by the ring elements in $primes$.
Requires $R$ to be an euclidean domain and $primes$ to be prime elements, both not checked.
If `cached == true` (the default) then the resulting
localization parent object is cached and returned for any subsequent calls
to the constructor with the same base ring $R$ and elements $primes$.
"""
function Localization(R::AbstractAlgebra.Ring, primes::Array{T,1}; cached=true) where {T <: RingElement}
   prime = R(prod(primes))
   return Loc{elem_type(R)}(prime, Array{elem_type(R),1}(primes), cached)
end
