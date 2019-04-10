export Localization, LocElem, Loc

###############################################################################

#   Declaration types
#   Loc / LocElem
#
###############################################################################

import AbstractAlgebra: base_ring, parent, check_parent, isunit, inv, +, -, *, divexact, zero, Base.promote_rule,
       elem_type, parent_type, Base.one, Base.iszero, Base.isone, Base.==, Base.gcd, Base.deepcopy_internal, needs_parentheses, valuation, Base.show,
       displayed_with_minus_in_front, show_minus_one, Base.^, data, Base.numerator, Base.denominator, canonical_unit, Base.gcdx, Base.div, divides,
       Base.lcm, Base.rand

import Nemo.prime

#prime might be product of several primes if localized at several primes, those primes are in array primes
mutable struct Loc{T<: RingElem} <: AbstractAlgebra.Ring
   base_ring::AbstractAlgebra.Ring
   prime::T
   primes::Array{T,1}

   function Loc{T}(prime::T, primes::Array{T,1}, cached::Bool = true) where {T <: RingElem}
      length(primes) == 0 && error("No element to localize at since array of primes is empty")
      if cached && haskey(LocDict, (parent(prime), prime))
         return LocDict[parent(prime), prime]::Loc{T}
      else
         z = new(parent(prime), prime, primes)
         if cached
            LocDict[parent(prime), prime] = z
         end
         return z
      end
   end
end


const LocDict = Dict{Tuple{AbstractAlgebra.Ring, RingElement}, AbstractAlgebra.Ring}()

mutable struct LocElem{T<: RingElem} <: AbstractAlgebra.RingElem
   data::FracElem{T}
   parent::Loc{T}
   function LocElem{T}(data::FracElem{T}, par::Loc, checked::Bool = true) where {T <: RingElem}
      checked && !isone(gcd(denominator(data), prime(par))) && error("No valid element of localization since its denominator and the primes localized at are not coprime")
      return new{T}(data,par)
   end
end

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

elem_type(::Type{Loc{T}}) where {T <: RingElem} = LocElem{T}

parent_type(::Type{LocElem{T}}) where {T <: RingElem} = Loc{T}

base_ring(L::Loc{T})  where {T <: RingElem}  = L.base_ring::parent_type(T)

base_ring(a::LocElem{T}) where {T <: RingElem} = base_ring(parent(a))

parent(a::LocElem{T})  where {T <: RingElem} = a.parent

function check_parent(a::LocElem{T}, b::LocElem{T})  where {T <: RingElem}
    parent(a) !== parent(b) && error("Parent objects do not match")
end


###############################################################################
#
#   Basic manipulation
#
###############################################################################

data(a::LocElem{T}) where {T <: RingElement} = a.data

numerator(a::LocElem{T}) where {T <: RingElement} = numerator(data(a))

denominator(a::LocElem{T}) where {T <: RingElement} = denominator(data(a))

prime(L::Loc{T}) where {T <: RingElement} = L.prime

primes(L::Loc{T}) where {T <: RingElement} = L.primes

zero(L::Loc{T}) where {T <: RingElement} = L(0)

one(L::Loc{T}) where {T <: RingElement} = L(1)

iszero(a::LocElem{T}) where {T <: RingElement} = iszero(data(a))

isone(a::LocElem{T}) where {T <: RingElement} = isone(data(a))

function isunit(a::LocElem{T})  where {T <: RingElem}
    return isone(gcd(numerator(data(a)),prime(parent(a))))
end

deepcopy_internal(a::LocElem{T}, dict::IdDict) where {T <: RingElem} = parent(a)(deepcopy(data(a)))

###############################################################################
#
#   AbstractString I/O
#
###############################################################################

function show(io::IO, a::LocElem{T}) where {T <: RingElem}
   print(io, data(a))
end

function show(io::IO, L::Loc{T}) where {T <: RingElem}
   print(io, "Localization of ", base_ring(L), " at ", primes(L))
end

needs_parentheses(x::LocElem{T})  where {T <: RingElem} = needs_parentheses(data(x))

displayed_with_minus_in_front(x::LocElem{T})  where {T <: RingElem} = displayed_with_minus_in_front(data(x))

show_minus_one(::Type{LocElem{T}}) where {T <: RingElement} = true

###############################################################################
#
#   Unary operations
#
###############################################################################

function -(a::LocElem{T})  where {T <: RingElem}
   parent(a)(-data(a))
end

###############################################################################
#
#   Binary operators
#
###############################################################################

function +(a::LocElem{T}, b::LocElem{T})  where {T <: RingElem}
   check_parent(a,b)
   return LocElem{T}(data(a) + data(b), parent(a), false)
end

function -(a::LocElem{T}, b::LocElem{T})  where {T <: RingElem}
   check_parent(a,b)
   return LocElem{T}(data(a) - data(b), parent(a), false)
end

function *(a::LocElem{T}, b::LocElem{T})  where {T <: RingElem}
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
> Returns the inverse element of $a$ if $a$ is a unit.
> If 'checked = false' the invertibility of $a$ is not checked and the corresponding inverse element
> of the Fraction Field is returned.
"""
function inv(a::LocElem{T}, checked::Bool = true)  where {T <: RingElem}
   checked && !isunit(a) && error("$a not invertible in given localization")
   return LocElem{T}(inv(data(a)), parent(a), false)
end

###############################################################################
#
#   Exact division
#
###############################################################################

@doc Markdown.doc"""
     divides(a::LocElem{T}, b::LocElem{T}, checked::Bool = true) where {T <: RingElem}
> Returns tuple (`true`,`c`) if $b$ divides $a$ where `c`*$b$ = $a$.
> If 'checked = false' the corresponding element of the Fraction Field is returned and it is not
> checked whether it is an element of the given localization.
"""
function divides(a::LocElem{T}, b::LocElem{T}, checked::Bool = true) where {T <: RingElem}
   check_parent(a,b)
   try
      true, parent(a)(divexact(data(a), data(b)), checked)
   catch
      false, parent(a)()
   end
end

@doc Markdown.doc"""
     divexact(a::LocElem{T}, b::LocElem{T}, checked::Bool = true)  where {T <: RingElem}
> Returns element 'c' of given localization s.th. `c`*$b$ = $a$ if such element exists.
> If 'checked = false' the corresponding element of the Fraction Field is returned and it is not
> checked whether it is an element of the given localization.
"""
function divexact(a::LocElem{T}, b::LocElem{T}, checked::Bool = true)  where {T <: RingElem}
   d = divides(a, b, checked)
   d[1] ? d[2] : error("$a not divisible by $b in the given Localization")
end

@doc Markdown.doc"""
     div(a::LocElem{T}, b::LocElem{T}, checked::Bool = true)  where {T <: RingElem}
> Returns element `c` if $b$ divides $a$ where `c`* $b$ = $a$.
> If $b$ does not divide $a$, `0`is returned.
> If 'checked = false' the corresponding element of the Fraction Field is returned and it is not
> checked whether it is an element of the given localization.
"""
function div(a::LocElem{T}, b::LocElem{T}, checked::Bool = true)  where {T <: RingElem}
   d = divides(a, b, checked)
   return d[2]
end

###############################################################################
#
#   GCD & LCM
#
###############################################################################

@doc Markdown.doc"""
    gcd(a::LocElem{T}, b::LocElem{T}) where {T <: RingElement}
> Returns gcd of $a$ and $b$ in canonical representation.
"""
function gcd(a::LocElem{T}, b::LocElem{T}) where {T <: RingElement}
   check_parent(a,b)
   iszero(a) && return canonical_unit(b) * b
   iszero(b) && return canonical_unit(a) * a
   par = parent(a)
   elem = prod([pi^min(valuation(a,pi), valuation(b,pi)) for pi in primes(par)])
   return par(elem)
end

@doc Markdown.doc"""
    lcm(a::LocElem{T}, b::LocElem{T}) where {T <: RingElement}
> Returns lcm of $a$ and $b$ in canonical representation.
"""
function lcm(a::LocElem{T}, b::LocElem{T}) where {T <: RingElement}
   check_parent(a,b)
   par = parent(a)
   (iszero(a) || iszero(b)) && return par()
   elem = prod([pi^max(valuation(a,pi), valuation(b,pi)) for pi in primes(par)])
   return par(elem)
end

###############################################################################
#
#   GCDX
#
###############################################################################

@doc Markdown.doc"""
    gcdx(a::LocElem{T}, b::LocElem{T}) where {T <: RingElement}
> Returns tuple `(g,u,v)` s.th. `g` = gcd($a$,$b$) and `g` = `u` * $a$ + `v` * $b$.
> Requires method gcdx for ring that is localized.
"""
function gcdx(a::LocElem{T}, b::LocElem{T}) where {T <: RingElement}
   check_parent(a,b)
   par = parent(a)
   g = gcd(a,b)
   can_a = canonical_unit(a)
   can_b = canonical_unit(b)
   a_temp = numerator(divexact(can_a * a, g, false))
   b_temp = numerator(divexact(can_b * b, g, false))
   (_,u,v) = gcdx(a_temp, b_temp)
   return (g, par(u)*can_a, par(v)*can_b)
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

function ^(a::LocElem{T}, b::Int) where {T <: RingElem}
   return LocElem{T}(data(a)^b, parent(a), false)
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

(L::Loc{T})() where {T <: RingElement} = L(zero(base_ring(L)))

(L::Loc{T})(a::Integer)  where {T <: RingElem} = L(base_ring(L)(a))

function (L::Loc{T})(data::FracElem{T}, checked::Bool = true) where {T <: RingElem}
   return LocElem{T}(data,L,checked)
end

function (L::Loc{T})(data::Rational{<: Integer}, checked::Bool = true) where {T <: RingElem}
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
    valuation(a::LocElem{T}) where {T <: RingElement}
> Returns the valuation of $a$ at the prime localized at. Only implemented for localizations at one prime ideal.
"""
function valuation(a::LocElem{T}) where {T <: RingElement}
   length(primes(parent(a))) != 1 && error("Only implemented for localizations at one prime ideal")
   return valuation(data(a), prime(parent(a)))
end

@doc Markdown.doc"""
    valuation(a::LocElem{T}, p::T) where {T <: RingElement}
> Returns the valuation `n` of $a$ at $p$, i.e. the integer `n` s.th $a$ = $p$^`n` * x, where x has valuation 0 at $p$
"""
valuation(a::LocElem{T}, p::T) where {T <: RingElement} = valuation(data(a), p)

###############################################################################
#
#   Canonicalisation
#
###############################################################################

@doc Markdown.doc"""
    canonical_unit(a::LocElem{T}) where {T <: RingElem}
> Returns unit `b`::LocElem{T} s.th. $a$ * `b` only consists of powers of primes localized at.
"""
function canonical_unit(a::LocElem{T}) where {T <: RingElem}
   temp = data(a)
   for pi in primes(parent(a))
      _,temp = remove(temp, pi)
   end
   return parent(a)(inv(temp))
end

###############################################################################
#
#   Constructors
#
###############################################################################

@doc Markdown.doc"""
    Localization(R::AbstractAlgebra.Ring, prime::T; cached=true) where {T <: RingElement}
> Returns the localization of the ring $R$ at the ideal generated by the ring element $prime$. Requires $R$ to
> be an euclidean domain and $prime$ to be a prime element, both not checked.
> If `cached == true` (the default) then the resulting
> localization parent object is cached and returned for any subsequent calls
> to the constructor with the same base ring $R$ and element $prime$.
"""
function Localization(R::AbstractAlgebra.Ring, prime::T; cached=true) where {T <: RingElement}
   primes = [R(prime)]
   return Loc{elem_type(R)}(R(prime), primes, cached)
end

@doc Markdown.doc"""
     Localization(R::AbstractAlgebra.Ring, primes::Array{T,1}; cached=true) where {T <: RingElement}
> Returns the localization of the ring $R$ at the union of principal ideals that are generated by the ring elements in $primes$.
> Requires $R$ to be an euclidean domain and $primes$ to be prime elements, both not checked.
> If `cached == true` (the default) then the resulting
> localization parent object is cached and returned for any subsequent calls
> to the constructor with the same base ring $R$ and elements $primes$.
"""
function Localization(R::AbstractAlgebra.Ring, primes::Array{T,1}; cached=true) where {T <: RingElement}
   prime = R(prod(primes))
   return Loc{elem_type(R)}(prime, Array{elem_type(R),1}(primes), cached)
end
