###############################################################################
#
#   Declaration types
#   OrdLoc / OrdLocElem
#
###############################################################################

mutable struct OrdLoc{T<:AbsSimpleNumFieldElem} <: Hecke.Ring
   OK::AbsNumFieldOrder{AbsSimpleNumField,T}
   prime::AbsNumFieldOrderIdeal{AbsSimpleNumField,T}
   comp::Bool

   function OrdLoc{T}(OK::AbsNumFieldOrder{AbsSimpleNumField,T}, prime::AbsNumFieldOrderIdeal{AbsSimpleNumField,T}, cached::Bool = true, comp::Bool = false) where {T <: AbsSimpleNumFieldElem}
      return get_cached!(OrdLocDict, (OK, prime, comp), cached) do
         return new(OK, prime, comp)
      end::OrdLoc{T}
   end
end

function ppio(a::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, b::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
   c = gcd(a, b)
   n = divexact(a, c)
   g = gcd(c, n)
   while !isone(g)
      c *= g
      n = divexact(n, g)
      g = gcd(c, n)
   end
   return c, n
end

function is_in(a::AbsSimpleNumFieldElem, L::OrdLoc{<:AbsSimpleNumFieldElem})
  iszero(a) && return true
  n, d = integral_split(a*L.OK)
  L.comp || (!isone(gcd(d, L.prime)) && return false)
  L.comp && ppio(d, L.prime)[1] != d && return false
  return true
end

#=
s an ideal (or element = principal ideal)
  S = { x in R | v_p(x) = 0 for all p | s}
  L = { x in K | gcd(den(<x>), s) = 1} = {a/b | v_p(a) - v_p(b) >= 0 for all p|s}
    N(x) = norm(num(<x>) + s^infty)
         = prod N(p)^v_p(x)    p|s
    K -> prod R_(p)  for p | s where R_(p) = {x | v_p(x) >=0 } subset R_p = completion at p
      find q_p, r_p s.th.
      a = q_p b + r_p and v_p(r_p) < v_p(b) (either a or 0)
      any r in K s.th. v_p(r) = v_p(r_p) should be a valid remainder, q = (a-r)/b is the quotient
        c = num(<a>) + s^infty
        d = num(<b>) + s^infty
        den(c/d) has support all p where v_p(c) < v_p(d)
        r = a mod (den(c/d)^2)
          = 0 mod s/gcd(s, den(c,d))
        should work...

some more detail in divrem

  S = { x in R | v_p(x) = 0 for all p not | s}
  L = { x in K | gcd(den(<x>), s^infty) = den(<x>) } = {a/b | v_p(a) - v_p(b) >= 0 for all p not | s}
    N(x) = norm(num(<x>):s^infty)
         = prod N(p)^v_p(x)    p not | s
    in general not euclidean since not PID (S = 1 => R = R).
    if S large enough (gen class group), then PID

=#

OrdLocDict = AbstractAlgebra.CacheDictType{Tuple{AbsNumFieldOrder{AbsSimpleNumField,AbsSimpleNumFieldElem}, AbsNumFieldOrderIdeal{AbsSimpleNumField,AbsSimpleNumFieldElem}, Bool}, Hecke.Ring}()

mutable struct OrdLocElem{T<:AbsSimpleNumFieldElem} <: RingElem
   data::T
   parent::OrdLoc{T}

   function OrdLocElem{T}(data::T, par::OrdLoc, checked::Bool = true) where {T <:AbsSimpleNumFieldElem}
      data == zero(parent(data)) && return new{T}(data,par)
      checked && (!is_in(data, par)) && error("No valid element of localization")
      return new{T}(data,par)
   end
end

###############################################################################
#
#   Unsafe operators and functions
#
###############################################################################

add!(c::OrdLocElem, a::OrdLocElem, b::OrdLocElem) = a + b

mul!(c::OrdLocElem, a::OrdLocElem, b::OrdLocElem) = a * b

###############################################################################
#
#   Data type and parent object methods
#
###############################################################################

elem_type(::Type{OrdLoc{T}}) where {T <: AbsSimpleNumFieldElem} = OrdLocElem{T}

parent_type(::Type{OrdLocElem{T}}) where {T <: AbsSimpleNumFieldElem} = OrdLoc{T}

order(L::OrdLoc{T}) where {T <: AbsSimpleNumFieldElem}  = L.OK

order(a::OrdLocElem{T}) where {T <: AbsSimpleNumFieldElem}  = order(parent(a))

nf(L::OrdLoc{T}) where {T <: AbsSimpleNumFieldElem}  = nf(L.OK)::parent_type(T)

nf(a::OrdLocElem{T}) where {T <: AbsSimpleNumFieldElem} = nf(parent(a))

parent(a::OrdLocElem{T})  where {T <: AbsSimpleNumFieldElem} = a.parent

###############################################################################
#
#   Basic manipulation
#
###############################################################################

data(a::OrdLocElem{T}) where {T <: AbsSimpleNumFieldElem} = a.data

numerator(a::OrdLocElem{T}) where {T <: AbsSimpleNumFieldElem} = numerator(data(a))

denominator(a::OrdLocElem{T}) where {T <: AbsSimpleNumFieldElem} = denominator(data(a))

prime(L::OrdLoc{T}) where {T <: AbsSimpleNumFieldElem} = L.prime

prime(a::OrdLocElem{T}) where {T <: AbsSimpleNumFieldElem} = prime(parent(a))

zero(L::OrdLoc{T}) where {T <: AbsSimpleNumFieldElem} = L(0)

one(L::OrdLoc{T}) where {T <: AbsSimpleNumFieldElem} = L(1)

iszero(a::OrdLocElem{T}) where {T <: AbsSimpleNumFieldElem} = iszero(data(a))

isone(a::OrdLocElem{T}) where {T <: AbsSimpleNumFieldElem} = isone(data(a))

function in(x::AbsSimpleNumFieldElem, L::OrdLoc)
   iszero(x) ? true :
   return is_in(x, L)
end

function is_unit(a::OrdLocElem{T})  where {T <: AbsSimpleNumFieldElem}
   iszero(a) ? false :
    return is_in(inv(a.data), parent(a))
end

deepcopy_internal(a::OrdLocElem{T}, dict::IdDict) where {T <: AbsSimpleNumFieldElem} = parent(a)(deepcopy(data(a)))

###############################################################################
#
#   AbstractString I/O
#
###############################################################################

function AbstractAlgebra.expressify(a::OrdLocElem; context = nothing)
  return AbstractAlgebra.expressify(data(a), context = context)
end

function show(io::IO, a::OrdLocElem)
   print(io, AbstractAlgebra.obj_to_string(a, context = io))
end

function show(io::IO, L::OrdLoc{T}) where {T <: AbsSimpleNumFieldElem}
  if L.comp
    print(io, "Localization of ", order(L), " at complement of ", prime(L))
  else
    print(io, "Localization of ", order(L), " at ", prime(L))
  end
end

##############################################################################
#
#   Unary operations
#
##############################################################################

function -(a::OrdLocElem{T})  where {T <: AbsSimpleNumFieldElem}
   parent(a)(-data(a))
end

###############################################################################
#
#   Binary operators
#
###############################################################################

function +(a::OrdLocElem{T}, b::OrdLocElem{T})  where {T <: AbsSimpleNumFieldElem}
   check_parent(a,b)
   return parent(a)(data(a) + data(b), false)
end

function -(a::OrdLocElem{T}, b::OrdLocElem{T})  where {T <: AbsSimpleNumFieldElem}
   check_parent(a,b)
   return parent(a)(data(a) - data(b), false)
end

function *(a::OrdLocElem{T}, b::OrdLocElem{T})  where {T <: AbsSimpleNumFieldElem}
   check_parent(a,b)
   return parent(a)(data(a) * data(b), false)
end

###############################################################################
#
#   Comparison
#
###############################################################################

function ==(a::OrdLocElem{T}, b::OrdLocElem{T}) where {T <: AbsSimpleNumFieldElem}
   check_parent(a, b)
   return data(a) == data(b)
end

##############################################################################
#
#  Inversion
#
##############################################################################

@doc raw"""
     inv(a::OrdLocElem{T}, checked::Bool = true)  where {T <: AbsSimpleNumFieldElem}
Returns the inverse element of $a$ if $a$ is a unit.
If 'checked = false' the invertibility of $a$ is not checked and the corresponding inverse element
of the numberfield is returned.
"""
function inv(a::OrdLocElem{T}, checked::Bool = true)  where {T <: AbsSimpleNumFieldElem}
   b = inv(data(a))
   checked && (!is_in(b, parent(a))) && error("$a not invertible in given localization")
   return parent(a)(b, false)
end

##############################################################################
#
#  Exact division
#
##############################################################################

@doc raw"""
     divides(a::OrdLocElem{T}, b::OrdLocElem{T}, checked::Bool = true) where {T <: AbsSimpleNumFieldElem}
Returns tuple (`true`,`c`) if $b$ divides $a$ where `c`*$b$ = $a$.
If 'checked = false' the corresponding element of the numberfield is returned and it is not
checked whether it is an element of the given localization.
"""
function divides(a::OrdLocElem{T}, b::OrdLocElem{T}, checked::Bool = true) where {T <: AbsSimpleNumFieldElem}
   check_parent(a,b)

   if iszero(b)
     if iszero(a)
       return true, parent(a)()
     else
       return false, parent(a)()
     end
   end

   elem = divexact(data(a), data(b))
   if !checked
      return true, parent(a)(elem, checked)
   elseif checked && in(elem,parent(a))
      return true, parent(a)(elem)
   else
      return false, parent(a)()
   end
end

@doc raw"""
     divexact(a::OrdLocElem{T}, b::OrdLocElem{T}, checked::Bool = true)  where {T <: AbsSimpleNumFieldElem}
Returns element 'c' of given localization s.th. `c`*$b$ = $a$ if such element exists.
If 'checked = false' the corresponding element of the numberfield is returned and it is not
checked whether it is an element of the given localization.
"""
function divexact(a::OrdLocElem{T}, b::OrdLocElem{T}, checked::Bool = true)  where {T <: AbsSimpleNumFieldElem}
   d = divides(a, b, checked)
   d[1] ? d[2] : error("$a not divisible by $b in the given localization")
end

@doc raw"""
     div(a::OrdLocElem{T}, b::OrdLocElem{T}, checked::Bool = true)  where {T <: AbsSimpleNumFieldElem}
"""
function _make_legal(a::AbsSimpleNumFieldElem, S::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  d = denominator(a, order(S))
  n = order(S)(d*a)
  b, _ = ppio(d*order(S), S)
  bi = inv(b)
  x = bi.num.gen_two.elem_in_nf//bi.den
  # a in OrdLoc(S) implies the true den of a is coprime to S
  # return a = n/d with n, d in the order and d coprime to S
  R = order(S)
  @assert (n*x) in R
  @assert (d*x) in R
  @assert isone(R(d*x)*R + S)
  return n*x, d*x
end

function divrem(a::OrdLocElem, b::OrdLocElem, checked::Bool = true)
  L = parent(a)
  L.comp && error("ring not known to be useful euclidean")

  na, da = _make_legal(a.data, L.prime)
  nb, db = _make_legal(b.data, L.prime)

  A = na*db
  B = nb*da
  #Plan: A = qB + R
  #then a = q/da b + R/db/da
  #moving to the residue ring (B+S^infty)*S helps
  # the euclidean function is the same, and division works in there
  # Plan: get the reminder from there, then lift and compute the quotient

  C = ppio(L.OK(B)*L.OK, L.prime)[1]*L.prime
  Q, mQ = quo(L.OK, C)
  R = L(preimage(mQ, divrem(mQ(L.OK(A)), mQ(L.OK(B)))[2]))

  r = divexact(R, L(da*db))
  q = divexact(a-r, b)
  @assert iszero(r) || euclid(r) < euclid(b)
  return q, r
end
#=
#XXX: those do not seem to be there for AbsOrdQuoRingElems
function div(a::OrdLocElem{T}, b::OrdLocElem{T}, checked::Bool = true)  where {T <: AbsSimpleNumFieldElem}
   return divrem(a, b)[1]
end

function rem(a::OrdLocElem{T}, b::OrdLocElem{T}, checked::Bool = true)  where {T <: AbsSimpleNumFieldElem}
   return divrem(a, b)[2]
end
=#

function euclid(a::OrdLocElem)
  iszero(a) && return ZZRingElem(0)
  L = parent(a)
  L.comp && error("ring not known to be useful euclidean")
  N, _ = integral_split(a.data * L.OK)
  N, _ = ppio(N, L.prime)
  return norm(N)
end

###############################################################################
#
#   GCD
#
###############################################################################

@doc raw"""
    gcd(a::OrdLocElem{T}, b::OrdLocElem{T}) where {T <: AbsSimpleNumFieldElem}

Returns gcd of $a$ and $b$ in canonical representation.
"""
function gcd(a::OrdLocElem{T}, b::OrdLocElem{T}) where {T <: AbsSimpleNumFieldElem}
  L = parent(a)
  L.comp && error("ring not known to be useful euclidean")
   check_parent(a,b)
   iszero(a) && return inv(canonical_unit(b)) * b
   iszero(b) && return inv(canonical_unit(a)) * a
   na, _ = _make_legal(a.data, L.prime)
   nb, _ = _make_legal(b.data, L.prime)
   g = L.OK(na) * L.OK + L.OK(nb) * L.OK + L.prime
   assure_2_normal(g)
   elem = L(g.gen_two)
   return inv(canonical_unit(elem)) * (elem)
end


###############################################################################
#
#   GCDX
#
###############################################################################

@doc raw"""
    gcdx(a::OrdLocElem{T}, b::OrdLocElem{T}) where {T <: AbsSimpleNumFieldElem}

Returns tuple `(g,u,v)` s.th. `g` = gcd($a$,$b$) and `g` = `u` * $a$ + `v` * $b$.
"""
function gcdx(a::OrdLocElem{T}, b::OrdLocElem{T}) where {T <: AbsSimpleNumFieldElem}
  L = parent(a)
  L.comp && error("ring not known to be useful euclidean")
   check_parent(a,b)
   L = parent(a)
   M = [L(1) L(0); L(0) L(1)]
   while !iszero(b)
     q,r = divrem(a, b)
     M = [L(0) L(1); L(1) L(-q)] * M
     a, b = b, r
   end
   c = inv(canonical_unit(a))
   return a*c, M[1,1]*c, M[1,2]*c
end

###############################################################################
#
#   PID
#
###############################################################################

function principal_generator(L::OrdLoc{T}, I::AbsNumFieldOrderIdeal{AbsSimpleNumField,T}) where {T <: AbsSimpleNumFieldElem}
  #possible for !L.comp due to semi local
  #theoretical for L.comp if L.prime large enough...
   valuation(L(I.gen_one)) >= valuation(L(I.gen_two)) ? L(I.gen_two) : L(I.gen_one)
end


###############################################################################
#
#   Powering
#
###############################################################################

function ^(a::OrdLocElem{T}, b::Int) where {T <: AbsSimpleNumFieldElem}
   return parent(a)(data(a)^b, false)
end

###############################################################################
#
#   Random Functions
#
###############################################################################

RandomExtensions.maketype(R::OrdLoc, _) = elem_type(R)

function rand(rng::AbstractRNG, sp::SamplerTrivial{<:Make2{OrdLocElem{T}, OrdLoc{T},
                                                           <:AbstractUnitRange{Int}}}) where {T}
   O, r = sp[][1:end]
   X = make(nf(O), r)
   while true
     _temp = rand(rng, X)
     if is_in(_temp, O)
       return O(_temp, false)
     end
   end
end

rand(rng::AbstractRNG, R::OrdLoc, r::AbstractUnitRange{Int}) = rand(rng, make(R, r))

rand(K::OrdLoc{T}, r::AbstractVector) where {T <: AbsSimpleNumFieldElem} = rand(Random.GLOBAL_RNG, K, r)

###############################################################################
#
#   Promotion rules
#
###############################################################################

AbstractAlgebra.promote_rule(::Type{OrdLocElem{T}}, ::Type{OrdLocElem{T}}) where {T <: AbsSimpleNumFieldElem} = OrdLocElem{T}

###############################################################################
#
#   Parent object call overloading
#
###############################################################################

(L::OrdLoc{T})() where {T <: AbsSimpleNumFieldElem} = L(zero(nf(L)))

(L::OrdLoc{T})(a::Integer)  where {T <: AbsSimpleNumFieldElem} = L(nf(L)(a))

function (L::OrdLoc{T})(data::T, checked::Bool = true) where {T <: AbsSimpleNumFieldElem}
   return OrdLocElem{T}(data,L,checked)
end

function (L::OrdLoc{T})(data::AbsNumFieldOrderElem{AbsSimpleNumField,T}, checked::Bool = true) where {T <: AbsSimpleNumFieldElem}
   return OrdLocElem{T}(nf(parent(data))(data),L,checked)
end

function (L::OrdLoc{T})(data::Rational{<: Integer}, checked::Bool = true) where {T <: AbsSimpleNumFieldElem}
   return OrdLocElem{T}(nf(L)(numerator(data)) // nf(L)(denominator(data)),L,checked)
end

function (L::OrdLoc{T})(data::ZZRingElem, checked::Bool = true) where {T <: AbsSimpleNumFieldElem}
   return OrdLocElem{T}(nf(L)(data),L,checked)
end

function (L::OrdLoc{T})(a::OrdLocElem{T}) where {T <: AbsSimpleNumFieldElem}
   L != parent(a) && error("No element of $L")
   return a
end

################################################################################
#
#   Valuation
#
################################################################################

@doc raw"""
    valuation(a::OrdLocElem{T}, prime::AbsNumFieldOrderIdeal{AbsSimpleNumField,T}) where {T <: AbsSimpleNumFieldElem}

Returns the valuation `n` of $a$ at $P$.
"""
valuation(a::OrdLocElem{T}, prime::AbsNumFieldOrderIdeal{AbsSimpleNumField,T}) where {T <: AbsSimpleNumFieldElem} = valuation(data(a), prime)

###############################################################################
#
#   Canonicalisation
#
###############################################################################

@doc raw"""
    canonical_unit(a::OrdLocElem{T}) where {T <: AbsSimpleNumFieldElem}

Returns unit `b`::OrdLocElem{T} s.th. ($a$ * inv(`b`)) is hopefully nicer.
"""
function canonical_unit(a::OrdLocElem{T}) where {T <: AbsSimpleNumFieldElem}
   iszero(a) && return parent(a)(1)
   is_unit(a) && return a
   L = parent(a)
   if L.comp
     return L(1)
   else
     na, _ = _make_legal(a.data, L.prime)
     A = ppio(L.OK(na)*L.OK, L.prime)[1] * L.prime
     z = mod(L.OK(na), A)
     #L(z) should be equivalent to a, since v_p(A) = v_p(a) + 1`for all p | prime
     # u = a//z
     u = divexact(a, L(z))
     @assert is_unit(u)
     return divexact(a, L(z))
   end

end

###############################################################################
#
#   Constructors
#
###############################################################################

@doc raw"""
    localization(OK::AbsNumFieldOrder{AbsSimpleNumField,T}, S::AbsNumFieldOrderIdeal{AbsSimpleNumField,T}; cached=true, comp = false) where {T <: AbsSimpleNumFieldElem}

Returns the localization of the order $OK$ at the ideal $S$.
If `cached == true` (the default) then the resulting
localization parent object is cached and returned for any subsequent calls
to the constructor with the same order $OK$ and ideal $S$.
`comp == false` means primes dividing $S$ are invertible,
`comp == true` means all primes not dividing $S$ become units.
"""
function localization(OK::AbsNumFieldOrder{AbsSimpleNumField,T}, S::AbsNumFieldOrderIdeal{AbsSimpleNumField,T}; cached=true, comp::Bool = false) where {T <: AbsSimpleNumFieldElem}
   return OrdLoc{T}(OK, S, cached, comp)
end
