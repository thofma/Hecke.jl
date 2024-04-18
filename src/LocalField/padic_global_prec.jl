# Copied from Nemo: src/flint/padic.jl
# s/PadicField/PadicField2/g
# s/PadicField2Elem/PadicFieldElem2/g

###############################################################################
#
#   Data type and parent object methods
#
###############################################################################

@doc raw"""
    O(R::PadicField2, m::ZZRingElem)

Construct the value $0 + O(p^n)$ given $m = p^n$. An exception results if $m$
is not found to be a power of `p = prime(R)`.
"""
function O(R::PadicField2, m::ZZRingElem)
   if isone(m)
      N = 0
   else
      p = prime(R)
      if m == p
         N = 1
      else
         N = flog(m, p)
         p^(N) != m && error("Not a power of p in p-adic O()")
      end
   end
   d = PadicFieldElem2(N)
   d.parent = R
   return d
end

@doc raw"""
    O(R::PadicField2, m::QQFieldElem)

Construct the value $0 + O(p^n)$ given $m = p^n$. An exception results if $m$
is not found to be a power of `p = prime(R)`.
"""
function O(R::PadicField2, m::QQFieldElem)
   d = denominator(m)
   if isone(d)
      return O(R, numerator(m))
   end
   !isone(numerator(m)) && error("Not a power of p in p-adic O()")
   p = prime(R)
   if d == p
      N = -1
   else
     N = -flog(d, p)
     p^(-N) != d && error("Not a power of p in p-adic O()")
   end
   r = PadicFieldElem2(N)
   r.parent = R
   return r
end

@doc raw"""
    O(R::PadicField2, m::Integer)

Construct the value $0 + O(p^n)$ given $m = p^n$. An exception results if $m$
is not found to be a power of `p = prime(R)`.
"""
O(R::PadicField2, m::Integer) = O(R, ZZRingElem(m))

elem_type(::Type{PadicField2}) = PadicFieldElem2

base_ring(a::PadicField2) = Union{}

base_ring(a::PadicFieldElem2) = Union{}

parent(a::PadicFieldElem2) = a.parent

is_domain_type(::Type{PadicFieldElem2}) = true

is_exact_type(R::Type{PadicFieldElem2}) = false

function check_parent(a::PadicFieldElem2, b::PadicFieldElem2)
   parent(a) != parent(b) &&
      error("Incompatible padic rings in padic operation")
end

parent_type(::Type{PadicFieldElem2}) = PadicField2

###############################################################################
#
#   Basic manipulation
#
###############################################################################

function Base.deepcopy_internal(a::PadicFieldElem2, dict::IdDict)
   z = parent(a)()
   z.N = precision(a)      # set does not transfer N - neither should it.
   ccall((:padic_set, libflint), Nothing,
         (Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicField2}), z, a, parent(a))
   return z
end

function Base.hash(a::PadicFieldElem2, h::UInt)
   return xor(hash(lift(FlintQQ, a), h), xor(hash(prime(parent(a)), h), h))
end

@doc raw"""
    prime(R::PadicField2)

Return the prime $p$ for the given $p$-adic field.
"""
function prime(R::PadicField2)
   z = ZZRingElem()
   ccall((:padic_ctx_pow_ui, libflint), Nothing,
         (Ref{ZZRingElem}, Int, Ref{PadicField2}), z, 1, R)
   return z
end

@doc raw"""
    precision(a::PadicFieldElem2)

Return the precision of the given $p$-adic field element, i.e. if the element
is known to $O(p^n)$ this function will return $n$.
"""
precision(a::PadicFieldElem2) = a.N

@doc raw"""
    valuation(a::PadicFieldElem2)

Return the valuation of the given $p$-adic field element, i.e. if the given
element is divisible by $p^n$ but not a higher power of $p$ then the function
will return $n$.
"""
valuation(a::PadicFieldElem2) = iszero(a) ? precision(a) : a.v

@doc raw"""
    lift(R::QQField, a::PadicFieldElem2)

Return a lift of the given $p$-adic field element to $\mathbb{Q}$.
"""
function lift(R::QQField, a::PadicFieldElem2)
    ctx = parent(a)
    r = QQFieldElem()
    ccall((:padic_get_fmpq, libflint), Nothing,
          (Ref{QQFieldElem}, Ref{PadicFieldElem2}, Ref{PadicField2}), r, a, ctx)
    return r
end

@doc raw"""
    lift(R::ZZRing, a::PadicFieldElem2)

Return a lift of the given $p$-adic field element to $\mathbb{Z}$.
"""
function lift(R::ZZRing, a::PadicFieldElem2)
    ctx = parent(a)
    r = ZZRingElem()
    ccall((:padic_get_fmpz, libflint), Nothing,
          (Ref{ZZRingElem}, Ref{PadicFieldElem2}, Ref{PadicField2}), r, a, ctx)
    return r
end

function zero(R::PadicField2)
   z = PadicFieldElem2(precision(PadicField2))
   ccall((:padic_zero, libflint), Nothing, (Ref{PadicFieldElem2},), z)
   z.parent = R
   return z
end

function one(R::PadicField2)
   z = PadicFieldElem2(precision(PadicField2))
   ccall((:padic_one, libflint), Nothing, (Ref{PadicFieldElem2},), z)
   z.parent = R
   return z
end

iszero(a::PadicFieldElem2) = Bool(ccall((:padic_is_zero, libflint), Cint,
                              (Ref{PadicFieldElem2},), a))

isone(a::PadicFieldElem2) = Bool(ccall((:padic_is_one, libflint), Cint,
                             (Ref{PadicFieldElem2},), a))

is_unit(a::PadicFieldElem2) = !Bool(ccall((:padic_is_zero, libflint), Cint,
                              (Ref{PadicFieldElem2},), a))

characteristic(R::PadicField2) = 0

###############################################################################
#
#   String I/O
#
###############################################################################

const PADIC_PRINTING_MODE2 = Ref(Cint(1))

@doc raw"""
    get_printing_mode(::Type{PadicField2})

Get the printing mode for the elements of the p-adic field `R`.
"""
function get_printing_mode(::Type{PadicField2})
   return flint_padic_printing_mode[PADIC_PRINTING_MODE2[] + 1]
end

@doc raw"""
    set_printing_mode(::Type{PadicField2}, printing::Symbol)

Set the printing mode for the elements of the p-adic field `R`. Possible values
are `:terse`, `:series` and `:val_unit`.
"""
function set_printing_mode(::Type{PadicField2}, printing::Symbol)
   if printing == :terse
      PADIC_PRINTING_MODE2[] = 0
   elseif printing == :series
      PADIC_PRINTING_MODE2[] = 1
   elseif printing == :val_unit
      PADIC_PRINTING_MODE2[] = 2
   else
      error("Invalid printing mode: $printing")
   end
   return printing
end

function expressify(x::PadicFieldElem2; context = nothing)
   p = BigInt(prime(parent(x)))
   pmode = PADIC_PRINTING_MODE2[]
   sum = Expr(:call, :+)
   if iszero(x)
      push!(sum.args, 0)
   elseif pmode == 0  # terse
      push!(sum.args, expressify(lift(FlintQQ, x), context = context))
   else
      pp = prime(parent(x))
      p = BigInt(pp)
      v = valuation(x)
      if v >= 0
        u = BigInt(lift(FlintZZ, x))
        if v > 0
          u = div(u, p^v)
        end
      else
        u = lift(FlintZZ, x*p^-v)
      end

      if pmode == 1  # series
         d = digits(u, base=p)
      else  # val_unit
         d = [u]
      end
      for i in 0:length(d)-1
         ppower = Expr(:call, :^, p, i + v)
         push!(sum.args, Expr(:call, :*, d[i + 1], ppower))
      end
   end
   push!(sum.args, Expr(:call, :O, Expr(:call, :^, p, precision(x))))
   return sum
end

function show(io::IO, a::PadicFieldElem2)
   print(io, AbstractAlgebra.obj_to_string(a, context = io))
end

function show(io::IO, R::PadicField2)
   if get(io, :supercompact, false)
     io = pretty(io)
     print(io, LowercaseOff(), "QQ_$(prime(R))")
   else
     print(io, "Field of ", prime(R), "-adic numbers")
   end
end

###############################################################################
#
#   Canonicalisation
#
###############################################################################

canonical_unit(x::PadicFieldElem2) = x

###############################################################################
#
#   Unary operators
#
###############################################################################

function -(x::PadicFieldElem2)
   if iszero(x)
      return x
   end
   ctx = parent(x)
   z = PadicFieldElem2(precision(x))
   ccall((:padic_neg, libflint), Nothing,
         (Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicField2}),
                     z, x, ctx)
   z.parent = ctx
   return z
end

###############################################################################
#
#   Binary operators
#
###############################################################################

function +(x::PadicFieldElem2, y::PadicFieldElem2)
   check_parent(x, y)
   ctx = parent(x)
   z = PadicFieldElem2(min(precision(x), precision(y)))
   z.parent = ctx
   ccall((:padic_add, libflint), Nothing,
         (Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicField2}),
               z, x, y, ctx)
   return z
end

function -(x::PadicFieldElem2, y::PadicFieldElem2)
   check_parent(x, y)
   ctx = parent(x)
   z = PadicFieldElem2(min(precision(x), precision(y)))
   z.parent = ctx
   ccall((:padic_sub, libflint), Nothing,
         (Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicField2}),
                  z, x, y, ctx)
   return z
end

function *(x::PadicFieldElem2, y::PadicFieldElem2)
   check_parent(x, y)
   ctx = parent(x)
   z = PadicFieldElem2(min(precision(x) + valuation(y), precision(y) + valuation(x)))
   z.parent = ctx
   ccall((:padic_mul, libflint), Nothing,
         (Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicField2}),
               z, x, y, ctx)
   return z
end

###############################################################################
#
#   Ad hoc binary operators
#
###############################################################################

+(a::PadicFieldElem2, b::Integer) = a + parent(a)(b)

+(a::PadicFieldElem2, b::ZZRingElem) = a + parent(a)(b)

+(a::PadicFieldElem2, b::QQFieldElem) = a + parent(a)(b)

+(a::Integer, b::PadicFieldElem2) = b + a

+(a::ZZRingElem, b::PadicFieldElem2) = b + a

+(a::QQFieldElem, b::PadicFieldElem2) = b + a

-(a::PadicFieldElem2, b::Integer) = a - parent(a)(b)

-(a::PadicFieldElem2, b::ZZRingElem) = a - parent(a)(b)

-(a::PadicFieldElem2, b::QQFieldElem) = a - parent(a)(b)

-(a::Integer, b::PadicFieldElem2) = parent(b)(a) - b

-(a::ZZRingElem, b::PadicFieldElem2) = parent(b)(a) - b

-(a::QQFieldElem, b::PadicFieldElem2) = parent(b)(a) - b

*(a::PadicFieldElem2, b::Integer) = a*parent(a)(b)

*(a::PadicFieldElem2, b::ZZRingElem) = a*parent(a)(b)

*(a::PadicFieldElem2, b::QQFieldElem) = a*parent(a)(b)

*(a::Integer, b::PadicFieldElem2) = b*a

*(a::ZZRingElem, b::PadicFieldElem2) = b*a

*(a::QQFieldElem, b::PadicFieldElem2) = b*a

###############################################################################
#
#   Comparison
#
###############################################################################

function ==(a::PadicFieldElem2, b::PadicFieldElem2)
   check_parent(a, b)
   ctx = parent(a)
   z = PadicFieldElem2(min(precision(a), precision(b)))
   ccall((:padic_sub, libflint), Nothing,
         (Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicField2}),
               z, a, b, ctx)
   return Bool(ccall((:padic_is_zero, libflint), Cint,
                (Ref{PadicFieldElem2},), z))
end

function isequal(a::PadicFieldElem2, b::PadicFieldElem2)
   if parent(a) != parent(b)
      return false
   end
   return precision(a) == precision(b) && a == b
end

###############################################################################
#
#   Ad hoc comparison
#
###############################################################################

==(a::PadicFieldElem2, b::Integer) = a == parent(a)(b)

==(a::PadicFieldElem2, b::ZZRingElem) = a == parent(a)(b)

==(a::PadicFieldElem2, b::QQFieldElem) = a == parent(a)(b)

==(a::Integer, b::PadicFieldElem2) = parent(b)(a) == b

==(a::ZZRingElem, b::PadicFieldElem2) = parent(b)(a) == b

==(a::QQFieldElem, b::PadicFieldElem2) = parent(b)(a) == b

###############################################################################
#
#   Powering
#
###############################################################################

function ^(a::PadicFieldElem2, n::Int)
   ctx = parent(a)
   z = PadicFieldElem2(precision(a) + (n - 1)*a.v)
   z.parent = ctx
   ccall((:padic_pow_si, libflint), Nothing,
                (Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Int, Ref{PadicField2}),
               z, a, n, ctx)
   return z
end

###############################################################################
#
#   Exact division
#
###############################################################################

function divexact(a::PadicFieldElem2, b::PadicFieldElem2; check::Bool=true)
   iszero(b) && throw(DivideError())
   check_parent(a, b)
   ctx = parent(a)
   z = PadicFieldElem2(min(precision(a) - valuation(b), precision(b) - 2*valuation(b) + valuation(a)))
   z.parent = ctx
   ccall((:padic_div, libflint), Cint,
         (Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicField2}),
               z, a, b, ctx)
   return z
end

###############################################################################
#
#   Ad hoc exact division
#
###############################################################################

divexact(a::PadicFieldElem2, b::Integer; check::Bool=true) = a*(ZZRingElem(1)//ZZRingElem(b))

divexact(a::PadicFieldElem2, b::ZZRingElem; check::Bool=true) = a*(1//b)

divexact(a::PadicFieldElem2, b::QQFieldElem; check::Bool=true) = a*inv(b)

divexact(a::Integer, b::PadicFieldElem2; check::Bool=true) = ZZRingElem(a)*inv(b)

divexact(a::ZZRingElem, b::PadicFieldElem2; check::Bool=true) = inv((ZZRingElem(1)//a)*b)

divexact(a::QQFieldElem, b::PadicFieldElem2; check::Bool=true) = inv(inv(a)*b)

###############################################################################
#
#   Inversion
#
###############################################################################

function inv(a::PadicFieldElem2)
   iszero(a) && throw(DivideError())
   ctx = parent(a)
   z = PadicFieldElem2(precision(a) - 2*valuation(a))
   z.parent = ctx
   ccall((:padic_inv, libflint), Cint,
         (Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicField2}), z, a, ctx)
   return z
end

###############################################################################
#
#   Divides
#
###############################################################################

function divides(a::PadicFieldElem2, b::PadicFieldElem2)
   if iszero(a)
      return true, zero(parent(a))
   end
   if iszero(b)
      return false, zero(parent(a))
   end
   return true, divexact(a, b)
end

###############################################################################
#
#   GCD
#
###############################################################################

function gcd(x::PadicFieldElem2, y::PadicFieldElem2)
   check_parent(x, y)
   if iszero(x) && iszero(y)
      z = zero(parent(x))
   else
      z = one(parent(x))
   end
   return z
end

###############################################################################
#
#   Square root
#
###############################################################################

function Base.sqrt(a::PadicFieldElem2; check::Bool=true)
   check && (a.v % 2) != 0 && error("Unable to take padic square root")
   ctx = parent(a)
   z = PadicFieldElem2(precision(a) - div(valuation(a), 2))
   z.parent = ctx
   res = Bool(ccall((:padic_sqrt, libflint), Cint,
                    (Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicField2}), z, a, ctx))
   check && !res && error("Square root of p-adic does not exist")
   return z
end

function is_square(a::PadicFieldElem2)
   if iszero(a)
      return true
   end
   if (a.v % 2) != 0
      return false
   end
   R = parent(a)
   u = ZZRingElem()
   ccall((:padic_get_unit, libflint), Nothing,
          (Ref{ZZRingElem}, Ref{PadicFieldElem2}), u, a)
   p = prime(R)
   if p == 2
      umod = mod(u, 8)
      return umod == 1
   else
      umod = mod(u, p)
      r = ccall((:n_jacobi, libflint), Cint, (UInt, UInt), umod, p)
      return isone(r)
   end
end

function is_square_with_sqrt(a::PadicFieldElem2)
   R = parent(a)
   if (a.v % 2) != 0
      return false, zero(R)
   end
   ctx = parent(a)
   z = PadicFieldElem2(precision(a) - div(valuation(a), 2))
   z.parent = ctx
   res = Bool(ccall((:padic_sqrt, libflint), Cint,
                    (Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicField2}), z, a, ctx))
   if !res
      return false, zero(R)
   end
   return true, z
end

###############################################################################
#
#   Special functions
#
###############################################################################

function Base.exp(a::PadicFieldElem2)
   !iszero(a) && a.v <= 0 && throw(DomainError(a, "Valuation must be positive"))
   ctx = parent(a)
   z = PadicFieldElem2(precision(a))
   z.parent = ctx
   res = Bool(ccall((:padic_exp, libflint), Cint,
                    (Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicField2}), z, a, ctx))
   !res && error("Unable to compute exponential")
   return z
end

function log(a::PadicFieldElem2)
   ctx = parent(a)
   z = PadicFieldElem2(precision(a))
   z.parent = ctx
   v = valuation(a)
   v == 0 || error("Unable to compute logarithm")
   v = valuation(a-1)
   if v == 0
     a = a^(prime(ctx)-1)
   end
   res = Bool(ccall((:padic_log, libflint), Cint,
                    (Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicField2}), z, a, ctx))
   !res && error("Unable to compute logarithm")
   if v == 0
     z = z//(prime(ctx)-1)
   end
   return z
end

@doc raw"""
    teichmuller(a::PadicFieldElem2)

Return the Teichmuller lift of the $p$-adic value $a$. We require the
valuation of $a$ to be non-negative. The precision of the output will be the
same as the precision of the input. For convenience, if $a$ is congruent to
zero modulo $p$ we return zero. If the input is not valid an exception is
thrown.
"""
function teichmuller(a::PadicFieldElem2)
   a.v < 0 && throw(DomainError(a.v, "Valuation must be non-negative"))
   ctx = parent(a)
   z = PadicFieldElem2(precision(a))
   z.parent = ctx
   ccall((:padic_teichmuller, libflint), Nothing,
         (Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicField2}), z, a, ctx)
   return z
end

###############################################################################
#
#   Unsafe operators
#
###############################################################################

function zero!(z::PadicFieldElem2)
   z.N = precision(PadicField2)
   ctx = parent(z)
   ccall((:padic_zero, libflint), Nothing,
         (Ref{PadicFieldElem2}, Ref{PadicField2}), z, ctx)
   return z
end

function mul!(z::PadicFieldElem2, x::PadicFieldElem2, y::PadicFieldElem2)
   z.N = min(precision(x) + valuation(y), precision(y) + valuation(x))
   ctx = parent(x)
   ccall((:padic_mul, libflint), Nothing,
         (Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicField2}),
               z, x, y, ctx)
   return z
end

function addeq!(x::PadicFieldElem2, y::PadicFieldElem2)
   x.N = min(precision(x), precision(y))
   ctx = parent(x)
   ccall((:padic_add, libflint), Nothing,
         (Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicField2}),
               x, x, y, ctx)
   return x
end

function add!(z::PadicFieldElem2, x::PadicFieldElem2, y::PadicFieldElem2)
   z.N = min(precision(x), precision(y))
   ctx = parent(x)
   ccall((:padic_add, libflint), Nothing,
         (Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicFieldElem2}, Ref{PadicField2}),
               z, x, y, ctx)
   return z
end

###############################################################################
#
#   Conversions and promotions
#
###############################################################################

promote_rule(::Type{PadicFieldElem2}, ::Type{T}) where {T <: Integer} = PadicFieldElem2

promote_rule(::Type{PadicFieldElem2}, ::Type{ZZRingElem}) = PadicFieldElem2

promote_rule(::Type{PadicFieldElem2}, ::Type{QQFieldElem}) = PadicFieldElem2

###############################################################################
#
#   Parent object overloads
#
###############################################################################

function (R::PadicField2)()
   z = PadicFieldElem2(precision(PadicField2))
   z.parent = R
   return z
end

function (R::PadicField2)(n::ZZRingElem)
   if isone(n)
      N = 0
   else
      p = prime(R)
      N, = remove(n, p)
   end
   z = PadicFieldElem2(N + precision(PadicField2))
   ccall((:padic_set_fmpz, libflint), Nothing,
         (Ref{PadicFieldElem2}, Ref{ZZRingElem}, Ref{PadicField2}), z, n, R)
   z.parent = R
   return z
end

function (R::PadicField2)(n::QQFieldElem)
   m = denominator(n)
   if isone(m)
      return R(numerator(n))
   end
   p = prime(R)
   if m == p
      N = -1
   else
     N = -remove(m, p)[1]
   end
   z = PadicFieldElem2(N + precision(PadicField2))
   ccall((:padic_set_fmpq, libflint), Nothing,
         (Ref{PadicFieldElem2}, Ref{QQFieldElem}, Ref{PadicField2}), z, n, R)
   z.parent = R
   return z
end

(R::PadicField2)(n::Integer) = R(ZZRingElem(n))

function (R::PadicField2)(n::PadicFieldElem2)
   parent(n) != R && error("Unable to coerce into p-adic field")
   return n
end

###############################################################################
#
#   PadicField2 constructor
#
###############################################################################

# inner constructor is also used directly

@doc raw"""
    PadicField2(p::Integer; kw...)

Returns the parent object for the $p$-adic field for given prime $p$.
"""
function PadicField2(p::Integer; kw...)
   return PadicField2(ZZRingElem(p); kw...)
end
