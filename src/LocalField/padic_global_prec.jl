###############################################################################
#
#   Data type and parent object methods
#
###############################################################################

@doc raw"""
    O(R::PadicField, m::ZZRingElem)

Construct the value $0 + O(p^n)$ given $m = p^n$. An exception results if $m$
is not found to be a power of `p = prime(R)`.
"""
function O(R::PadicField, m::ZZRingElem)
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
   d = PadicFieldElem(N)
   d.parent = R
   return d
end

@doc raw"""
    O(R::PadicField, m::QQFieldElem)

Construct the value $0 + O(p^n)$ given $m = p^n$. An exception results if $m$
is not found to be a power of `p = prime(R)`.
"""
function O(R::PadicField, m::QQFieldElem)
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
   r = PadicFieldElem(N)
   r.parent = R
   return r
end

@doc raw"""
    O(R::PadicField, m::Integer)

Construct the value $0 + O(p^n)$ given $m = p^n$. An exception results if $m$
is not found to be a power of `p = prime(R)`.
"""
O(R::PadicField, m::Integer) = O(R, ZZRingElem(m))

elem_type(::Type{PadicField}) = PadicFieldElem

base_ring(a::PadicField) = Union{}

base_ring(a::PadicFieldElem) = Union{}

parent(a::PadicFieldElem) = a.parent

is_domain_type(::Type{PadicFieldElem}) = true

is_exact_type(R::Type{PadicFieldElem}) = false

function check_parent(a::PadicFieldElem, b::PadicFieldElem)
   parent(a) != parent(b) &&
      error("Incompatible padic rings in padic operation")
end

parent_type(::Type{PadicFieldElem}) = PadicField

###############################################################################
#
#   Basic manipulation
#
###############################################################################

function Base.deepcopy_internal(a::PadicFieldElem, dict::IdDict)
   z = parent(a)()
   z.N = precision(a)      # set does not transfer N - neither should it.
   ccall((:padic_set, libflint), Nothing,
         (Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicField}), z, a, parent(a))
   return z
end

function Base.hash(a::PadicFieldElem, h::UInt)
   return xor(hash(lift(FlintQQ, a), h), xor(hash(prime(parent(a)), h), h))
end

@doc raw"""
    prime(R::PadicField)

Return the prime $p$ for the given $p$-adic field.
"""
function prime(R::PadicField)
   z = ZZRingElem()
   ccall((:padic_ctx_pow_ui, libflint), Nothing,
         (Ref{ZZRingElem}, Int, Ref{PadicField}), z, 1, R)
   return z
end

@doc raw"""
    precision(a::PadicFieldElem)

Return the precision of the given $p$-adic field element, i.e. if the element
is known to $O(p^n)$ this function will return $n$.
"""
precision(a::PadicFieldElem) = a.N

@doc raw"""
    valuation(a::PadicFieldElem)

Return the valuation of the given $p$-adic field element, i.e. if the given
element is divisible by $p^n$ but not a higher power of $p$ then the function
will return $n$.
"""
valuation(a::PadicFieldElem) = iszero(a) ? precision(a) : a.v

@doc raw"""
    lift(R::QQField, a::PadicFieldElem)

Return a lift of the given $p$-adic field element to $\mathbb{Q}$.
"""
function lift(R::QQField, a::PadicFieldElem)
    ctx = parent(a)
    r = QQFieldElem()
    ccall((:padic_get_fmpq, libflint), Nothing,
          (Ref{QQFieldElem}, Ref{PadicFieldElem}, Ref{PadicField}), r, a, ctx)
    return r
end

@doc raw"""
    lift(R::ZZRing, a::PadicFieldElem)

Return a lift of the given $p$-adic field element to $\mathbb{Z}$.
"""
function lift(R::ZZRing, a::PadicFieldElem)
    ctx = parent(a)
    r = ZZRingElem()
    ccall((:padic_get_fmpz, libflint), Nothing,
          (Ref{ZZRingElem}, Ref{PadicFieldElem}, Ref{PadicField}), r, a, ctx)
    return r
end

function zero(R::PadicField)
   z = PadicFieldElem(precision(PadicField))
   ccall((:padic_zero, libflint), Nothing, (Ref{PadicFieldElem},), z)
   z.parent = R
   return z
end

function one(R::PadicField)
   z = PadicFieldElem(precision(PadicField))
   ccall((:padic_one, libflint), Nothing, (Ref{PadicFieldElem},), z)
   z.parent = R
   return z
end

iszero(a::PadicFieldElem) = Bool(ccall((:padic_is_zero, libflint), Cint,
                              (Ref{PadicFieldElem},), a))

isone(a::PadicFieldElem) = Bool(ccall((:padic_is_one, libflint), Cint,
                             (Ref{PadicFieldElem},), a))

is_unit(a::PadicFieldElem) = !Bool(ccall((:padic_is_zero, libflint), Cint,
                              (Ref{PadicFieldElem},), a))

characteristic(R::PadicField) = 0

###############################################################################
#
#   String I/O
#
###############################################################################

const PADIC_PRINTING_MODE2 = Ref(Cint(1))

@doc raw"""
    get_printing_mode(::Type{PadicField})

Get the printing mode for the elements of the p-adic field `R`.
"""
function get_printing_mode(::Type{PadicField})
   return flint_padic_printing_mode[PADIC_PRINTING_MODE2[] + 1]
end

@doc raw"""
    set_printing_mode(::Type{PadicField}, printing::Symbol)

Set the printing mode for the elements of the p-adic field `R`. Possible values
are `:terse`, `:series` and `:val_unit`.
"""
function set_printing_mode(::Type{PadicField}, printing::Symbol)
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

function expressify(x::PadicFieldElem; context = nothing)
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

function show(io::IO, a::PadicFieldElem)
   print(io, AbstractAlgebra.obj_to_string(a, context = io))
end

function show(io::IO, R::PadicField)
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

canonical_unit(x::PadicFieldElem) = x

###############################################################################
#
#   Unary operators
#
###############################################################################

function -(x::PadicFieldElem)
   if iszero(x)
      return x
   end
   ctx = parent(x)
   z = PadicFieldElem(precision(x))
   ccall((:padic_neg, libflint), Nothing,
         (Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicField}),
                     z, x, ctx)
   z.parent = ctx
   return z
end

###############################################################################
#
#   Binary operators
#
###############################################################################

function +(x::PadicFieldElem, y::PadicFieldElem)
   check_parent(x, y)
   ctx = parent(x)
   z = PadicFieldElem(min(precision(x), precision(y)))
   z.parent = ctx
   ccall((:padic_add, libflint), Nothing,
         (Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicField}),
               z, x, y, ctx)
   return z
end

function -(x::PadicFieldElem, y::PadicFieldElem)
   check_parent(x, y)
   ctx = parent(x)
   z = PadicFieldElem(min(precision(x), precision(y)))
   z.parent = ctx
   ccall((:padic_sub, libflint), Nothing,
         (Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicField}),
                  z, x, y, ctx)
   return z
end

function *(x::PadicFieldElem, y::PadicFieldElem)
   check_parent(x, y)
   ctx = parent(x)
   z = PadicFieldElem(min(precision(x) + valuation(y), precision(y) + valuation(x)))
   z.parent = ctx
   ccall((:padic_mul, libflint), Nothing,
         (Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicField}),
               z, x, y, ctx)
   return z
end

###############################################################################
#
#   Ad hoc binary operators
#
###############################################################################

+(a::PadicFieldElem, b::Integer) = a + parent(a)(b)

+(a::PadicFieldElem, b::ZZRingElem) = a + parent(a)(b)

+(a::PadicFieldElem, b::QQFieldElem) = a + parent(a)(b)

+(a::Integer, b::PadicFieldElem) = b + a

+(a::ZZRingElem, b::PadicFieldElem) = b + a

+(a::QQFieldElem, b::PadicFieldElem) = b + a

-(a::PadicFieldElem, b::Integer) = a - parent(a)(b)

-(a::PadicFieldElem, b::ZZRingElem) = a - parent(a)(b)

-(a::PadicFieldElem, b::QQFieldElem) = a - parent(a)(b)

-(a::Integer, b::PadicFieldElem) = parent(b)(a) - b

-(a::ZZRingElem, b::PadicFieldElem) = parent(b)(a) - b

-(a::QQFieldElem, b::PadicFieldElem) = parent(b)(a) - b

*(a::PadicFieldElem, b::Integer) = a*parent(a)(b)

*(a::PadicFieldElem, b::ZZRingElem) = a*parent(a)(b)

*(a::PadicFieldElem, b::QQFieldElem) = a*parent(a)(b)

*(a::Integer, b::PadicFieldElem) = b*a

*(a::ZZRingElem, b::PadicFieldElem) = b*a

*(a::QQFieldElem, b::PadicFieldElem) = b*a

###############################################################################
#
#   Comparison
#
###############################################################################

function ==(a::PadicFieldElem, b::PadicFieldElem)
   check_parent(a, b)
   ctx = parent(a)
   z = PadicFieldElem(min(precision(a), precision(b)))
   ccall((:padic_sub, libflint), Nothing,
         (Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicField}),
               z, a, b, ctx)
   return Bool(ccall((:padic_is_zero, libflint), Cint,
                (Ref{PadicFieldElem},), z))
end

function isequal(a::PadicFieldElem, b::PadicFieldElem)
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

==(a::PadicFieldElem, b::Integer) = a == parent(a)(b)

==(a::PadicFieldElem, b::ZZRingElem) = a == parent(a)(b)

==(a::PadicFieldElem, b::QQFieldElem) = a == parent(a)(b)

==(a::Integer, b::PadicFieldElem) = parent(b)(a) == b

==(a::ZZRingElem, b::PadicFieldElem) = parent(b)(a) == b

==(a::QQFieldElem, b::PadicFieldElem) = parent(b)(a) == b

###############################################################################
#
#   Powering
#
###############################################################################

function ^(a::PadicFieldElem, n::Int)
   ctx = parent(a)
   z = PadicFieldElem(precision(a) + (n - 1)*a.v)
   z.parent = ctx
   ccall((:padic_pow_si, libflint), Nothing,
                (Ref{PadicFieldElem}, Ref{PadicFieldElem}, Int, Ref{PadicField}),
               z, a, n, ctx)
   return z
end

###############################################################################
#
#   Exact division
#
###############################################################################

function divexact(a::PadicFieldElem, b::PadicFieldElem; check::Bool=true)
   iszero(b) && throw(DivideError())
   check_parent(a, b)
   ctx = parent(a)
   z = PadicFieldElem(min(precision(a) - valuation(b), precision(b) - 2*valuation(b) + valuation(a)))
   z.parent = ctx
   ccall((:padic_div, libflint), Cint,
         (Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicField}),
               z, a, b, ctx)
   return z
end

###############################################################################
#
#   Ad hoc exact division
#
###############################################################################

divexact(a::PadicFieldElem, b::Integer; check::Bool=true) = a*(ZZRingElem(1)//ZZRingElem(b))

divexact(a::PadicFieldElem, b::ZZRingElem; check::Bool=true) = a*(1//b)

divexact(a::PadicFieldElem, b::QQFieldElem; check::Bool=true) = a*inv(b)

divexact(a::Integer, b::PadicFieldElem; check::Bool=true) = ZZRingElem(a)*inv(b)

divexact(a::ZZRingElem, b::PadicFieldElem; check::Bool=true) = inv((ZZRingElem(1)//a)*b)

divexact(a::QQFieldElem, b::PadicFieldElem; check::Bool=true) = inv(inv(a)*b)

###############################################################################
#
#   Inversion
#
###############################################################################

function inv(a::PadicFieldElem)
   iszero(a) && throw(DivideError())
   ctx = parent(a)
   z = PadicFieldElem(precision(a) - 2*valuation(a))
   z.parent = ctx
   ccall((:padic_inv, libflint), Cint,
         (Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicField}), z, a, ctx)
   return z
end

###############################################################################
#
#   Divides
#
###############################################################################

function divides(a::PadicFieldElem, b::PadicFieldElem)
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

function gcd(x::PadicFieldElem, y::PadicFieldElem)
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

function Base.sqrt(a::PadicFieldElem; check::Bool=true)
   check && (a.v % 2) != 0 && error("Unable to take padic square root")
   ctx = parent(a)
   z = PadicFieldElem(precision(a) - div(valuation(a), 2))
   z.parent = ctx
   res = Bool(ccall((:padic_sqrt, libflint), Cint,
                    (Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicField}), z, a, ctx))
   check && !res && error("Square root of p-adic does not exist")
   return z
end

function is_square(a::PadicFieldElem)
   if iszero(a)
      return true
   end
   if (a.v % 2) != 0
      return false
   end
   R = parent(a)
   u = ZZRingElem()
   ccall((:padic_get_unit, libflint), Nothing,
          (Ref{ZZRingElem}, Ref{PadicFieldElem}), u, a)
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

function is_square_with_sqrt(a::PadicFieldElem)
   R = parent(a)
   if (a.v % 2) != 0
      return false, zero(R)
   end
   ctx = parent(a)
   z = PadicFieldElem(precision(a) - div(valuation(a), 2))
   z.parent = ctx
   res = Bool(ccall((:padic_sqrt, libflint), Cint,
                    (Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicField}), z, a, ctx))
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

function Base.exp(a::PadicFieldElem)
   !iszero(a) && a.v <= 0 && throw(DomainError(a, "Valuation must be positive"))
   ctx = parent(a)
   z = PadicFieldElem(precision(a))
   z.parent = ctx
   res = Bool(ccall((:padic_exp, libflint), Cint,
                    (Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicField}), z, a, ctx))
   !res && error("Unable to compute exponential")
   return z
end

function log(a::PadicFieldElem)
   ctx = parent(a)
   z = PadicFieldElem(precision(a))
   z.parent = ctx
   v = valuation(a)
   v == 0 || error("Unable to compute logarithm")
   v = valuation(a-1)
   if v == 0
     a = a^(prime(ctx)-1)
   end
   res = Bool(ccall((:padic_log, libflint), Cint,
                    (Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicField}), z, a, ctx))
   !res && error("Unable to compute logarithm")
   if v == 0
     z = z//(prime(ctx)-1)
   end
   return z
end

@doc raw"""
    teichmuller(a::PadicFieldElem)

Return the Teichmuller lift of the $p$-adic value $a$. We require the
valuation of $a$ to be non-negative. The precision of the output will be the
same as the precision of the input. For convenience, if $a$ is congruent to
zero modulo $p$ we return zero. If the input is not valid an exception is
thrown.
"""
function teichmuller(a::PadicFieldElem)
   a.v < 0 && throw(DomainError(a.v, "Valuation must be non-negative"))
   ctx = parent(a)
   z = PadicFieldElem(precision(a))
   z.parent = ctx
   ccall((:padic_teichmuller, libflint), Nothing,
         (Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicField}), z, a, ctx)
   return z
end

###############################################################################
#
#   Unsafe operators
#
###############################################################################

function zero!(z::PadicFieldElem)
   z.N = precision(PadicField)
   ctx = parent(z)
   ccall((:padic_zero, libflint), Nothing,
         (Ref{PadicFieldElem}, Ref{PadicField}), z, ctx)
   return z
end

function mul!(z::PadicFieldElem, x::PadicFieldElem, y::PadicFieldElem)
   z.N = min(precision(x) + valuation(y), precision(y) + valuation(x))
   ctx = parent(x)
   ccall((:padic_mul, libflint), Nothing,
         (Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicField}),
               z, x, y, ctx)
   return z
end

function addeq!(x::PadicFieldElem, y::PadicFieldElem)
   x.N = min(precision(x), precision(y))
   ctx = parent(x)
   ccall((:padic_add, libflint), Nothing,
         (Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicField}),
               x, x, y, ctx)
   return x
end

function add!(z::PadicFieldElem, x::PadicFieldElem, y::PadicFieldElem)
   z.N = min(precision(x), precision(y))
   ctx = parent(x)
   ccall((:padic_add, libflint), Nothing,
         (Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicField}),
               z, x, y, ctx)
   return z
end

###############################################################################
#
#   Conversions and promotions
#
###############################################################################

promote_rule(::Type{PadicFieldElem}, ::Type{T}) where {T <: Integer} = PadicFieldElem

promote_rule(::Type{PadicFieldElem}, ::Type{ZZRingElem}) = PadicFieldElem

promote_rule(::Type{PadicFieldElem}, ::Type{QQFieldElem}) = PadicFieldElem

###############################################################################
#
#   Parent object overloads
#
###############################################################################

function (R::PadicField)()
   z = PadicFieldElem(precision(PadicField))
   z.parent = R
   return z
end

function (R::PadicField)(n::ZZRingElem)
   if isone(n)
      N = 0
   else
      p = prime(R)
      N, = remove(n, p)
   end
   z = PadicFieldElem(N + precision(PadicField))
   ccall((:padic_set_fmpz, libflint), Nothing,
         (Ref{PadicFieldElem}, Ref{ZZRingElem}, Ref{PadicField}), z, n, R)
   z.parent = R
   return z
end

function (R::PadicField)(n::QQFieldElem)
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
   z = PadicFieldElem(N + precision(PadicField))
   ccall((:padic_set_fmpq, libflint), Nothing,
         (Ref{PadicFieldElem}, Ref{QQFieldElem}, Ref{PadicField}), z, n, R)
   z.parent = R
   return z
end

(R::PadicField)(n::Integer) = R(ZZRingElem(n))

function (R::PadicField)(n::PadicFieldElem)
   parent(n) != R && error("Unable to coerce into p-adic field")
   return n
end

###############################################################################
#
#   PadicField constructor
#
###############################################################################

# inner constructor is also used directly

@doc raw"""
    PadicField(p::Integer; kw...)

Returns the parent object for the $p$-adic field for given prime $p$.
"""
function PadicField(p::Integer; kw...)
   return PadicField(ZZRingElem(p); kw...)
end
