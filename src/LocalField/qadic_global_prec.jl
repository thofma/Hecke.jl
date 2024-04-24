###############################################################################
#
#   Data type and parent object methods
#
###############################################################################

@doc raw"""
    O(R::QadicField, m::ZZRingElem)

Construct the value $0 + O(p^n)$ given $m = p^n$. An exception results if $m$
is not found to be a power of `p = prime(R)`.
"""
function O(R::QadicField, m::ZZRingElem)
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
   d = QadicFieldElem(N)
   d.parent = R
   return d
end

@doc raw"""
    O(R::QadicField, m::QQFieldElem)

Construct the value $0 + O(p^n)$ given $m = p^n$. An exception results if $m$
is not found to be a power of `p = prime(R)`.
"""
function O(R::QadicField, m::QQFieldElem)
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
   r = QadicFieldElem(N)
   r.parent = R
   return r
end

@doc raw"""
    O(R::QadicField, m::Integer)

Construct the value $0 + O(p^n)$ given $m = p^n$. An exception results if $m$
is not found to be a power of `p = prime(R)`.
"""
O(R::QadicField, m::Integer) = O(R, ZZRingElem(m))

elem_type(::Type{QadicField}) = QadicFieldElem

@doc raw"""
    base_ring(a::QadicField)

Returns `Union{}` as this field is not dependent on another field.
"""
base_ring(a::QadicField) = Union{}

@doc raw"""
    base_ring(a::QadicFieldElem)

Returns `Union{}` as this field is not dependent on another field.
"""
base_ring(a::QadicFieldElem) = Union{}

parent(a::QadicFieldElem) = a.parent

is_domain_type(::Type{QadicFieldElem}) = true

is_exact_type(R::Type{QadicFieldElem}) = false

function check_parent(a::QadicFieldElem, b::QadicFieldElem)
   parent(a) != parent(b) &&
      error("Incompatible qadic rings in qadic operation")
end

parent_type(::Type{QadicFieldElem}) = QadicField

function _prime(R::QadicField, n::Int = 1)
   z = ZZRingElem()
   ccall((:padic_ctx_pow_ui, libflint), Nothing,
         (Ref{ZZRingElem}, UInt, Ref{QadicField}), z, n, R)
   return z
end

###############################################################################
#
#   Basic manipulation
#
###############################################################################

function Base.deepcopy_internal(a::QadicFieldElem, dict::IdDict{Any, Any})
   z = parent(a)()
   z.N = a.N
   ccall((:qadic_set, libflint), Nothing,
         (Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicField}), z, a, parent(a))
   return z
end

function Base.hash(a::QadicFieldElem, h::UInt)
   return xor(hash(lift(QQPolyRing(FlintQQ, :x), a), h),
              xor(hash([prime(parent(a)),degree(parent(a))], h), h))
end

function degree(R::QadicField)
   return ccall((:qadic_ctx_degree, libflint), Int, (Ref{QadicField}, ), R)
end

@doc raw"""
    prime(R::QadicField)

Return the prime $p$ for the given $q$-adic field.
"""
function prime(R::QadicField)
   z = ZZRingElem()
   ccall((:padic_ctx_pow_ui, libflint), Nothing,
         (Ref{ZZRingElem}, UInt, Ref{QadicField}), z, 1, R)
   return z
end

@doc raw"""
    precision(a::QadicFieldElem)

Return the precision of the given $q$-adic field element, i.e. if the element
is known to $O(p^n)$ this function will return $n$.
"""
precision(a::QadicFieldElem) = a.N

@doc raw"""
    valuation(a::QadicFieldElem)

Return the valuation of the given $q$-adic field element, i.e. if the given
element is divisible by $p^n$ but not a higher power of $q$ then the function
will return $n$.
"""
function valuation(a::QadicFieldElem)
    iszero(a) ? precision(a) : ccall((:qadic_val, libflint), Int, (Ref{QadicFieldElem}, ), a)
end

@doc raw"""
    lift(R::QQPolyRing, a::QadicFieldElem)

Return a lift of the given $q$-adic field element to $\mathbb{Q}[x]$.
"""
function lift(R::QQPolyRing, a::QadicFieldElem)
   ctx = parent(a)
   r = R()
   ccall((:padic_poly_get_fmpq_poly, libflint), Nothing,
         (Ref{QQPolyRingElem}, Ref{QadicFieldElem}, Ref{QadicField}), r, a, ctx)
   return r
end

@doc raw"""
    lift(R::ZZPolyRing, a::QadicFieldElem)

Return a lift of the given $q$-adic field element to $\mathbb{Z}[x]$ if possible.
"""
function lift(R::ZZPolyRing, a::QadicFieldElem)
   ctx = parent(a)
   r = R()
   res = Bool(ccall((:padic_poly_get_fmpz_poly, libflint), Cint,
                    (Ref{ZZPolyRingElem}, Ref{QadicFieldElem}, Ref{QadicField}), r, a, ctx))
   !res && error("Unable to lift")
   return r
end

function zero(R::QadicField)
   z = QadicFieldElem(precision(QadicField))
   ccall((:qadic_zero, libflint), Nothing, (Ref{QadicFieldElem},), z)
   z.parent = R
   return z
end

function one(R::QadicField)
   z = QadicFieldElem(precision(QadicField))
   ccall((:qadic_one, libflint), Nothing, (Ref{QadicFieldElem},), z)
   z.parent = R
   return z
end

iszero(a::QadicFieldElem) = Bool(ccall((:qadic_is_zero, libflint), Cint,
                              (Ref{QadicFieldElem},), a))

isone(a::QadicFieldElem) = Bool(ccall((:qadic_is_one, libflint), Cint,
                             (Ref{QadicFieldElem},), a))

is_unit(a::QadicFieldElem) = !Bool(ccall((:qadic_is_zero, libflint), Cint,
                              (Ref{QadicFieldElem},), a))

characteristic(R::QadicField) = 0

###############################################################################
#
#   AbstractString I/O
#
###############################################################################

function var(Q::QadicField)
  return Symbol(unsafe_string(Q.var))
end

function expressify(b::QadicFieldElem, x = var(parent(b)); context = nothing)
   R = PadicField(prime(parent(b)), precision(QadicField))
   if iszero(b)
      return 0
   end
   sum = Expr(:call, :+)
   c = R()
   for i in degree(parent(b)):-1:0
      ccall((:padic_poly_get_coeff_padic, libflint), Nothing,
            (Ref{PadicFieldElem}, Ref{QadicFieldElem}, Int, Ref{QadicField}),
            c, b, i, parent(b))
      ec = expressify(c, context = context)
      if !iszero(c)
         if iszero(i)
            push!(sum.args, ec)
         elseif isone(i)
            push!(sum.args, Expr(:call, :*, ec, x))
         else
            push!(sum.args, Expr(:call, :*, ec, Expr(:call, :^, x, i)))
         end
      end
   end
   return sum
end

function show(io::IO, a::QadicFieldElem)
   print(io, AbstractAlgebra.obj_to_string(a, context = io))
end

function show(io::IO, R::QadicField)
   if get(io, :supercompact, false)
     io = pretty(io)
     print(io, LowercaseOff(), "QQ_$(prime(R))^$(degree(R))")
   else
     print(io, "Unramified extension of $(prime(R))-adic numbers of degree $(degree(R))")
   end
end

###############################################################################
#
#   Canonicalisation
#
###############################################################################

canonical_unit(x::QadicFieldElem) = x

###############################################################################
#
#   Unary operators
#
###############################################################################

function -(x::QadicFieldElem)
   if iszero(x)
      return x
   end
   ctx = parent(x)
   z = QadicFieldElem(x.N)
   ccall((:qadic_neg, libflint), Nothing,
         (Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicField}),
                     z, x, ctx)
   z.parent = ctx
   return z
end

###############################################################################
#
#   Binary operators
#
###############################################################################

function +(x::QadicFieldElem, y::QadicFieldElem)
   check_parent(x, y)
   ctx = parent(x)
   z = QadicFieldElem(min(x.N, y.N))
   z.parent = ctx
   ccall((:qadic_add, libflint), Nothing,
         (Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicField}),
               z, x, y, ctx)
   return z
end

function -(x::QadicFieldElem, y::QadicFieldElem)
   check_parent(x, y)
   ctx = parent(x)
   z = QadicFieldElem(min(x.N, y.N))
   z.parent = ctx
   ccall((:qadic_sub, libflint), Nothing,
         (Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicField}),
                  z, x, y, ctx)
   return z
end

function *(x::QadicFieldElem, y::QadicFieldElem)
   check_parent(x, y)
   ctx = parent(x)
   z = QadicFieldElem(min(x.N + valuation(y), y.N + valuation(x)))
   z.parent = ctx
   ccall((:qadic_mul, libflint), Nothing,
         (Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicField}),
               z, x, y, ctx)
   return z
end

###############################################################################
#
#   Ad hoc binary operators
#
###############################################################################

+(a::QadicFieldElem, b::Integer) = a + parent(a)(b)

+(a::QadicFieldElem, b::ZZRingElem) = a + parent(a)(b)

+(a::QadicFieldElem, b::QQFieldElem) = a + parent(a)(b)

+(a::Integer, b::QadicFieldElem) = b + a

+(a::ZZRingElem, b::QadicFieldElem) = b + a

+(a::QQFieldElem, b::QadicFieldElem) = b + a

-(a::QadicFieldElem, b::Integer) = a - parent(a)(b)

-(a::QadicFieldElem, b::ZZRingElem) = a - parent(a)(b)

-(a::QadicFieldElem, b::QQFieldElem) = a - parent(a)(b)

-(a::Integer, b::QadicFieldElem) = parent(b)(a) - b

-(a::ZZRingElem, b::QadicFieldElem) = parent(b)(a) - b

-(a::QQFieldElem, b::QadicFieldElem) = parent(b)(a) - b

*(a::QadicFieldElem, b::Integer) = a*parent(a)(b)

*(a::QadicFieldElem, b::ZZRingElem) = a*parent(a)(b)

*(a::QadicFieldElem, b::QQFieldElem) = a*parent(a)(b)

*(a::Integer, b::QadicFieldElem) = b*a

*(a::ZZRingElem, b::QadicFieldElem) = b*a

*(a::QQFieldElem, b::QadicFieldElem) = b*a

###############################################################################
#
#   Comparison
#
###############################################################################

function ==(a::QadicFieldElem, b::QadicFieldElem)
   check_parent(a, b)
   ctx = parent(a)
   z = QadicFieldElem(min(a.N, b.N))
   ccall((:qadic_sub, libflint), Nothing,
         (Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicField}),
               z, a, b, ctx)
   return Bool(ccall((:qadic_is_zero, libflint), Cint,
                (Ref{QadicFieldElem},), z))
end

function isequal(a::QadicFieldElem, b::QadicFieldElem)
   if parent(a) != parent(b)
      return false
   end
   return a.N == b.N && a == b
end

###############################################################################
#
#   Ad hoc comparison
#
###############################################################################

==(a::QadicFieldElem, b::Integer) = a == parent(a)(b)

==(a::QadicFieldElem, b::ZZRingElem) = a == parent(a)(b)

==(a::QadicFieldElem, b::QQFieldElem) = a == parent(a)(b)

==(a::Integer, b::QadicFieldElem) = parent(b)(a) == b

==(a::ZZRingElem, b::QadicFieldElem) = parent(b)(a) == b

==(a::QQFieldElem, b::QadicFieldElem) = parent(b)(a) == b

###############################################################################
#
#   Powering
#
###############################################################################

^(q::QadicFieldElem, n::Int) = q^ZZRingElem(n)

function ^(a::QadicFieldElem, n::ZZRingElem)
   ctx = parent(a)
   if n < 0
      return inv(a)^(-n)
   end
   if valuation(a) == 0
     z = QadicFieldElem(a.N) #if expo is ZZRingElem, Int(n) would throw an error
   else             #for units (v==0) this is fine hower.
     z = QadicFieldElem(a.N + (Int(n) - 1)*valuation(a))
   end
   z.parent = ctx
   ccall((:qadic_pow, libflint), Nothing,
                 (Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{ZZRingElem}, Ref{QadicField}),
               z, a, n, ctx)
   return z
end

###############################################################################
#
#   Exact division
#
###############################################################################

function divexact(a::QadicFieldElem, b::QadicFieldElem; check::Bool=true)
   iszero(b) && throw(DivideError())
   return a * inv(b)
end

###############################################################################
#
#   Ad hoc exact division
#
###############################################################################

divexact(a::QadicFieldElem, b::Integer; check::Bool=true) = a*(ZZRingElem(1)//ZZRingElem(b))

divexact(a::QadicFieldElem, b::ZZRingElem; check::Bool=true) = a*(1//b)

divexact(a::QadicFieldElem, b::QQFieldElem; check::Bool=true) = a*inv(b)

divexact(a::Integer, b::QadicFieldElem; check::Bool=true) = ZZRingElem(a)*inv(b)

divexact(a::ZZRingElem, b::QadicFieldElem; check::Bool=true) = inv((ZZRingElem(1)//a)*b)

divexact(a::QQFieldElem, b::QadicFieldElem; check::Bool=true) = inv(inv(a)*b)

###############################################################################
#
#   Inversion
#
###############################################################################

function inv(a::QadicFieldElem)
   iszero(a) && throw(DivideError())
   ctx = parent(a)
   z = QadicFieldElem(a.N - 2*valuation(a))
   z.parent = ctx
   ccall((:qadic_inv, libflint), Cint,
         (Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicField}), z, a, ctx)
   return z
end

###############################################################################
#
#   Divides
#
###############################################################################

function divides(a::QadicFieldElem, b::QadicFieldElem)
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

function gcd(x::QadicFieldElem, y::QadicFieldElem)
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

function Base.sqrt(a::QadicFieldElem; check::Bool=true)
   av = valuation(a)
   check && (av % 2) != 0 && error("Unable to take qadic square root")
   ctx = parent(a)
   z = QadicFieldElem(a.N - div(av, 2))
   z.parent = ctx
   res = Bool(ccall((:qadic_sqrt, libflint), Cint,
                    (Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicField}), z, a, ctx))
   check && !res && error("Square root of p-adic does not exist")
   return z
end

###############################################################################
#
#   Special functions
#
###############################################################################

function Base.exp(a::QadicFieldElem)
   !iszero(a) && valuation(a) <= 0 && throw(DomainError(a, "Valuation must be positive"))
   ctx = parent(a)
   z = QadicFieldElem(a.N)
   z.parent = ctx
   res = Bool(ccall((:qadic_exp, libflint), Cint,
                    (Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicField}), z, a, ctx))
   !res && error("Unable to compute exponential")
   return z
end

function log(a::QadicFieldElem)
   av = valuation(a)
   (av > 0 || av < 0 || iszero(a)) && throw(DomainError(a, "Valuation must be zero"))
   av = valuation(a-1)
   ctx = parent(a)
   if av == 0
     qm1 = _prime(ctx, degree(ctx)) - 1
     a = a^qm1
   end

   ctx = parent(a)
   z = QadicFieldElem(a.N)
   z.parent = ctx
   res = Bool(ccall((:qadic_log, libflint), Cint,
                    (Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicField}), z, a, ctx))
   !res && error("Unable to compute logarithm")
   if av == 0
     z = divexact(z, qm1)
   end
   return z
end

@doc raw"""
    teichmuller(a::QadicFieldElem)

Return the Teichmuller lift of the $q$-adic value $a$. We require the
valuation of $a$ to be non-negative. The precision of the output will be the
same as the precision of the input. For convenience, if $a$ is congruent to
zero modulo $q$ we return zero. If the input is not valid an exception is
thrown.
"""
function teichmuller(a::QadicFieldElem)
   valuation(a) < 0 && throw(DomainError(a, "Valuation must be non-negative"))
   ctx = parent(a)
   z = QadicFieldElem(a.N)
   z.parent = ctx
   ccall((:qadic_teichmuller, libflint), Nothing,
         (Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicField}), z, a, ctx)
   return z
end

@doc raw"""
    frobenius(a::QadicFieldElem, e::Int = 1)

Return the image of the $e$-th power of Frobenius on the $q$-adic value $a$.
The precision of the output will be the same as the precision of the input.
"""
function frobenius(a::QadicFieldElem, e::Int = 1)
   ctx = parent(a)
   z = QadicFieldElem(a.N)
   z.parent = ctx
   ccall((:qadic_frobenius, libflint), Nothing,
         (Ref{QadicFieldElem}, Ref{QadicFieldElem}, Int, Ref{QadicField}), z, a, e, ctx)
   return z
end

###############################################################################
#
#   Unsafe operators
#
###############################################################################

function zero!(z::QadicFieldElem)
   z.N = precision(QadicField)
   ctx = parent(z)
   ccall((:qadic_zero, libflint), Nothing,
         (Ref{QadicFieldElem}, Ref{QadicField}), z, ctx)
   return z
end

function mul!(z::QadicFieldElem, x::QadicFieldElem, y::QadicFieldElem)
   z.N = min(x.N + valuation(y), y.N + valuation(x))
   ctx = parent(x)
   ccall((:qadic_mul, libflint), Nothing,
         (Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicField}),
               z, x, y, ctx)
   return z
end

function addeq!(x::QadicFieldElem, y::QadicFieldElem)
   x.N = min(x.N, y.N)
   ctx = parent(x)
   ccall((:qadic_add, libflint), Nothing,
         (Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicField}),
               x, x, y, ctx)
   return x
end

function add!(z::QadicFieldElem, x::QadicFieldElem, y::QadicFieldElem)
   z.N = min(x.N, y.N)
   ctx = parent(x)
   ccall((:qadic_add, libflint), Nothing,
         (Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicField}),
               z, x, y, ctx)
   return z
end

###############################################################################
#
#   Conversions and promotions
#
###############################################################################

promote_rule(::Type{QadicFieldElem}, ::Type{T}) where {T <: Integer} = QadicFieldElem

promote_rule(::Type{QadicFieldElem}, ::Type{Rational{V}}) where {V <: Integer} = QadicFieldElem

promote_rule(::Type{QadicFieldElem}, ::Type{ZZRingElem}) = QadicFieldElem

promote_rule(::Type{QadicFieldElem}, ::Type{QQFieldElem}) = QadicFieldElem

promote_rule(::Type{QadicFieldElem}, ::Type{PadicFieldElem}) = QadicFieldElem

###############################################################################
#
#   Parent object overloads
#
###############################################################################

function (R::QadicField)()
   z = QadicFieldElem(precision(QadicField))
   z.parent = R
   return z
end

function gen(R::QadicField)
   if degree(R) == 1
      # Work around flint limitation
      # https://github.com/wbhart/flint2/issues/898
      a = ZZRingElem()
      GC.@preserve R begin
         ccall((:fmpz_set, libflint), Nothing, (Ref{ZZRingElem}, Ptr{ZZRingElem}),
                                               a, reinterpret(Ptr{ZZRingElem}, R.a))
      end
      return R(-a)
   end

   z = QadicFieldElem(precision(QadicField))
   ccall((:qadic_gen, libflint), Nothing,
         (Ref{QadicFieldElem}, Ref{QadicField}), z, R)
   z.parent = R
   return z
end

function (R::QadicField)(a::UInt)
   if a == 0
     z = QadicFieldElem(precision(QadicField))
     z.parent = R
     return z
   end
   v = valuation(a, prime(R))
   z = QadicFieldElem(precision(QadicField) + v)
   ccall((:qadic_set_ui, libflint), Nothing,
         (Ref{QadicFieldElem}, UInt, Ref{QadicField}), z, a, R)
   z.parent = R
   return z
end

function (R::QadicField)(a::Int)
   if a == 0
     z = QadicFieldElem(precision(QadicField))
     z.parent = R
     return z
   end
   v = valuation(a, prime(R))
   z = QadicFieldElem(precision(QadicField) + v)
   ccall((:padic_poly_set_si, libflint), Nothing,
         (Ref{QadicFieldElem}, Int, Ref{QadicField}), z,a, R)
   z.parent = R
   return z
end

function (R::QadicField)(n::ZZRingElem)
   if iszero(n) || isone(n)
      N = 0
   else
      p = prime(R)
      N = valuation(n, p)
   end
   z = QadicFieldElem(N + precision(QadicField))
   ccall((:padic_poly_set_fmpz, libflint), Nothing,
         (Ref{QadicFieldElem}, Ref{ZZRingElem}, Ref{QadicField}), z, n, R)
   z.parent = R
   return z
end

function (R::QadicField)(n::QQFieldElem)
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
   z = QadicFieldElem(N + precision(QadicField))
   ccall((:padic_poly_set_fmpq, libflint), Nothing,
         (Ref{QadicFieldElem}, Ref{QQFieldElem}, Ref{QadicField}), z, n, R)
   z.parent = R
   return z
end

function (R::QadicField)(n::ZZPolyRingElem, pr::Int = precision(QadicField))
   z = QadicFieldElem(pr)
   ccall((:qadic_set_fmpz_poly, libflint), Nothing,
         (Ref{QadicFieldElem}, Ref{ZZPolyRingElem}, Ref{QadicField}), z, n, R)
   z.parent = R
   return z
end

function (R::QadicField)(n::QQPolyRingElem)

   if degree(n) > degree(R) + 1
       error("Polynomial degree larger than degree of qadic field.")
   end
   m = denominator(n)
   p = prime(R)
   if m == p
      N = -1
   else
     N = -remove(m, p)[1]
   end
   z = QadicFieldElem(N + precision(QadicField))
   ccall((:padic_poly_set_fmpq_poly, libflint), Nothing,
         (Ref{QadicFieldElem}, Ref{QQPolyRingElem}, Ref{QadicField}), z, n, R)
   z.parent = R
   return z
end

function (R::QadicField)(b::Rational{<:Integer})
   return R(QQFieldElem(b))
end

(R::QadicField)(n::Integer) = R(ZZRingElem(n))

function (R::QadicField)(n::QadicFieldElem)
   parent(n) != R && error("Unable to coerce into q-adic field")
   return n
end

###############################################################################
#
#   QadicField constructor
#
###############################################################################

# inner constructor is also used directly

@doc raw"""
    QadicField(p::Integer, d::Int, var::String = "a")

Returns the parent object for the $q$-adic field for given prime $p$ and
degree $d$, where the generator of the field is printed as `var`.
"""
function QadicField(p::Integer, d::Int, var::String = "a"; cached::Bool = true)
   return QadicField(ZZRingElem(p), d, var, cached = cached)
end
