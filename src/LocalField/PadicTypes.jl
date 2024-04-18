###############################################################################
#
#   PadicField2 / PadicFieldElem2
#
###############################################################################

@doc raw"""
    PadicField2 <: FlintLocalField <: NonArchLocalField <: Field

A $p$-adic field for some prime $p$ without fixed precision.
"""
@attributes mutable struct PadicField2 <: FlintLocalField
   p::Int
   pinv::Float64
   pow::Ptr{Nothing}
   minpre::Int
   maxpre::Int
   mode::Cint

   function PadicField2(p::ZZRingElem; cached::Bool = true, check::Bool = true)
      check && !is_probable_prime(p) && throw(DomainError(p, "Base must be prime"))

      return get_cached!(PadicBase2, (p), cached) do
         d = new()
         ccall((:padic_ctx_init, libflint), Nothing,
               (Ref{PadicField2}, Ref{ZZRingElem}, Int, Int, Cint),
               d, p, 0, 0, 0)
         finalizer(Nemo._padic_ctx_clear_fn, d)
         return d
      end
   end
end

const PadicBase2 = AbstractAlgebra.CacheDictType{ZZRingElem, PadicField2}()

function Nemo._padic_ctx_clear_fn(a::PadicField2)
   ccall((:padic_ctx_clear, libflint), Nothing, (Ref{PadicField2},), a)
end

@doc raw"""
    PadicFieldElem2 <: FlintLocalFieldElem <: NonArchLocalFieldElem <: FieldElem

An element of a $p$-adic field. See [`PadicField2`](@ref).
"""
mutable struct PadicFieldElem2 <: FlintLocalFieldElem
   u::Int
   v::Int
   N::Int
   parent::PadicField2

   function PadicFieldElem2(prec::Int)
      d = new()
      ccall((:padic_init2, libflint), Nothing, (Ref{PadicFieldElem2}, Int), d, prec)
      finalizer(Nemo._padic_clear_fn, d)
      return d
   end
end

function Nemo._padic_clear_fn(a::PadicFieldElem2)
   ccall((:padic_clear, libflint), Nothing, (Ref{PadicFieldElem2},), a)
end

################################################################################
#
#  Precision management
#
################################################################################

const PADIC_DEFAULT_PRECISION = Ref{Int}(64)

@doc raw"""
    set_precision!(::Type{PadicField2}, n::Int)

Set the precision for all $p$-adic arithmetic to be `n`.
"""
function set_precision!(::Type{PadicField2}, n::Int)
  @assert n > 0
  PADIC_DEFAULT_PRECISION[] = n
end

set_precision!(::PadicField2, n::Int) = set_precision!(PadicField2, n)

@doc raw"""
    precision(::Type{PadicField2})

Return the precision for $p$-adic arithmetic.
"""
function Base.precision(::Type{PadicField2})
  return PADIC_DEFAULT_PRECISION[]
end

precision(::PadicField2) = precision(PadicField2)

@doc raw"""
    set_precision!(f, ::Type{PadicField2}, n::Int)

Change $p$-adic arithmetic precision to `n` for the duration of `f`.
"""
function set_precision!(f, ::Type{PadicField2}, n::Int)
  @assert n > 0
  old = precision(PadicField2)
  set_precision!(PadicField2, n)
  x = f()
  set_precision!(PadicField2, old)
  return x
end

set_precision!(f, ::PadicField2, n::Int) = set_precision!(f, PadicField2, n)
