###############################################################################
#
#   PadicField / PadicFieldElem
#
###############################################################################

@doc raw"""
    PadicField <: FlintLocalField <: NonArchLocalField <: Field

A $p$-adic field for some prime $p$ without fixed precision.
"""
@attributes mutable struct PadicField <: FlintLocalField
   p::Int
   pinv::Float64
   pow::Ptr{Nothing}
   minpre::Int
   maxpre::Int
   mode::Cint

   function PadicField(p::ZZRingElem; cached::Bool = true, check::Bool = true)
      check && !is_probable_prime(p) && throw(DomainError(p, "Base must be prime"))

      return get_cached!(PadicFieldID, (p), cached) do
         d = new()
         ccall((:padic_ctx_init, libflint), Nothing,
               (Ref{PadicField}, Ref{ZZRingElem}, Int, Int, Cint),
               d, p, 0, 0, 0)
         finalizer(Nemo._padic_ctx_clear_fn, d)
         return d
      end
   end
end

const PadicFieldID = AbstractAlgebra.CacheDictType{ZZRingElem, PadicField}()

function Nemo._padic_ctx_clear_fn(a::PadicField)
   ccall((:padic_ctx_clear, libflint), Nothing, (Ref{PadicField},), a)
end

@doc raw"""
    PadicFieldElem <: FlintLocalFieldElem <: NonArchLocalFieldElem <: FieldElem

An element of a $p$-adic field. See [`PadicField`](@ref).
"""
mutable struct PadicFieldElem <: FlintLocalFieldElem
   u::Int
   v::Int
   N::Int
   parent::PadicField

   function PadicFieldElem(prec::Int)
      d = new()
      ccall((:padic_init2, libflint), Nothing, (Ref{PadicFieldElem}, Int), d, prec)
      finalizer(Nemo._padic_clear_fn, d)
      return d
   end
end

function Nemo._padic_clear_fn(a::PadicFieldElem)
   ccall((:padic_clear, libflint), Nothing, (Ref{PadicFieldElem},), a)
end

################################################################################
#
#  Precision management for p-adics
#
################################################################################

const PADIC_DEFAULT_PRECISION = Ref{Int}(64)

@doc raw"""
    set_precision!(::Type{PadicField}, n::Int)

Set the precision for all $p$-adic arithmetic to be `n`.
"""
function set_precision!(::Type{PadicField}, n::Int)
  @assert n > 0
  PADIC_DEFAULT_PRECISION[] = n
end

set_precision!(::PadicField, n::Int) = set_precision!(PadicField, n)

@doc raw"""
    precision(::Type{PadicField})

Return the precision for $p$-adic arithmetic.
"""
function Base.precision(::Type{PadicField})
  return PADIC_DEFAULT_PRECISION[]
end

precision(::PadicField) = precision(PadicField)

@doc raw"""
    set_precision!(f, ::Type{PadicField}, n::Int)

Change $p$-adic arithmetic precision to `n` for the duration of `f`.
"""
function set_precision!(f, ::Type{PadicField}, n::Int)
  @assert n > 0
  old = precision(PadicField)
  set_precision!(PadicField, n)
  x = f()
  set_precision!(PadicField, old)
  return x
end

set_precision!(f, ::PadicField, n::Int) = set_precision!(f, PadicField, n)

# For compatibility
setprecision(f, ::PadicField, n::Int) = set_precision!(f, PadicField, n)
setprecision!(::PadicField, n::Int) = set_precision!(PadicField, n)

###############################################################################
#
#   QadicField / QadicFieldElem
#
###############################################################################

@doc raw"""
    QadicField <: FlintLocalField <: NonArchLocalField <: Field

A $p^n$-adic field for some prime power $p^n$.
"""
@attributes mutable struct QadicField <: FlintLocalField
   p::Int
   pinv::Float64
   pow::Ptr{Nothing}
   minpre::Int
   maxpre::Int
   mode::Cint
   a::Int         # ZZRingElem
   j::Ptr{Nothing}   # slong*
   len::Int
   var::Cstring   # char*

   function QadicField(p::ZZRingElem, d::Int, var::String = "a"; cached::Bool = true, check::Bool = true)

      check && !is_probable_prime(p) && throw(DomainError(p, "Characteristic must be prime"))

      z = get_cached!(QadicFieldID, (p, d), cached) do
         zz = new()
         ccall((:qadic_ctx_init, libflint), Nothing,
              (Ref{QadicField}, Ref{ZZRingElem}, Int, Int, Int, Cstring, Cint),
                                        zz, p, d, 0, 0, var, 0)
         finalizer(Nemo._qadic_ctx_clear_fn, zz)
         return zz
      end

      return z, gen(z)
   end
end

const QadicFieldID = AbstractAlgebra.CacheDictType{Tuple{ZZRingElem, Int}, QadicField}()

function Nemo._qadic_ctx_clear_fn(a::QadicField)
   ccall((:qadic_ctx_clear, libflint), Nothing, (Ref{QadicField},), a)
end

@doc raw"""
    QadicFieldElem <: FlintLocalFieldElem <: NonArchLocalFieldElem <: FieldElem

An element of a $q$-adic field. See [`QadicField`](@ref).
"""
mutable struct QadicFieldElem <: FlintLocalFieldElem
   coeffs::Int
   alloc::Int
   length::Int
   val::Int
   N::Int
   parent::QadicField

   function QadicFieldElem(prec::Int)
      z = new()
      ccall((:qadic_init2, libflint), Nothing, (Ref{QadicFieldElem}, Int), z, prec)
      finalizer(Nemo._qadic_clear_fn, z)
      return z
   end
end

function Nemo._qadic_clear_fn(a::QadicFieldElem)
   ccall((:qadic_clear, libflint), Nothing, (Ref{QadicFieldElem},), a)
end

################################################################################
#
#  Precision management for q-adics
#
################################################################################

# TODO: Should this just be shared with PADIC_DEFAULT_PRECISION?
const QADIC_DEFAULT_PRECISION = Ref{Int}(64)

@doc raw"""
    set_precision!(::Type{QadicField}, n::Int)

Set the precision for all $q$-adic arithmetic to be `n`.
"""
function set_precision!(::Type{QadicField}, n::Int)
  @assert n > 0
  QADIC_DEFAULT_PRECISION[] = n
end

set_precision!(::QadicField, n::Int) = set_precision!(QadicField, n)

@doc raw"""
    precision(::Type{QadicField})

Return the precision for $q$-adic arithmetic.
"""
function Base.precision(::Type{QadicField})
  return QADIC_DEFAULT_PRECISION[]
end

precision(::QadicField) = precision(QadicField)

@doc raw"""
    set_precision!(f, ::Type{QadicField}, n::Int)

Change $q$-adic arithmetic precision to `n` for the duration of `f`.
"""
function set_precision!(f, ::Type{QadicField}, n::Int)
  @assert n > 0
  old = precision(QadicField)
  set_precision!(QadicField, n)
  x = f()
  set_precision!(QadicField, old)
  return x
end

set_precision!(f, ::QadicField, n::Int) = set_precision!(f, QadicField, n)

# For compatibility
setprecision(f, ::QadicField, n::Int) = set_precision!(f, QadicField, n)
setprecision!(::QadicField, n::Int) = set_precision!(QadicField, n)
