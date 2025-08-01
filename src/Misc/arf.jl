################################################################################
#
#                       arf.jl: wrapper for arf
#
################################################################################
#
#  TODO:
#  - Sensible way to deal with rounding modes (at least documentation)
#
################################################################################

################################################################################
#
#  Types and memory management
#
################################################################################

const ArfFieldID = IdDict()

mutable struct ArfField <: Field
  prec::Int
  rndmode::Cint

  function ArfField(p::Int = 256, r::Cint = Cint(4))
    try
      return ArfFieldID[p,r]::ArfField
    catch
      z = new(p,r)
      ArfFieldID[p,r] = z
      return z
    end
  end
end

mutable struct arf
  exp::Int # ZZRingElem
  size::UInt64 # mp_size_t
  d1::Int64 # mantissa_struct
  d2::Int64
  parent::ArfField

  function arf()
    z = new()
    ccall((:arf_init, libflint), Nothing, (Ref{arf}, ), z)
    finalizer(_arf_clear_fn, z)
    return z
  end

  function arf(i::Int)
    z = new()
    ccall((:arf_init, libflint), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_si, libflint), Nothing, (Ref{arf}, Int), z, i)
    finalizer(_arf_clear_fn, z)
    return z
  end

  function arf(i::UInt)
    z = new()
    ccall((:arf_init, libflint), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_ui, libflint), Nothing, (Ref{arf}, UInt), z, i)
    finalizer(_arf_clear_fn, z)
    return z
  end

  function arf(i::ZZRingElem)
    z = new()
    ccall((:arf_init, libflint), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_fmpz, libflint), Nothing, (Ref{arf}, Ref{ZZRingElem}), z, i)
    finalizer(_arf_clear_fn, z)
    return z
  end

  function arf(x::BigFloat)
    z = new()
    ccall((:arf_init, libflint), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_mpfr, libflint), Nothing, (Ref{arf}, Ref{BigFloat}), z, x)
    finalizer(_arf_clear_fn, z)
    return z
  end

  function arf(x::Cdouble)
    z = new()
    ccall((:arf_init, libflint), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_d, libflint), Nothing, (Ref{arf}, Cdouble), z, x)
    finalizer(_arf_clear_fn, z)
    return z
  end

  function arf(x::mag)
    z = new()
    ccall((:arf_init, libflint), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_mag, libflint), Nothing, (Ref{arf}, Ref{mag}), z, x)
    finalizer(_arf_clear_fn, z)
    return z
  end

  function arf(x::arf, p::Int, r::Cint)
    z = new()
    ccall((:arf_init, libflint), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_round, libflint), Nothing,
                (Ref{arf}, Ref{arf}, Int, Cint), z, x, p, r)
    finalizer(_arf_clear_fn, z)
    return z
  end

  function arf(x::Int, p::Int, r::Cint)
    z = new()
    ccall((:arf_init, libflint), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_round_si, libflint), Nothing,
                  (Ref{arf}, Int, Int, Cint), z, x, p, r)
    finalizer(_arf_clear_fn, z)
    return z
  end

 function arf(x::UInt, p::Int, r::Cint)
    z = new()
    ccall((:arf_init, libflint), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_round_ui, libflint), Nothing,
                  (Ref{arf}, UInt, Int, Cint), z, x, p, r)
    finalizer(_arf_clear_fn, z)
    return z
  end

 function arf(x::ZZRingElem, p::Int, r::Cint)
    z = new()
    ccall((:arf_init, libflint), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_round_fmpz, libflint), Nothing,
                  (Ref{arf}, Ref{ZZRingElem}, Int, Cint), z, x, p, r)
    finalizer(_arf_clear_fn, z)
    return z
  end
end

function _arf_clear_fn(x::arf)
  ccall((:arf_clear, libflint), Nothing, (Ref{arf}, ), x)
end

parent(x::arf) = x.parent

################################################################################
#
#  Parent object overloads
#
################################################################################

function (r::ArfField)()
  z = arf()
  z.parent = r
  return z
end

function (r::ArfField)(x::Int)
  z = arf(x, r.prec, r.rndmode)
  z.parent = r
  return z
end

function (r::ArfField)(x::UInt)
  z = arf(x, r.prec, r.rndmode)
  z.parent = r
  return z
end

function (r::ArfField)(x::ZZRingElem)
  z = arf(x, r.prec, r.rndmode)
  z.parent = r
  return z
end

function (r::ArfField)(x::Float64)
  z = arf(x)
  z = arf(z, r.prec, r.rndmode)
  z.parent = r
  return z
end

function (r::ArfField)(x::BigFloat)
  z = arf(x)
  z = arf(z, r.prec, r.rndmode)
  z.parent = r
  return z
end

function (r::ArfField)(x::mag)
  z = arf(x)
  z = arf(z, r.prec, r.rndmode)
  z.parent = r
  return z
end

################################################################################
#
#  Special values
#
################################################################################

for (s,f) in (("zero", "arf_zero"), ("one", "arf_one"),
              ("pos_inf", "arf_pos_inf"), ("neg_inf", "arf_neg_inf"),
              ("nan", "arf_nan"))
  @eval begin
    function($(Symbol(s)))(r::ArfField)
      z = r()
      ccall(($f, libflint), Nothing, (Ref{arf}, ), z)
      return z
    end
  end
end

################################################################################
#
#  String I/O
#
################################################################################

# this function is crap
function show(io::IO, a::arf)
  #cstr = ccall((:arf_get_str, libflint), Ref{UInt8}, (Ref{arf}, ), a.data)
  #print(io, bytestring(cstr))
  #ccall((:flint_free, libflint), Nothing, (Ref{UInt8},), cstr)
  return show(io, BigFloat(a))
end

function show(io::IO, a::ArfField)
  print(io, "Field of arf's with precision $(a.prec)")
  print(io, " and rounding mode $(a.rndmode)")
end

################################################################################
#
#  Predicates
#
################################################################################

for (s,f) in (("iszero", "arf_iszero"), ("isone", "arf_is_one"),
              ("isposinf", "arf_is_pos_inf"),
              ("isneginf", "arf_is_neg_inf"),
              ("isinf", "arf_is_inf"),
              ("isnan", "arf_is_nan"),
              ("is_normal", "arf_is_normal"),
              ("isfinite", "arf_isfinite"),
              ("isspecial", "arf_is_special"))
  @eval begin
    function($(Symbol(s)))(x::arf)
      return Bool(ccall(($f, libflint), Cint, (Ref{arf},), x.data))
    end
  end
end

################################################################################
#
#  Comparison
#
################################################################################

function ==(x::arf, y::arf)
  r = ccall((:arf_equal, libflint), Cint, (Ref{arf}, Ref{arf}), x, y)
  return Bool(r)
end

function compare(x::arf, y::arf)
  r = ccall((:arf_cmp, libflint), Cint, (Ref{arf}, Ref{arf}), x, y)
  return r
end

function <(x::arf, y::arf)
  r = compare(x,y)
  r < 0 ? true : false
end

function >(x::arf, y::arf)
  r = compare(x,y)
  r > 0 ? true : false
end

function max(x::arf, y::arf)
  z = parent(x)()
  ccall((:arf_max, libflint), Nothing, (Ref{arf}, Ref{arf}, Ref{arf}), z, x, y)
  return z
end

function min(x::arf, y::arf)
  z = parent(x)()
  ccall((:arf_min, libflint), Nothing, (Ref{arf}, Ref{arf}, Ref{arf}), z, x, y)
  return z
end

################################################################################
#
#  Unary operations
#
################################################################################

function -(x::arf)
  z = parent(x)()
  ccall((:arf_neg, libflint), Nothing, (Ref{arf}, Ref{arf}), z, x)
  return z
end

################################################################################
#
#  Binary operations
#
################################################################################

function +(x::arf, y::arf)
  check_parent(x,y)
  z = parent(x)()
  ccall(("arf_add", libflint), Nothing,
              (Ref{arf}, Ref{arf}, Ref{arf}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

function +(x::arf, y::UInt)
  z = parent(x)()
  ccall(("arf_add_ui", libflint), Nothing,
              (Ref{arf}, Ref{arf}, UInt, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

+(x::UInt, y::arf) = +(y, x)

function +(x::arf, y::Int)
  z = parent(x)()
  ccall(("arf_add_si", libflint), Nothing,
              (Ref{arf}, Ref{arf}, Int, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

+(x::Int, y::arf) = +(y, x)

function +(x::arf, y::ZZRingElem)
  z = parent(x)()
  ccall(("arf_add_fmpz", libflint), Nothing,
              (Ref{arf}, Ref{arf}, Ref{ZZRingElem}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

+(x::ZZRingElem, y::arf) = +(y, x)

function *(x::arf, y::arf)
  z = parent(x)()
  ccall(("_arf_mul", libflint), Nothing,
              (Ref{arf}, Ref{arf}, Ref{arf}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

function *(x::arf, y::UInt)
  z = parent(x)()
  ccall(("arf_mul_ui", libflint), Nothing,
              (Ref{arf}, Ref{arf}, UInt, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

*(x::UInt, y::arf) = *(y, x)

function *(x::arf, y::Int)
  z = parent(x)()
  ccall(("arf_mul_si", libflint), Nothing,
              (Ref{arf}, Ref{arf}, Int, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

*(x::Int, y::arf) = *(y, x)

function *(x::arf, y::ZZRingElem)
  z = parent(x)()
  ccall(("arf_mul_fmpz", libflint), Nothing,
              (Ref{arf}, Ref{arf}, Ref{ZZRingElem}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

*(x::ZZRingElem, y::arf) = *(y, x)

function -(x::arf, y::arf)
  check_parent(x,y)
  z = parent(x)()
  ccall(("arf_sub", libflint), Nothing,
                (Ref{arf}, Ref{arf}, Ref{arf}, Int, Cint),
                z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

function -(x::arf, y::UInt)
  z = parent(x)()
  ccall(("arf_sub_ui", libflint), Nothing,
              (Ref{arf}, Ref{arf}, UInt, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

-(x::UInt, y::arf) = -(y - x)

function -(x::arf, y::Int)
  z = parent(x)()
  ccall(("arf_sub_si", libflint), Nothing,
              (Ref{arf}, Ref{arf}, Int, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

-(x::Int, y::arf) = -(y - x)

function -(x::arf, y::ZZRingElem)
  z = parent(x)()
  ccall(("arf_sub_fmpz", libflint), Nothing,
              (Ref{arf}, Ref{arf}, Ref{ZZRingElem}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

-(x::ZZRingElem, y::arf) = -(y - x)

function /(x::arf, y::arf)
  check_parent(x,y)
  z = parent(x)()
  ccall((:arf_div, libflint), Nothing,
              (Ref{arf}, Ref{arf}, Ref{arf}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

################################################################################
#
#  Unsafe arithmetic
#
################################################################################

function add!(x::arf, y::arf)
  ccall(("arf_add", libflint), Nothing,
              (Ref{arf}, Ref{arf}, Ref{arf}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
end


function div!(z::arf, x::arf, y::arf)
  ccall((:arf_div, libflint), Nothing,
              (Ref{arf}, Ref{arf}, Ref{arf}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
end

function sub!(x::arf, y::arf)
  ccall((:arf_sub, libflint), Nothing,
              (Ref{arf}, Ref{arf}, Ref{arf}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
end

function mul!(x::arf, y::arf)
  ccall((:_arf_mul, libflint), Nothing,
              (Ref{arf}, Ref{arf}, Ref{arf}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
end

################################################################################
#
#  Some functions
#
################################################################################

function sign(x::arf)
  r = ccall((:arf_sgn, libflint), Cint, (Ref{arf}, ), x)
  return r
end

function abs(x::arf)
  z = parent(x)()
  ccall((:arf_abs, libflint), Nothing, (Ref{arf}, Ref{arf}), z, x)
  return z
end

function Base.sqrt(x::arf)
  z = parent(x)()
  ccall((:arf_sqrt, libflint), Nothing,
              (Ref{arf}, Ref{arf}, Int, Cint),
              z, x, parent(x).prec, parent(x).rndmode)
  return z
end


################################################################################
#
#  Conversion
#
################################################################################

function Cdouble(a::arf, rnd::Cint = 4)
  z = ccall((:arf_get_d, libflint), Cdouble, (Ref{arf}, Cint), a.data, rnd)
  return z
end

function BigFloat(x::arf)
  old_prec = get_bigfloat_precision()
  set_bigfloat_precision(parent(x).prec)
  z = BigFloat(0)
  r = ccall((:arf_get_mpfr, libflint), Cint,
                (Ref{BigFloat}, Ref{arf}, Cint), z, x, Cint(0))
  set_bigfloat_precision(old_prec)
  return z
end

