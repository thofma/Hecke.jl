################################################################################
#
#  arf_t.jl: Wrapping arf_t C-struct
#
################################################################################

export arf_t, ArfField

export pos_inf, neg_inf, nan, isposinf, isneginf, isnan, isnormal, max, min

################################################################################
#
#  Types and memory management
#
################################################################################

ArfFieldID = ObjectIdDict()

type ArfField <: Field
  prec::Clong
  rndmode::Cint
  
  function ArfField(p::Clong = 256, r::Cint = Cint(4))
    try
      return ArfFieldID[p,r]
    catch
      z = new(p,r)
      ArfFieldID[p,r] = z
      return z
    end
  end
end
  
type arf_t
  data::Ptr{Void} # Pointer to arf_t C-struct
  parent::ArfField

  function arf_t()
    z = new()
    r = ccall((:arf_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(2))
    z.data = r
    finalizer(z, _arf_t_clear_fn)
    return z
  end

  # Use the following at own risk. r should point to arf_t C-struct
  # r and the associated arf_t struct should already be finalized

  function arf_t(r::Ptr{Void})
    z = new()
    z.data = r
    return z
  end

  function arf_t(i::Clong)
    z = new()
    z.data = ccall((:arf_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    ccall((:arf_set_si, :libarb), Ptr{Void}, (Ptr{Void}, Culong), z.data, i)
    finalizer(z, _arf_t_clear_fn)
    return z
  end

  function arf_t(i::Culong)
    z = new()
    z.data = ccall((:arf_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    ccall((:arf_set_ui, :libarb), Void, (Ptr{Void}, Culong), z.data, i)
    finalizer(z, _arf_t_clear_fn)
    return z
  end

  function arf_t(i::fmpz)
    z = new()
    z.data = ccall((:arf_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    ccall((:arf_set_fmpz, :libarb), Void, (Ptr{Void}, Ptr{fmpz}), z.data, &i)
    finalizer(z, _arf_t_clear_fn)
    return z
  end

  function arf_t(x::BigFloat)
    z = new()
    r = ccall((:arf_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    ccall((:arf_set_mpfr, :libarb), Ptr{Void}, (Ptr{Void}, Ptr{BigFloat}), r, &x)
    z.data = r
    finalizer(z, _arf_t_clear_fn)
    return z
  end

  function arf_t(x::Cdouble)
    z = new()
    z.data = ccall((:arf_vec_init, :libarb), Ptr{Void}, (Clong, ), Clong(1))
    ccall((:arf_set_d, :libarb), Void, (Ptr{Void}, Cdouble), z.data, x)
    finalizer(z, _arf_t_clear_fn)
    return z
  end

  function arf_t(a::mag_t)
    z = new()
    z.data = ccall((:arf_vec_init, :libarb), Ptr{Void}, (Clong, ), Clong(1))
    ccall((:arf_set_mag, :libarb), Void, (Ptr{Void}, Ptr{Void}), z.data, a.data)
    finalizer(z, _arf_t_clear_fn)
    return z
  end

  function arf_t(x::arf_t, p::Clong, r::Cint)
    z = new()
    z.data = ccall((:arf_vec_init, :libarb), Ptr{Void}, (Clong, ), Clong(1))
    ccall((:arf_set_round, :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong, Cint), z.data, x.data, p, r)
    finalizer(z, _arf_t_clear_fn)
    return z
  end

  function arf_t(x::Clong, p::Clong, r::Cint)
    z = new()
    z.data = ccall((:arf_vec_init, :libarb), Ptr{Void}, (Clong, ), Clong(1))
    ccall((:arf_set_round_si, :libarb), Void, (Ptr{Void}, Clong, Clong, Cint), z.data, x, p, r)
    finalizer(z, _arf_t_clear_fn)
    return z
  end

 function arf_t(x::Culong, p::Clong, r::Cint)
    z = new()
    z.data = ccall((:arf_vec_init, :libarb), Ptr{Void}, (Clong, ), Clong(1))
    ccall((:arf_set_round_ui, :libarb), Void, (Ptr{Void}, Culong, Clong, Cint), z.data, x.data, p, r)
    finalizer(z, _arf_t_clear_fn)
    return z
  end

 function arf_t(x::fmpz, p::Clong, r::Cint)
    z = new()
    z.data = ccall((:arf_vec_init, :libarb), Ptr{Void}, (Clong, ), Clong(1))
    ccall((:arf_set_round_fmpz, :libarb), Void, (Ptr{Void}, Ptr{fmpz}, Clong, Cint), z.data, &x, p, r)
    finalizer(z, _arf_t_clear_fn)
    return z
  end
end

function _arf_t_clear_fn(a::arf_t)
  ccall((:arf_vec_clear, :libarb), Ptr{Void}, (Ptr{Void}, Clong), a.data, Clong(1))
end

parent(a::arf_t) = a.parent

for (s,f) in (("zero", "arf_zero"), ("one", "arf_one"),
              ("pos_inf", "arf_pos_inf"), ("neg_inf", "arf_neg_inf"),
              ("nan", "arf_nan"))
  @eval begin
    function($(symbol(s)))(arf_t)
      z = arf_t()
      ccall(($f, :libarb), Void, (Ptr{Void},), z.data)
      return z
    end
  end
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::arf_t)
  #cstr = ccall((:arf_get_str, :libarb), Ptr{Uint8}, (Ptr{Void}, ), a.data)
  #print(io, bytestring(cstr))
  #ccall((:flint_free, :libflint), Void, (Ptr{Uint8},), cstr)
  return show(io,BigFloat(a))
end

################################################################################
#
#  Predicates
#
################################################################################

for (s,f) in (("iszero", "arf_is_zero"), ("isone", "arf_is_one"),
              ("isposinf", "arf_is_pos_inf"),
              ("isneginf", "arf_is_neg_inf"),
              ("isinf", "arf_is_inf"),
              ("isnan", "arf_is_nan"),
              ("isnormal", "arf_is_normal"),
              ("isfinite", "arf_is_finite"),
              ("isspecial", "arf_is_special"))
  @eval begin
    function($(symbol(s)))(a::arf_t)
      i = ccall(($f, :libarb), Cint, (Ptr{Void},), a.data)
      return Bool(i)
    end
  end
end

################################################################################
#
#  Comparison
#
################################################################################

function ==(x::arf_t, y::arf_t)
  r = ccall((:arf_equal, :libarb), Cint, (Ptr{Void}, Ptr{Void}), x.data, y.data)
  return Bool(r)
end

function compare(x::arf_t, y::arf_t)
  r = ccall((:arf_cmp, :libarb), Cint, (Ptr{Void}, Ptr{Void}), x.data, y.data)
  return r
end

function <(x::arf_t, y::arf_t)
  r = compare(x,y)
  r < 0 ? true : false
end

function >(x::arf_t, y::arf_t)
  r = compare(x,y)
  r > 0 ? true : false
end

function max(x::arf_t, y::arf_t)
  z = arf_t()
  ccall((:arf_max, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}), z.data, x.data, y.data)
  return z
end

function min(x::arf_t, y::arf_t)
  z = arf_t()
  ccall((:arf_min, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}), z.data, x.data, y.data)
  return z
end

################################################################################
#
#  Arithmetic
#
################################################################################

function +(x::arf_t, y::arf_t)
  check_parent(x,y)
  z = parent(x)()
  ccall(("arf_add", :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}, Clong, Cint), z.data, x.data, y.data, parent(x).prec, parent(x).rndmode)
  return z
end

function +(x::arf_t, y::Culong)
  z = parent(x)()
  ccall(("arf_add_ui", :libarb), Void, (Ptr{Void}, Ptr{Void}, Culong, Clong, Cint), z.data, x.data, y, parent(x).prec, parent(x).rndmode)
  return z
end

+(x::Culong, y::arf_t) = +(y,x)

function +(x::arf_t, y::Clong)
  z = parent(x)()
  ccall(("arf_add_si", :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong, Clong, Cint), z.data, x.data, y, parent(x).prec, parent(x).rndmode)
  return z
end

+(x::Clong, y::arf_t) = +(y,x)

function +(x::arf_t, y::fmpz)
  z = parent(x)()
  ccall(("arf_add_fmpz", :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{fmpz}, Clong, Cint), z.data, x.data, &y, parent(x).prec, parent(x).rndmode)
  return z
end

+(x::fmpz, y::arf_t) = +(y,x)

function *(x::arf_t, y::arf_t)
  check_parent(x,y)
  z = parent(x)()
  ccall(("_arf_mul", :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}, Clong, Cint), z.data, x.data, y.data, parent(x).prec, parent(x).rndmode)
  return z
end

function *(x::arf_t, y::Culong)
  z = parent(x)()
  ccall(("arf_mul_ui", :libarb), Void, (Ptr{Void}, Ptr{Void}, Culong, Clong, Cint), z.data, x.data, y, parent(x).prec, parent(x).rndmode)
  return z
end

*(x::Culong, y::arf_t) = *(y,x)

function *(x::arf_t, y::Clong)
  z = parent(x)()
  ccall(("arf_mul_si", :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong, Clong, Cint), z.data, x.data, y, parent(x).prec, parent(x).rndmode)
  return z
end

*(x::Clong, y::arf_t) = *(y,x)

function *(x::arf_t, y::fmpz)
  z = parent(x)()
  ccall(("arf_mul_fmpz", :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{fmpz}, Clong, Cint), z.data, x.data, &y, parent(x).prec, parent(x).rndmode)
  return z
end

*(x::fmpz, y::arf_t) = *(y,x)

function -(x::arf_t, y::arf_t)
  check_parent(x,y)
  z = parent(x)()
  ccall(("arf_sub", :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}, Clong, Cint), z.data, x.data, y.data, parent(x).prec, parent(x).rndmode)
  return z
end

function -(x::arf_t, y::Culong)
  z = parent(x)()
  ccall(("arf_sub_ui", :libarb), Void, (Ptr{Void}, Ptr{Void}, Culong, Clong, Cint), z.data, x.data, y, parent(x).prec, parent(x).rndmode)
  return z
end

-(x::Culong, y::arf_t) = -(y-x)

function -(x::arf_t, y::Clong)
  z = parent(x)()
  ccall(("arf_sub_si", :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong, Clong, Cint), z.data, x.data, y, parent(x).prec, parent(x).rndmode)
  return z
end

-(x::Clong, y::arf_t) = -(y-x)

function -(x::arf_t, y::fmpz)
  z = parent(x)()
  ccall(("arf_sub_fmpz", :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{fmpz}, Clong, Cint), z.data, x.data, &y, parent(x).prec, parent(x).rndmode)
  return z
end

-(x::fmpz, y::arf_t) = -(y-x)
 
function /(x::arf_t, y::arf_t)
  check_parent(x,y)
  z = parent(x)()
  ccall((:arf_div, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}, Clong, Cint), z.data, x.data, y.data, parent(x).prec, parent(x).rndmode)
  return z
end

################################################################################
#
#  Unsafe arithmetic
#
################################################################################

function add!(x::arf_t, y::arf_t)
  ccall(("arf_add", :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}, Clong, Cint), z.data, x.data, y.data, parent(x).prec, parent(x).rndmode)
end


function div!(z::arf_t, x::arf_t, y::arf_t)
  ccall((:arf_div, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}, Clong, Cint), z.data, x.data, y.data, parent(x).prec, parent(x).rndmode)
end

function sub!(x::arf_t, y::arf_t)
  ccall((:arf_sub, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}, Clong, Cint), z.data, x.data, y.data, parent(x).prec, parent(x).rndmode)
end

function mul!(x::arf_t, y::arf_t)
  ccall((:_arf_mul, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}, Clong, Cint), z.data, x.data, y.data, parent(x).prec, parent(x).rndmode)
end

################################################################################
#
#  Some functions
#
################################################################################

function sign(a::arf_t)
  r = ccall((:arf_sgn, :libarb), Cint, (Ptr{Void}, ), a.data)
  return r
end

function abs(x::arf_t)
  z = parent(x)()
  ccall((:arf_abs, :libarb), Void, (Ptr{Void}, Ptr{Void}), z.data, x.data)
  return z
end

function -(x::arf_t)
  z = parent(x)()
  ccall((:arf_neg, :libarb), Void, (Ptr{Void}, Ptr{Void}), z.data, x.data)
  return z
end


function sqrt(x::arf_t)
  z = parent(x)()
  ccall((:arf_sqrt, :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong, Cint), z.data, x.data, parent(x).prec, parent(x).rndmode)
  return z
end

################################################################################
#
#  Parent object overloads
#
################################################################################

function Base.call(r::ArfField)
  z = arf_t()
  z.parent = r
  return z
end

function Base.call(r::ArfField, x::Clong)
  z = arf_t(x, r.prec, r.rndmode)
  z.parent = r
  return z
end

function Base.call(r::ArfField, x::Culong)
  z = arf_t(x, r.prec, r.rndmode)
  z.parent = r
  return z
end

function Base.call(r::ArfField, x::fmpz)
  z = arf_t(x, r.prec, r.rndmode)
  z.parent = r
  return z
end

function Base.call(r::ArfField, x::Float64)
  z = arf_t(x)
  z = arf_t(z, r.prec, r.rndmode)
  z.parent = r
  return z
end

function Base.call(r::ArfField, x::BigFloat)
  z = arf_t(x)
  z = arf_t(z, r.prec, r.rndmode)
  z.parent = r
  return z
end

function Base.call(r::ArfField, x::mag_t)
  z = arf_t(x)
  z = arf_t(z, r.prec, r.rndmode)
  z.parent = r
  return z
end

################################################################################
#
#  Conversion
#
################################################################################

function Cdouble(a::arf_t, rnd::Cint = 4)
  z = ccall((:arf_get_d, :libarb), Cdouble, (Ptr{Void}, Cint), a.data, rnd)
  return z
end

function BigFloat(x::arf_t)
  old_prec = get_bigfloat_precision()
  set_bigfloat_precision(parent(x).prec)
  z = BigFloat(0)
  r = ccall((:arf_get_mpfr, :libarb), Cint, (Ptr{BigFloat}, Ptr{Void}, Cint), &z, x.data, Cint(0))
  set_bigfloat_precision(old_prec)
  return z
end
