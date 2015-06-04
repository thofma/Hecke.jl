################################################################################
#
#  mag_t.jl: Wrapping mag_t C-struct
#
################################################################################

################################################################################
#
#  TODO
#  - fix (the function name of) the conversion to Rational{BigInt}
#
################################################################################

export mag_t, MagSet

export one, zero, inf, lttwopower, gttwopower, eqtwopower, isone, iszero, isinf,
       isfinite, isspecial

################################################################################
#
#  Types and memory management
#
################################################################################

type MagnSet
end  

type mag_t
  data::Ptr{Void} # pointer to mag_t C-struct

  function mag_t()
    z = new()
    z.data = ccall((:_mag_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    finalizer(z, _mag_t_clear_fn)
    return z
  end

  function mag_t(r::Ptr{Void})
    z = new()
    z.data = r
    return z
  end
  
  function mag_t(i::Culong)
    z = new()
    z.data = ccall((:_mag_vec_init, :libarb), Ptr{Void}, (Clong, ), Clong(1))
    ccall((:mag_set_ui, :libarb), Void, (Ptr{Void}, Culong), z.data, i)
    finalizer(z, _mag_t_clear_fn)
    return z
  end

  function mag_t(x::fmpz)
    z = new()
    z.data = ccall((:_mag_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    ccall((:mag_set_fmpz, :libarb), Void, (Ptr{Void}, Ptr{fmpz}), z.data, &x)
    finalizer(z, _mag_t_clear_fn)
    return z
  end

  function mag_t(d::Float64)
    z = new()
    z.data = ccall((:_mag_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    ccall((:mag_set_d, :libarb), Void, (Ptr{Void}, Cdouble), z.data, Cdouble(d))
    finalizer(z, _mag_t_clear_fn)
    return z
  end

  function mag_t(d::Cdouble, x::fmpz)
    z = new()
    z.data = ccall((:_mag_vec_init, :libarb), Ptr{Void}, (Clong, ), Clong(1))
    ccall((:mag_set_d_2exp_fmpz, :libarb), Void, (Ptr{Void}, Cdouble, Ptr{fmpz}), z.data, &x)
    finalizer(z, _mag_t_clear_fn)
    return z
  end

  function mag_t(x::fmpz, y::fmpz)
    z = new()
    z.data = ccall((:_mag_vec_init, :libarb), Ptr{Void}, (Clong, ), Clong(1))
    ccall((:mag_set_fmpz_2_exp_fmpz, :libarb), Void, (Ptr{Void}, Ptr{fmpz}, Ptr{fmpz}), z.data, &x, &y)
    finalizer(z, _mag_t_clear_fn)
    return z
  end

  function mag_t(x::Culong, y::Clong)
    z = new()
    z.data = ccall((:_mag_vec_init, :libarb), Ptr{Void}, (Clong, ), Clong(1))
    ccall((:mag_set_ui_2exp_si, :libarb), Void, (Ptr{Void}, Culong, Clong), z.data, x, y)
    finalizer(z, _mag_t_clear_fn)
    return z
  end
end

function _mag_t_clear_fn(a::mag_t)
  ccall((:_mag_vec_clear, :libarb), Void, (Ptr{Void}, Clong), a.data, Clong(1))
end

MagSet = MagnSet()

parent(::mag_t) = MagSet

function mag_t_lower(x::Culong)
  z = mag_t()
  ccall((:mag_set_ui_lower, :libarb), Void, (Ptr{Void}, Culong), z.data, x)
  return z
end

function mag_t_lower(x::BigInt)
  z = mag_t()
  x = fmpz(x)
  ccall((:mag_set_fmpz_lower, :libarb), Void, (Ptr{Void}, Ptr{fmpz}), z.data, &x)
  return z
end

function mag_t_lower(x::BigInt, y::BigInt)
  x = fmpz(x)
  y = fmpz(y)
  z = mag_t()
  ccall((:mag_set_fmpz_2_exp_fmpz_lower, :libarb), Void, (Ptr{Void}, Ptr{fmpz}, Ptr{fmpz}), z.data, &x, &y)
  return z
end

function one(mag_t)
  z = mag_t()
  ccall((:mag_one, :libarb), Void, (Ptr{Void}, ), z.data)
  return z
end

function zero(mag_t)
  z = mag_t()
  ccall((:mag_zero, :libarb), Void, (Ptr{Void}, ), z.data)
  return z
end

function inf(mag_t)
  z = mag_t()
  ccall((:mag_inf, :libarb), Void, (Ptr{Void}, ), z.data)
  return z
end


################################################################################
#
#  String I/O
#
################################################################################

#function show(io::IO, a::mag_t)
#  show(io,arf_t(a))
#end

################################################################################
#
#  Predicates
#
################################################################################

for (s,f) in (("iszero", "mag_is_zero"), ("isone", "mag_is_one"),
              ("isinf", "mag_is_inf"), ("isspecial", "mag_is_special"),
              ("isfinite", "mag_is_finite"))
  @eval begin
    function($(symbol(s)))(a::mag_t)
      i::Cint
      i = ccall(($f, :libarb), Cint, (Ptr{Void},), a.data)
      return Bool(i)
    end
  end
end

################################################################################
#
#  Comparisons
#
################################################################################

function ==(a::mag_t, b::mag_t)
  r = ccall((:mag_equal, :libarb), Cint, (Ptr{Void}, Ptr{Void}), a.data, b.data)
  return Bool(r)
end

function compare(a::mag_t, b::mag_t)
  r = ccall((:mag_cmp, :libarb), Cint, (Ptr{Void}, Ptr{Void}), a.data, b.data)
  return r
end

function <(a::mag_t, b::mag_t)
  r = compare(a,b)
  r < 0 ? true : false
end

function >(a::mag_t, b::mag_t)
  r = compare(a,b)
  r > 0 ? true : false
end

function compare_with_twopower(a::mag_t, e::Clong)
  r = ccall((:mag_cmp_2exp_si, :libarb), Cint, (Ptr{Void}, Clong), a.data, e)
  return r
end

function lttwopower(a::mag_t, e::Clong)
  r = compare_with_twopower(a,e)
  r < 0 ? true : false
end

function gttwopower(a::mag_t, e::Clong)
  r = compare_with_twopower(a,e)
  r > 0 ? true : false
end

function eqtwopower(a::mag_t, e::Clong)
  r = compare_with_twopower(a,e)
  r == 0 ? true : false
end

function min(a::mag_t, b::mag_t)
  z = mag_t()
  ccall((:mag_min, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}), z.data, a.data, b.data)
  return z
end

function max(a::mag_t, b::mag_t)
  z = mag_t()
  ccall((:mag_max, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}), z.data, a.data, b.data)
  return z
end
  
################################################################################
#
#  Conversion
#
################################################################################

function Rat(x::mag_t)
  y = fmpq()
  ccall((:mag_get_fmpq, :libarb), Void, (Ptr{fmpq}, Ptr{Void}), &y, x.data)
  return Rational(y)
end
  
################################################################################
#
#  Arithmetic
#
################################################################################

function  +(x::mag_t, y::mag_t)
  z = mag_t()
  ccall((:mag_add, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}), z.data, x.data, y.data)
  return z
end

function *(x::mag_t, y::mag_t)
  z = mag_t()
  ccall((:mag_mul, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}), z.data, x.data, y.data)
  return z
end

function *(x::mag_t,y::Culong)
  z = mag_t()
  ccall((:mag_mul_ui, :libarb), Void, (Ptr{Void}, Ptr{Void}, Culong), z.data, x.data, y)
  return z
end

function *(x::mag_t, y::BigInt)
  z = mag_t()
  y = fmpz(y)
  ccall((:mag_mul_fmpz, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{fmpz}), z.data, x.data, &y)
  return z
end

*(x::BigInt, y::mag_t) = y*x

function /(x::mag_t, y::mag_t)
  z = mag_t()
  ccall((:mag_div, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}), z.data, x.data, y.data)
  return z
end

function /(x::mag_t, y::Culong)
  z = mag_t()
  ccall((:mag_div_ui, :libarb), Void, (Ptr{Void}, Ptr{Void}, Culong), z.data, x.data, y)
  return z
end

function /(x::mag_t, y::BigInt)
  z = mag_t()
  y = fmpz(y)
  ccall((:mag_div_fmpz, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{fmpz}), z.data, x.data, &y)
  return z
end

################################################################################
#
#  Parent object overloads
#
################################################################################

function Base.call(::MagnSet)
  return mag_t()
end

function Base.call(::MagnSet, a::Culong)
  return mag_t(a)
end

function Base.call(::MagnSet, a::fmpz)
  return mag_t(a)
end

function Base.call(::MagnSet, a::Int)
  return mag_t(ZZ(a))
end

function Base.call(::MagnSet, d::Float64)
  return mag_t(d)
end

function Base.call(::MagnSet, a::Float64, b::fmpz)
  return mag_t(a,b)
end

function Base.call(::MagnSet, a::fmpz, b::fmpz)
  return mag_t(a,b)
end

function Base.call(::MagnSet, a::Culong, b::Clong)
  return mag_t(a,b)
end
