################################################################################
#
#  arb_t.jl: Wrapping arb_t C-struct
#
################################################################################

export arb_t, ArbField

export radius, midpoint, zeropminf, indeterminate, contains, contains_zero, contains_negative, contains_positive, contains_nonnegative, contains_nonpositive, isnonzero, isexact, isint, ispositive, isnonnegative, isnegative, isnonpositive, sin, cos, tan, add!, mul!, sub!, div!, strongequal

ArbFieldID = ObjectIdDict()

type ArbField <: Field
  prec::Clong
  
  function ArbField(p::Clong = 256)
    try
      return ArbFieldID[p]
    catch
      ArbFieldID[p] = new(p)
    end
  end
end

type arb_t
  data::Ptr{Void} # Pointer to arb_t C-struct
  rad::mag_t      # Pointer to mag_t C-struct, which holds the radius 
  mid::arf_t      # Pointer to arf_t C-struct, which holds the midpoint
  parent::ArbField
  

  function arb_t()
    z = new()
    z.data = ccall((:_arb_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    finalizer(z, _arb_t_clear_fn)
    return z
  end

  function arb_t(x::arb_t, p::Clong)
    z = new()
    z.data = ccall((:_arb_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    ccall((:arb_set_round, :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong), z.data, x.data, p)
    finalizer(z, _arb_t_clear_fn)
    return z
  end

  function arb_t(r::Ptr{Void})
    z = new()
    z.data = r
    return z
  end

  function arb_t(i::Clong)
    z = new()
    z.data = ccall((:_arb_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    ccall((:arb_set_si, :libarb), Void, (Ptr{Void}, Clong), z.data, i)
    finalizer(z, _arb_t_clear_fn)
    return z
  end

  function arb_t(i::Culong)
    z = new()
    z.data = ccall((:_arb_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    ccall((:arb_set_ui, :libarb), Void, (Ptr{Void}, Culong), z.data, i)
    finalizer(z, _arb_t_clear_fn)
    return z
  end

  function arb_t(x::fmpz)
    z = new()
    z.data = ccall((:_arb_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    ccall((:arb_set_fmpz, :libarb), Void, (Ptr{Void}, Ptr{fmpz}), z.data, &x)
    finalizer(z, _arb_t_clear_fn)
    return z
  end
 
  function arb_t(x::fmpz, p::Clong)
    z = new()
    z.data = ccall((:_arb_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    ccall((:arb_set_round_fmpz, :libarb), Void, (Ptr{Void}, Ptr{fmpz}, Clong), z.data, &x, p)
    finalizer(z, _arb_t_clear_fn)
    return z
  end
 
  function arb_t(x::fmpq, p::Clong)
    z = new()
    z.data = ccall((:_arb_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    ccall((:arb_set_fmpq, :libarb), Void, (Ptr{Void}, Ptr{fmpq},Clong), z.data, &x, p)
    finalizer(z, _arb_t_clear_fn)
    return z
  end
 
  function arb_t(x::arf_t)
    z = new()
    z.data = ccall((:_arb_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    ccall((:arb_set_arf, :libarb), Void, (Ptr{Void}, Ptr{Void}), z.data, x.data)
    finalizer(z, _arb_t_clear_fn)
    return z
  end
end

function _arb_t_clear_fn(a::arb_t)
  ccall((:_arb_vec_clear, :libarb), Void, (Ptr{Void}, Clong), a.data, Clong(1))
end

parent(a::arb_t) = a.parent

for (s,f) in (("zero", "arb_zero"), ("one", "arb_one"),
              ("pos_inf", "arb_pos_inf"), ("neg_inf", "arb_neg_inf"),
              ("zeropminf", "arb_zero_pm_inf"),
              ("indeterminate", "arb_indeterminate"))
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

function show(io::IO, a::arb_t)
  cstr = ccall((:arb_get_str, :libarb), Ptr{UInt8}, (Ptr{Void}, Clong, Culong),
                                                  a.data, Clong(10), Culong(1))
  print(io, bytestring(cstr))
  ccall((:flint_free, :libflint), Void, (Ptr{Uint8},), cstr)
end

################################################################################
#
#  Comparisons
#
################################################################################

function strongequal(x::arb_t, y::arb_t)
  r = ccall((:arb_equal, :libarb), Cint, (Ptr{Void}, Ptr{Void}), x.data, y.data)
  return Bool(r)
end

function overlaps(x::arb_t, y::arb_t)
  r = ccall((:arb_overlaps, :libarb), Cint, (Ptr{Void}, Ptr{Void}),
                                      x.data, y.data)
  return Bool(r)
end

function contains(x::arb_t, y::arf_t)
  r = ccall((:arb_contains_arf, :libarb), Cint, (Ptr{Void}, Ptr{Void}), x.data, y.data)
  return Bool(r)
end

function contains(x::arb_t, y::fmpq)
  r = ccall((:arb_contains_fmpq, :libarb), Cint, (Ptr{Void}, Ptr{fmpq}), x.data, &y)
  return Bool(r)
end

function contains(x::arb_t, y::fmpz)
  r = ccall((:arb_contains_fmpz, :libarb), Cint, (Ptr{Void}, Ptr{fmpz}), x.data, &y)
  return Bool(r)
end

function contains(x::arb_t, y::Clong)
  r = ccall((:arb_contains_si, :libarb), Cint, (Ptr{Void}, Ptr{fmpz}), x.data, y)
  return Bool(r)
end

function contains(x::arb_t, y::BigFloat)
  r = ccall((:arb_contains_mpfr, :libarb), Cint, (Ptr{Void}, Ptr{BigFloat}), x.data, &y)
  return Bool(r)
end

function contains(x::arb_t, y::arb_t)
  r = ccall((:arb_contains, :libarb), Cint, (Ptr{Void}, Ptr{Void}), x.data, y.data)
  return Bool(r)
end

for (s,f) in (("contains_zero", "arb_contains_zero"),
              ("contains_negative", "arb_contains_negative"),
              ("contains_positive", "arb_contains_positive"),
              ("contains_nonpositive", "arb_contains_nonpositive"),
              ("contains_nonnegative", "arb_contains_nonnegative"))
  @eval begin
    function($(symbol(s)))(a::arb_t)
      r = ccall(($f, :libarb), Cint, (Ptr{Void}, ), a.data)
      return Bool(r)
    end
  end
end

################################################################################
#
#  Predicates
#
################################################################################

for (s,f) in (("iszero", "arb_is_zero"),
              ("isnonzero", "arb_is_nonzero"),
              ("isone", "arb_is_one"),
              ("isfinite", "arb_is_finite"),
              ("isexact", "arb_is_exact"),
              ("isint", "arb_is_int"),
              ("ispositive", "arb_is_positive"),
              ("isnonnegative", "arb_is_nonnegative"),
              ("isnegative", "arb_is_negative"),
              ("isnonpositive", "arb_is_nonpositive"))
  @eval begin
    function($(symbol(s)))(a::arb_t)
      i = ccall(($f, :libarb), Cint, (Ptr{Void},), a.data)
      return Bool(i)
    end
  end
end


function radius(a::arb_t)
  if isdefined(a, :rad)
    return a.rad
  end
  r = ccall((:arb_get_rad, :libarb), Ptr{Void}, (Ptr{Void},), a.data)
  a.rad =  mag_t(r)
  return a.rad
end

function midpoint(a::arb_t)
  if isdefined(a, :mid)
    return a.mid
  end
  r = ccall((:arb_get_mid, :libarb), Ptr{Void}, (Ptr{Void},), a.data)
  a.mid = arf_t(r)
  a.mid.parent = ArfField(parent(a).prec)
  return a.mid
end

for (s,f) in (("iszero", "arb_is_zero"), ("isnonzero", "arb_is_nonzero"),
              ("isone", "arb_is_one"), ("isfinite", "arb_is_finite"),
              ("isexact", "arb_is_exact"), ("isint", "arb_is_int"),
              ("ispositive", "arb_is_positive"),
              ("isnonnegative", "arb_is_nonnegative"),
              ("isnegative", "arb_is_negative"),
              ("isnonnegative", "arb_is_nonnegative"))
  @eval begin
    function($(symbol(s)))(a::arb_t)
      i::Cint
      i = ccall(($f, :libarb), Cint, (Ptr{Void},), a.data)
      return Bool(i)
    end
  end
end

################################################################################
#
#  Arithmetic
#
################################################################################

function -(a::arb_t)
  z = arb_t()
  ccall((:arb_neg, :libarb), Void, (Ptr{Void}, Ptr{Void}), z.data, a.data)
  z = arb_t(z, parent(a).prec)
  z.parent = a.parent
  return z
end

for (s,f) in ((:+,"arb_add"), (:*,"arb_mul"), (:/, "arb_div"), (:-,"arb_sub"))
  @eval begin
    function ($s)(x::arb_t, y::arb_t)
      check_parent(x,y)
      z = parent(x)()
      ccall(($f, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}, Clong),
                           z.data, x.data, y.data, parent(x).prec)
      return z
    end
  end
end

for (f,s) in ((:+, "add"), (:*, "mul"))
  @eval begin
    function ($f)(x::arb_t, y::arf_t)
      z = parent(x)()
      ccall(($("arb_"*s*"_arf"), :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}, Clong), z.data, x.data, y.data, parent(x).prec)
      return z
    end

    ($f)(x::arf_t,y::arb_t) = ($f)(y,x)

    function ($f)(x::arb_t, y::Culong)
      z = parent(x)()
      ccall(($("arb_"*s*"_ui"), :libarb), Void, (Ptr{Void}, Ptr{Void}, Culong, Clong), z.data, x.data, y, parent(x).prec)
      return z
    end

    ($f)(x::Culong, y::arb_t) = ($f)(y,x)

    function ($f)(x::arb_t, y::Clong)
      z = parent(x)()
      ccall(($("arb_"*s*"_si"), :libarb), Ptr{Void}, (Ptr{Void}, Ptr{Void}, Clong, Clong), z.data, x.data, y, parent(x).prec)
      return z
    end

    ($f)(x::Clong, y::arb_t) = ($f)(y,x)

    function ($f)(x::arb_t, y::fmpz)
      z = parent(x)()
      ccall(($("arb_"*s*"_fmpz"), :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{fmpz}, Clong), z.data, x.data, &y, parent(x).prec)
      return z
    end

    ($f)(x::fmpz, y::arb_t) = ($f)(y,x)
  end
end

function -(x::arb_t, y::arf_t)
  z = parent(x)()
  ccall((:arb_sub_arf, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}, Clong), z.data, x.data, y.data, parent(x).prec)
  return z
end

-(x::arf_t, y::arb_t) = -(y-x)

function -(x::arb_t, y::Culong)
  z = parent(x)()
  ccall((:arb_sub_ui, :libarb), Void, (Ptr{Void}, Ptr{Void}, Culong, Clong), z.data, x.data, y, parent(x).prec)
  return z
end

-(x::Culong, y::arb_t) = -(y-x)

function -(x::arb_t, y::Clong)
  z = parent(x)()
  ccall((:arb_sub_si, :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong, Clong), z.data, x.data, y, parent(x).prec)
  return z
end

-(x::Clong, y::arb_t) = -(y-x)

function -(x::arb_t, y::fmpz)
  z = parent(x)()
  ccall((:arb_sub_fmpz, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{fmpz}, Clong), z.data, x.data, &y, parent(x).prec)
  return z
end

-(x::fmpz, y::arb_t) = -(y-x)

function /(x::arb_t, y::arf_t)
  z = parent(x)()
  ccall((:arb_div_arf, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}, Clong), z.data, x.data, y.data, parent(x).prec)
  return z
end

function /(x::arb_t, y::Culong)
  z = parent(x)()
  ccall((:arb_div_ui, :libarb), Void, (Ptr{Void}, Ptr{Void}, Culong, Clong), z.data, x.data, y, parent(x).prec)
  return z
end

function /(x::arb_t, y::Clong)
  z = parent(x)()
  ccall((:arb_div_si, :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong, Clong), z.data, x.data, y, parent(x).prec)
  return z
end

function /(x::arb_t, y::fmpz)
  z = parent(x)()
  ccall((:arb_div_fmpz, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{fmpz}, Clong), z.data, x.data, &y, parent(x).prec)
  return z
end

function ^(x::arb_t, y::arb_t)
  z = parent(x)()
  ccall((:arb_pow, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}, Clong), z.data, x.data, y.data, parent(x).prec)
  return z
end

function ^(x::arb_t, y::fmpz)
  z = parent(x)()
  ccall((:arb_pow_fmpz, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{fmpz}, Clong), z.data, x.data, &y, parent(x).prec)
  return z
end

function ^(x::arb_t, y::Culong)
  z = parent(x)()
  ccall((:arb_pow_ui, :libarb), Void, (Ptr{Void}, Ptr{Void}, Culong, Clong), z.data, x.data, y, parent(x).prec)
  return z
end

function inv(x::arb_t)
  z = arb_t()
  ccall((:arb_inv, :libarb), Void, (Ptr{Void}, Ptr{Void}), z.data, x.data)
  return parent(x)(z)
end

################################################################################
#
#  Unsafe binary operations
#
################################################################################

for (s,f) in (("add!","arb_add"), ("mul!","arb_mul"), ("div!", "arb_div"), ("sub!","arb_sub"))
  @eval begin
    function ($(symbol(s)))(z::arb_t, x::arb_t, y::arb_t)
      ccall(($f, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}, Clong),
                           z.data, x.data, y.data, parent(x).prec)
    end
  end
end

################################################################################
#
#  Functions
#
################################################################################

function log(x::arb_t)
  z = parent(x)()
  ccall((:arb_log, :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong), z.data, x.data, parent(x).prec)
  return z
end

function exp(x::arb_t)
  z = parent(x)()
  ccall((:arb_exp, :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong), z.data, x.data, parent(x).prec)
  return z
end

function sqrt(x::arb_t)
  z = parent(x)()
  ccall((:arb_sqrt, :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong), z.data, x.data, parent(x).prec)
  return z
end

function sin(x::arb_t)
  z = parent(x)()
  ccall((:arb_sin, :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong), z.data, x.data, parent(x).prec)
  return z
end

function cos(x::arb_t)
  z = parent(x)()
  ccall((:arb_cos, :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong), z.data, x.data, parent(x).prec)
  return z
end

function tan(x::arb_t)
  z = parent(x)()
  ccall((:arb_tan, :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong), z.data, x.data, parent(x).prec)
  return z
end

################################################################################
#
#  Parent object overloads
#
################################################################################

#function Base.call(r::ArbField)
#  z = arb_t()
#  z.parent = r
#  return z
#end
#
#function Base.call(r::ArbField, a::Clong)
#  z = arb_t(arb_t(a), r.prec)
#  z.parent = r
#  return z
#end
#
#function Base.call(r::ArbField, a::Culong)
#  z = arb_t(arb_t(a), r.prec)
#  z.parent = r
#  return z
#end
#
#function Base.call(r::ArbField, a::fmpz)
#  z = arb_t(a, r.prec)
#  z.parent = r
#  return z
#end
#
#function Base.call(r::ArbField, a::fmpq)
#  z = arb_t(a, r.prec)
#  z.parent = r
#  return z
#end
#  
#function Base.call(r::ArbField, a::arf_t)
#  z = arb_t(arb_t(a), r.prec)
#  z.parent = r
#  return z
#end
#
#function Base.call(r::ArbField, a::Float64)
#  return r(arf_t(a))
#end
#
#function Base.call(r::ArbField, a::arb_t)
#  z = arb_t(a, r.prec)
#  z.parent = r
#  return z
#end
#
#function Base.call(r::ArbField, a::MathConst)
#  if a == pi
#    z = pi_arb_t(r.prec)
#    z.parent = r
#    return z
#  elseif a == e
#    z = e_arb_t(r.prec)
#    z.parent = r 
#    return z
#  else
#    error("constant not supported")
#  end
#end

################################################################################
#
#  Constants
#
################################################################################

function pi_arb_t(p::Clong)
  z = arb_t()
  ccall((:arb_const_pi, :libarb), Void, (Ptr{Void}, Clong), z.data, p)
  return z
end

function e_arb_t(p::Clong)
  z = arb_t()
  ccall((:arb_const_e, :libarb), Void, (Ptr{Void}, Clong), z.data, p)
  return z
end

# the following is bugged

#for (s,f) in (("pi", "arb_const_pi"), ("e", "arb_const_e"))
#  @eval begin
#    function ($(symbol("arb_t")))(s)
#      z = arb_t()
#      ccall(($f, :libarb), Void, (Ptr{Void}, Clong), z.data, get_arb_precision())
#      return z
#    end
#  end
#end


