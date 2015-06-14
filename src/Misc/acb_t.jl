################################################################################
#
#  acb_t.jl: Wrapper for acb_t C-struct
#
################################################################################

export acb_t, AcbField

export imag, real, one, onei, copy

################################################################################
#
#  Types and memory management
#
################################################################################

AcbFieldID = ObjectIdDict()

type AcbField <: Field
  prec::Clong
  
  function AcbField(p::Clong = 256)
    try
      return AcbFieldID[p]
    catch
      AcbFieldID[p] = new(p)
    end
  end
end

type acb_t
  data::Ptr{Void}
  real::arb_t
  imag::arb_t
  parent::AcbField

  function acb_t()
    z = new()
    z.data = ccall((:_acb_vec_init, :libarb), Ptr{Void}, (Clong, ), Clong(1))
    finalizer(z, _acb_t_clear_fn)
    return z
  end

  function acb_t(r::Ptr{Void})
    z = new()
    z.data = r
    return z
  end

  function acb_t(i::Clong)
    z = new()
    z.data = ccall((:_acb_vec_init, :libarb), Ptr{Void}, (Clong, ), Clong(1))
    ccall((:acb_set_si, :libarb), Void, (Ptr{Void}, Clong), z.data, i)
    finalizer(z, _acb_t_clear_fn)
    return z
  end

  function acb_t(i::Culong)
    z = new()
    z.data = ccall((:_acb_vec_init, :libarb), Ptr{Void}, (Clong, ), Clong(1))
    ccall((:acb_set_ui, :libarb), Void, (Ptr{Void}, Culong), z.data, i)
    finalizer(z, _acb_t_clear_fn)
    return z
  end

  function acb_t(x::fmpz)
    z = new()
    z.data = ccall((:_acb_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    ccall((:acb_set_fmpz, :libarb), Void, (Ptr{Void}, Ptr{fmpz}), z.data, &x)
    finalizer(z, _acb_t_clear_fn)
    return z
  end

  function acb_t(a::arb_t)
    z = new()
    z.data = ccall((:_acb_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    ccall((:acb_set_arb, :libarb), Void, (Ptr{Void}, Ptr{Void}), z.data, a.data)
    finalizer(z, _acb_t_clear_fn)
    return z
  end

  function acb_t(x::acb_t, p::Clong)
    z = new()
    z.data = ccall((:_acb_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    ccall((:acb_set_round, :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong), z.data, x.data, p)
    finalizer(z, _acb_t_clear_fn)
    return z
  end

  function acb_t(x::fmpz, p::Clong)
    z = new()
    z.data = ccall((:_acb_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    ccall((:acb_set_round_fmpz, :libarb), Void, (Ptr{Void}, Ptr{fmpz}, Clong), z.data, &x, p)
    finalizer(z, _acb_t_clear_fn)
    return z
  end

  function acb_t(x::fmpq, p::Clong)
    z = new()
    z.data = ccall((:_acb_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    ccall((:acb_set_fmpq, :libarb), Void, (Ptr{Void}, Ptr{fmpq}, Clong), z.data, &x, p)
    finalizer(z, _acb_t_clear_fn)
    return z
  end

  function acb_t(x::arb_t, p::Clong)
    z = new()
    z.data = ccall((:_acb_vec_init, :libarb), Ptr{Void}, (Clong,), Clong(1))
    ccall((:acb_set_round_arb, :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong), z.data, x.data, p)
    finalizer(z, _acb_t_clear_fn)
    return z
  end
end

parent(x::acb_t) = x.parent

function copy(a::acb_t)
  b = parent(a)()
  ccall((:acb_set, :libarb), Void, (Ptr{Void}, Ptr{Void}), b.data, a.data)
  return b
end

function _acb_t_clear_fn(a::acb_t)
  ccall((:_acb_vec_clear, :libarb), Void, (Ptr{Void}, Clong), a.data, Clong(1))
end

function one(r::AcbField)
  z = acb_t()
  ccall((:acb_one, :libarb), Void, (Ptr{Void}, ), z.data)
  z.parent = r
  return z
end

function onei(r::AcbField)
  z = acb_t()
  ccall((:acb_onei, :libarb), Void, (Ptr{Void}, ), z.data)
  z.parent = r
  return z
end

################################################################################
#
#  Comparison
#
################################################################################

function strongequal(x::acb_t, y::acb_t)
  check_parent(x,y)
  r = ccall((:acb_equal, :libarb), Cint, (Ptr{Void}, Ptr{Void}), x.data, y.data)
  return Bool(r)
end

################################################################################
#
#  Arithmetic
#
################################################################################

function +(x::acb_t, y::acb_t)
  #check_parent(x,y)
  z = parent(x)()
  ccall((:acb_add, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}), z.data, x.data, y.data)
  return z
end

function -(x::acb_t, y::acb_t)
  check_parent(x,y)
  z = parent(x)()
  ccall((:acb_sub, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}), z.data, x.data, y.data)
  return z
end

function *(x::acb_t, y::acb_t)
  #check_parent(x,y)
  z = parent(x)()
  ccall((:acb_mul, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}), z.data, x.data, y.data)
  return z
end

function /(x::acb_t, y::acb_t)
  check_parent(x,y)
  z = parent(x)()
  ccall((:acb_div, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}), z.data, x.data, y.data)
  return z
end

################################################################################
#
#  Unsafe arithmetic
#
################################################################################

function add!(z::acb_t, x::acb_t, y::acb_t)
  ccall((:acb_add, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}), z.data, x.data, y.data)
end

function sub!(z::acb_t, x::acb_t, y::acb_t)
  ccall((:acb_sub, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}), z.data, x.data, y.data)
end

function mul!(z::acb_t, x::acb_t, y::acb_t)
  ccall((:acb_mul, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}), z.data, x.data, y.data)
end

function div!(z::acb_t, x::acb_t, y::acb_t)
  ccall((:acb_div, :libarb), Void, (Ptr{Void}, Ptr{Void}, Ptr{Void}), z.data, x.data, y.data)
end
 
################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::acb_t)
  show(io,real(a))
  print(io, " + i*")
  show(io,imag(a))
end

################################################################################
#
#  Functions
#
###############################################################################

function real(a::acb_t)
  if isdefined(a, :real)
    return a.real
  else
    r = ccall((:acb_get_real, :libarb), Ptr{Void}, (Ptr{Void}, ), a.data)
    z = arb_t(r)
    a.real = z
    a.real.parent = ArbField(parent(a).prec)
    return a.real
  end
end

function imag(a::acb_t)
  if isdefined(a, :imag)
    return a.imag
  else
    r = ccall((:acb_get_imag, :libarb), Ptr{Void}, (Ptr{Void}, ), a.data)
    z = arb_t(r)
    a.imag = z
    a.imag.parent = ArbField(parent(a).prec)
    return a.imag
  end
end

function -(x::acb_t)
  z = acb_t()
  ccall((:acb_neg, :libarb), Void, (Ptr{Void}, Ptr{Void}), z.data, x.data)
  z = acb_t(z, parent(x).prec)
  z.parent = parent(x)
  return z
end

function conj(x::acb_t)
  z = acb_t()
  ccall((:acb_conj, :libarb), Void, (Ptr{Void}, Ptr{Void}), z.data, x.data)
  z = acb_t(z, parent(x).prec)
  z.parent = parent(x)
  return z
end

function abs(x::acb_t)
  z = arb_t()
  ccall((:acb_abs, :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong), z.data, x.data, parent(x).prec)
  z.parent = ArbField(parent(x).prec)
  return z
end

################################################################################
#
#  Parent object overload
#
################################################################################

function Base.call(r::AcbField)
  z = acb_t()
  z.parent = r
  return z
end

function Base.call(r::AcbField, x::Clong)
  z = acb_t(x)
  z = acb_t(z, r.prec)
  z.parent = r
  return z
end

function Base.call(r::AcbField, x::Culong)
  z = acb_t(x)
  z = acb_t(z, r.prec)
  z.parent = r
  return z
end

function Base.call(r::AcbField, x::fmpz)
  z = acb_t(x, r.prec)
  z.parent = r
  return z
end

function Base.call(r::AcbField, x::fmpq)
  z = acb_t(x, r.prec)
  z.parent = r
  return z
end

function Base.call(r::AcbField, x::arb_t)
  z = acb_t(x, r.prec)
  z.parent = r
  return z
end

