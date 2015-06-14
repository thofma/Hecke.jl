export arf

type arf
  exp::Int # fmpz
  size::UInt64 # mp_size_t
  d1::Int64 # mantissa_struct
  d2::Int64

  function arf()
    z = new()
    finalizer(z, _arf_clear_fn)
  end
  
  function arf(i::Clong)
    z = new()
    ccall((:arf_init, :libarb), Void, (Ptr{arf}, ), &z)
    ccall((:arf_set_si, :libarb), Void, (Ptr{arf}, Clong), &z, i)
    finalizer(z, _arf_clear_fn)
    return z
  end
end

function _arf_clear_fn(x::arf)
  ccall((:arf_clear, :libarb), Void, (Ptr{arf}, ), &x)
end

function BigFloat(x::arf)
  old_prec = get_bigfloat_precision()
  set_bigfloat_precision(50)
  z = Base.MPFR.BigFloat(0)
  r = ccall((:arf_get_mpfr, :libarb), Cint, (Ptr{Base.MPFR.BigFloat}, Ptr{arf}, Cint), &z, &x, Cint(0))
  set_bigfloat_precision(old_prec)
  return z
end

function show(io::IO, a::arf)
  #cstr = ccall((:arf_get_str, :libarb), Ptr{Uint8}, (Ptr{Void}, ), a.data)
  #print(io, bytestring(cstr))
  #ccall((:flint_free, :libflint), Void, (Ptr{Uint8},), cstr)
  return show(io,BigFloat(a))
end


