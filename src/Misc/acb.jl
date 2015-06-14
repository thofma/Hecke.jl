export acb

type acb
  real_mid_exp::Int # fmpz
  real_mid_size::UInt64 # mp_size_t
  real_mid_d1::Int64 # mantissa_struct
  real_mid_d2::Int64
  real_rad_exp::Int # fmpz
  real_rad_man::UInt64
  imag_mid_exp::Int # fmpz
  imag_mid_size::UInt64 # mp_size_t
  imag_mid_d1::Int64 # mantissa_struct
  imag_mid_d2::Int64
  imag_rad_exp::Int # fmpz
  imag_rad_man::UInt64

  function acb()
    z = new()
    ccall((:acb_init, :libarb), Void, (Ptr{acb}, ), &z)
    finalizer(z, _acb_clear_fn)
    return z
  end

  function acb(x::Clong)
    z = new()
    ccall((:acb_init, :libarb), Void, (Ptr{acb}, ), &z)
    ccall((:acb_set_si, :libarb), Void, (Ptr{acb}, Clong), &z, x)
    finalizer(z, _acb_clear_fn)
    return z
  end
end

function _acb_clear_fn(x::acb)
  ccall((:acb_clear, :libarb), Void, (Ptr{acb}, ), &x)
end

function real(x::acb)
  z = arb()
  r = ccall((:acb_get_real, :libarb), Ptr{arb}, (Ptr{acb}, ), &x)
  ccall((:arb_set, :libarb), Void, (Ptr{arb}, Ptr{arb}), &z, r)
  return z
end

function imag(x::acb)
  z = arb()
  r = ccall((:acb_get_imag, :libarb), Ptr{arb}, (Ptr{acb}, ), &x)
  ccall((:arb_set, :libarb), Void, (Ptr{arb}, Ptr{arb}), &z, r)
  return z
end

function show(io::IO, x::acb)
  show(io,real(x))
  print(io, " + i*")
  show(io,imag(x))
end

