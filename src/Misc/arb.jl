export arb

type arb
  mid_exp::Int # fmpz
  mid_size::UInt64 # mp_size_t
  mid_d1::Int64 # mantissa_struct
  mid_d2::Int64
  rad_exp::Int # fmpz
  rad_man::UInt64

  function arb()
    z = new()
    ccall((:arb_init, :libarb), Void, (Ptr{arb}, ), &z)
    finalizer(z, _arb_clear_fn)
    return z
  end

  function arb(x::Clong)
    z = new()
    ccall((:arb_init, :libarb), Void, (Ptr{arb}, ), &z)
    ccall((:arb_set_si, :libarb), Void, (Ptr{arb}, Clong), &z, x)
    finalizer(z, _arb_clear_fn)
    return z
  end
end

function _arb_clear_fn(x::arb)
  ccall((:arb_clear, :libarb), Void, (Ptr{arb}, ), &x)
end

function show(io::IO, x::arb)
  cstr = ccall((:arb_get_str, :libarb), Ptr{UInt8}, (Ptr{arb}, Clong, Culong),
                                                  &x, Clong(10), Culong(1))
  print(io, bytestring(cstr))
  ccall((:flint_free, :libflint), Void, (Ptr{Uint8},), cstr)
end

