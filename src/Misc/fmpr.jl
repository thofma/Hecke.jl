type fmpr
  _man::Int
  _exp::Int

  function fmpr()
    z = new()
    ccall((:fmpr_init, :libarb), Void, (Ptr{fmpr}, ), &z)
    finalizer(z, _fmpr_clear_fn)
    return z
  end

  function fmpr(x::arf_struct)
    z = new()
    ccall((:fmpr_init, :libarb), Void, (Ptr{fmpr}, ), &z)
    ccall((:arf_get_fmpr, :libarb), Void, (Ptr{fmpr}, Ptr{arf_struct}), &z, &x)
    finalizer(z, _fmpr_clear_fn)
    return z
  end
end

function _fmpr_clear_fn(x::fmpr)
  ccall((:fmpr_clear, :libarb), Void, (Ptr{fmpr}, ), &x)
end
  
function fmpq(x::fmpr)
  z = fmpq()
  ccall((:fmpr_get_fmpq, :libarb), Void, (Ptr{fmpq}, Ptr{fmpr}), &z, &x)
  return z
end

type cfrac
  coeff::Ptr{fmpz}
  n::Clong
  l::Clong # real length

  function cfrac(x::Clong)
    z = new()
    z.coeff = ccall((:_fmpz_vec_init, :libflint), Ptr{fmpz}, (Clong, ), x)
    z.n = x
    finalizer(z, _cfrac_clear_fn)
    return z
  end
end

function _cfrac_clear_fn(x::cfrac)
  ccall((:_fmpz_vec_clear, :libflint), Void, (Ptr{fmpz}, Clong), x.coeff, x.n)
end

function show(io::IO, x::cfrac)
  print(io, "[ ")
  for i in 1:x.l
    print(io, unsafe_load(x.coeff, i))
    print(io, " ,")
  end
  print(io, "]")
end
  

# THIS LEAKS MEMORY
function cfrac(x::fmpq, y::Int)
  r = fmpq()
  z = cfrac(y)
  l = ccall((:fmpq_get_cfrac, :libflint), Clong, (Ptr{fmpz}, Ptr{fmpq}, Ptr{fmpq}, Clong), z.coeff, &r, &x, y)
  z.l = l
  return z, r
end

function fmpq(x::cfrac)
  z = fmpq()
  ccall((:fmpq_set_cfrac, :libflint), Void, (Ptr{fmpq}, Ptr{fmpz}, Clong), &z, x.coeff, x.l)
  return z
end

function fmpq(x::cfrac, y::Int)
  z = fmpq()
  ccall((:fmpq_set_cfrac, :libflint), Void, (Ptr{fmpq}, Ptr{fmpz}, Clong), &z, x.coeff, y)
  return z
end

