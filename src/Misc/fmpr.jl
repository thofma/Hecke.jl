#=
mutable struct fmpr
  _man::Int
  _exp::Int

  function fmpr()
    z = new()
    ccall((:fmpr_init, libarb), Nothing, (Ref{fmpr}, ), z)
    finalizer(_fmpr_clear_fn, z)
    return z
  end

  function fmpr(x::Ref{arf_struct})
    z = new()
    ccall((:fmpr_init, libarb), Nothing, (Ref{fmpr}, ), z)
    ccall((:arf_get_fmpr, libarb), Nothing, (Ref{fmpr}, Ref{arf_struct}), z, x)
    finalizer(_fmpr_clear_fn, z)
    return z
  end

  function fmpr(x::arf_struct)
    z = new()
    ccall((:fmpr_init, libarb), Nothing, (Ref{fmpr}, ), z)
    ccall((:arf_get_fmpr, libarb), Nothing, (Ref{fmpr}, Ref{arf_struct}), z, x)
    finalizer(_fmpr_clear_fn, z)
    return z
  end
end

function _fmpr_clear_fn(x::fmpr)
  ccall((:fmpr_clear, libarb), Nothing, (Ref{fmpr}, ), x)
end

function fmpq(x::fmpr)
  z = fmpq()
  ccall((:fmpr_get_fmpq, libarb), Nothing, (Ref{fmpq}, Ref{fmpr}), z, x)
  return z
end
=#

mutable struct cfrac
  coeff::Ptr{fmpz}
  n::Int
  l::Int # real length

  function cfrac(x::Int)
    z = new()
    z.coeff = ccall((:_fmpz_vec_init, libflint), Ptr{fmpz}, (Int, ), x)
    z.n = x
    finalizer(_cfrac_clear_fn, z)
    return z
  end
end

function _cfrac_clear_fn(x::cfrac)
  ccall((:_fmpz_vec_clear, libflint), Nothing, (Ptr{fmpz}, Int), x.coeff, x.n)
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
  l = ccall((:fmpq_get_cfrac, libflint), Int, (Ptr{fmpz}, Ref{fmpq}, Ref{fmpq}, Int), z.coeff, r, x, y)
  z.l = l
  return z, r
end

function fmpq(x::cfrac)
  z = fmpq()
  ccall((:fmpq_set_cfrac, libflint), Nothing, (Ref{fmpq}, Ptr{fmpz}, Int), z, x.coeff, x.l)
  return z
end

function fmpq(x::cfrac, y::Int)
  z = fmpq()
  ccall((:fmpq_set_cfrac, libflint), Nothing, (Ref{fmpq}, Ptr{fmpz}, Int), z, x.coeff, y)
  return z
end

