#=
mutable struct fmpr
  _man::Int
  _exp::Int

  function fmpr()
    z = new()
    ccall((:fmpr_init, libflint), Nothing, (Ref{fmpr}, ), z)
    finalizer(_fmpr_clear_fn, z)
    return z
  end

  function fmpr(x::Ref{arf_struct})
    z = new()
    ccall((:fmpr_init, libflint), Nothing, (Ref{fmpr}, ), z)
    ccall((:arf_get_fmpr, libflint), Nothing, (Ref{fmpr}, Ref{arf_struct}), z, x)
    finalizer(_fmpr_clear_fn, z)
    return z
  end

  function fmpr(x::arf_struct)
    z = new()
    ccall((:fmpr_init, libflint), Nothing, (Ref{fmpr}, ), z)
    ccall((:arf_get_fmpr, libflint), Nothing, (Ref{fmpr}, Ref{arf_struct}), z, x)
    finalizer(_fmpr_clear_fn, z)
    return z
  end
end

function _fmpr_clear_fn(x::fmpr)
  ccall((:fmpr_clear, libflint), Nothing, (Ref{fmpr}, ), x)
end

function QQFieldElem(x::fmpr)
  z = QQFieldElem()
  ccall((:fmpr_get_fmpq, libflint), Nothing, (Ref{QQFieldElem}, Ref{fmpr}), z, x)
  return z
end
=#

mutable struct cfrac
  coeff::Ptr{ZZRingElem}
  n::Int
  l::Int # real length

  function cfrac(x::Int)
    z = new()
    z.coeff = ccall((:_fmpz_vec_init, libflint), Ptr{ZZRingElem}, (Int, ), x)
    z.n = x
    finalizer(_cfrac_clear_fn, z)
    return z
  end
end

function _cfrac_clear_fn(x::cfrac)
  ccall((:_fmpz_vec_clear, libflint), Nothing, (Ptr{ZZRingElem}, Int), x.coeff, x.n)
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
function cfrac(x::QQFieldElem, y::Int)
  r = QQFieldElem()
  z = cfrac(y)
  l = ccall((:fmpq_get_cfrac, libflint), Int, (Ptr{ZZRingElem}, Ref{QQFieldElem}, Ref{QQFieldElem}, Int), z.coeff, r, x, y)
  z.l = l
  return z, r
end

function QQFieldElem(x::cfrac)
  z = QQFieldElem()
  ccall((:fmpq_set_cfrac, libflint), Nothing, (Ref{QQFieldElem}, Ptr{ZZRingElem}, Int), z, x.coeff, x.l)
  return z
end

function QQFieldElem(x::cfrac, y::Int)
  z = QQFieldElem()
  ccall((:fmpq_set_cfrac, libflint), Nothing, (Ref{QQFieldElem}, Ptr{ZZRingElem}, Int), z, x.coeff, y)
  return z
end

