function _arb_get_fmpq(x::arb)
  mid = ccall((:arb_mid_ptr, :libarb), Ptr{arf_struct}, (Ptr{arb}, ), &x)
  e = fmpz()
  m = fmpz()
  b = ccall((:arf_get_fmpz_2exp, :libarb), Cint, (Ptr{fmpz}, Ptr{fmpz}, Ptr{arf_struct}), &m, &e, mid)
  @assert abs(e) < typemax(Int)
  ee = Int(e)
  return fmpq(m, fmpz(1))*fmpq(2)^(ee)
end

function mul2exp!(z::arb, x::arb, y::Int)
  ccall((:arb_mul_2exp_si, :libarb), Void, (Ptr{arb}, Ptr{arb}, Int), &z, &x, y)
  return nothing
end
 

function muleq!(z::arb, x::arb, y::arb)
  ccall((:arb_mul, :libarb), Void, (Ptr{arb}, Ptr{arb}, Ptr{arb}, Int), &z, &x, &y, parent(x).prec)
  return nothing
end

function muleq!(z::arb, x::arb, y::fmpz)
  ccall((:arb_mul_fmpz, :libarb), Void, (Ptr{arb}, Ptr{arb}, Ptr{fmpz}, Int), &z, &x, &y, parent(x).prec)
  return nothing
end

function addmul!(z::arb, x::arb, y::fmpz)
  ccall((:arb_addmul_fmpz, :libarb), Void, (Ptr{arb}, Ptr{arb}, Ptr{fmpz}, Int), &z, &x, &y, parent(x).prec)
  return nothing
end

function abs!(z::arb, x::arb)
  ccall((:arb_abs, :libarb), Void, (Ptr{arb}, Ptr{arb}, Int), &z, &x, parent(x).prec)
  return nothing
end

function abs!(z::arb, x::acb)
  ccall((:acb_abs, :libarb), Void, (Ptr{arb}, Ptr{acb}, Int), &z, &x, parent(x).prec)
  return nothing
end

function log!(z::arb, x::arb)
  ccall((:arb_log, :libarb), Void, (Ptr{arb}, Ptr{arb}, Int), &z, &x, parent(x).prec)
  return nothing
end
