
function _arb_get_fmpq(x::arb)
  mid = ccall((:arb_mid_ptr, :libarb), Ptr{arf_struct}, (Ptr{arb}, ), &x)
  e = fmpz()
  m = fmpz()
  b = ccall((:arf_get_fmpz_2exp, :libarb), Cint, (Ptr{fmpz}, Ptr{fmpz}, Ptr{arf_struct}), &m, &e, mid)
  @assert abs(e) < 2^63 - 1
  ee = Int(e)
  return fmpq(m, fmpz(1))*fmpq(2)^(ee)
end

