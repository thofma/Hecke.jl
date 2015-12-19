@doc """
  lift(a::padic) -> fmpz

  Returns the positive canonical representative in Z. a needs
  to be integral.
""" ->
function lift(a::padic)
  b = fmpz()
  R = parent(a)
  ccall((:padic_get_fmpz, :libflint), Void, (Ptr{fmpz}, Ptr{padic}, Ptr{FlintPadicField}), &b, &a, &R)
  return b
end

