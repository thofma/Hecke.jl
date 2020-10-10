@doc Markdown.doc"""
    lift(a::padic) -> fmpz

Returns the positive canonical representative in $\mathbb{Z}$. $a$ needs
to be integral.
"""
function lift(a::padic)
  b = fmpz()
  R = parent(a)
  ccall((:padic_get_fmpz, libflint), Nothing, (Ref{fmpz}, Ref{padic}, Ref{FlintPadicField}), b, a, R)
  return b
end


function Base.setprecision(f::Generic.Poly{padic}, N::Int)
  f = deepcopy(f)
  for i=1:length(f)
    f.coeffs[i].N = N
  end
  return f
end

function setprecision!(f::Generic.Poly{padic}, N::Int)
  for i=1:length(f)
    f.coeffs[i].N = N
  end
  return f
end
