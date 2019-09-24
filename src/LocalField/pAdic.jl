@doc Markdown.doc"""
  lift(a::padic) -> fmpz

  Returns the positive canonical representative in Z. a needs
  to be integral.
"""
function lift(a::padic)
  b = fmpz()
  R = parent(a)
  ccall((:padic_get_fmpz, :libflint), Nothing, (Ref{fmpz}, Ref{padic}, Ref{FlintPadicField}), b, a, R)
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

function is_eisenstein(f::Generic.Poly{padic})
    if valuation(f.coeffs[1]) != 1
        return false
    end
    for i=2:length(f)-1
        if valuation(f.coeffs[i]) < 1
            return false
        end
    end
    if valuation(f.coeffs[length(f)]) != 0
        return false
    end
    return true
end
