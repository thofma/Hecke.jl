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

function is_eisenstein(f::Generic.Poly{<:NALocalFieldElem})

    pi = uniformizer(base_ring(f))
    g  = valuation(pi)
    
    if valuation(f.coeffs[1]) != g
        return false
    end
    for i=2:length(f)-1
        if valuation(f.coeffs[i]) < g
            return false
        end
    end
    if valuation(f.coeffs[length(f)]) != 0
        return false
    end
    return true
end
