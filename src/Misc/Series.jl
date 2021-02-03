Nemo.fit!(::fmpq_rel_series, Int) = nothing
Nemo.fit!(::fmpq_abs_series, Int) = nothing

@doc Markdown.doc"""
    integral(f::RelSeriesElem{T}) -> RelSeriesElem

Return the integral of the power series $f$.
"""
function Nemo.integral(f::RelSeriesElem{T}) where T
  g = parent(f)()
  fit!(g, precision(f)+1)
  set_precision!(g, precision(f)+1)
  v = valuation(f)
  Nemo.set_valuation!(g, v+1)
  for i=0:Nemo.pol_length(f)
    c = Nemo.polcoeff(f, i)
    if !iszero(c)
      setcoeff!(g, i, divexact(c, i+v+1))
    end
  end
  Nemo.renormalize!(g) 
  return g
end
