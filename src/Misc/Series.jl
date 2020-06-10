function inv(a::RelSeriesElem{<:Nemo.FieldElem}) 
#function inv(a::RelSeriesElem{nf_elem})
  @assert valuation(a)==0
  # x -> x*(2-xa) is the lifting recursion
  x = parent(a)(inv(coeff(a, 0)))
  x = set_prec!(x, 1)
  p = precision(a)
  la = [p]
  while la[end]>1
    push!(la, div(la[end]+1, 2))
  end

  two = parent(a)(base_ring(a)(2))
  two = set_prec!(two, p)

  n = length(la)-1
  y = parent(a)()
  while n>0
    x = set_prec!(x, la[n])
    y = set_prec!(y, la[n])
#    y = mul!(y, a, x)
#    y = two-y #sub! is missing...
#    x = mul!(x, x, y)
    x = x*(two-x*a)
    n -=1 
  end
  return x
end

function log(a::RelSeriesElem{<:Nemo.FieldElem}) 
  @assert valuation(a)==0 
  return integral(derivative(a)*inv(a))
end

function exp(a::RelSeriesElem{<:Nemo.FieldElem})
  @assert valuation(a) >0
  R = base_ring(parent(a))
  x = parent(a)([R(1)], 1, 2, 0)
  p = precision(a)
  la = [p]
  while la[end]>1
    push!(la, div(la[end]+1, 2))
  end

  one = parent(a)([R(1)], 1, 2, 0)

  n = length(la)-1
  # x -> x*(1-log(a)+a) is the recursion
  while n>0
    x = set_prec!(x, la[n])
    one = set_prec!(one, la[n])
    x = x*(one - log(x) + a) # TODO: can be optimized...
    n -=1 
  end
  return x
end

@doc Markdown.doc"""
    derivative(f::RelSeriesElem{T}) -> RelSeriesElem
Return the derivative of the power series $f$.
"""
function derivative(f::RelSeriesElem{T}) where T
  g = parent(f)()
  g = set_prec!(g, precision(f)-1)
  fit!(g, pol_length(f))
  v = valuation(f)
  g = set_val!(g, 0)
  if v==0
    for i=1:Nemo.pol_length(f)
      setcoeff!(g, i-1, (i+v)*Nemo.polcoeff(f, i))
    end
  else
    for i=0:Nemo.pol_length(f)
      setcoeff!(g, i, (i+v)*Nemo.polcoeff(f, i))
    end
    g = set_val!(g, v-1)
  end
  Nemo.renormalize!(g)  
  return g
end

Nemo.fit!(::fmpq_rel_series, Int) = nothing
Nemo.fit!(::fmpq_abs_series, Int) = nothing

@doc Markdown.doc"""
    integral(f::RelSeriesElem{T}) -> RelSeriesElem
Return the integral of the power series $f$.
"""
function Nemo.integral(f::RelSeriesElem{T}) where T
  g = parent(f)()
  fit!(g, precision(f)+1)
  g = set_prec!(g, precision(f)+1)
  v = valuation(f)
  g = Nemo.set_val!(g, v+1)
  for i=0:Nemo.pol_length(f)
    setcoeff!(g, i, divexact(Nemo.polcoeff(f, i), i+v+1))
  end
  Nemo.renormalize!(g) 
  return g
end


