###############################################################################
# other stuff, trivia and non-trivia
###############################################################################

function Nemo.PolynomialRing(R::Nemo.Ring, n::Int, s::String="x";
                             cached::Bool = false, ordering::Symbol = :lex)
  return Nemo.PolynomialRing(R, ["$s$i" for i=1:n], cached = cached,
                                                    ordering = ordering)
end

#TODO: makes only sense if f is univ (uses only one var)
function (Rx::FmpzPolyRing)(f::fmpq_mpoly)
  fp = Rx()
  R = base_ring(Rx)
  d = denominator(f)
  @assert d == 1
  for t = terms(f)
    e = total_degree(t)
    @assert length(t) == 1
    c = coeff(t, 1)
    setcoeff!(fp, e, numerator(c*d))
  end
  return fp
end

function (Rx::FmpqPolyRing)(f::fmpq_mpoly)
  fp = Rx()
  R = base_ring(Rx)
  for t = terms(f)
    e = total_degree(t)
    @assert length(t) == 1
    c = coeff(t, 1)
    setcoeff!(fp, e, c)
  end
  return fp
end

function (Rx::GFPPolyRing)(f::fmpq_mpoly)
  fp = Rx()
  R = base_ring(Rx)
  d = denominator(f)
  for t = terms(f)
    e = total_degree(t)
    @assert length(t) == 1
    c = coeff(t, 1)
    setcoeff!(fp, e, R(numerator(c*d)))
  end
  return fp * inv(R(d))
end

function derivative(f::Generic.Frac{T}, x::T) where {T <: MPolyElem}
  return derivative(f, var_index(x))
end

function derivative(f::Generic.Frac{T}, i::Int) where {T <: MPolyElem}
  n = numerator(f)
  d = denominator(f)
  return (derivative(n, i)*d - n*derivative(d, i))//d^2
end

function evaluate(f::Generic.Frac{T}, V::Vector{U}) where {T <: RingElem, U <: RingElem}
  return evaluate(numerator(f), V)//evaluate(denominator(f), V)
end

function evaluate(f::Generic.Frac{T}, v::U) where {T <: RingElem, U <: RingElem}
  return evaluate(numerator(f), v)//evaluate(denominator(f), v)
end

function Hecke.lead(f::AbstractAlgebra.MPolyElem)
  iszero(f) && error("zero poly")
  return coeff(f, 1)
end

function Hecke.coefficients(f::AbstractAlgebra.MPolyElem)
  return Hecke.PolyCoeffs(f)
end

function Base.iterate(PC::Hecke.PolyCoeffs{<:AbstractAlgebra.MPolyElem}, st::Int = 0)
  st += 1
  if st > length(PC.f)
    return nothing
  else
    return coeff(PC.f, st), st
  end
end

Base.length(M::Hecke.PolyCoeffs{<:AbstractAlgebra.MPolyElem}) = length(M.f)

function mul!(res::fmpq_mpoly, a::fmpq_mpoly, c::fmpz)
  ccall((:fmpq_mpoly_scalar_mul_fmpz, libflint), Nothing,
    (Ref{fmpq_mpoly}, Ref{fmpq_mpoly}, Ref{fmpz}, Ref{FmpqMPolyRing}), res, a, c, parent(a))
  return nothing
end


