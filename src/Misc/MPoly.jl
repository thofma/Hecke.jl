###############################################################################
# other stuff, trivia and non-trivia
###############################################################################

#TODO: only makes sense if f is univ (uses only one var)
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

function mul!(res::fmpq_mpoly, a::fmpq_mpoly, c::fmpz)
  ccall((:fmpq_mpoly_scalar_mul_fmpz, libflint), Nothing,
    (Ref{fmpq_mpoly}, Ref{fmpq_mpoly}, Ref{fmpz}, Ref{FmpqMPolyRing}), res, a, c, parent(a))
  return nothing
end

#@doc Markdown.doc"""
#    is_univariate(f::Generic.MPoly{T}) where T <: NumFieldElem -> Bool, PolyElem{T}
#
#Tests if $f$ involves only one variable. If so, return a corresponding univariate polynomial.
#"""
#function is_univariate(f::Generic.MPoly{T}) where T
#  kx, x = PolynomialRing(base_ring(f), "x", cached = false)
#  if ngens(parent(f)) == 1
#    f1 = kx()
#    for i = 1:f.length
#      setcoeff!(f1, Int(f.exps[1, i]), f.coeffs[i])
#    end
#    return true, f1
#  end
#  if f.length == 0
#    @assert iszero(f)
#    return true, kx(0)
#  end
#  n = ngens(parent(f))
#  i = 1
#  while i <= n && iszero(f.exps[i, :])
#    i += 1
#  end
#  j = n
#  while j >= 1 && iszero(f.exps[j, :])
#    j -= 1
#  end
#  if i != j
#    return false, x
#  end
#  f1 = kx()
#  for j = 1:f.length
#    setcoeff!(f1, Int(f.exps[i, j]), f.coeffs[j])
#  end
#  return true, f1
#end

function (R::FmpzMPolyRing)(f::fmpq_mpoly)
  return map_coefficients(ZZ, f, parent = R)
end
Hecke.ngens(R::FmpzMPolyRing) = length(gens(R))

#check with Nemo/ Dan if there are better solutions
#the block is also not used here I think
#functionality to view mpoly as upoly in variable `i`, so the
#coefficients are mpoly's without variable `i`.
function Hecke.leading_coefficient(f::MPolyElem, i::Int)
  g = MPolyBuildCtx(parent(f))
  d = degree(f, i)
  for (c, e) = zip(coefficients(f), exponent_vectors(f))
    if e[i] == d
      e[i] = 0
      push_term!(g, c, e)
    end
  end
  return finish(g)
end

#not used here
"""
`content` as a polynomial in the variable `i`, i.e. the gcd of all the
coefficients when viewed as univariate polynomial in `i`.
"""
function Hecke.content(f::MPolyElem, i::Int)
  return reduce(gcd, coefficients(f, i))
end

"""
The coefficients of `f` when viewed as a univariate polynomial in the `i`-th
variable.
"""
function Hecke.coefficients(f::MPolyElem, i::Int)
  d = degree(f, i)
  cf = [MPolyBuildCtx(parent(f)) for j=0:d]
  for (c, e) = zip(coefficients(f), exponent_vectors(f))
    a = e[i]
    e[i] = 0
    push_term!(cf[a+1], c, e)
  end
  return map(finish, cf)
end

