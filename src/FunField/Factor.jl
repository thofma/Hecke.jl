module FactorFF
using ..Hecke

function _is_separable(F::Generic.FunctionField)
  return is_separable(defining_polynomial(F))
end

function _isomorphic_separable_extension(F::Generic.FunctionField{<:FinFieldElem})
  @assert !_is_separable(F)
  f = defining_polynomial(F)
  K = base_ring(f)
  # K = k(t)
  d = lcm(denominator.(coefficients(f)))
  fint = map_coefficients(numerator, d * f; cached = false)
  R = base_ring(fint)
  Rxy, (x, y) = polynomial_ring(R, [:x, :y]; cached = false)
  fintbiv = map_coefficients(c -> c(y), fint)(x)
  # new do the switcheroo
  # this is in R[y][x] = R[x, y]
  gint = fintbiv(gen(base_ring(fint)), gen(parent(fint)))
  g = map_coefficients(base_ring(F), gint)
  FF, FFprim = function_field(g, :b; cached = false)
  # now the maps ...
  FtoFF = function(a)
    anum = numerator(a)    
    aden = denominator(a) # parent(aden) == R
    abiv = (map_coefficients(c -> c(y), anum)(x))
    abivswap = abiv(gen(base_ring(fint)), FFprim)/aden(FFprim)
    return abivswap::typeof(a)
  end

  FFtoF = function(b)
    bnum = numerator(b)    
    bden = denominator(b) # parent(aden) == R
    bbiv = (map_coefficients(c -> c(y), bnum)(x))
    bbivswap = bbiv(gen(base_ring(fint)), gen(F))/bden(gen(F))
    return bbivswap::typeof(b)
  end

  for i in 1:10
    a = rand(F, 0:5)
    b = rand(F, 0:5)
    @assert FtoFF(a * b) == FtoFF(a) * FtoFF(b)
    @assert FFtoF(FtoFF(a)) == a
  end
  return FF, FtoFF, FFtoF
end

function Hecke.norm(f::PolyRingElem{<: Generic.FunctionFieldElem})
    K = base_ring(f)
    P = polynomial_to_power_sums(f, degree(f)*degree(K))
    PQ = elem_type(base_field(K))[tr(x) for x in P]
    return power_sums_to_polynomial(PQ)
end

function from_mpoly(f::MPolyRingElem, S::PolyRing{<:Generic.RationalFunctionFieldElem})
  @assert ngens(parent(f)) == 2
  @assert base_ring(f) == base_ring(base_ring(S))
  R = parent(numerator(gen(base_ring(S))))
  @assert isa(R, PolyRing)
  F = [zero(R) for i=0:degree(f, 1)]
  for (c, e) = zip(coefficients(f), exponent_vectors(f))
    setcoeff!(F[e[1]+1], e[2], c)
  end
  o = one(parent(F[1]))
  return S(map(x->base_ring(S)(x//o), F))
end

function to_mpoly(f::Generic.Poly{<:Generic.RationalFunctionFieldElem})
  Pf = parent(f)
  R, r = polynomial_ring(base_ring(base_ring(f)), 2)
  d = is_zero(f) ? one(R) : lcm(map(denominator, coefficients(f)))
  Fc = MPolyBuildCtx(R)
  for i=0:degree(f)
    c = numerator(coeff(f, i)*d)
    for j=0:degree(c)
      push_term!(Fc, coeff(c, j), [i,j])
    end
  end
  return finish(Fc)
end

function Hecke.factor_absolute(f::Generic.Poly{<:Generic.RationalFunctionFieldElem})
  Pf = parent(f)
  lf = factor_absolute(to_mpoly(f))

  la = Any[from_mpoly(lf[1], Pf)]
  for (gh, v) = lf[2:end]
    g = gh[1]
    h = gh[2]
    k = base_ring(g)
    kt, t = rational_function_field(k, base_ring(Pf).S, cached = false)
    ktx, x = polynomial_ring(kt, symbols(Pf)[1], cached = false)
    push!(la, [from_mpoly(g, ktx), from_mpoly(h, ktx)]=>v)
  end
  return la
end

function is_absolutely_irreducible(f::Generic.Poly{<:Generic.RationalFunctionFieldElem})
  return is_absolutely_irreducible(to_mpoly(f))
end

function Hecke.factor(F::Generic.FunctionField{T}, f::Generic.Poly{<:Generic.RationalFunctionFieldElem{T}}) where {T}
  return factor(map_coefficients(F, f, cached = false))
end

# squarefree factorization a la Trager-Gianni

function is_separable(f::PolyRingElem{<:FieldElem})
  # Bourbaki, N. (2003). *Algebra II. Chapters 4--7*. Springer-Verlag, Berlin.
  # Chapter 5, §7, No. 2.
  return is_unit(gcd(f, derivative(f)))
end

function _induced_derivation(a::Generic.FunctionFieldElem)
  # Given F/k(T), extend the non-trivial deriviation from k(T) to F
  # see Gianni-Trager, Prop. 11.
  #
  # TODO: improve this by caching the extension to the primitive element
  f = minpoly(a)
  b = -((map_coefficients(derivative, f)))(a)/(derivative(f)(a))
  return b
end

function _induced_derivation(f::PolyRingElem{<:Generic.FunctionFieldElem})
  # Gianni-Trager, Ex. 4
  return  map_coefficients(_induced_derivation, f; parent = parent(f))
end

function Hecke.factor_squarefree(f::PolyRingElem{<:Generic.FunctionFieldElem})
  if characteristic(base_ring(f)) == 0
    return Hecke.Nemo._factor_squarefree_char_0(f)
  end
  if is_separable(defining_polynomial(base_ring(f)))
    return _factor_squarefree_sep_ext(f)
  end
  FF, FtoFF, FFtoF = _isomorphic_separable_extension(base_ring(f))
  ff = map_coefficients(FtoFF, f; cached = false)
  fa = _factor_squarefree_sep_ext(ff)
  D = Dict{typeof(f), Int}((map_coefficients(FFtoF, q; parent = parent(f)), e) for (q, e) in fa)
  return Fac(map_coefficients(FFtoF, unit(fa); parent = parent(f)), D)
end

function _factor_squarefree_sep_ext(f::PolyRingElem{<:Generic.FunctionFieldElem})
  @req is_separable(defining_polynomial(base_ring(f))) "Defining polynomial must be separable"
  D = Dict{typeof(f), Int}() 
  un = leading_coefficient(f)
  f = divexact(f, leading_coefficient(f))
  p = characteristic(base_ring(f))
  C = gcd(f, derivative(f), _induced_derivation(f))
  B = divexact(f, C)
  R = Tuple{typeof(f), Int}[]
  i = 1
  while !is_unit(B)
    _B = B
    B = gcd(C, _B)
    C = divexact(C, B)
    P = divexact(_B, B)
    D[P] = i
    i += 1
  end
  delete!(D, one(f))
  R = Fac(parent(f)(un), D)
  k = i - 1
  if degree(C) == 0
    return R
  end
  h = Hecke.absolute_frobenius_inverse(C)
  Hecke.AbstractAlgebra.mulpow!(R, factor_squarefree(h), Int(p))
  return R
end

function Hecke.is_squarefree(f::PolyRingElem{<:Generic.FunctionFieldElem})
  if characteristic(base_ring(f)) == 0
    return is_unit(gcd(f, derivative(f)))
  end
  return all(e == 1 for (_, e) in factor_squarefree(f)) 
end

function Hecke.factor(f::Generic.Poly{<:Generic.FunctionFieldElem})
  if !_is_separable(base_ring(f))
    FF, FtoFF, FFtoF = _isomorphic_separable_extension(base_ring(f))
    return Hecke.AbstractAlgebra.Generic._transport_factor(factor, f, FtoFF, FFtoF)
  end
  return _factor_assume_separable(f)
end

function _factor_assume_separable(f::Generic.Poly{<:Generic.FunctionFieldElem})
  lc = leading_coefficient(f)
  f = divexact(f, lc)
  fsqf = factor_squarefree(f)
  res = Fac(one(f), Dict{typeof(f), Int}())
  for (p, e) in fsqf
    D = _factor_assume_squarefree_and_separable(p)
    Hecke.AbstractAlgebra.mulpow!(res, D, e)
  end
  Hecke.AbstractAlgebra.mulpow!(res, parent(f)(lc), 1)
  return res
end

#plain vanilla Trager, possibly doomed in pos. small char.
function _factor_assume_squarefree_and_separable(f::Generic.Poly{<:Generic.FunctionFieldElem})
  i = 0
  local N
  g = f
  t = gen(parent(f))
  a = gen(base_ring(t))

  while true
    if !iszero(constant_coefficient(g))
      N = norm(g)
      if is_squarefree(N)
        break
      end
    end
    i += 1
    g = evaluate(g, t-a)
    if i > 10
      error("not plausible")
    end
  end

  fN = factor(N)
  @assert isone(fN.unit)
  D = Fac(one(parent(f)), Dict((gcd(map_coefficients(base_ring(f), p, parent = parent(f)), g)(t+i*a), k) for (p,k) = fN.fac))
  return D
end

#TODO: don't think this strategy is optimal, but it works...
function Hecke.splitting_field(f::Generic.Poly{<:Generic.RationalFunctionFieldElem})
  f = divexact(f, gcd(f, derivative(f)))

  lf = factor(f)
  lf = [x for x = keys(lf.fac) if degree(x) > 1]
  if length(lf) == 0
    return base_ring(f)
  end

  while true
    G, b = function_field(lf[1], "b", cached = false)
    if length(lf) == 1 && degree(G) < 3
      return G
    end

    f = prod(lf)

    GT, t = polynomial_ring(G, cached = false)
    g = divexact(map_coefficients(G, f, parent = GT), t-b)

    i = 0
    local N
    while true
      if !iszero(constant_coefficient(g))
        N = norm(g)
        if is_squarefree(N)
          break
        end
      end
      i += 1
      g = evaluate(g, t-b)
      if i > 10
        error("not plausible")
      end
    end

    fN = factor(N)
    lf = [x for x = keys(fN.fac) if degree(x) > degree(G)]
      #the gcd of x with deg(x) == deg(G) will yield a linear
      #factor, hence does not contribute further
    if length(lf) == 0
      return G
    end
  end
end


@doc raw"""
    swinnerton_dyer(V::Vector, x::Generic.Poly{<:Generic.RationalFunctionFieldElem})
    swinnerton_dyer(n::Int, x::Generic.Poly{<:Generic.RationalFunctionFieldElem})

Compute the minimal polynomial of $\sum \pm \sqrt{t+v_i}$ evaluated at $x$.
$t$ is the generator of the base field of the parent of $x$.

In the second variant, the polynomial has roots $\sum\pm\sqrt{t+i}$ for
  $i=1,\ldots,n$.
"""
function Hecke.swinnerton_dyer(V::Vector, x::Generic.Poly{<:Generic.RationalFunctionFieldElem})
  n = length(V)
  @assert characteristic(parent(x)) == 0 || characteristic(parent(x)) > length(V)
  S = base_ring(x)
  T = gen(S)
  X = gen(parent(x))
  l = [(X^2 + T + i) for i = V]
  l = [ vcat([2*one(S)], polynomial_to_power_sums(x, 2^n)) for x = l]
  while n > 1
    i = 1
    while 2*i <= n
      l[i] = [sum(binomial(ZZRingElem(h), ZZRingElem(j))*l[2*i-1][j+1]*l[2*i][h-j+1] for j=0:h) for h=0:length(l[1])-1]
      i += 1
    end
    if isodd(n)
      l[i] = l[n]
      n = i
    else
      n = i-1
    end
  end
  f = power_sums_to_polynomial(l[1][2:end], parent(x))
  if x == gen(parent(x))
    return f
  else
    return f(x)
  end
end

function Hecke.swinnerton_dyer(n::Int, x::Generic.Poly{<:Generic.RationalFunctionFieldElem})
  return swinnerton_dyer(x, collect(1:n))
end

end
