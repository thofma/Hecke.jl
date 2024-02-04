module FactorFF
using Hecke

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

function Hecke.factor(f::Generic.Poly{<:Generic.RationalFunctionFieldElem})
  Pf = parent(f)
  lf = factor(to_mpoly(f))
  @assert is_constant(lf.unit)

  fa = Fac(Pf(constant_coefficient(lf.unit)), Dict((from_mpoly(k, Pf), e) for (k,e) = lf))
  @assert iszero(f) || sum(degree(x)*y for (x,y) = fa; init = 0) == degree(f)
  return fa
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

#plain vanilla Trager, possibly doomed in pos. small char.
function Hecke.factor(f::Generic.Poly{<:Generic.FunctionFieldElem})
  if !is_squarefree(f)
    sf = gcd(f, derivative(f))
    f = divexact(f, sf)
  else
    sf = one(parent(f))
  end
  lc = leading_coefficient(f)
  f = divexact(f, lc)
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
  D = Fac(parent(f)(lc), Dict((gcd(map_coefficients(base_ring(f), p, parent = parent(f)), g)(t+i*a), k) for (p,k) = fN.fac))
  if !isone(sf)
    for k = keys(D.fac)
      D.fac[k] += valuation(sf, k)
    end
  end
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
