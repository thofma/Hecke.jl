module MPolyFact

using Hecke
import Hecke: Nemo, @vprint, @hassert, @vtime, rational_reconstruction, set_precision!,
              set_precision, find_morphism

import Nemo: shift_left, shift_right
import Base: *

export factor_absolute

add_verbose_scope(:AbsFact)
add_assert_scope(:AbsFact)

function Hecke.norm(f::MPolyElem{nf_elem})
  Kx = parent(f)
  K = base_ring(Kx)
  n = nvars(Kx)
  Qx, x = PolynomialRing(QQ, [String(x) for x= symbols(Kx)], cached = false)
  Qxy, y = PolynomialRing(Qx, "y", cached = false)
  gg = [MPolyBuildCtx(Qx) for i=1:degree(K)]
  for (c, e) = zip(coefficients(f), exponent_vectors(f))
    for i=0:degree(K)-1
      d = coeff(c, i)
      if !iszero(d)
        push_term!(gg[i+1], d, e)
      end
    end
  end
  g = Qxy(map(finish, gg))
  return resultant(g, K.pol(y))
end

#= AbsFact: strategy
 f in Q[x,y] = Q[x][y], not necc. monic, irre. over Q

 find evaluation x <- x+ly s.th. g = f(0, y) is square-free
 find p s.th g mod p is square-free and such that the lcm of the factors
   is small
 compute the roots up to a bound B over the F_q splitting field
   as power series
 compute the coeffs. of f (as elements in Q[x]) as power series

 TODO: factor f over F_p[[t]], then compute the roots of the
       factors in F_q[[t]]. Each factor over F_p[[t]] should
       correspong to a Frobenius orbit of roots.
       This way the degrees are smaller....
       Done.

 TODO: refactor: a HenselCtx for fmpq_mpoly (or fmpz_mpoly) factored
       in F_p[[t]][x]
       a RootCtx for poly in F_p[[t]][x] to find roots in F_q[[t]]
       Done.
       
       See what Dan did in this case.
=#

function set_precision(f::PolyElem{T}, n::Int) where {T <: SeriesElem}
  g = parent(f)()
  for i=0:length(f)
    setcoeff!(g, i, set_precision(coeff(f, i), n))
  end
  return g
end

function set_precision!(f::PolyElem{T}, n::Int) where {T <: SeriesElem}
  for i=0:length(f)
    setcoeff!(f, i, set_precision!(coeff(f, i), n))
  end
  return f
end

mutable struct HenselCtxFqRelSeries{T}
  f :: fmpz_mpoly # bivariate
  n :: Int # number of factors
  lf :: Array{PolyElem{T}, 1} # T should be nmod_rel_series or fq_nmod_rel_series
  cf :: Array{PolyElem{T}, 1} # the cofactors for lifting
  t :: Int # shift, not used, so might be wrong.

  function HenselCtxFqRelSeries(f::fmpz_mpoly, lf::Array{<:PolyElem{S}, 1}, lg::Array{<:PolyElem{S}, 1}, n::Int, s::Int = 0) where {S <: Union{Nemo.FinFieldElem, Nemo.nmod}}
    @assert ngens(parent(f)) == 2
    k = base_ring(lf[1])
    R, t = PowerSeriesRing(k, 10, "t", cached = false) #, model = :capped_absolute)
    Rx, x = PolynomialRing(R, cached = false)
    r = new{typeof(t)}()
    r.f = f
    r.n = n
    r.t = s
    r.lf = [set_precision(s(x), 1) for s = lf]
    r.cf = [set_precision(s(x), 1) for s = lg]
    return r
  end

  function HenselCtxFqRelSeries(f::fmpz_mpoly, lf::Array{<:PolyElem{<:SeriesElem{qadic}}, 1}, lc::Array{<:PolyElem{<:SeriesElem{qadic}}, 1}, n::Int, s::Int = 0)
    @assert ngens(parent(f)) == 2
    r = new{elem_type(base_ring(lf[1]))}()
    r.f = f
    r.n = n
    r.t = s
    r.lf = lf
    r.cf = lc
    return r
  end

  function HenselCtxFqRelSeries(f::fmpz_mpoly, p::Int, s::Int = 0)
    k = GF(p, cached = false)
    return HenselCtxFqRelSeries(f, k, s)
  end

  function HenselCtxFqRelSeries(f::fmpz_mpoly, k::FinField, s::Int = 0)
    kt, t = PolynomialRing(k, cached = false)
    g = evaluate(f, [t, kt(-s)])
    issquarefree(g) || return nothing
    @assert issquarefree(g)

    lf = collect(keys(factor(g).fac))
    return HenselCtxFqRelSeries(f, lf, s)
  end

  function HenselCtxFqRelSeries(f::fmpz_mpoly, lf::Array{<:PolyElem{<:SeriesElem{<:FinFieldElem}}}, s::Int = 0)
    k, mk = ResidueField(base_ring(lf[1]))
    kt, t = PolynomialRing(k, cached = false)
    return HenselCtxFqRelSeries(f, [map_coeffs(mk, x, parent = kt) for x = lf], s)
  end

  function HenselCtxFqRelSeries(f::fmpz_mpoly, lf::Array{<:PolyElem{<:FinFieldElem}}, s::Int = 0)
    n = length(lf)
    lg = typeof(lf[1])[]
    i = 1
    while i < length(lf)
      g, a, b = gcdx(lf[i], lf[i+1])
      @assert isone(g)
      push!(lg, a)
      push!(lg, b)
      push!(lf, lf[i] * lf[i+1])
      i += 2
    end
    k = base_ring(lf[1])
    if isa(k, Nemo.GaloisField)
      p = Int(characteristic(k))
      k = quo(ZZ, p)[1]
      kt, t = PolynomialRing(k, cached = false)
      lf = [map_coeffs(k, x, parent = kt) for x = lf]
      lg = [map_coeffs(k, x, parent = kt) for x = lg]
    end

    return HenselCtxFqRelSeries(f, lf, lg, n, s)
  end
end

function shift_coeff_left!(f::PolyElem{<:SeriesElem}, n::Int)
  for i=0:length(f)
    setcoeff!(f, i, shift_left(coeff(f, i), n))
  end
end

function shift_coeff_right!(f::PolyElem{<:SeriesElem}, n::Int)
  for i=0:length(f)
    setcoeff!(f, i, shift_right(coeff(f, i), n))
  end
end

function shift_coeff_left(f::PolyElem{<:SeriesElem}, n::Int)
  g = parent(f)()
  for i=0:length(f)
    setcoeff!(g, i, shift_left(coeff(f, i), n))
  end
  return g
end

function shift_coeff_right(f::PolyElem{<:SeriesElem}, n::Int)
  g = parent(f)()
  for i=0:length(f)
    setcoeff!(g, i, shift_right(coeff(f, i), n))
  end
  return g
end

function lift(C::HenselCtxFqRelSeries{<:SeriesElem})
  St = parent(C.lf[1])
  S = base_ring(C.lf[1])
 
  pr = precision(coeff(C.lf[1], 0))
  N2 = 2*pr
  
  S.prec_max = N2+1

  i = length(C.lf)
  j = i-1
  while j > 0
    if i==length(C.lf)
      f = evaluate(C.f, [gen(St), St(gen(S)-C.t)])
      f *= inv(leading_coefficient(f))
    else
      f = set_precision(C.lf[i], N2)
      @assert ismonic(C.lf[i])
    end
    @assert ismonic(f)
    #formulae and names from the Flint doc
    h = C.lf[j]
    g = C.lf[j-1]
    b = C.cf[j]
    a = C.cf[j-1]
    set_precision!(h, N2)
    set_precision!(g, N2)
    set_precision!(a, N2)
    set_precision!(b, N2)

    fgh = shift_coeff_right(f-g*h, pr)
    
    G = shift_coeff_left(rem(fgh*b, g), pr)+g
    H = shift_coeff_left(rem(fgh*a, h), pr)+h
   
    t = shift_coeff_right(1-a*G-b*H, pr)
  
    B = shift_coeff_left(rem(t*b, g), pr)+b
    A = shift_coeff_left(rem(t*a, h), pr)+a
    if i < length(C.lf)
      C.lf[i] = G*H
    end
    C.lf[j-1] = G
    C.lf[j] = H
    C.cf[j-1] = A
    C.cf[j] = B
    i -= 1
    j -= 2
  end
end

function _set_precision(f::PolyElem{<:SeriesElem{qadic}}, n::Int)
  g = deepcopy(f)
  return _set_precision!(g, n)
end

function _set_precision!(f::PolyElem{<:SeriesElem{qadic}}, n::Int)
  for i=0:length(f)
    c = coeff(f, i)
    for j=0:pol_length(c)
      setprecision!(polcoeff(c, j), n)
    end
  end
  return f
end
# TODO: bad names... 
function _shift_coeff_left(f::PolyElem{<:SeriesElem{qadic}}, n::Int)
  g = parent(f)()
  p = prime(base_ring(base_ring(g)))^n
  for i = 0:length(f)
    setcoeff!(g, i, map_coeffs(x -> p*x, coeff(f, i), parent = base_ring(f)))
  end
  return g
end

function _shift_coeff_right(f::PolyElem{<:SeriesElem{qadic}}, n::Int)
  g = parent(f)()
  p = prime(base_ring(base_ring(g)))^n
  for i = 0:length(f)
    @assert all(y -> valuation(polcoeff(coeff(f, i), y)) >= n, 0:pol_length(coeff(f, i))) 
    setcoeff!(g, i, map_coeffs(x -> divexact(x, p), coeff(f, i), parent = base_ring(f)))
  end
  return g
end

mutable struct Preinv{T, S <: PolyElem{T}}
  f::S
  n::Int
  fi::S
  function Preinv(f::PolyElem)
    r = new{elem_type(base_ring(f)), typeof(f)}()
    r.f = reverse(f)
    @assert degree(f) == degree(r.f)
    r.fi = one(parent(f))
    r.n = 1
    return r
  end
end

preinv(f::PolyElem) = Preinv(f)

function lift(P::Preinv)
  f = truncate(P.f, 2*P.n)
  P.fi = truncate(P.fi*truncate((parent(f)(2)-f*P.fi), 2*P.n), 2*P.n)
  P.n *= 2
end

function Base.rem(g::PolyElem, P::Preinv)
  if degree(g) < degree(P.f)
    return g
  end
  if degree(g) == degree(P.f)
    return g - leading_coefficient(g)*reverse(P.f)
  end

  v = 0
  while iszero(coeff(g, v))
    v += 1
  end
  gr = reverse(g)
  while P.n < degree(g) - degree(P.f) + 1
    lift(P)
  end
  q = truncate(gr*P.fi, degree(g) - degree(P.f) + 1)
  q = reverse(q)
  if v > 0
    q = shift_left(q, v)
  end
  r = g-q*reverse(P.f)
#  global last_bad = (g, reverse(P.f))
  @hassert :AbsFact 2 r == rem(g, reverse(P.f))
  return r
end

function lift_q(C::HenselCtxFqRelSeries{<:SeriesElem{qadic}})
  St = parent(C.lf[1])
  S = base_ring(C.lf[1])
  Q = base_ring(S)
 
  pr = precision(coeff(coeff(C.lf[1], 0), 0))
  N2 = 2*pr
  
  setprecision!(Q, N2+1)

  i = length(C.lf)
  j = i-1
  while j > 0
    if i==length(C.lf)
      f = evaluate(map_coeffs(Q, C.f), [gen(St), St(gen(S))])
      f *= inv(leading_coefficient(f))
    else
#      f = _set_precision(C.lf[i], N2)
      f = C.lf[i]
      @assert precision(coeff(coeff(f, 0), 0)) >= N2
      @assert ismonic(C.lf[i])
    end
    @assert ismonic(f)
    #formulae and names from the Flint doc
    h = C.lf[j]
    g = C.lf[j-1]
    b = C.cf[j]
    a = C.cf[j-1]
    h = _set_precision(h, N2)
    g = _set_precision(g, N2)
    a = _set_precision(a, N2)
    b = _set_precision(b, N2)

    fgh = _shift_coeff_right(f-g*h, pr)
    
    @assert ismonic(g)
    @assert !iszero(constant_coefficient(g))
    @assert ismonic(h)
    @assert !iszero(constant_coefficient(h))
    gi = preinv(g)
    hi = preinv(h)

    G = _shift_coeff_left(rem(fgh*b, gi), pr)+g
    H = _shift_coeff_left(rem(fgh*a, hi), pr)+h

    t = _shift_coeff_right(1-a*G-b*H, pr)
  
    B = _shift_coeff_left(rem(t*b, gi), pr)+b
    A = _shift_coeff_left(rem(t*a, hi), pr)+a

    C.lf[j-1] = G
    C.lf[j] = H
    C.cf[j-1] = A
    C.cf[j] = B
    i -= 1
    j -= 2
  end
end

mutable struct RootCtxSingle{T}
  f::PolyElem{T}
  R::T  # the root
  o::T  # inv(f'(R)) for the double lifting.

  function RootCtxSingle(f::PolyElem{S}, K::FqNmodFiniteField) where {S <: SeriesElem}
    #not used I think
    RR,  = PowerSeriesRing(K, max_precision(R), string(var(R)), cached = false) #can't get the modell
    return RootCtxSingle(f, RR)
  end

  function RootCtxSingle(f::PolyElem{<:SeriesElem{T}}, r::T) where {T}
    R = base_ring(parent(f))
    k, mk = ResidueField(R)
    g = map_coeffs(mk, f)
    # should be zero-ish, but if T is acb, this is difficult.
    isexact_type(T) && @assert iszero(g(r))
    o = inv(derivative(g)(r))
    return new{elem_type(R)}(f, R([r], 1, 1, 0), R([o], 1, 1, 0))
  end

  function RootCtxSingle(f::PolyElem{S}, RR::FqNmodRelSeriesRing) where {S <: SeriesElem}
    K = base_ring(RR)
    R = base_ring(f) # should be a series ring
    r = new{elem_type(RR)}()
    r.f = map_coeffs(x->map_coeffs(K, x, parent = RR), f)
    k, mk = ResidueField(R)
    _, mK = ResidueField(RR)
    g = map_coeffs(mk, f)
    @vtime :AbsFact 2 rt = Nemo.any_root(map_coeffs(K, g))
    r.R = preimage(mK, rt)
    g = map_coeffs(K, g)
    @vtime :AbsFact 2 r.o = preimage(mK, inv(derivative(g)(r.R)))
    return r
  end
end

"""
Computes the roots of `f` as power series over the complex numbers up to
power series precision `pr` and complex precision `prec`. The roots
are given as power series around `r`, the 2nd argument.

Not very bright algorithm, `f` has to be square-free and `r` cannot be a singularity.
"""
function analytic_roots(f::fmpz_mpoly, r::Integer, pr::Int = 10; prec::Int = 100, max_roots = degree(f, 2))
  return analytic_roots(f, fmpz(r), pr; prec...)
end

function analytic_roots(f::fmpz_mpoly, r::fmpz, pr::Int = 10; prec::Int = 100, max_roots = degree(f, 2))
  @assert ngens(parent(f)) == 2
  g = evaluate(f, [Hecke.Globals.Zx(r), gen(Hecke.Globals.Zx)])
  @assert issquarefree(g)
  C = ComplexField(prec)
  rt = Hecke.roots(g, C)[1:max_roots]
  @assert all(x->parent(x) == C, rt)
  Cs, s = PowerSeriesRing(C, pr+2, "s", cached = false)
  Cst, t = PolynomialRing(Cs, cached = false)
  ff = evaluate(f, [Cst(s+C(r)), t])
  RT = []
  for x = rt
    R = RootCtxSingle(ff, x)
    for i=1:clog(pr, 2)
      lift(R)
    end
    push!(RT, R.R)
  end
  return RT
end

"""
Computes the roots of `f` as power series over some number field up to
power series precision `pr`. The roots
are given as power series around `r`, the 2nd argument.

Not very bright algorithm, `f` has to be square-free and `r` cannot be a singularity.
"""
function symbolic_roots(f::fmpz_mpoly, r::Integer, pr::Int = 10; max_roots::Int = degree(f, 2))
  return symbolic_roots(f, fmpz(r), pr; max_roots...)
end

function symbolic_roots(f::fmpz_mpoly, r::fmpz, pr::Int = 10; max_roots::Int = degree(f, 2))
  @assert ngens(parent(f)) == 2
  g = evaluate(f, [Hecke.Globals.Zx(r), gen(Hecke.Globals.Zx)])
  @assert issquarefree(g)
  lg = factor(g)
  rt = vcat([Hecke.roots(x, number_field(x)[1]) for x = keys(lg.fac)]...)
  rt = rt[1:min(length(rt), max_roots)]
  RT = []
  for x = rt
    C = parent(x)
    Cs, s = PowerSeriesRing(C, pr+2, "s", cached = false)
    Cst, t = PolynomialRing(Cs, cached = false)
    ff = evaluate(f, [Cst(s+C(r)), t])
    R = RootCtxSingle(ff, x)
    for i=1:clog(pr, 2)
      lift(R)
    end
    push!(RT, R.R)
  end
  return RT
end

"""
A single lifting step for the easy Newton iteration for a isolated simple root.
"""
function lift(R::RootCtxSingle)
  pr = precision(R.R)
  set_precision!(R.o, 2*pr)
  set_precision!(R.R, 2*pr)
  parent(R.R).prec_max = 2*pr+1
  R.o = R.o*(2-R.o*derivative(R.f)(R.R))
  R.R = R.R - R.f(R.R)*R.o
end

mutable struct RootCtx
  f :: fmpq_mpoly
  H :: HenselCtxFqRelSeries{nmod_rel_series}
  R :: Array{RootCtxSingle{fq_nmod_rel_series}, 1}
  RP :: Array{Array{fq_nmod_rel_series, 1}, 1}
  all_R :: Array{fq_nmod_rel_series, 1}

  function RootCtx(f::fmpq_mpoly, p::Int, d::Int, t::Int = 0)
    r = new()
    r.f = f
    den = lcm(map(denominator, coefficients(f)))
    g = map_coeffs(numerator, den*f)
    @vtime :AbsFact 2 mu = HenselCtxFqRelSeries(g, p, t)
    mu === nothing && return mu
    r.H = mu
    r.R = RootCtxSingle{fq_nmod_rel_series}[]
    K = GF(p, d)[1]
    S, _ = PowerSeriesRing(K, 10, "s", cached = false)
    for i=1:r.H.n
      @vtime :AbsFact 2 push!(r.R, RootCtxSingle(r.H.lf[i], S))
    end
    return r
  end
end

"""
Computes `R[i]^j`, cached
"""
function root(R::RootCtx, i::Int, j::Int)
  if length(R.all_R) == 0 || precision(R.R[1].R) > precision(R.all_R[1])
    empty!(R.all_R)
    for i=1:R.H.n
      push!(R.all_R, copy(R.R[i].R))
      @hassert :AbsFact 2 iszero(R.R[i].f(R.all_R[end]))
      S = parent(R.all_R[end])
      for j=1:degree(R.R[i].f)-1
        push!(R.all_R, map_coeffs(frobenius, R.all_R[end], parent = S))
        @hassert :AbsFact 3 iszero(R.R[i].f(R.all_R[end]))
      end
    end
  end

  if length(R.RP) == 0 || precision(R.all_R[1]) != precision(R.RP[1][1])
    o = one(parent(R.all_R[1]))
    R.RP = [[set_precision(o, precision(R.all_R[1])) for x = R.all_R], copy(R.all_R)]
  end
  if length(R.RP) > j 
    return (R.RP[j+1][i])
  end
  while length(R.RP) <= j+1
    push!(R.RP, R.RP[2] .* R.RP[end])
  end

  s = R.RP[j+1][i]
  return (s)
end

"""
Computes the roots of `f` in a suitable splitting field: a power series
over a finite field. The characteristic will be chosen, trying to have the
degree small. The initial precision if `2`.

Returns, not the roots, but the root context `RootCtx`, so the precision
can be increased (`newton_lift`, `roots`, `more_precision`).
"""
function roots(f::fmpq_mpoly, p_max::Int=2^15; pr::Int = 2)
  @assert nvars(parent(f)) == 2
  #requires f to be irred. over Q - which is not tested
  #requires f(x, 0) to be same degree and irred. - should be arranged by the absolute_bivariate_factorisation

  #f in Qxy
  Zx = Hecke.Globals.Zx
  f *= lcm([denominator(x) for x = coefficients(f)])
  ff = map_coeffs(ZZ, f)
  #TODO: 0 might not be a good evaluation point...
  #f needs to be irreducible over Q and g square-free
  g = evaluate(ff, [gen(Zx), Zx(0)])
  @assert degree(g) == degree(f, 1)
  
  d = degree(g)
  best_p = p_max
  pc = 0
  local p
  while true
    p_max = next_prime(p_max)
    gp = factor(g, GF(p_max, cached = false))
    if any(x->x>1, values(gp.fac))
      @vprint :AbsFact 1 "not squarefree mod $p_max\n"
      continue
    end
    e = lcm([degree(x) for x = keys(gp.fac)])
    if e < d
      d = e
      best_p = p_max
      pc = 0
    else
      pc += 1
    end
    
    if e == 1 || pc > 1.5 * degree(g)
      p = best_p
      @vprint :AbsFact 1 "using $best_p of degree $d\n"
      break
    end
  end

  R = RootCtx(f, p, d)
  R === nothing && return R, p_max

  @vprint :AbsFact 1 "need to seriously lift $(R.H.n) elements\n"
  R.all_R = typeof(R.R[1].R)[]
  R.RP = typeof(R.R[1].R)[]

  for i=1:pr
    more_precision(R)
  end

  return R, p_max
end

function more_precision(R::RootCtx)
  lift(R.H)
  S = base_ring(R.R[1].f)
  S.prec_max = 2*S.prec_max + 1
  T = parent(R.R[1].f)
  K = base_ring(S)
  for i=1:R.H.n
    R.R[i].f = map_coeffs(x->map_coeffs(K, x, parent = S), R.H.lf[i], parent = T)
    lift(R.R[i])
  end
end

"""
Internal use.
"""
function combination(RC::RootCtx)
  #R is a list of roots, ie. power series over F_q (finite field)
  root(RC, 1, 1)
  f = RC.f
  R = RC.all_R
  Ft = parent(R[1])
  t = gen(Ft)
  n = precision(R[1])
  @assert all(x->precision(x) == n, R)

  #ps = [[div(x^i % tn, td^i) for i = 1:n] for x = R] 
  
  F = base_ring(Ft)
  k = degree(F)

  p = characteristic(F)
  Fp = GF(p, cached = false)

  #the paper
  # https://www.math.univ-toulouse.fr/~cheze/facto_abs.m
  #seems to say that a combination works iff the sum of the
  # deg 2 terms vanish (for almost all choices of specialisations)
  #this would be even easier
  #also: it would make the lifting above trivial (precision 2)
  #deal: if monic in x of degree n and deg_y(coeff of x^(n-1)) = r,
  # then for the 1st power sum we get r as a degree bound. In the paper
  # r == 1... 
  # reasoning: sum of second highest terms of factor == second highest
  # of poly => bound
  # similar would be for other power sums - if I'd compute them.
  #all vanishing results in the paper do not depend on the assumption
  #D. Rupprecht / Journal of Symbolic Computation 37 (2004) 557–574
  # doi:10.1016/S0747-7171(02)00011-1
  # https://core.ac.uk/download/pdf/82425943.pdf
  #
  # This allows (should allow) to only use the 1st power sum (trace)
  # which makes denominators easier
  #
  #for non-monic: think about interaction with any_order
  #
  # instead of LLL use direct rref over GF(q)
  # for non-monics, the generalised equation order might be better than
  # trying to scale
  #
  j = 0
  nn = matrix(Fp, 0, length(R), [])

  d = degree(f, 2)+degree(f, 1)
  lc = leading_coefficient(f, 1)
  d += degree(lc, 2)

  ld = evaluate(map_coeffs(x->F(ZZ(x)), lc), [set_precision(Ft(0), n), set_precision(gen(Ft), n)])
  @assert precision(ld) >= n
  R = R .* ld

  pow = 1
  bad = 0
  stable = 0
  last_rank = length(R)
  while true
    j += 1
    while pow*d+j >= n
      @vprint :AbsFact 1 "need more precicsion: $n ($d, $pow, $j)\n"
      @vtime :AbsFact 2 more_precision(RC)
      n = precision(RC.R[1].R)
      if false && n > 170 #too small - but a safety valve
        error("too much n")
      end
    end
    root(RC, 1, 1)
    R = RC.all_R
    n = precision(R[1])
    ld = evaluate(map_coeffs(x->F(ZZ(x)), lc), [set_precision(Ft(0), n), set_precision(gen(Ft), n)])
    R = R .* ld
    @assert precision(R[1]) >= n
    
    mn = matrix([[Fp(coeff(coeff(x^pow, pow*d+j), lk)) for lk = 0:k-1] for x = R])
    
    if false && iszero(mn)
      @vprint :AbsFact 2 "found zero column, disgarding\n"
      bad += 1
      if bad > max(2, div(length(R), 2))
        pow += 1
        d += degree(lc, 2)
        @vprint :AbsFact 1 "increasing power to $pow\n"
        j = 0
        bad = 0
      end
      continue
    else
      @vprint :AbsFact 2 "found non zero column\n"
    end

    nn = vcat(nn, mn)

    ke = kernel(nn)
    @vprint :AbsFact 2 "current kernel dimension: $(ke[1])\n"
    if last_rank == ke[1] 
      bad += 1
      if bad > max(2, div(length(R), 2))
        pow += 1
        @vprint :AbsFact 2 "increasing power to $pow\n"
        j = 0
        bad = 0
        continue
      end
    else
      bad = 0
      stable = 0
      last_rank = ke[1]
    end
    if ke[1] == 0 || mod(length(R), ke[1]) != 0 || mod(total_degree(f), ke[1]) != 0
      continue
    end
    m = ke[2]
    z = m'*m
    if z != div(length(R), ke[1])
      @vprint :AbsFact 2 "not a equal size partition\n"
      continue
    end
    stable += 1
    if stable < max(5, degree(f, 1)/3)
      @vprint :AbsFact 2 "need confirmation...\n"
      continue
    end
    return m'
  end
end

function lift(R::PolyRing{S}, s::SeriesElem{S}) where {S}
  t = R()
  for x = 0:pol_length(s)
    setcoeff!(t, x, polcoeff(s, x))
  end
  return shift_left(t, valuation(s))
end

#TODO: possibly rename and export. This is used elsewhere
# Combine with the Hecke._meet into a POSet structure?
"""
Compute an array of arrays of indices (Int) indicating a partitioning of
the indices according to the values in `a`
"""
function block_system(a::Vector{T}) where {T}
  d = Dict{T, Array{Int, 1}}()
  for i=1:length(a)
    if haskey(d, a[i])
      push!(d[a[i]], i)
    else
      d[a[i]] = [i]
    end
  end
  return sort(collect(values(d)), lt = (a,b) -> isless(a[1], b[1])) 
end

#= bounds:
  f in Z[x,y], g, h in C[x,y]
  H(f) = max abs value coeff of f
  gh = f
  then 
  H(g) H(h) <= 2^(deg_x(f) + deg_y(g) - 2) ((deg_x(f)+1)(deg_y(f)+1))^(1/2) H(f)
=#
"""
Internal use.
"""
function field(RC::RootCtx, m::MatElem)
  R = RC.all_R
  P = RC.f


  bnd = numerator(maximum(abs(x) for x = coefficients(RC.f))) * fmpz(2)^(degree(RC.f, 1) + degree(RC.f, 2)-2) * Hecke.root(fmpz((degree(RC.f, 1)+1)*(degree(RC.f, 2)+1)), 2)
  #all coeffs should be bounded by bnd...  

  #we have roots, we need to combine roots for each row in m where the entry is pm 1
  #the coeffs then live is a number field, meaning that the elem sym functions or
  #the power sums will be needed
  #the field degree apears to be nrows(m)...

  #need primitive element, can use power sums up to #factors

  #we will ONLY find one factor, the others are Galois conjugate
  #the field here is not necc. normal

  #the leading_coeff of P needs to be monic.

  d_f = div(ncols(m), nrows(m))
  @assert ncols(m) == length(R)

  Ft = parent(R[1])
  F = base_ring(Ft)
  t = gen(Ft)
  d = precision(R[1])

  #TODO think, the bound might be too large...
  tf = divexact(total_degree(P), nrows(m)) + degree(P, 2)

  #TODO use Frobenius (again) to save on multiplications
  #TODO invest work in one factor only - need only powers of the roots involved there
  #     the other factor is then just a division away
  #     if complete orbits are combined, use the trace (pointwise) rather than powers
  @vprint :AbsFact 2 "combining: $([findall(x->!iszero(x), collect(m[i, :])) for i=1:nrows(m)])\n"
  k, mk = ResidueField(parent(R[1]))
  kt, t = PolynomialRing(k, cached = false)
  RR = map(mk, R)
  RP = [copy(RR)]
  for j=2:d_f
    push!(RP, RR .* RP[end])
  end
  @vtime :AbsFact 2 el = [[sum(RP[j][i] for i=1:ncols(m) if m[lj, i] != 0) for j=1:d_f] for lj=1:nrows(m)]

  #now find the degree where the coeffs actually live:
  k = 1
  for x = el
    for y = x
      d = degree(minpoly(y))
      k = lcm(d, k)
    end
  end

  @vprint :AbsFact 1 "target field has (local) degree $k\n"

  Qq = QadicField(characteristic(F), k, 1, cached = false)[1]
  Qqt = PolynomialRing(Qq, cached = false)[1]
  k, mk = ResidueField(Qq)
 
  phi = find_morphism(k, F) #avoids embed - which stores the info

  kt, t = PolynomialRing(k, cached = false)

  fl = [power_sums_to_polynomial(map(t->preimage(phi, t), x)) for x = el]
  fl = [map_coeffs(x->x, y, parent = kt) for y = fl]
  HH = HenselCtxFqRelSeries(RC.H.f, fl)
  while precision(coeff(HH.lf[1], 0)) < tf+2
    lift(HH)
  end

  kXY, (X, Y) = PolynomialRing(k, ["X", "Y"], cached = false)

  nl = []
  kS = PowerSeriesRing(k, tf+2, "s")[1]
  for x = HH.lf[1:HH.n]
    f = MPolyBuildCtx(kXY)
    lc = one(kt)
    cz = []
    z = x
    for i=0:degree(x)
      c = coeff(z, i)
      local fl, n, d = rational_reconstruction(c, parent = kt)
      @assert fl
      b = lcm(lc, d)
      n *= divexact(b, d)
      if b != lc
        cz = divexact(b, lc) .* cz
        lc = b
      end
      push!(cz, n)
    end
    for i=0:degree(z)
      c = cz[i+1]
      for j=0:degree(c)
        if !iszero(coeff(c, j))
          push_term!(f, coeff(c, j), [i,j])
        end
      end
    end
    push!(nl, finish(f))
  end
  @vprint :AbsFact 2 "now building the leading coeff...\n"
  lc = map(x->evaluate(leading_coefficient(x, 1), [0*t, t]), nl)

  for i = 1:length(lc)
    l = leading_coefficient(lc[i])
    lc[i] *= inv(l)
    nl[i] *= inv(l)
  end

  llc = coeff(P, 1)
  P *= inv(llc)
 
  _lc = evaluate(leading_coefficient(P, 1), [zero(Hecke.Globals.Qx), gen(Hecke.Globals.Qx)])
  _lc = Hecke.squarefree_part(_lc)
  local H, fa
  if !isone(_lc)
    ld = coprime_base(vcat(lc, [map_coeffs(k, _lc, parent = kt)]))
    if sum(map(degree, ld)) != degree(_lc) #TODO: this should(?) be caught earlier
      @vprint :AbsFact 1 "leading coeff not square-free mod p, bad prime\n"
      return nothing
    end

    fa = [[valuation(x, y) for y = ld] for x = lc]
    lc = _lc
    H = Hecke.HenselCtxQadic(map_coeffs(Qq, lc, parent = Qqt), ld)
  else
    @vprint :AbsFact 2 "is monic, no leading coefficient...\n"
    lc = _lc
    fa = []
  end

  el = nl

  @vprint :AbsFact 1 "locating primitive element...\n"
  #currently, we're in F_q[[t]], not Q_q[[t]], however, the primitivity
  #can already be decided over F_q as lifting can not enlarge the field

  #if no single coefficient is primtive, use block systems and sums of coeffs
  #to find a primitive one.
  all_bs = []
  pe_j = 0
  for i = 1:length(el[1])
    bs = block_system([coeff(x, i) for x = el])
    @vprint :AbsFact 3 "block system of coeff $i is $bs\n"
    @assert all(x->length(x) == length(bs[1]), bs)
    if length(bs[1]) == 1
      pe_j = i
      break
    end
    push!(all_bs, bs)
  end

  local pe, pow, used
  if pe_j == 0
    @vprint :AbsFact 2 "no single coefficient is primitive, having to to combinations\n"
    bs = [collect(1:length(el))]
    used = Int[]
    for i=1:length(el[1])
      cs = Hecke._meet(bs, all_bs[i])
      if length(cs) > length(bs)
        bs = cs
        push!(used, i)
      end
      if length(bs[1]) == 1
        break
      end
    end
    @vprint :AbsFact 2 "using coeffs $used to form primtive element\n"
    pow = 1
    while true
      pe = x -> (sum(coeff(x, t) for t = used)^pow)
      bs = block_system([pe(x) for x = el])
      if length(bs[1]) == 1
        @vprint :AbsFact 2 "using sum to the power $pow\n"
        break
      end
      pow += 1
    end
  else
    @vprint :AbsFact 2 "$(pe_j)-th coeff is primitive\n"
    pe = x -> coeff(x, pe_j)
    pow = 1
    used = [1]
  end

  @vprint :AbsFact 1 "hopefully $(length(el)) degree field\n"

  bnd = (length(el)*(length(used)*bnd))^(pow*length(el))
  @vprint :AbsFact 1 "power sums (coeffs of minpoly of field) should have at most $(clog(bnd, characteristic(F))) p-adic digits\n"

  #TODO: Think: Do we need to lift all n factors? In the end we're going
  #      to return el[1] and prod(el[2:n]) only.
  #      Problem: currently I need all conjugates of the coeffs, hence all
  #      the el's individually.

  SQq, _ = PowerSeriesRing(Qq, tf+2, "s", cached = false)
  SQqt, _ = PolynomialRing(SQq, cached = false)

  mc(f) = # PolyElem{SeriesElem{Fq}} -> PolyElem{SeriesElem{Qq}}
    map_coeffs(x->map_coeffs(y->setprecision(preimage(mk, y), 1), x, parent = SQq), f, parent = SQqt)
  

  HQ = HenselCtxFqRelSeries(HH.f, map(mc, HH.lf), map(mc, HH.cf), HH.n)

  QqXY, (X, Y) = PolynomialRing(Qq, 2, cached = false)

  pr = 1 
  while true
    pr *= 2
    if pr > 400 
      error("too bas")
    end
    @vprint :AbsFact 1  "using p-adic precision of $pr\n"

    setprecision!(Qq, pr+1)
    if length(fa) > 0
      H.f = map_coeffs(Qq, _lc, parent = Qqt)
      @vprint :AbsFact 2 "lifting leading coeff factorisation\n"
      @vtime :AbsFact 2 Hecke.lift(H, pr+1)
      fH = factor(H)
      lc = [prod(fH[i]^t[i] for i=1:length(t)) for t = fa]
    end

    @vprint :AbsFact 1 "lifting factors\n"
    global last_HQ = HQ
    @vtime :AbsFact 2 while precision(coeff(coeff(HQ.lf[1], 0), 0)) < pr+1
      lift_q(HQ)
    end

    if length(fa) > 0
      z = [lc[i](gen(SQq)) * HQ.lf[i] for i=1:HQ.n]
    else
      z = HQ.lf[1:HQ.n]
    end

    setprecision!(coeff(X, 1), pr+2)
    setprecision!(coeff(Y, 1), pr+2)
    el = [map_coeffs(q -> lift(Qqt, q)(Y), f)(X) for f = z]

#    # lift mod p^1 -> p^pr x^2+y^2+px+1 was bad I think
#    @vtime :AbsFact 1 ok, el = lift_prime_power(P*inv(coeff(P, 1)), el, [0], 1, pr)
#    ok || @vprint :AbsFact 1 "bad prime found, q-adic lifting failed\n"
#    ok || return nothing
#    @assert ok  # can fail but should fail for only finitely many p


    #to make things integral...
    fl = Qq(llc) .* el

    p = [coeff(sum(pe(x)^l for x = fl), 0) for l=1:length(el)]
    p = map(rational_reconstruction, p)

    if !all(x->x[1], p)
      @vprint :AbsFact 2 "reco failed (for poly), increasing p-adic precision\n"
      if 2*clog(bnd, prime(Qq)) < pr
        @vprint :AbsFact 2 "bad prime? too much precision and still no poly, so changing prime\n"
        return nothing
      end
      continue
    end

    p = [x[2]//x[3] for x = p]
    p = Hecke.power_sums_to_polynomial(p)
    if any(x->denominator(x)>1, coefficients(p))
      @vprint :AbsFact 2 "poly wrong, increasing p-adic precision\n"
      continue
    end


    k, a = number_field(p)

    @vprint :AbsFact 1  "using as number field: $k\n"

    m = matrix([[pe(x)^l for x = fl] for l=0:degree(k)-1])
    kx, x = PolynomialRing(k, "x", cached = false)
    kX, _ = PolynomialRing(k, ["X", "Y"], cached = false)
    B = MPolyBuildCtx(kX)
    for j=1:length(el[1])
      n = matrix([[coeff(x, j)] for x = fl])
      s = solve(m, n')
      @assert all(x->iszero(coeff(s[x, 1], 1)), 1:degree(k))
      s = [rational_reconstruction(coeff(s[i, 1], 0)) for i=1:degree(k)]
      if !all(x->x[1], s)
        break
      end
      push_term!(B, k([x[2]//x[3] for x = s]), exponent_vector(el[1], j))
    end
    q = finish(B)
    if length(q) < length(el[1])
      continue
    end
    b, r = divrem(map_coeffs(k, P, parent = kX), [q])
    if iszero(r)
      return q, b[1]
    end
    @vprint :AbsFact 2 "division failed, increasing precision\n"
  end
end

"""
Given an irreducible bivariate polynomial over `Q` compute the
absolute factorisation.

Returns two polynomials: 
 - the (absolutely) irreducible factor over the smallest number field
 - the co-factor

All the other factors would be conjugates of the first, hence representing
them exactly requires the splitting field to be computed.
"""
function absolute_bivariate_factorisation(f::fmpq_mpoly)
  d = degree(f, 1)
  R = parent(f)
  x, y = gens(R)

  lf = factor(f)
  if length(lf.fac) > 1 || any(x->x>1, values(lf.fac)) 
    error("poly must be irreducible over Q")
  end

  if degree(f, 2) < d
    @vprint :AbsFact 1 "swapping variables to have smaller degree\n"
    f = evaluate(f, [y, x])
    a, ca = absolute_bivariate_factorisation(f)
    S = parent(a)
    X, Y = gens(S)
    return evaluate(a, [Y, X]), evaluate(ca, [Y, X])
  end

  if degree(f, 2) == d && !isone(leading_coefficient(f, 1)) && isone(leading_coefficient(f, 2))
    @vprint :AbsFact 1 "swapping variables to be monic\n"
    f = evaluate(f, [y, x])
    a, ca = absolute_bivariate_factorisation(f)
    S = parent(a)
    X, Y = gens(S)
    return evaluate(a, [Y, X]), evaluate(ca, [Y, X])
  end

  Qt, t = PolynomialRing(QQ, cached = false)

  if degree(f, 1) == 0 #constant in
    k, a = number_field(evaluate(f, [Qt(0), t]), cached = false)
    kXY, (X, Y) = PolynomialRing(k, ["X", "Y"], cached = false)
    b = Y-a
    return b, divexact(map_coeffs(k, f, parent = kXY), b)
  end

  s =-1 
  while true
    s += 1
    @vprint :AbsFact 1 "substitution to $s\n"
    z = evaluate(f, [t, Qt(s)])
    if degree(z) == d && issquarefree(z)
      break
    end
  end
  ff = evaluate(f, [x, y+s])
  d = lcm([denominator(x) for x = coefficients(ff)])
  ff *= d
  @assert all(x->isone(denominator(x)), coefficients(ff))
  gg = ff

  p = 2^24
  local aa
  while true
    @vtime :AbsFact 1 r, p = roots(gg, p)
    if r === nothing
      continue
    end
    @vtime :AbsFact 1 z = combination(r)
    if nrows(z) == 1
      return f, one(parent(f))
    end
   
    @vtime :AbsFact 1 aa = field(r, z)
    aa !== nothing && break
  end
  a, b = aa
  S = parent(a)
  X, Y = gens(S)
  a = evaluate(a, [X, Y-s])
  b = evaluate(b, [X, Y-s])
  return a, b
end

# From Dan, the lifting in Qq[x,y]

function map_down(Rp, a, mKp :: Map, pr::Int)
    M = MPolyBuildCtx(Rp)
    pk = prime(base_ring(a))^pr
    for (c, v) in zip(coefficients(a), exponent_vectors(a))
        @assert valuation(c) >= pr
        q = divexact(c, pk)  #should be a shift
        push_term!(M, mKp(q), v)
    end
    return finish(M)
end

function map_up(R, a, mKp :: Map, pr::Int)
    Rp = parent(a)
    Kp = base_ring(Rp)
    M = MPolyBuildCtx(R)
    pk = prime(base_ring(R))^pr

    for (c, v) in zip(coefficients(a), exponent_vectors(a))
        d = preimage(mKp, c)
        push_term!(M, d*pk, v)
    end
    return finish(M)
end

#=
    supposed to have a = prod(fac) mod p^kstart
    furthermore, the fac's are supposed to be pairwise coprime univariate in
        Fq[gen(1)] when evaluated at gen(2) = alphas[1], ... gen(n) = alphas[n-1]

    try to lift to a factorization mod p^kstop  (or maybe its mod p^(kstop+1))
=#
function lift_prime_power(
    a::fmpq_mpoly,
    fac::Vector{Generic.MPoly{qadic}},
    alphas::Vector,
    kstart::Int,
    kstop::Int)

    if kstop <= kstart
        return
    end

    r = length(fac)
    R = parent(fac[1])
    n = nvars(R)
    ZZ = base_ring(R)
    Kp, mKp = ResidueField(ZZ)
    Rp, x = PolynomialRing(Kp, n, cached = false)

    minorvars = [i for i in 2:n]
    degs = [degree(a, i) for i in 2:n]

    md = [map_down(Rp, f, mKp, 0) for f in fac]
    ok, I = Hecke.AbstractAlgebra.MPolyFactor.pfracinit(md, 1, minorvars, alphas)
    @assert ok  # evaluation of fac's should be pairwise coprime

    a = map_coeffs(ZZ, a, parent = parent(fac[1]))

    for l in kstart:kstop
        error = a - prod(fac)

        for c in coefficients(error)
          if valuation(c) < l
            throw(AssertionError("factorization is not correct mod p^$l"))
          end
        end

        if iszero(error)
            break
        end
        t = map_down(Rp, error, mKp, l)
        ok, deltas = Hecke.AbstractAlgebra.MPolyFactor.pfrac(I, t, degs, true)
        if !ok
            return false, fac
        end
        for i in 1:r
            fac[i] += map_up(R, deltas[i], mKp, l)
        end
    end
    return true, fac
end


function example(k::AnticNumberField, d::Int, nt::Int, c::AbstractRange=-10:10)
  kx, (x, y) = PolynomialRing(k, 2, cached = false)
  f = kx()
  for i=1:nt
    f += rand(k, c)*x^rand(0:d)*y^rand(0:d)
  end
  return norm(f)
end

function Hecke.isirreducible(a::fmpq_mpoly)
  af = factor(a)
  return !(length(af.fac) > 1 || any(x->x>1, values(af.fac)))
end

# f is bivariate. return f(xvar, 0) where xvar is in the multivar ring R
function _yzero_image(R, f, xvar::Int)
  z = MPolyBuildCtx(R)
  zexps = zeros(Int, nvars(R))
  for (c, exps) in zip(coefficients(f), exponent_vectors(f))
    @assert length(exps) == 2
    if exps[2] == 0
      zexps[xvar] = exps[1]
      push_term!(z, base_ring(R)(c), zexps)
    end
  end
  return finish(z)
end

function absolute_multivariate_factorisation(a::fmpq_mpoly)

  Qxy, (x, y) = PolynomialRing(QQ, ["x", "y"], cached = false)

  R = parent(a)
  K = base_ring(R)

  alphas = zeros(ZZ, nvars(R))
  bi_sub = zeros(Qxy, nvars(R))

  @assert length(a) > 0

  unit = coeff(a, 1)
  if !isone(unit)
    a *= inv(unit)
  end

  degs = degrees(a)
  vars = Int[]    # variables that actually appear
  for v in 1:nvars(R)
    if degs[v] > 0
      push!(vars, v)
    end
  end

  if isempty(vars)
    @assert isone(a)
    return (unit, [])
  end

  sort!(vars, by = (v -> degs[v]), alg=InsertionSort)

  if degs[1] == 1
    # linear is irreducible by assumption
    return (unit, [a])
  elseif length(vars) == 1
    uni_sub = zeros(Hecke.Globals.Qx, nvars(R))
    uni_sub[vars[1]] = gen(Hecke.Globals.Qx)
    K1, alpha = number_field(evaluate(a, uni_sub), cached = false)
    R1 = PolynomialRing(K1, map(string, symbols(R)), ordering = ordering(R), cached = false)[1]
    A = map_coeffs(K1, a, parent = R1)
    x = gen(R1, vars[1])
    return (unit, [x - alpha, divexact(A, x - alpha)])
  elseif length(vars) == 2
    bi_sub[vars[1]] = x
    bi_sub[vars[2]] = y
    f, fbar = absolute_bivariate_factorisation(evaluate(a, bi_sub))
    K1 = base_ring(f)
    R1 = PolynomialRing(K1, map(string, symbols(R)), ordering = ordering(R), cached = false)[1]
    revsub = [gen(R1, vars[1]), gen(R1, vars[2])]
    return (unit, [evaluate(f, revsub), evaluate(fbar, revsub)])
  end

  maindeg = degree(a, vars[1])
  mainvar = vars[1]
  minorvars = vars[2:end]

  lcaf = factor_squarefree(Hecke.AbstractAlgebra.MPolyFactor.get_lc(a, mainvar))

  lcc_fails_remaining = 3
  bits = 1

@label next_alpha

  if bits > 1000
    error("too many iterations")
  end

  bi_sub[mainvar] = x
  for i in 1:length(minorvars)
    alphas[i] = rand_bits(ZZ, rand(1:bits))
    bi_sub[minorvars[i]] = Qxy(alphas[i])
  end

  uni_a = evaluate(a, bi_sub)

  if degree(uni_a, mainvar) != maindeg || !isirreducible(uni_a)
    bits += 1
    @goto next_alpha
  end

  bi_sub_degree = 1

  if bi_sub_degree > 1 + bits/8
    bits += 2
    @goto next_alpha
  end

  # The substitution down to univariate is good and produces an irreducible.
  # Therefore, whatever bivariate is generated, the primitive part will be
  # irreducible if the y = 0 image agrees with the univariate substitution.
  bi_sub[mainvar] = x
  for i in 1:length(minorvars)
    bi_sub[minorvars[i]] = Qxy(alphas[i])
    for j in 1:bi_sub_degree
      bi_sub[minorvars[i]] += Qxy(rand_bits(ZZ, rand(1:bits)))*y^j
    end
  end

  bi_a = evaluate(a, bi_sub)
  bi_a = Hecke.AbstractAlgebra.MPolyFactor.primitive_part(bi_a, 1)
  if degree(bi_a, 2) < 2
    if degree(bi_a, 2) == 1
      # a is abs irreducible
      return (unit, [a])
    end
    @goto next_alpha
  end

  f, fbar = absolute_bivariate_factorisation(bi_a)

  K1 = base_ring(f)
  R1 = PolynomialRing(K1, map(string, symbols(R)), ordering = ordering(R), cached = false)[1]
  f = _yzero_image(R1, f, mainvar)
  fbar = _yzero_image(R1, fbar, mainvar)

  if degree(f, mainvar) < 1 || degree(fbar, mainvar) < 1
    # a is abs irreducible
    return (unit, [a])
  end

  # map the stuff in Q to the number field
  A = map_coeffs(K1, a, parent = R1)
  lcAf = Fac{elem_type(R1)}()
  lcAf.unit = map_coeffs(K1, lcaf.unit, parent = R1)
  for i in lcaf.fac
    lcAf[map_coeffs(K1, i[1], parent = R1)] = i[2]
  end

  ok, divs = Hecke.AbstractAlgebra.MPolyFactor.lcc_kaltofen(
                       lcAf, A, mainvar, maindeg, minorvars, alphas, [f, fbar])
  if !ok
    lcc_fails_remaining -= 1
    if lcc_fails_remaining >= 0
      @goto next_alpha
    end
  end

  ok, fac = Hecke.AbstractAlgebra.MPolyFactor.hlift_with_lcc(
                                A, [f, fbar], divs, mainvar, minorvars, alphas)
  if !ok
    @goto next_alpha
  end

  @assert length(fac) == 2
  return (unit, map(Hecke.AbstractAlgebra.MPolyFactor.make_monic, fac))
end

function factor_absolute(a::fmpq_mpoly)
  result = Any[]
  @vprint :AbsFact 1 "factoring over QQ first...\n"
  @vtime :AbsFact 2 fa = factor(a)
  push!(result, fa.unit)
  for (p, e) in fa
    @vtime :AbsFact 2 unit, fp = absolute_multivariate_factorisation(p)
    result[1] *= unit
    push!(result, fp => e)
  end
  return result
end

end

using .MPolyFact
export factor_absolute

#= revised strategy until I actually understand s.th. better
 - "shift" to make f(o, y) square-free
 - find a prime s.th. f(0, y) is square-free with a small degree splitting field
 - compute roots in F_q[[x]] (finite field!)
   TODO: first factor f in F_p[[x]], then compute roots of the factors
         should be faster (see above, more comments)
 - use combine to find the combinations giving the proper factor
 - find the (small) field the factor lives over
 - lift the factor in the q-adic field
 - find the number field

 TODO:
  bounds on the precisions (poly prec)

example:

Qxy, (y, x) = PolynomialRing(QQ, ["y", "x"])
include("/home/fieker/Downloads/n60s3.m"); 
  #from  https://www.math.univ-toulouse.fr/~cheze/n60s3.m

  r = absolute_bivariate_factorisation(P)

  from the Rupprecht paper, but the 3rd is boring (probably wrong)

  y^9+3*x^5*y^6+5*x^4*y^5+3*x^10*y^3-3*x^6*y^3+5*x^9*y^2+x^15

  y^5*x^5+9*x^8*y^4-6*x^14*y^2-18*x^10*y^6-18*x^6*y^10+x^20+5*x^16*y^4+10*x^12*y^8+10*x^8*y^12+5*y^16*x^4+9*y^8*x^4-6*y^14*x^2+y^20

  -125685*x+151959*x^8+917230*x^6+8717398*y^5*x^5+5108544*x^8*y^4-1564434*x^5+7744756*x^5*y^6+306683*x^3*y^6+413268*x^4*y^6+9081976*x^6*y^6+1317780*x^6*y^5+76745*x^4*y^5-15797040*x^7*y^5+99348*x^3*y^5+4106178*x^6*y^4+2010995*x^4*y^4-11264228*x^7*y^4-12465712*x^5*y^4+40908*x^2*y^4+404227*x^3*y^4-9204694*x^7*y^3-49266*x^2*y^3-3500343*x^4*y^3+1512264*x^3*y^3+6405504*x^8*y^3+9879662*x^6*y^3-3821606*x^5*y^3-592704*x^9*y^3-8503779*x^5*y^2-783216*x^9*y^2+10608275*x^6*y^2+574917*x^2*y^2-10143*x*y^2+5943180*x^4*y^2-3295022*x^3*y^2+3452692*x^8*y^2-6432756*x^7*y^2-344988*x^9*y+67473*x*y+2548458*x^4*y-2646351*x^7*y+1059606*x^8*y-3698541*x^5*y-491400*x^2*y+430155*x^3*y+4011984*x^6*y+1530912*x^4+617526
=#


