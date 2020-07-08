module MPolyFact

using Hecke
import Hecke: Nemo

Hecke.example("mfactor.jl")

function Hecke.lead(f::fmpq_mpoly)
  return first(coeffs(f))
end

function Hecke.ismonic(f::fmpq_mpoly)
  return isone(lead(f))
end

function (k::Nemo.GaloisField)(a::fmpq)
  return k(numerator(a))//k(denominator(a))
end

function (R::FmpzMPolyRing)(f::fmpq_mpoly)
  return map_coeffs(ZZ, f, parent = R)
end

function Hecke.representation_matrix(a::ResElem{<:PolyElem})
  R = parent(a)
  S = base_ring(base_ring(R))
  n = degree(modulus(R))
  m = zero_matrix(S, n, n)
  for i=0:n-1
    m[1, i+1] = coeff(a.data, i)
  end
  for j=2:n
    a *= gen(R)
    for i=0:n-1
      m[j, i+1] = coeff(a.data, i)
    end
  end
  return m
end

function Hecke.preimage(phi::Nemo.FinFieldMorphism, x::FinFieldElem)
  return preimage_map(phi)(x)
end

function Nemo.canonical_unit(a::SeriesElem) 
  iszero(a) && return one(parent(a))
  v = valuation(a)
  v == 0 && return a
  v > 0 && return shift_right(a, v)
  return shift_left(a, -v)
end

function Base.gcd(a::T, b::T) where {T <: SeriesElem}
  iszero(a) && iszero(b) && return a
  iszero(a) && return gen(parent(a))^valuation(b)
  iszero(b) && return gen(parent(a))^valuation(a)
  return gen(parent(a))^min(valuation(a), valuation(b))
end

function Base.lcm(a::T, b::T) where {T <: SeriesElem}
  iszero(a) && iszero(b) && return a
  iszero(a) && return a
  iszero(b) && return b
  return gen(parent(a))^max(valuation(a), valuation(b))
end


Hecke.inv(phi :: Nemo.FinFieldMorphism) = preimage_map(phi)

#= AbsFact: strategy
 f in Q[x,y] = Q[x][y], not necc. monic, irre. over Q

 find evaluation x <- x+ly s.th. g = f(0, y) is square-free
 find p s.th g mod p is square-free and such that the lcm of the factors
   is small
 compute the roots up to a bound B over the F_q splitting field
   as power series
 compute the coeffs. of f (as elements in Q[x]) as power series
=#
mutable struct RootCtx
  f::fmpq_mpoly
  R::Array{<:SeriesElem, 1}
  o::Array{<:SeriesElem, 1} #1/f'(r)
  RP::Array{Array{<:SeriesElem , 1}, 1}
  t::Int

  function RootCtx(f::fmpq_mpoly, r::Array{<:RingElem, 1}, t::Int = 0)
    @assert nvars(parent(f)) == 2

    s = parent(r[1])

    S = PowerSeriesRing(s, 16, "s")[1]
    l = new()
    l.f = f
    l.R = [S(x) for x = r]
    for i=1:length(r)
      set_prec!(l.R[i], 1)
    end
    g = map_coeffs(parent(r[1]), f)
    tt = gen(S) - t
    set_prec!(tt, 1)
    l.o = [inv(evaluate(derivative(g, 1), [x, tt])) for x = l.R]
    l.t = t

    l.RP = [[one(S) for x = r], l.R]
    return l
  end
end

function root(R::RootCtx, i::Int, j::Int)
  if length(R.RP) > j 
    return R.RP[j+1][i]
  end
  while length(R.RP) <= j+1
    push!(R.RP, R.RP[2] .* R.RP[end])
  end

  return R.RP[j+1][i]
end

function set_prec(a::SeriesElem, i::Int)
  b = deepcopy(a)
  set_prec!(b, i)
  return b
end

function newton_lift!(R::RootCtx)

  S = parent(R.R[1])
  t = gen(S) - R.t

  for i = 1:length(R.R)
    a = R.R[i]
    o = R.o[i]
    set_prec!(a, 2*precision(a))
    set_prec!(o, precision(a))
  end
  set_prec!(t, precision(R.R[1]))
  #delete powers...

  for i=1:length(R.R)
    a = R.R[i]
    o = R.o[i]
    ev_f = zero(S)
    ev_fs = zero(S)

    @show precision(R.R[1])
    if precision(R.R[1]) > 2
      for j=1:length(R.f)
        e = exponent_vector(R.f, j)
        c = coeff(R.f, j)
        if e[1] > 0
          ev_fs += S(c)*e[1]*root(R, i, e[1] - 1) * t^e[2]
        end
      end

      @assert evaluate(derivative(R.f, 1), [R.R[i], t]) == ev_fs
      o = R.o[i] = o*(2-o*ev_fs)
    end

    for j=1:length(R.f)
      e = exponent_vector(R.f, j)
      c = coeff(R.f, j)
      _r = root(R, i, e[1])
      @assert root(R, i, 1)^e[1] == _r
      ev_f += S(c)*t^e[2] * root(R, i, e[1])
    end
    R.R[i] = a - ev_f*o
    @assert evaluate(R.f, [a, t]) == ev_f
  end
  R.RP = [[one(S) for x = R.R], R.R]
end


function Hecke.roots(f::fmpq_mpoly; p::Int=2^25, pr::Int = 5)
  @assert nvars(parent(f)) == 2

  #f in Qxy
  Zx = Hecke.Globals.Zx
  ff = map_coeffs(ZZ, f)
  #TODO: 0 might not be a good evaluation point...
  #f needs to be irreducible over Q and g square-free
  @show g = evaluate(ff, [gen(Zx), Zx(0)])
  local d
  while true
    p = next_prime(p)
    gp = factor(g, GF(p))
    d = lcm([degree(x) for x = keys(gp.fac)])
    if d < degree(g)/2
      @show "using $p of degree $d"
      break
    end
  end
  F = FiniteField(p, d)[1]
  @assert !iszero(discriminant(map_coeffs(F, g)))
  @time r = Set(roots(g, F))
  #use action of Frobenius to lift less roots!!!

  #all roots with the same minpoly can be combined...

  Ft, t = PowerSeriesRing(F, 2^pr, "t")

  R = []
  while length(r) > 0
    s = pop!(r)
    o = Ft(inv(evaluate(derivative(g), s)))
    S = Ft(s)
    set_prec!(S, 1)
    set_prec!(t, 2)
    set_prec!(o, 1)
    @assert s == coeff(S, 0)
    @show "lift"
    @time for i = 1:pr
      set_prec!(S, 2*precision(S))
      set_prec!(t, 1+precision(S))
      set_prec!(o, precision(S))
      _g = evaluate(ff, [S, t])
      S = (S - _g*o)
      o = (o*(2-o*evaluate(derivative(ff, 1), [S, t])))
    end
    @assert s == coeff(S, 0)
    push!(R, S)
    T = deepcopy(S)
    @time for i = 2:degree(minpoly(s))
      for j=0:T.length-1
        setcoeff!(T, j, frobenius(coeff(T, j)))
      end
      push!(R, deepcopy(T))
      @assert coeff(T, 0) in r
      pop!(r, coeff(T, 0))
    end
  end
  return R
end

function combination(R::Array, d::Int)
  #R is a lost of roots, ie. polynomials over a q-Adic field
  #d a bound on the degree in "x" of the factors
  Ft = parent(R[1])
  t = gen(Ft)
  n = precision(R[1])
  @assert all(x->precision(x) == n, R)

  #ps = [[div(x^i % tn, td^i) for i = 1:n] for x = R] 
  
  F = base_ring(Ft)
  k = degree(F)

  if !true
    p = prime(F)
    ll = precision(F)
  else
    p = characteristic(F)
    ll = 1
  end

  m = identity_matrix(FlintZZ, length(R)) 
  i = 1
  j = 0
  #the paper
  # https://www.math.univ-toulouse.fr/~cheze/facto_abs.m
  #seems to say that a combination works iff the sum of the
  # deg 2 terms vanish (for almost all choices of specialisations)
  #this would be even easier
  #also: it would make the lifting above trivial (precision 2)
  #
  # instead of LLL use direct rref over GF(q)
  # for non-monics, the generalised equation order might be better than
  # trying to scale
  #
  while true
    @assert n> d*i
    @show nn = matrix([[fmpz(coeff(coeff(shift_right(x^i, d*i), j), lk)) for lk = 0:k-1] for x = R])'
    nn = m[:, 1:length(R)]*nn
    m = [m nn; zero_matrix(FlintZZ, ncols(nn), ncols(m)) p^ll*identity_matrix(FlintZZ, ncols(nn))]
    @time r, m = lll_with_removal(m, fmpz(length(R))^2)
    @show m = m[1:r, :]
    if all(i->sum(m[i,j]^2 for j = 1:length(R)) <= length(R)^2, 1:r)
      if all(ll -> sum([shift_right(R[l]^(i+1), d*(i+1)) for l=1:length(R) if m[ll, l] != 0]) == 0, 1:r)
        return m[:, 1:length(R)]
      else
        i += 1
        j = 0
      end
    end
    j += 1
    if j > n-d*i
      i += 1
      j = 0
    end
  end

  return m[:, 1:length(R)]
end

function field(P::fmpq_mpoly, R::Array, m::fmpz_mat)
  #we have roots, we need to combine roots for each row in m where the entry is pm 1
  #the coeffs then live is a number field, meaning that the elem sym functions or
  #the power sums will be needed
  #the field degree apears to be nrows(m)...

  #need primitive element, can use power sums up to #factors

  #we will ONLY find one factor, the others are galois conjugate
  #the field here is not necc. normal

  d_f = div(ncols(m), nrows(m))
  @assert ncols(m) == length(R)

  Ft = parent(R[1])
  F = base_ring(Ft)
  t = gen(Ft)
  d = precision(R[1])

  Qq = QadicField(characteristic(F), nrows(m), 10)
  k, mk = ResidueField(Qq)
  F.overfields = Dict{Int64,Array{Nemo.FinFieldMorphism,1}}()
  F.subfields = Dict{Int64,Array{Nemo.FinFieldMorphism,1}}()
  k.overfields = Dict{Int64,Array{Nemo.FinFieldMorphism,1}}()
  k.subfields = Dict{Int64,Array{Nemo.FinFieldMorphism,1}}()
  phi = embed(k, F)


  #TODO given that all powers are used, build them up properly
  @time el = [[sum(R[i]^j for i=1:ncols(m) if m[lj, i] != 0) for j=1:d_f] for lj=1:nrows(m)]

  kt, t = PolynomialRing(k)
  kXY, (X, Y) = PolynomialRing(k, ["X", "Y"])

  el = [Hecke.power_sums_to_polynomial([kt([preimage(phi, coeff(x, i)) for i=0:d_f])(Y) for x = y])(X) for y = el]

  #assuming one coeff is primtive...
  j = 1
  local s
  while true
    s = Set([(coeff(x, j)) for x = el])
    if length(s) == length(el)
      break
    end
    j += 1
  end

  @show "$j is primitive"


  QqXY, _ = PolynomialRing(Qq, 2)

  el = [map_coeffs(x->preimage(mk, x), y, parent = QqXY) for y = el]

  pr = 0
  while true
    @show pr += 5
    el  = Main.MFactor.lift_prime_power(P, el, [0], [degree(P, 2)], pr)

    F = Qq
    
    pk = prime(F)^precision(F)
    p = [coeff(sum(coeff(x, j)^l for x = el), 0) for l=1:length(el)]
    p = map(lift, p)
    @show p = map(x->rational_reconstruction(x, pk), p)
    if !all(x->x[1], p)
      continue
    end
    @show p = [x[2]//x[3] for x = p]

    k, a = number_field(Hecke.power_sums_to_polynomial(p))

    @show "using", k

    m = matrix([[(coeff(x, j)^l) for x = el] for l=0:degree(k)-1])
    kx, x = k["x"]
    P = elem_type(kx)[]


    kX, (X, Y) = PolynomialRing(k, ["X", "Y"])
    B = MPolyBuildCtx(kX)
    for j=1:length(el[1])
      n = matrix([[coeff(x, j)] for x = el])
      s = solve(m, n')
      @assert all(x->iszero(coeff(s[x, 1], 1)), 1:degree(k))
      s = [rational_reconstruction(lift(coeff(s[i, 1], 0))% pk, pk) for i=1:degree(k)]
      if !all(x->x[1], s)
        break
      end
      push_term!(B, k([x[2]//x[3] for x = s]), exponent_vector(el[1], j))
    end
    q = finish(B)
    if length(q) < length(el[1])
      continue
    end
    return q
  end
end

function absolute_factorisation(f::fmpq_mpoly)
  p = next_prime(2^30)
  d = degree(f, 1)
  r = roots(f, p, 2) #compute up to 16 in x
  @show z = combination(r, 16, d+2)
  if nrows(z) == 1
    return f
  end
  return field(r, z, d)
end
  
end

#= revised strategy until I actually understand s.th. better
 - assumming f is monic in y, irreducible over Q and f(0) is squarefree
 - find a prime s.th. f(0, y) is square-free with a small degree splitting field
 - compute roots in F_q[[x]] (finite field!)
 - use combine to find the combinations giving the proper factor
 - find the (small) field the factor lives over
 - lift the factor in the q-adic field
 - find the number field

 TODO:
  bounds on the precisions (poly prec)
  non-monic: use "any_order", the generizlised equation order to produce
    integral power sums
  find good evaluation points
  more variables
  more rings

example:

Qxy, (y, x) = PolynomialRing(QQ, ["y", "x"])
include("/home/fieker/Downloads/n60s3.m"); 
  #from  https://www.math.univ-toulouse.fr/~cheze/n60s3.m

  r = MpolyFact(P, pr = 7)
  c = MpolyFact.combination(r, 21)
  q = MpolyFact.field(P, R, c)

=#
