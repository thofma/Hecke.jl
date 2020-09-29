module MPolyFact

using Hecke
import Hecke: Nemo, @vprint, @hassert, @vtime

add_verbose_scope(:AbsFact)
add_assert_scope(:AbsFact)

Hecke.example("mfactor.jl")

function Hecke.norm(f::MPolyElem{nf_elem})
  Kx = parent(f)
  K = base_ring(Kx)
  n = nvars(Kx)
  Qx, x = PolynomialRing(QQ, [String(x) for x= symbols(Kx)])
  Qxy, y = PolynomialRing(Qx, "y")
  gg = [MPolyBuildCtx(Qx) for i=1:degree(K)]
  for (c, e) = zip(coeffs(f), exponent_vectors(f))
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

function Hecke.lead(f::fmpq_mpoly)
  return first(coeffs(f))
end

function Hecke.ismonic(f::fmpq_mpoly)
  return isone(lead(f))
end

#dodgy
function (k::Nemo.GaloisField)(a::fmpq)
  return k(numerator(a))//k(denominator(a))
end
function (k::Nemo.FqNmodFiniteField)(a::fmpq)
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

#should be in AA/ Nemo
function Nemo.canonical_unit(a::SeriesElem) 
  iszero(a) && return one(parent(a))
  v = valuation(a)
  v == 0 && return a
  v > 0 && return shift_right(a, v)
  return shift_left(a, -v)
end

#TODO: this is for rings, not for fields, maybe different types?
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
  RP::Array{Array{<:SeriesElem , 1}, 1}  #root powers
  t::Int

  all_R::Array{<:SeriesElem, 1} #all roots - if different from R

  function RootCtx(f::fmpq_mpoly, r::Array{<:RingElem, 1}, t::Int = 0)
    @assert nvars(parent(f)) == 2

    s = parent(r[1])

    S = PowerSeriesRing(s, 2, "s")[1]
    l = new()
    l.f = f
    l.R = [S(x) for x = r]
    for i=1:length(r)
      set_precision!(l.R[i], 1)
    end
    g = map_coeffs(parent(r[1]), f)
    tt = gen(S) - t
    set_precision!(tt, 1)
    l.o = [inv(evaluate(derivative(g, 1), [x, tt])) for x = l.R]
    l.t = t

    l.RP = [[one(S) for x = r], l.R]
    return l
  end
end

function root(R::RootCtx, i::Int, j::Int)
  if precision(R.R[1]) != precision(R.RP[1][1])
    o = one(parent(R.R[1]))
    R.RP = [[set_precision(o, precision(R.R[1])) for x = R.R], copy(R.R)]
  end
  if length(R.RP) > j 
#    @assert R.RP[j+1][i] == R.R[i]^j
    return (R.RP[j+1][i])
  end
  while length(R.RP) <= j+1
    push!(R.RP, R.RP[2] .* R.RP[end])
  end

  s = R.RP[j+1][i]
#  @assert s == R.R[i]^j
  return (s)
end

#TODO: in Nemo, rename to setprecision
#      fix/report series add for different length
function set_precision(a::SeriesElem, i::Int)
  b = deepcopy(a)
  set_precision!(b, i)
  return b
end

function newton_lift!(R::RootCtx)

  #TODO: given that f might be sparse, do NOT compute all powers 
  #      of the roots, only those needed - and this in an "optimized"
  #      way
  S = parent(R.R[1])
  T = base_ring(S)
#  set_precision!(S, 2*precision(S))
  S.prec_max = 2*precision(R.R[1])+1

  t = gen(S) - R.t

  for i = 1:length(R.R)
    a = R.R[i]
    o = R.o[i]
    set_precision!(a, 2*precision(a))
    set_precision!(o, precision(a))
  end
  set_precision!(t, precision(R.R[1])+1)

  for i=1:length(R.R)
    a = R.R[i]
    o = R.o[i]
    ev_f = zero(S)
    ev_fs = zero(S)

    if precision(R.R[1]) > 2
      for j=1:length(R.f)
        e = exponent_vector(R.f, j)
        c = coeff(R.f, j)
        if e[1] > 0
          ev_fs += S(T(c*e[1]))*root(R, i, e[1] - 1) * t^e[2]
        end
      end

      o = R.o[i] = o*(2-o*ev_fs)
    end

    for j=1:length(R.f)
      e = exponent_vector(R.f, j)
      c = coeff(R.f, j)
      ev_f += S(T(c))*t^e[2] * root(R, i, e[1])
    end
    R.R[i] = a - ev_f*o
#    @assert evaluate(R.f, [a, t]) == ev_f
  end
end


function roots(f::fmpq_mpoly; p::Int=2^25, pr::Int = 2)
  @assert nvars(parent(f)) == 2
  #requires f to be irred. over Q - which is not tested
  #requires f(x, 0) to be same degree and irred. - should be arranged by the absolute_bivariate_factorisation

  #f in Qxy
  Zx = Hecke.Globals.Zx
  ff = map_coeffs(ZZ, f)
  #TODO: 0 might not be a good evaluation point...
  #f needs to be irreducible over Q and g square-free
  g = evaluate(ff, [gen(Zx), Zx(0)])
  @assert degree(g) == degree(f, 1)
  
  d = degree(g)
  best_p = p
  pc = 0
  while true
    p = next_prime(p)
    gp = factor(g, GF(p))
    if any(x->x>1, values(gp.fac))
      @vprint :AbsFact 1 "not squarefree mod $p\n"
      continue
    end
    e = lcm([degree(x) for x = keys(gp.fac)])
    if e < d
      d = e
      best_p = p
      pc = 0
    else
      pc += 1
    end
    
    if e == 1 || pc > div(degree(g), 2)
      @vprint :AbsFact 1 "using $best_p of degree $d\n"
      p = best_p
      break
    end
  end
  F = FiniteField(p, d)[1]
  @hassert :AbsFact 1 !iszero(discriminant(map_coeffs(F, g)))
  @vtime :AbsFact 2 r = Set(Hecke.roots(g, F))
  @assert length(r) == degree(g)
  #use action of Frobenius to lift less roots!!!
  rr = Tuple{eltype(r), Int}[]
  while length(r) > 0
    s = pop!(r)
    d = degree(minpoly(s))
    push!(rr, (s, d))
    for i=1:d-1
      s = frobenius(s)
      pop!(r, s)
    end
  end
  @vprint :AbsFact 1 "need to seriously lift $(length(rr)) elements\n"

  R = RootCtx(f, [x[1] for x = rr])
  for i=1:pr
    newton_lift!(R)
  end

  @vprint :AbsFact 1 "now Frobenius action...\n"

  S = typeof(R.R[1])[]
  all_o = []
  for i=1:length(rr)
    push!(S, R.R[i])
    o = [length(S)]
    T = S[end]
    for i=1:rr[i][2]-1
      T = deepcopy(T)
      for j=0:T.length-1
        setcoeff!(T, j, frobenius(coeff(T, j)))
      end
      push!(S, T)
      push!(o, length(S))
    end
    push!(all_o, o)
  end
  @vprint :AbsFact 2 "orbits: $all_o\n"
  R.all_R = S
  return R
end

function more_precision(R::RootCtx)
  @vtime :AbsFact 2 newton_lift!(R)
  S = typeof(R.R[1])[]
  for r = R.R
    push!(S, r)
    s = coeff(r, 0)
    @assert !iszero(s)
    @assert valuation(r) == 0
    d = degree(minpoly(s))
    T = r
    for i=1:d-1
      T = deepcopy(T)
      for j=0:T.length-1
        setcoeff!(T, j, frobenius(coeff(T, j)))
      end
      push!(S, T)
    end
  end
  R.all_R = S
end

#check with Nemo/ Dan if there are better solutions

function Hecke.leading_coefficient(f::MPolyElem, i::Int)
  g = MPolyBuildCtx(parent(f))
  d = degree(f, i)
  for (c, e) = zip(coeffs(f), exponent_vectors(f))
    if e[i] == d
      e[i] = 0
      push_term!(g, c, e)
    end
  end
  return finish(g)
end

function make_monic(f::MPolyElem, i::Int)
  d = degree(f, i)
  cf = [MPolyBuildCtx(parent(f)) for j=0:d]
  for (c, e) = zip(coeffs(f), exponent_vectors(f))
    a = e[i]
    e[i] = 0
    push_term!(cf[a+1], c, e)
  end
  df = map(finish, cf)
  for j=0:d-1
    df[j+1] *= df[d+1]^(d-1-j)
  end
  df[d+1] = one(parent(f))
  return sum(gen(parent(f), i)^j*df[j+1] for j=0:d)
end

function Hecke.content(f::MPolyElem, i::Int)
  d = degree(f, i)
  cf = [MPolyBuildCtx(parent(f)) for j=0:d]
  for (c, e) = zip(coeffs(f), exponent_vectors(f))
    a = e[i]
    e[i] = 0
    push_term!(cf[a+1], c, e)
  end
  df = map(finish, cf)
  return reduce(gcd, df)
end

function Hecke.coefficients(f::MPolyElem, i::Int)
  d = degree(f, i)
  cf = [MPolyBuildCtx(parent(f)) for j=0:d]
  for (c, e) = zip(coeffs(f), exponent_vectors(f))
    a = e[i]
    e[i] = 0
    push_term!(cf[a+1], c, e)
  end
  return map(finish, cf)
end



function combination(RC::RootCtx)
  #R is a list of roots, ie. power series over F_q (finite field)
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
  Fp = GF(p)

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
  last_rank = length(R)
  while true
    j += 1
    while pow*d+j >= n
      @vprint :AbsFact 1 "need more precicsion: $n ($d, $pow, $j)\n"
      more_precision(RC)
      R = RC.all_R
      n = precision(R[1])
      if false && n > 570 #too small - but a safety valve
        error("too much n")
      end
      set_precision!(ld, n)
      R = R .* ld
      @assert precision(R[1]) >= n
    end
    
    mn = matrix([[Fp(coeff(coeff(x^pow, pow*d+j), lk)) for lk = 0:k-1] for x = R])
    
    if false && iszero(mn)
      @vprint :AbsFact 2 "found zero column, disgarding\n"
      bad += 1
      if bad > max(2, div(length(R), 2))
        pow += 1
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
    @vprint :AbsFact 1 "current kernel dimension: $(ke[1])\n"
    if last_rank == ke[1]
      bad += 1
      if bad > max(2, div(length(R), 2))
        pow += 1
        @vprint :AbsFact 1 "increasing power to $pow\n"
        j = 0
        bad = 0
        continue
      end
    else
      bad = 0
      last_rank = ke[1]
    end
    if ke[1] == 0 || mod(length(R), ke[1]) != 0
      continue
    end
    m = ke[2]
    z = m'*m
    if z != div(length(R), ke[1])
      @vprint :AbsFact 1 "not a equal size partition\n"
      continue
    end
    return m'
  end
end

function field(RC::RootCtx, m::MatElem)
  R = RC.all_R
  P = RC.f

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

  tf = divexact(total_degree(P), nrows(m))

  #TODO given that all powers are used, build them up properly
  #TODO use Frobenius (again) to save on multiplications
  #TODO invest work in one factor only - need only powers of the roots involved there
  #     the other factor is then just a division away
  #     if complete orbits are combined, use the trace (pointwise) rather than powers
  @vprint :AbsFact 2 "combining: $([findall(x->!iszero(x), collect(m[i, :])) for i=1:nrows(m)])\n"
  RP = [[set_precision(x, tf+2) for x = R]]
  @vtime :AbsFact 2 for j=2:d_f
    push!(RP, RP[1] .* RP[end])
  end
  @vtime :AbsFact 2 el = [[sum(RP[j][i] for i=1:ncols(m) if m[lj, i] != 0) for j=1:d_f] for lj=1:nrows(m)]

  #now find the degree where the coeffs actually live:
  k = 1
  for x = el
    for y = x
      d = degree(minpoly(coeff(y, valuation(y))))
      k = max(d, k)
    end
  end

  @vprint :AbsFact 1 "target field has (local) degree $k\n"

  Qq = QadicField(characteristic(F), k, 10)
  k, mk = ResidueField(Qq)
  #TODO: debug and fix in Nemo
  F.overfields = Dict{Int64,Array{Nemo.FinFieldMorphism,1}}()
  F.subfields = Dict{Int64,Array{Nemo.FinFieldMorphism,1}}()
  k.overfields = Dict{Int64,Array{Nemo.FinFieldMorphism,1}}()
  k.subfields = Dict{Int64,Array{Nemo.FinFieldMorphism,1}}()
  
  phi = embed(k, F)

  kt, t = PolynomialRing(k)
  kXY, (X, Y) = PolynomialRing(k, ["X", "Y"])

  el = [Hecke.power_sums_to_polynomial([kt([preimage(phi, coeff(x, i)) for i=0:precision(x)])(Y) for x = y])(X) for y = el]
  #assuming one coeff is primtive...
  #the first coeff has to be primitive as the other could be re-computed by lifting, hence cannot
  #enlarge the field
  j = 1
  local s
  while true
    s = Set([(coeff(x, j)) for x = el])
    if length(s) == length(el)
      break
    end
    j += 1
  end

  @vprint :AbsFact 2 "$j-th coeff is primitive\n"
  @vprint :AbsFact 1 "hopefully $(length(el)) degree field\n"

  QqXY, _ = PolynomialRing(Qq, 2)

  el = [map_coeffs(x->preimage(mk, x), y, parent = QqXY) for y = el]

  #at this point, hopefully, prod(el) = P/lead

  pr = 10 
  while true
    pr *= 2
    @vprint :AbsFact 1  "using p-adic precision of $pr\n"
    setprecision!(Qq, pr+1)
    el = [map_coeffs(x->setprecision(x, pr), y, parent = QqXY) for y = el]

    #TODO: allow continue to lift
    @vtime :AbsFact 1 el = Main.MFactor.lift_prime_power(P, el, [0], [degree(P, 2)], pr)

    pk = prime(Qq)^pr
    p = [coeff(sum(coeff(x, j)^l for x = el), 0) for l=1:length(el)]
    p = map(lift, p)
    p = map(x->QQ(Hecke.mod_sym(x, pk)), p)
#    @show p = map(x->rational_reconstruction(x, pk), p) #all arranged to be integral, so farey not used here
#    if !all(x->x[1], p)
#      @show "reco failed"
#      continue
#    end
#    p = [x[2]//x[3] for x = p]

    pp = Hecke.power_sums_to_polynomial(p)
    if any(x->!isone(denominator(x)), coefficients(pp))
      @vprint :AbsFact 2 "poly not integral, increasing p-adic precision\n"
      continue
    end
    k, a = number_field(Hecke.power_sums_to_polynomial(p))

    @vprint :AbsFact 1  "using as number field: $k\n"

    m = matrix([[(coeff(x, j)^l) for x = el] for l=0:degree(k)-1])
    kx, x = k["x"]
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

function absolute_bivariate_factorisation(f::fmpq_mpoly)
  d = degree(f, 1)
  R = parent(f)
  x, y = gens(R)

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
  gg = make_monic(ff, 1)
  r = roots(gg)
  z = combination(r)
  if nrows(z) == 1
    return f, one(parent(f))
  end
  a = field(r, z)
  S = parent(a)
  X, Y = gens(S)
  l = leading_coefficient(ff, 1)
  if !isone(l)
    ll = evaluate(l, [S(0), Y])
    a = evaluate(a, [X*ll, Y])
    a = divexact(a, ll^(degree(a, 1)-1))
    a = divexact(a, content(a, 1))
  end
  a = evaluate(a, [X, Y-s])
  return a, divexact(map_coeffs(base_ring(a), f, parent =parent(a)), a)
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
    integral power sums -> make_monic
  find good evaluation points
  more variables
  more rings

example:

Qxy, (y, x) = PolynomialRing(QQ, ["y", "x"])
include("/home/fieker/Downloads/n60s3.m"); 
  #from  https://www.math.univ-toulouse.fr/~cheze/n60s3.m

  r = MPolyFact.roots(P)
  c = MPolyFact.combination(r)
  q = MPolyFact.field(r, c)

  from the Rupprecht paper, but the 3rd is boring (probably wrong)

  y^9+3*x^5*y^6+5*x^4*y^5+3*x^10*y^3-3*x^6*y^3+5*x^9*y^2+x^15

  y^5*x^5+9*x^8*y^4-6*x^14*y^2-18*x^10*y^6-18*x^6*y^10+x^20+5*x^16*y^4+10*x^12*y^8+10*x^8*y^12+5*y^16*x^4+9*y^8*x^4-6*y^14*x^2+y^20

  -125685*x+151959*x^8+917230*x^6+8717398*y^5*x^5+5108544*x^8*y^4-1564434*x^5+7744756*x^5*y^6+306683*x^3*y^6+413268*x^4*y^6+9081976*x^6*y^6+1317780*x^6*y^5+76745*x^4*y^5-15797040*x^7*y^5+99348*x^3*y^5+4106178*x^6*y^4+2010995*x^4*y^4-11264228*x^7*y^4-12465712*x^5*y^4+40908*x^2*y^4+404227*x^3*y^4-9204694*x^7*y^3-49266*x^2*y^3-3500343*x^4*y^3+1512264*x^3*y^3+6405504*x^8*y^3+9879662*x^6*y^3-3821606*x^5*y^3-592704*x^9*y^3-8503779*x^5*y^2-783216*x^9*y^2+10608275*x^6*y^2+574917*x^2*y^2-10143*x*y^2+5943180*x^4*y^2-3295022*x^3*y^2+3452692*x^8*y^2-6432756*x^7*y^2-344988*x^9*y+67473*x*y+2548458*x^4*y-2646351*x^7*y+1059606*x^8*y-3698541*x^5*y-491400*x^2*y+430155*x^3*y+4011984*x^6*y+1530912*x^4+617526
=#
