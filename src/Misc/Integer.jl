################################################################################
#
#  Integer functions
#
################################################################################

is_commutative(::ZZRing) = true

@doc raw"""
    modord(a::ZZRingElem, m::ZZRingElem) -> Int
    modord(a::Integer, m::Integer)

  The multiplicative order of a modulo $m$ (not a good algorithm).
"""
function modord(a::ZZRingElem, m::ZZRingElem)
  gcd(a, m) != 1 && error("1st argument not a unit")
  i = 1
  b = a % m
  while b != 1
    i += 1
    b = b * a % m
  end
  return i
end

function modord(a::Integer, m::Integer)
  gcd(a, m) != 1 && error("1st argument not a unit")
  i = 1
  b = a % m
  while b != 1
    i += 1
    b = b * a % m
  end
  return i
end

function _fmpz_preinvn_struct_clear_fn(z::fmpz_preinvn_struct)
  ccall((:fmpz_preinvn_clear, libflint), Nothing, (Ref{fmpz_preinvn_struct},), z)
end

function fdiv_qr_with_preinvn!(q::ZZRingElem, r::ZZRingElem, g::ZZRingElem, h::ZZRingElem, hinv::fmpz_preinvn_struct)
  ccall((:fmpz_fdiv_qr_preinvn, libflint), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{fmpz_preinvn_struct}), q, r, g, h, hinv)
end

################################################################################
#
#  sunit group
#
################################################################################

mutable struct MapSUnitGrpZFacElem <: Map{FinGenAbGroup,FacElemMon{QQField},HeckeMap,MapSUnitGrpZFacElem}
  header::MapHeader{FinGenAbGroup,FacElemMon{QQField}}
  idl::Vector{ZZRingElem}

  function MapSUnitGrpZFacElem()
    return new()
  end
end

function show(io::IO, mC::MapSUnitGrpZFacElem)
  println(io, "SUnits (in factored form) map of $(codomain(mC)) for $(mC.idl)")
end

mutable struct MapSUnitGrpZ <: Map{FinGenAbGroup,QQField,HeckeMap,MapSUnitGrpZ}
  header::MapHeader{FinGenAbGroup,QQField}
  idl::Vector{ZZRingElem}

  function MapSUnitGrpZ()
    return new()
  end
end

function show(io::IO, mC::MapSUnitGrpZ)
  println(io, "SUnits map of $(codomain(mC)) for $(mC.idl)")
end

@doc raw"""
    sunit_group_fac_elem(S::Vector{ZZRingElem}) -> FinGenAbGroup, Map
    sunit_group_fac_elem(S::Vector{Integer}) -> FinGenAbGroup, Map

The $S$-unit group of $Z$ supported at $S$: the group of
rational numbers divisible only by primes in $S$.
The second return value is the map mapping group elements to rationals
in factored form or rationals back to group elements.
"""
function sunit_group_fac_elem(S::Vector{T}) where {T<:Integer}
  return sunit_group_fac_elem(ZZRingElem[x for x = S])
end

function sunit_group_fac_elem(S::Vector{ZZRingElem})
  S = coprime_base(S)  #TODO: for S-units use factor???
  G = abelian_group(vcat(ZZRingElem[2], ZZRingElem[0 for i = S]))
  S = vcat(ZZRingElem[-1], S)

  mp = MapSUnitGrpZFacElem()
  mp.idl = S

  Sq = QQFieldElem[x for x = S]

  function dexp(a::FinGenAbGroupElem)
    return FacElem(Sq, ZZRingElem[a.coeff[1, i] for i = 1:length(S)])
  end

  mp.header = MapHeader(G, FacElemMon(FlintQQ), dexp)

  return G, mp
end

function preimage(f::MapSUnitGrpZFacElem, a::ZZRingElem)
  g = Int[a >= 0 ? 0 : 1]
  S = f.idl
  g = vcat(g, Int[valuation(a, x) for x = S[2:end]])
  return domain(f)(g)
end

function preimage(f::MapSUnitGrpZFacElem, a::Integer)
  return preimage(f, ZZRingElem(a))
end

function preimage(f::MapSUnitGrpZFacElem, a::Rational)
  return preimage(f, QQFieldElem(a))
end

function preimage(f::MapSUnitGrpZFacElem, a::QQFieldElem)
  return preimage(f, numerator(a)) - preimage(f, denominator(a))
end

function preimage(f::MapSUnitGrpZFacElem, a::FacElem)
  return sum(FinGenAbGroupElem[e * preimage(f, k) for (k, e) = a.fac])
end

@doc raw"""
    sunit_group(S::Vector{ZZRingElem}) -> FinGenAbGroup, Map
    sunit_group(S::Vector{Integer}) -> FinGenAbGroup, Map

The $S$-unit group of $Z$ supported at $S$: the group of
rational numbers divisible only by primes in $S$.
The second return value is the map mapping group elements to rationals
or rationals back to group elements.
"""
function sunit_group(S::Vector{T}) where {T<:Integer}
  return sunit_group(ZZRingElem[x for x = S])
end

function sunit_group(S::Vector{ZZRingElem})
  u, mu = sunit_group_fac_elem(S)

  mp = MapSUnitGrpZ()
  mp.idl = S

  function dexp(a::FinGenAbGroupElem)
    return evaluate(image(mu, a))
  end

  mp.header = MapHeader(u, FlintQQ, dexp, y->preimage(mu, y))

  return u, mp
end

@doc raw"""
    is_prime_power(n::ZZRingElem) -> Bool
    is_prime_power(n::Integer) -> Bool

Tests if $n$ is the exact power of a prime number.
"""
function is_prime_power(n::ZZRingElem)
  e, p = is_power(n)
  return is_prime(p)
end

function is_prime_power(n::Integer)
  return is_prime_power(ZZRingElem(n))
end

################################################################################
# random and factor
################################################################################

factor(a...; b...) = Nemo.factor(a...; b...)

factor(a::Integer) = factor(ZZRingElem(a))

mutable struct flint_rand_ctx_t
  a::Ptr{Nothing}
  function flint_rand_ctx_t()
    return new()
  end
end

function show(io::IO, A::flint_rand_ctx_t)
  println(io, "Flint random state")
end

function flint_rand_state()
  A = flint_rand_ctx_t()
  A.a = ccall((:flint_rand_alloc, libflint), Ptr{Nothing}, (Int,), 1)
  ccall((:flint_randinit, libflint), Nothing, (Ptr{Nothing},), A.a)

  function clean_rand_state(A::flint_rand_ctx_t)
    ccall((:flint_randclear, libflint), Nothing, (Ptr{Nothing},), A.a)
    ccall((:flint_rand_free, libflint), Nothing, (Ptr{Nothing},), A.a)
    nothing
  end
  finalizer(clean_rand_state, A)
  return A
end

global flint_rand_ctx

function ecm(a::ZZRingElem, B1::UInt, B2::UInt, ncrv::UInt, rnd=flint_rand_ctx)
  f = ZZRingElem()
  r = ccall((:fmpz_factor_ecm, libflint), Int32, (Ref{ZZRingElem}, UInt, UInt, UInt, Ptr{Nothing}, Ref{ZZRingElem}), f, ncrv, B1, B2, rnd.a, a)
  return r, f
end

function ecm(a::ZZRingElem, B1::Int, B2::Int, ncrv::Int, rnd=flint_rand_ctx)
  return ecm(a, UInt(B1), UInt(B2), UInt(ncrv), rnd)
end

#data from http://www.mersennewiki.org/index.php/Elliptic_Curve_Method
const B1 = [2, 11, 50, 250, 1000, 3000, 11000, 43000, 110000, 260000, 850000, 2900000];
const nC = [25, 90, 300, 700, 1800, 5100, 10600, 19300, 49000, 124000, 210000, 340000];

function ecm(a::ZZRingElem, max_digits::Int=div(ndigits(a), 3), rnd=flint_rand_ctx)
  n = ndigits(a, 10)
  B1s = 15

  i = 1
  s = max(div(max_digits - 10, 5), 1)
  #i = s = max(i, s)
  while i <= s
    e, f = ecm(a, B1[i] * 1000, B1[i] * 1000 * 100, nC[i], rnd)
    if e != 0
      return (e, f)
    end
    i += 1
    if i > length(B1)
      return (e, f)
    end
  end
  return (Int32(0), a)
end

function factor_trial_range(N::ZZRingElem, start::Int=0, np::Int=10^5)
  F = Nemo.fmpz_factor()
  ccall((:fmpz_factor_trial_range, libflint), Nothing, (Ref{Nemo.fmpz_factor}, Ref{ZZRingElem}, UInt, UInt), F, N, start, np)
  res = Dict{ZZRingElem,Int}()
  for i in 1:F.num
    z = ZZRingElem()
    ccall((:fmpz_factor_get_fmpz, libflint), Nothing,
      (Ref{ZZRingElem}, Ref{Nemo.fmpz_factor}, Int), z, F, i - 1)
    res[z] = unsafe_load(F.exp, i)
  end
  return res, canonical_unit(N)
end

const big_primes = ZZRingElem[]

function factor(N::ZZRingElem)
  if iszero(N)
    throw(ArgumentError("Argument is not non-zero"))
  end
  N_in = N
  global big_primes
  r, c = factor_trial_range(N)
  for (p, v) = r
    N = divexact(N, p^v)
  end
  if is_unit(N)
    @assert N == c
    return Nemo.Fac(c, r)
  end
  N *= c
  @assert N > 0

  for p = big_primes
    v, N = remove(N, p)
    if v > 0
      @assert !haskey(r, p)
      r[p] = v
    end
  end
  factor_insert!(r, N)
  for p = keys(r)
    if nbits(p) > 60 && !(p in big_primes)
      push!(big_primes, p)
    end
  end
  return Nemo.Fac(c, r)
end

function factor_insert!(r::Dict{ZZRingElem,Int}, N::ZZRingElem, scale::Int=1)
  #assumes N to be positive
  #        no small divisors
  #        no big_primes
  if isone(N)
    return r
  end
  fac, N = is_power(N)
  if fac > 1
    return factor_insert!(r, N, fac)
  end
  if is_prime(N)
    @assert !haskey(r, N)
    r[N] = scale
    return r
  end
  if ndigits(N) < 60
    s = Nemo.factor(N) #MPQS
    for (p, k) in s
      if haskey(r, p)
        r[p] += k * scale
      else
        r[p] = k * scale
      end
    end
    return r
  end

  e, f = ecm(N)
  if e == 0
    s = Nemo.factor(N)
    for (p, k) in s
      if haskey(r, p)
        r[p] += k * scale
      else
        r[p] = k * scale
      end
    end
    return r
  end
  cp = coprime_base([N, f])
  for i = cp
    factor_insert!(r, i, scale * valuation(N, i))
  end
  return r
end

#TODO: problem(s)
# Nemo.factor = mpqs is hopeless if > n digits, but asymptotically and practically
# faster than ecm.
# ecm is much better if there are "small" factors.
# p-1 and p+1 methods are missing
# so probably
# if n is small enough -> Nemo
# if n is too large: ecm
# otherwise
#  need ecm to find small factors
# then recurse...

function _factors_trial_division(n::ZZRingElem, np::Int=10^5)
  res, u = factor_trial_range(n, 0, np)
  factors = ZZRingElem[]
  for (p, v) in res
    push!(factors, p)
    n = divexact(n, p^v)
  end
  return factors, n

end

@doc raw"""
    Divisors{T}

An iterator for the divisors of a given object.
Create using
    `Divisors(A, power::Int = 1)`
where $A$ is either a FacElem or a direct element. Power can be used
to restrict to objects $B$ s.th. $B$^power still divides $A$, e.g.
    `Divisors(12, powers = 2)`
will produce square divisors.

For rings where this makes sense, i.e. where the unit group is finite,
```units = true``` can be passed in to also take into account
the units.
"""
mutable struct Divisors{T}
  n::T
  lf::MSet{T}
  s#::Iterator
  f::Function
  U::FinGenAbGroup
  function Divisors(a::T; units::Bool=false, power::Int=1) where {T}
    r = new{T}()
    r.n = a
    r.lf = MSet{T}()
    for (p, k) = factor(a).fac
      k = div(k, power)
      if k > 0
        push!(r.lf, T(p), k)
      end
    end
    r.f = x -> length(x) == 0 ? one(parent(a)) : prod(x)
    r.s = subsets(r.lf)
    if units
      U, mU = unit_group(parent(a))
      r.U = U
      g = r.f
      r.f = x -> mU(x[1]) * g(x[2])
      r.s = Base.Iterators.ProductIterator((U, r.s))
    end
    return r
  end
  function Divisors(a::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}; units::Bool=false, power::Int=1)
    r = new{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
    r.n = a
    r.lf = MSet{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
    for (p, k) = factor(a)
      k = div(k, power)
      if k > 0
        push!(r.lf, p, k)
      end
    end
    r.f = x -> length(x) == 0 ? one(parent(a)) : prod(x)
    r.s = subsets(r.lf)
    return r
  end
  function Divisors(a::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}; units::Bool=false, power::Int=1)
    r = new{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
    r.n = evaluate(a)
    r.lf = MSet{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
    for (p, k) = factor(a)
      k = div(k, power)
      if k > 0
        push!(r.lf, p, k)
      end
    end
    r.f = x -> length(x) == 0 ? one(parent(a)) : prod(x)
    r.s = subsets(r.lf)
    return r
  end

  function Divisors(a::FacElem{ZZRingElem,ZZRing}; units::Bool=false, power::Int=1)
    r = new{ZZRingElem}()
    r.n = evaluate(a)
    r.lf = MSet{ZZRingElem}()
    for (p, k) = factor(a).fac
      k = div(k, power)
      if k > 0
        push!(r.lf, p, k)
      end
    end
    r.f = x -> length(x) == 0 ? one(parent(r.n)) : prod(x)
    r.s = subsets(r.lf)
    if units
      U, mU = unit_group(parent(a))
      r.U = U
      g = r.f
      r.f = x -> mU(x[1]) * g(x[2])
      r.s = Base.Iterators.ProductIterator((U, r.s))
    end
    return r
  end
  function Divisors(a::Fac{ZZRingElem}; units::Bool=false, power::Int=1)
    return Divisors(FacElem(a), units=units, power=power)
  end
end

Base.IteratorSize(::Divisors) = Base.HasLength()
Base.length(D::Divisors) = length(D.s)
Base.eltype(::Type{Divisors{T}}) where {T} = T

function Base.iterate(D::Divisors{T}) where {T}
  x = iterate(D.s)
  if x === nothing
    return x
  end
  return D.f(x[1])::T, x[2]
end

function Base.iterate(D::Divisors{T}, i) where {T}
  x = iterate(D.s, i)
  if x === nothing
    return x
  end
  return D.f(x[1])::T, x[2]
end

function Base.show(io::IO, D::Divisors)
  print(io, "Divisors of $(D.n) = $(D.lf)")
  if isdefined(D, :U)
    print(io, " times $(D.U)")
  end
end

@doc raw"""
    unit_group(::ZZRing) -> FinGenAbGroup, Map

The unit group of $\mathbb{Z}$, i.e. $C_2$ and the map translating between the group and $\mathbb{Z}$.
"""
function unit_group(::ZZRing)
  G = abelian_group([2])
  exp = function (z::FinGenAbGroupElem)
    return isodd(z[1]) ? ZZRingElem(-1) : ZZRingElem(1)
  end
  log = function (z::ZZRingElem)
    return z == -1 ? G[1] : G[0]
  end
  return G, MapFromFunc(G, FlintZZ, exp, log)
end

@doc raw"""
    unit_group(::Integers{T}) -> FinGenAbGroup, Map

The unit group of , i.e. $C_2$ and the map translating between the group and $\mathbb{Z}$.
"""
function unit_group(R::AbstractAlgebra.Integers{T}) where {T}
  G = abelian_group([2])
  exp = function (z::FinGenAbGroupElem)
    return isodd(z[1]) ? T(-1) : T(1)
  end
  log = function (z::T)
    return z == -1 ? G[1] : G[0]
  end
  return G, MapFromFunc(G, R, exp, log)
end

#Nemo.fpField = zzModRingElem?
# PolyRing

#basically from
#http://people.math.gatech.edu/~ecroot/shparlinski_final.pdf
#Contini, Croot, Shparlinski: Complexity of inverting the Euler function
@doc raw"""
    euler_phi_inv_fac_elem(n::ZZRingElem)

The inverse of the Euler totient functions: find all $x$ s.th. $phi(x) = n$
holds. The elements are returned in factored form.
"""
function euler_phi_inv_fac_elem(n::ZZRingElem)
  lp = ZZRingElem[]
  for d = Divisors(n)
    if is_prime(d + 1)
      push!(lp, d + 1)
    end
  end
  #  println("possible primes: ", lp)

  E = Tuple{ZZRingElem,Vector{Tuple{ZZRingElem,Int}}}[]
  res = FacElem{ZZRingElem,ZZRing}[]
  for p = lp
    v = valuation(n, p)
    for i = 0:v
      push!(E, ((p - 1) * p^i, [(p, i + 1)]))
      if E[end][1] == n
        push!(res, FacElem(Dict(E[end][2])))
      end
    end
  end
  while true
    F = []
    for e = E
      nn = divexact(n, e[1])
      x = e[2]
      pm = x[end][1]
      for p = lp
        if p <= pm
          continue
        end
        if nn % (p - 1) == 0
          v = valuation(nn, p)
          for i = 0:v
            push!(F, (e[1] * (p - 1) * p^i, vcat(e[2], [(p, i + 1)])))
            if F[end][1] == n
              push!(res, FacElem(Dict(F[end][2])))
            end
          end
        end
      end
    end
    if length(F) == 0
      return res
    end
    E = F
  end
end

#phi(n) < n and n/phi(n) can be arbitrarily large.
#whowever, prod(p/(p-1) for p = PrimesSet(1, 1000000)) < 25
#so for 32-bit input, the output is also small
function euler_phi_inv(n::Int)
  @assert n > 0
  T = Int
  if nbits(n) > 55 #to be safe...
    return T[T(x) for x = euler_phi_inv(ZZ(n))]
  end
  lp = T[]
  for d = Divisors(n)
    if is_prime(d + 1)
      push!(lp, d + 1)
    end
  end
  #  println("possible primes: ", lp)

  E = Tuple{T,T,T}[]
  res = T[]
  for p = lp
    v = valuation(n, p)
    push!(E, (p - 1, p, p))
    if n == p - 1
      push!(res, p)
    end
    for i = 1:v
      push!(E, (p * E[end][1], p * E[end][2], p))
      if E[end][1] == n
        push!(res, prod(E[end][2]))
      end
    end
  end
  while true
    F = Tuple{T,T,T}[]
    for e = E
      nn = divexact(n, e[1])
      pm = e[3]
      for p = lp
        if p <= pm
          continue
        end
        if nn % (p - 1) == 0
          v = valuation(nn, p)
          push!(F, (e[1] * (p - 1), e[2] * p, p))
          if F[end][1] == n
            push!(res, F[end][2])
          end
          for i = 1:v
            push!(F, (p * F[end][1], p * F[end][2], p))
            if F[end][1] == n
              push!(res, F[end][2])
            end
          end
        end
      end
    end
    if length(F) == 0
      return res
    end
    E = F
  end
end




function euler_phi(x::FacElem{ZZRingElem,ZZRing})
  x = factor(x)
  return prod((p - 1) * p^(v - 1) for (p, v) = x.fac)
end

function carmichael_lambda(x::Fac{ZZRingElem})
  two = ZZRingElem(2)
  if haskey(x.fac, two)
    y = deepcopy(x.fac)
    v = y[two]
    delete!(y, two)
    if v == 2
      c = two
    elseif v > 2
      c = two^(v - 2)
    else
      c = ZZRingElem(1)
    end
  else
    c = ZZRingElem(1)
    y = x.fac
  end
  if length(y) == 0
    return c
  end
  return lcm(c, reduce(lcm, (p - 1) * p^(v - 1) for (p, v) = y))
end

function carmichael_lambda(x::ZZRingElem)
  v, x = remove(x, ZZRingElem(2))
  if isone(x)
    c = ZZRingElem(1)
  else
    x = factor(x)
    c = reduce(lcm, (p - 1) * p^(v - 1) for (p, v) = x.fac)
  end
  if v == 2
    c = lcm(2, c)
  elseif v > 2
    c = lcm(ZZRingElem(2)^(v - 2), c)
  end
  return c
end

function carmichael_lambda(x::FacElem{ZZRingElem,ZZRing})
  x = factor(x)
  return carmichael_lambda(x)
end

function carmichael_lambda(n::T) where {T<:Integer}
  return T(carmichael_lambda(ZZRingElem(n)))
end

@doc raw"""
    euler_phi_inv(n::Integer) -> Vector{ZZRingElem}

The inverse of the Euler totient functions: find all $x$ s.th. $phi(x) = n$
holds.
"""
function euler_phi_inv(n::Integer)
  return euler_phi_inv(ZZRingElem(n))
end

@doc raw"""
    euler_phi_inv(n::ZZRingElem) -> Vector{ZZRingElem}

The inverse of the Euler totient functions: find all $x$ s.th. $phi(x) = n$
holds.
"""
function euler_phi_inv(n::ZZRingElem)
  return [evaluate(x) for x = euler_phi_inv_fac_elem(n)]
end

function factor(a::FacElem{ZZRingElem,ZZRing})
  b = simplify(a)
  c = Dict{ZZRingElem,Int}()
  s = ZZRingElem(1)
  for (p, k) = b.fac
    lp = factor(p)
    s *= lp.unit
    for (q, w) = lp.fac
      c[q] = w * k
    end
  end
  l = Fac{ZZRingElem}()
  l.fac = c
  l.unit = s
  return l
end

function FacElem(a::Fac{ZZRingElem})
  f = FacElem(a.fac)
  if a.unit == -1
    return a.unit * f
  end
  return f
end

#= for torsion units:

   [maximum([maximum(vcat([ZZRingElem(-1)], euler_phi_inv(x))) for x = Divisors(ZZRingElem(n))]) for n = 1:250]

=#

radical(a::ZZRingElem) = prod(keys(factor(a).fac))
function radical(a::T) where {T<:Integer}
  return T(radical(ZZRingElem(a)))
end

function quo(::ZZRing, a::ZZRingElem)
  R, f = residue_ring(FlintZZ, a)
  return R, f
end

function quo(::ZZRing, a::Integer)
  R, f = residue_ring(FlintZZ, a)
  return R, f
end


^(a::AbsNumFieldOrderIdeal, n::IntegerUnion) = Nemo._generic_power(a, n)

#^(a::RelNumFieldOrderIdeal, n::IntegerUnion)  = Nemo._generic_power(a, n)


################################################################################
#
#  Prime numbers up to
#
################################################################################

@doc raw"""
    primes_up_to(n::Int) -> Vector{Int}

Returns a vector containing all the prime numbers up to $n$.
"""
function primes_up_to(n::Int)
  list = trues(n)
  list[1] = false
  i = 2
  s = 4
  while s <= n
    list[s] = false
    s += 2
  end
  i = 3
  b = sqrt(n)
  while i <= b
    if list[i]
      j = 3 * i
      s = 2 * i
      while j <= n
        list[j] = false
        j += s
      end
    end
    i += 1
  end
  return findall(list)
end

################################################################################
#
#  Squarefree numbers up to
#
################################################################################

@doc raw"""
    squarefree_up_to(n::Int) -> Vector{Int}

Returns a vector containing all the squarefree numbers up to $n$.
"""
function squarefree_up_to(n::Int; coprime_to::Vector{ZZRingElem}=ZZRingElem[], prime_base::Vector{ZZRingElem}=ZZRingElem[])

  @assert isempty(coprime_to) || isempty(prime_base)
  if !isempty(prime_base)
    listi = Int[1]
    for x in prime_base
      if x > n
        continue
      end
      el = Int(x)
      to_add = Int[]
      for i = 1:length(listi)
        eln = el * listi[i]
        if eln <= n
          push!(to_add, eln)
        else
          break
        end
      end
      append!(listi, to_add)
      sort!(listi)
    end
    return listi
  end
  list = trues(n)
  for x in coprime_to
    if x > n
      continue
    end
    t = Int(x)
    while t <= n
      list[t] = false
      t += Int(x)
    end
  end
  i = 2
  b = isqrt(n)
  lp = primes_up_to(b)
  for i = 1:length(lp)
    p2 = lp[i]^2
    ind = p2
    while ind <= n
      list[ind] = false
      ind += p2
    end
  end
  return findall(list)
end

################################################################################
#
#  Squarefree part
#
################################################################################

@doc raw"""
    squarefree_part(a::ZZRingElem) -> ZZRingElem

Returns the squarefee part $b$ of $a$, which is the smallest (absolute value)
integer $b$ such that $a/b$ is positive and squarefree.
"""
function squarefree_part(a::ZZRingElem)
  f = factor(a)
  s = sign(a)
  for (p, e) in f
    if isodd(e)
      s = s * p
    end
  end
  return s
end

################################################################################
#
#  Factorization of a rational
#
################################################################################

@doc raw"""
    factor(::ZZRing, a::QQFieldElem) -> Fac{ZZRingElem}

Factor the rational number $a$ into prime numbers.
"""
function factor(::ZZRing, a::QQFieldElem)
  fn = factor(numerator(a))
  fd = factor(denominator(a))
  for (p, e) = fd
    fn.fac[p] = -e
  end
  return fn
end

################################################################################
#
#   Support
#
################################################################################

function support(d::ZZRingElem)
  return collect(keys(factor(d).fac))
end

function support(a::QQFieldElem)
  d = denominator(a)
  n = numerator(a)
  res = ZZRingElem[]
  for (p, _) in factor(d)
    push!(res, p)
  end
  for (p, _) in factor(n)
    push!(res, p)
  end
  return res
end

