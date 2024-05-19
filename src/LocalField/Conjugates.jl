#XXX: valuation(Q(0)) == 0 !!!!!
function newton_lift(f::ZZPolyRingElem, r::QadicFieldElem, prec::Int = parent(r).prec_max, starting_prec::Int = 2)
  Q = parent(r)
  n = prec
  i = n
  chain = [n]
  while i>starting_prec
    i = div(i+1, 2)
    push!(chain, i)
  end
  fs = derivative(f)
  qf = change_base_ring(Q, f, cached = false)
  qfs = change_base_ring(Q, fs, cached = false)
  r = setprecision(r, 1)
  o = Q(r)
  s = qf(r)
  o = inv(setprecision(qfs, 1)(o))
  @assert r.N == 1
  for p = reverse(chain)
    setprecision!(r, p)
    setprecision!(o, p)
    Q.prec_max = r.N
    if r.N > precision(Q)
      setprecision!(qf, r.N)
      setprecision!(qfs, r.N)
    end
    r = r - qf(r)*o
    if r.N >= n
      Q.prec_max = n
      return r
    end
    o = o*(2-qfs(r)*o)
  end
  return r
end

function newton_lift(f::ZZPolyRingElem, r::LocalFieldElem, precision::Int = parent(r).prec_max, starting_prec::Int = 2)
  Q = parent(r)
  n = precision
  i = n
  chain = [n]
  while i > starting_prec
    i = div(i+1, 2)
    push!(chain, i)
  end
  fs = derivative(f)
  qf = change_base_ring(Q, f, cached = false)
  qfs = change_base_ring(Q, fs, cached = false)
  o = Q(r)
  o = setprecision(o, 1)
  s = qf(r)
  o = inv(setprecision!(qfs, 1)(o))
  for p = reverse(chain)
    r = setprecision!(r, p)
    o = setprecision!(o, p)
    setprecision!(Q, p)
    setprecision!(qf, p)
    setprecision!(qfs, p)
    r = r - qf(r)*o
    if Nemo.precision(r) >= n
      setprecision!(Q, n)
      return r
    end
    o = o*(2-qfs(r)*o)
  end
  return r
end

@doc raw"""
    roots(Q::QadicField, f::ZZPolyRingElem; max_roots::Int = degree(f)) -> Vector{QadicFieldElem}

The roots of $f$ in $Q$, $f$ has to be square-free (at least the roots have to be simple roots).
"""
function roots(Q::QadicField, f::ZZPolyRingElem; max_roots::Int = degree(f))
  k, mk = residue_field(Q)
  rt = roots(k, f)
  RT = QadicFieldElem[]
  for r = rt
    push!(RT, newton_lift(f, preimage(mk, r)))
    if length(RT) >= max_roots
      return RT
    end
  end
  return RT
end

is_splitting(C::qAdicRootCtx) = C.is_splitting

function roots(C::qAdicRootCtx, n::Int = 10)
  if isdefined(C, :R) && all(x -> x.N >= n, C.R)
    return [setprecision(x, n) for x = C.R]
  end
  lf = factor_mod_pk(Array, C.H, n)
  rt = QadicFieldElem[]
  for Q = C.Q
    Q.prec_max = n
    for x = lf
      if is_splitting(C) || degree(x[1]) == degree(Q)
        append!(rt, roots(Q, x[1], max_roots = 1))
      end
    end
  end
  if isdefined(C, :R)
    st = QadicFieldElem[]
    for r = C.R
      p = findfirst(x -> degree(parent(r)) == degree(parent(x)) && iszero(x-r), rt)
      push!(st, rt[p])
    end
    rt = st
  end
  C.R = rt
  return rt
end

@doc raw"""
    qAdicConj(K::AbsSimpleNumField, p::Int)

Creates a data structure to compute the conjugates in an unramified splitting field
over $Q_p$.
"""
mutable struct qAdicConj
  K::AbsSimpleNumField
  C::qAdicRootCtx
  cache::Dict{AbsSimpleNumFieldElem, Any}

  function qAdicConj(K::AbsSimpleNumField, p::Int; splitting_field::Bool = false)
    if discriminant(map_coefficients(Native.GF(p), K.pol)) == 0
      error("cannot deal with difficult primes yet")
    end
    #=
    is_index_divisor(maximal_order(K), p) && error("cannot deal with index divisors yet")
    is_ramified(maximal_order(K), p) && error("cannot deal with ramification yet")
    =#
    if splitting_field
      Zx = polynomial_ring(FlintZZ, cached = false)[1]
      C = qAdicRootCtx(Zx(K.pol), p, splitting_field = true)
      r = new()
      r.C = C
      r.K = K
      r.cache = Dict{AbsSimpleNumFieldElem, Any}()
      return r
    end
    D = get_attribute!(K, :nf_conjugate_data_qAdic) do
      return Dict{Int, Tuple{qAdicRootCtx, Dict{AbsSimpleNumFieldElem, Any}}}()
    end::Dict{Int, Tuple{qAdicRootCtx, Dict{AbsSimpleNumFieldElem, Any}}}
    Dp = get!(D, p) do
      Zx = polynomial_ring(FlintZZ, cached = false)[1]
      d = lcm(map(denominator, coefficients(K.pol)))
      C = qAdicRootCtx(Zx(K.pol*d), p)
      return (C, Dict{AbsSimpleNumFieldElem, Any}())
    end

    return new(K, Dp[1], Dp[2])
  end
end

function Base.show(io::IO, C::qAdicConj)
  println(io, "data for the $(C.C.p)-adic completions of $(C.K)")
end

#to compare to the classical conjugates
#  all = true/ false: only on of a pair of complex conjugates is returned
#  flat = true/ false: return (Re, Im) or the complex number
#TODO: not sure how this would work in the ramified, not-normal case.
@doc raw"""
    conjugates(a::AbsSimpleNumFieldElem, C::qAdicConj, n::Int = 10; flat::Bool = false, all:Bool = true) -> []

Returns an array of the $q$-adic conjugates of $a$: Let $p Z_K = \prod P_i$ for the maximal order
$Z_K$ of the parent of $a$. Then $K \otimes Q_p = \prod K_{P_i}$. For each of the $P_i$
a $q$-adic (unramifed) extension $K_{P_i}$ of $Q_p$ is computed, sth. $a$ has $\deg P_i = \deg K_{P_i}$
many conjugates in $K_{P_i}$.
If `all = true` and `flat = false`, the default, then all $n$ conjugates are returned.
If `all = false`, then for each $P_i$ only one conjugate is returned, the others could be
computed using automorphisms (the Frobenius).
If `flat = true`, then instead of the conjugates, only the $p$-adic coefficients are returned.
"""
function conjugates(a::AbsSimpleNumFieldElem, C::qAdicConj, n::Int = 10; flat::Bool = false, all::Bool = true)
  if is_splitting(C.C)
    return expand(_conjugates(a, C, n, x -> x), flat = flat, all = all, degs = degrees(C.C.H))
  else
    return expand(_conjugates(a, C, n, x -> x), flat = flat, all = all)
  end
end

function expand(a::Vector{QadicFieldElem}; all::Bool, flat::Bool, degs::Vector{Int}= Int[])
  re = QadicFieldElem[]
  if all
    for ix = 1:length(a)
      x = a[ix]
      push!(re, x)
      y = x
      d = degree(parent(x))
      if ix <= length(degs)
        for i=2:degs[ix]
          y = frobenius(y)
          push!(re, y)
        end
      else
        for i=2:degree(parent(x))
          y = frobenius(y)
          push!(re, y)
        end
      end
    end
  else
    re = a
  end
  if flat
    r = PadicFieldElem[]
    for x = re
      for i=1:degree(parent(x))
        push!(r, coeff(x, i-1))
      end
    end
    return r
  else
    return re
  end
end

#TODO: implement a proper Frobenius - with caching of the frobenius_a element
function _conjugates(a::AbsSimpleNumFieldElem, C::qAdicConj, n::Int, op::Function)
  R = roots(C.C, n)
  @assert parent(a) == C.K
  Zx = polynomial_ring(FlintZZ, cached = false)[1]
  d = denominator(a)
  f = Zx(d*a)
  res = QadicFieldElem[]
  for x = R
    a = op(inv(parent(x)(d))*f(x))::QadicFieldElem
    push!(res, a)
  end
  return res
end

function _log(a::QadicFieldElem)
  q = prime(parent(a))^degree(parent(a))
  if iseven(q) # an error in flint
    return log((a^(q-1))^2)//2//(q-1)
  end
  return log(a^(q-1))//(q-1) # faster than the teichmuller stuff
  return log(a*inv(teichmuller(a)))
end

@doc raw"""
    conjugates_log(a::AbsSimpleNumFieldElem, C::qAdicConj, n::Int = 10; flat::Bool = false, all:Bool = true) -> []
    conjugates_log(a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, C::qAdicConj, n::Int = 10; flat::Bool = false, all:Bool = true) -> []

Returns an array of the logarithms of the $q$-adic conjugates of $a$: Let $p Z_K = \prod P_i$ for the maximal order
$Z_K$ of the parent of $a$. Then $K \otimes Q_p = \prod K_{P_i}$. For each of the $P_i$
a $q$-adic (unramifed) extension $K_{P_i}$ of $Q_p$ is computed, sth. $a$ has $\deg P_i = \deg K_{P_i}$
many cojugates in $K_{P_i}$.
If `all = true` and `flat = false`, then all $n$ logarithms of conjugates are returned.
If `all = false`, then for each $P_i$ only one logarithm of a conjugate is returned, the others could be
computed using automorphisms (the Frobenius).
If `flat = true`, then instead of the conjugates, only the $p$-adic coefficients are returned.
"""
function conjugates_log(a::AbsSimpleNumFieldElem, C::qAdicConj, n::Int = 10; all::Bool = false, flat::Bool = true)
  if haskey(C.cache, a)
    b = C.cache[a]
    if b[1,1].N == n
      return expand(b, all = all, flat = flat)
    end
  end
  C.cache[a] = b = _conjugates(a, C, n, _log)
  return expand(b, all = all, flat = flat)
end

function conjugates_log(a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, C::qAdicConj, n::Int = 10; all::Bool = false, flat::Bool = true)
  first = true
  local res::Vector{QadicFieldElem}
  for (k, v) = a.fac
    try
      y = conjugates_log(k, C, n, flat = false, all = false)
      if first
        res = v .* y
        first = false
      else
        res += v .* y
      end
    catch e
      if isa(e, DivideError) || isa(e, DomainError)
        lp = prime_decomposition(maximal_order(parent(k)), C.C.p)
        @assert Base.all(x -> has_2_elem_normal(x[1]), lp)
        val = map(x -> valuation(k, x[1]), lp)
        pe = prod(lp[i][1].gen_two^val[i] for i = 1:length(lp) if val[i] != 0)
        aa = k//pe
        y = conjugates_log(aa, C, n, all = false, flat = false)
        if first
          res = v .* y
          first = false
        else
          res += v .* y
        end
      else
        rethrow(e)
      end
    end
  end

  if is_splitting(C.C)
    return expand(res, flat = flat, all = all, degs = degrees(C.C.H))
  else
    return expand(res, all = all, flat = flat)
  end
end


function special_gram(m::Vector{Vector{QadicFieldElem}})
  g = Vector{PadicFieldElem}[]
  for i = m
    r = PadicFieldElem[]
    for j = m
      k = 1
      S = 0
      while k <= length(i)
        s = i[k] * j[k]
        for l = 1:degree(parent(s))-1
          s += i[k+l] * j[k+l]
        end
        S += coeff(s, 0)
        @assert s == coeff(s, 0)
        k += degree(parent(s))
      end
      push!(r, S)
    end
    push!(g, r)
  end
  return g
end

function special_gram(m::Vector{Vector{PadicFieldElem}})
  n = transpose(matrix(m))
  n = transpose(n)*n
  return [[n[i,j] for j=1:ncols(n)] for i = 1:nrows(n)]
end

@doc raw"""
    regulator(u::Vector{T}, C::qAdicConj, n::Int = 10; flat::Bool = true) where {T<: Union{AbsSimpleNumFieldElem, FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}}
    regulator(K::AbsSimpleNumField, C::qAdicConj, n::Int = 10; flat::Bool = true)
    regulator(R::AbsNumFieldOrder, C::qAdicConj, n::Int = 10; flat::Bool = true)

Returns the determinant of $m^t m$ where the columns of $m$ are the `conjugates_log` of the units
in either the array, or the fundamental units for $K$ (the maximal order of $K$) or $R$.
If `flat = false`, then all prime ideals over $p$ need to have the same degree.
In either case, Leopold's conjecture states that the regulator is zero iff the units are dependent.
"""
function regulator(u::Vector{T}, C::qAdicConj, n::Int = 10; flat::Bool = true) where {T<: Union{AbsSimpleNumFieldElem, FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}}
  c = map(x -> conjugates_log(x, C, n, all = !flat, flat = flat), u)
  return det(transpose(matrix(special_gram(c))))
end

function regulator(K::AbsSimpleNumField, C::qAdicConj, n::Int = 10; flat::Bool = false)
  return regulator(maximal_order(K), C, n, flat = flat)
end

function regulator(R::AbsSimpleNumFieldOrder, C::qAdicConj, n::Int = 10; flat::Bool = false)
  u, mu = unit_group_fac_elem(R)
  return regulator([mu(u[i]) for i=2:ngens(u)], C, n, flat = flat)
end

@doc raw"""
    regulator_iwasawa(u::Vector{T}, C::qAdicConj, n::Int = 10) where {T<: Union{AbsSimpleNumFieldElem, FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}} -> QadicFieldElem
    regulator_iwasawa(K::AbsSimpleNumField, C::qAdicConj, n::Int = 10) -> QadicFieldElem
    regulator_iwasawa(R::AbsNumFieldOrder, C::qAdicConj, n::Int = 10) -> QadicFieldElem

For a totally real field $K$, the regulator as defined by Iwasawa: the determinant of the
matrix containing the logarithms of the conjugates, supplemented by a column containing all $1$.
"""
function regulator_iwasawa(u::Vector{T}, C::qAdicConj, n::Int = 10) where {T<: Union{AbsSimpleNumFieldElem, FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}}
  k = base_ring(u[1])
  @assert is_totally_real(k)
  c = map(x -> conjugates_log(x, C, n, all = true, flat = false), u)
  m = matrix(c)
  m = vcat(m, matrix(base_ring(m), 1, ncols(m), [one(base_ring(m)) for i=1:ncols(m)]))
  return det(m)//degree(k)
end

function regulator_iwasawa(K::AbsSimpleNumField, C::qAdicConj, n::Int = 10)
  @assert is_totally_real(K)
  return regulator_iwasawa(maximal_order(K), C, n)
end

function regulator_iwasawa(R::AbsNumFieldOrder, C::qAdicConj, n::Int = 10)
  @assert is_totally_real(nf(R))
  u, mu = unit_group_fac_elem(R)
  return regulator_iwasawa([mu(u[i]) for i=2:ngens(u)], C, n)
end

function eval_f_fs(f::PolyRingElem, x::RingElem)
  d = Int[]
  for i=1:degree(f)
    if !iszero(coeff(f, i))
      if i>0 && !((i-1) in d)
        push!(d, i-1)
      end
      push!(d, i)
    end
  end
  p = Dict{Int, typeof(x)}()
  p[0] = one(x)
  p[1] = x
  p[d[1]] = x^d[1]

  for i = 2:length(d)
    if haskey(p, d[i])
      continue
    end
    q, r = divrem(d[i], d[i-1])
    if haskey(p, r)
      xr = p[r]
    else
      xr = p[r] = x^r
    end
    p[d[i]] = p[d[i-1]]^q * xr
  end
  s1 = zero(x)
  s2 = zero(x)
  for i=0:degree(f)
    c = coeff(f, i)
    if !iszero(c)
      s1 += c*p[i]
      if i>0
        s2 += i*c*p[i-1]
      end
    end
  end
  return s1, s2
end

struct nf_elem_mod <: RingElem
  a::AbsSimpleNumFieldElem
  p::ZZRingElem
end
function *(a::ZZRingElem, b::nf_elem_mod)
  c = a*b.a
  return nf_elem_mod(mod_sym(c, b.p), b.p)
end
function *(a::nf_elem_mod, b::nf_elem_mod)
  c = a.a*b.a
  return nf_elem_mod(mod_sym(c, a.p), a.p)
end
function one(a::nf_elem_mod)
  return nf_elem_mod(one(a.a), a.p)
end
function zero(a::nf_elem_mod)
  return nf_elem_mod(zero(a.a), a.p)
end
function +(a::nf_elem_mod, b::nf_elem_mod)
  return nf_elem_mod(a.a+b.a, a.p)
end
function ^(a::nf_elem_mod, i::Int)
  b = one(a)
  c = a
  while i > 0
    if isodd(i)
      b *= c
    end
    i >>= 1
    if !iszero(i)
      c *= c
    end
  end
  return b
end
function lift_root(f::ZZPolyRingElem, a::AbsSimpleNumFieldElem, o::AbsSimpleNumFieldElem, p::ZZRingElem, n::Int)
  #f(a) = 0 mod p, o*f'(a) = 1 mod p, want f(a) = 0 mod p^n
  k = 1
  while k < n
    p *= p
    k *= 2
    #TODO: here f will be sparse (and possibly large degree), so
    #      this evaluation is bad.
    # in the calling cite: don't work in the large field, restrict
    # to working (mod p^k) in the field defined by the factor

    if false
      pa = [one(a)]
      while length(pa) <= degree(f)
        push!(pa, pa[end]*a)
        mod_sym!(pa[end], p)
      end
      fa  = sum(coeff(f, i-1) * pa[i] for i=1:length(pa))
      fsa = sum(coeff(f, i) * i * pa[i] for i=1:length(pa)-1)
    else
      _fa, _fsa = eval_f_fs(f, nf_elem_mod(a, p))
      fa = _fa.a
      fsa = _fsa.a
    end
    o = o*(2-fsa*o)
    a = a - fa*o
    mod_sym!(o, p)
    mod_sym!(a, p)
  end
  return a
end

@doc raw"""
    completion_easy(K::AbsSimpleNumField, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
                                               -> QadicField, CompletionMap

The completion of $K$ wrt to the topology induced by the valuation at the
unramified prime ideal $P$.

The map giving the embedding of $K$ into the completion, admits a pointwise
preimage to obtain a lift.  Note, that the map is not well defined by this
data: $K$ will have $\deg P$ many embeddings.
"""
function completion_easy(K::AbsSimpleNumField, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, precision::Int = 10)
  #non-unique!! will have deg(P) many
  p = minimum(P)
  C = qAdicConj(K, Int(p))
  g = conjugates(P.gen_two.elem_in_nf, C)
#  @show map(x->valuation(x), g)
  i = findfirst(x->valuation(x) > 0, g)
  return completion(K, p, i, precision)
end

completion(K::AbsSimpleNumField, p::Integer, i::Int, precision::Int = 64) = completion(K, ZZRingElem(p), i, precision)

@doc raw"""
    completion(K::AbsSimpleNumField, p::ZZRingElem, i::Int) -> QadicField, Map

The completion corresponding to the $i$-th conjugate in the non-canonical ordering of
`conjugates`.
"""
function completion(K::AbsSimpleNumField, p::ZZRingElem, i::Int, n = 64)
  C = qAdicConj(K, Int(p))
  @assert 0<i<= degree(K)

  ca = conjugates(gen(K), C, n, all = true, flat = false)[i]
  return completion(K, ca)
end

function completion(K::AbsSimpleNumField, ca::QadicFieldElem)
  p = prime(parent(ca))
  C = qAdicConj(K, Int(p))
  r = roots(C.C, precision(ca))
  i = findfirst(x->parent(r[x]) == parent(ca) && r[x] == ca, 1:length(r))
  Zx = polynomial_ring(FlintZZ, cached = false)[1]
  function inj(a::AbsSimpleNumFieldElem)
    d = denominator(a)
    pr = precision(parent(ca))
    if pr > precision(ca)
      ri = roots(C.C, precision(parent(ca)))[i]
    else
      ri = ca
    end
    return inv(parent(ca)(d))*(Zx(a*d)(ri))
  end
  # gen(K) -> conj(a, p)[i] -> a = sum a_i o^i
  # need o = sum o_i a^i
  R, mR = residue_field(parent(ca))
  pa = [one(R), mR(ca)]
  d = degree(R)
  while length(pa) < d
    push!(pa, pa[end]*pa[2])
  end
  m = matrix(GF(p), d, d, [lift(ZZ, coeff(pa[i], j-1)) for j=1:d for i=1:d])
  o = matrix(GF(p), d, 1, [lift(ZZ, coeff(gen(R), j-1)) for j=1:d])
  s = solve(m, o, side = :right)
  @hassert :qAdic 1 m*s == o
  a = K()
  for i=1:d
    _num_setcoeff!(a, i-1, lift(ZZ, s[i, 1]))
  end
  f = defining_polynomial(parent(ca), FlintZZ)
  fso = inv(derivative(f)(gen(R)))
  o = matrix(GF(p), d, 1, [lift(ZZ, coeff(fso, j-1)) for j=1:d])
  s = solve(m, o; side = :right)
  b = K()
  for i=1:d
    _num_setcoeff!(b, i-1, lift(ZZ, s[i,1]))
  end

  #TODO: don't use f, use the factors i the HenselCtx
  #seems to be slower...
#  lf = factor_mod_pk(Array, C.C.H, Int(C.C.H.N))
#  jj = findfirst(x->iszero(x[1](ca)), lf)
#  Kjj = number_field(lf[jj][1], check = false, cached = false)[1]
#  ajj = Kjj(parent(Kjj.pol)(a))
#  bjj = Kjj(parent(Kjj.pol)(b))
#  cjj = lift_root(f, ajj, bjj, p, 10)
#  c = K(parent(K.pol)(cjj))

  c = lift_root(f, a, b, p, 10)
  pc = ZZRingElem(10)
  function lif(x::QadicFieldElem)
    if iszero(x)
      return K(0)
    end
    if precision(x) > pc
      #XXX this changes (c, pc) inplace as a cache
      #probably should be done with a new map type that can
      #store c, pc on the map.
      d = lift_root(f, a, b, p, precision(x))
#  Kjj = number_field(lf[jj][1], check = false, cached = false)[1]
#  ajj = Kjj(parent(Kjj.pol)(a))
#  bjj = Kjj(parent(Kjj.pol)(b))
#  djj = lift_root(f, ajj, bjj, p, 10)
#  d = K(parent(K.pol)(djj))
      ccall((:nf_elem_set, libantic), Nothing, (Ref{AbsSimpleNumFieldElem}, Ref{AbsSimpleNumFieldElem}, Ref{AbsSimpleNumField}), c, d, K)
      ccall((:fmpz_set_si, libflint), Nothing, (Ref{ZZRingElem}, Cint), pc, precision(x))
    elseif precision(x) < pc
      d = mod_sym(c, p^precision(x))
    else
      d = c
    end
    n = x.length
    r = K(lift(ZZ, coeff(x, n-1)))
    pk = p^precision(x)
    while n > 1
      n -= 1
      r = mod_sym(r*d, pk) + lift(ZZ, coeff(x, n-1))
    end
    return r#*K(p)^valuation(x)
  end
  return parent(ca), MapFromFunc(K, parent(ca), inj, lif)
end
