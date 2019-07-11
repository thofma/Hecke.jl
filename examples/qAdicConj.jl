
module QAdic

using Hecke


mutable struct qAdicRootCtx
  f::fmpz_poly
  p::Int
  n::Int
  Q::Array{FlintQadicField, 1}
  H::Hecke.HenselCtx
  R::Array{qadic, 1}
  function qAdicRootCtx(f::fmpz_poly, p::Int)
    r = new()
    r.f = f
    r.p = p
    r.H = H = Hecke.factor_mod_pk_init(f, p)
    lf = Hecke.factor_mod_pk(H, 1)
    #TODO:XXX: Careful: QadicField ONLY works, currently, in Conway range
    Q = [QadicField(p, x, 1) for x = Set(degree(y) for y = keys(lf))]
    @assert all(isone, values(lf))
    r.Q = Q
    return r
  end
end

function Hecke.precision(H::Hecke.HenselCtx)
  return Int(H.N)
end

function Hecke.prime(H::Hecke.HenselCtx)
  return Int(H.p)
end

function Base.setprecision(q::qadic, N::Int)
  r = parent(q)()
  r.N = N
  ccall((:padic_poly_set, :libflint), Nothing, (Ref{qadic}, Ref{qadic}, Ref{FlintQadicField}), r, q, parent(q))
  return r
end

function Base.setprecision(q::padic, N::Int)
  r = parent(q)()
  r.N = N
  ccall((:padic_set, :libflint), Nothing, (Ref{padic}, Ref{padic}, Ref{FlintPadicField}), r, q, parent(q))
  return r
end

export setprecision!

function setprecision!(q::qadic, N::Int)
  @assert N >= q.N
  q.N = N
  return q
end

function setprecision!(Q::FlintQadicField, n::Int)
  Q.prec_max = n
end

function setprecision!(Q::FlintPadicField, n::Int)
  Q.prec_max = n
end

function setprecision!(f::Generic.Poly{qadic}, N::Int)
  for i=1:length(f)
    f.coeffs[i].N = N
  end
  return f
end

function Base.setprecision(f::Generic.Poly{qadic}, N::Int)
  f = deepcopy(f)
  for i=1:length(f)
    f.coeffs[i].N = N
  end
  return f
end


function setprecision!(a::AbstractArray{qadic}, N::Int)
  for x = a
    setprecision!(x, N)
  end
end

function Base.setprecision(a::AbstractArray{qadic}, N::Int)
  return map(x->setprecision(x, N), a)
end

function setprecision!(a::Generic.MatSpaceElem{qadic}, N::Int)
  setprecision!(a.entries, N)
end

function Base.setprecision(a::Generic.MatSpaceElem{qadic}, N::Int)
  b = deepcopy(a)
  setprecision!(b, N)
  return B
end

function Hecke.trace(r::qadic)
  t = base_ring(parent(r))()
  ccall((:qadic_trace, :libflint), Nothing, (Ref{padic}, Ref{qadic}, Ref{FlintQadicField}), t, r, parent(r))
  return t
end

function Hecke.norm(r::qadic)
  t = base_ring(parent(r))()
  ccall((:qadic_norm, :libflint), Nothing, (Ref{padic}, Ref{qadic}, Ref{FlintQadicField}), t, r, parent(r))
  return t
end

#XXX: valuation(Q(0)) == 0 !!!!!
function newton_lift(f::fmpz_poly, r::qadic)
  Q = parent(r)
  n = Q.prec_max
  i = n
  chain = [n]
  while i>2
    i = div(i+1, 2)
    push!(chain, i)
  end
  fs = derivative(f)
  qf = change_base_ring(f, Q)
  qfs = change_base_ring(fs, Q)
  o = Q(r)
  o.N = 1
  s = qf(r)
  o = inv(setprecision!(qfs, 1)(o))
  @assert r.N == 1
  for p = reverse(chain)
    r.N = p
    o.N = p
    Q.prec_max = r.N
    setprecision!(qf, r.N)
    setprecision!(qfs, r.N)
    r = r - qf(r)*o
    if r.N >= n
      Q.prec_max = n
      return r
    end
    o = o*(2-qfs(r)*o)
  end
end

function Hecke.setcoeff!(x::fq_nmod, n::Int, u::UInt)
  ccall((:nmod_poly_set_coeff_ui, :libflint), Nothing, 
                (Ref{fq_nmod}, Int, UInt), x, n, u)
end

function Hecke.coeff(x::qadic, i::Int)
  R = FlintPadicField(prime(parent(x)), parent(x).prec_max)
  c = R()
  ccall((:padic_poly_get_coeff_padic, :libflint), Nothing, 
           (Ref{padic}, Ref{qadic}, Int, Ref{FlintQadicField}), c, x, i, parent(x))
  return c         
end

function Hecke.setcoeff!(x::qadic, i::Int, y::padic)
  ccall((:padic_poly_set_coeff_padic, :libflint), Nothing, 
           (Ref{qadic}, Int, Ref{padic}, Ref{FlintQadicField}), x, i, y, parent(x))
end

function Hecke.setcoeff!(x::qadic, i::Int, y::UInt)
  R = FlintPadicField(prime(parent(x)), parent(x).prec_max)
  Y = R(fmpz(y))
  ccall((:padic_poly_set_coeff_padic, :libflint), Nothing, 
           (Ref{qadic}, Int, Ref{padic}, Ref{FlintQadicField}), x, i, Y, parent(x))
end

function Hecke.ResidueField(Q::FlintQadicField)
  k = GF(Int(prime(Q)), degree(Q))[1]
  pro = function(x::qadic)
    v = valuation(x)
    v < 0 && error("elt non integral")
    v > 0 && return k(0)
    z = k()
    for i=0:degree(Q)
      setcoeff!(z, i, UInt(lift(coeff(x, i))%prime(Q)))
    end
    return z
  end
  lif = function(x::fq_nmod)
    z = Q()
    for i=0:degree(Q)-1
      setcoeff!(z, i, coeff(x, i))
    end
    return z
  end
  return k, MapFromFunc(pro, lif, Q, k)
end

function Hecke.ResidueField(Q::FlintPadicField)
  k = GF(Int(prime(Q)))
  pro = function(x::padic)
    v = valuation(x)
    v < 0 && error("elt non integral")
    v > 0 && return k(0)
    z = k(lift(x))
    return z
  end
  lif = function(x::Hecke.gfp_elem)
    z = Q(lift(x))
    return z
  end
  return k, MapFromFunc(pro, lif, Q, k)
end

function Hecke.base_ring(Q::FlintQadicField)
  return FlintPadicField(prime(Q), precision(Q))
end
base_field(Q::FlintQadicField) = base_ring(Q)

function Hecke.roots(f::fmpz_poly, Q::FlintQadicField; max_roots::Int = degree(f))
  k, mk = ResidueField(Q)
  rt = roots(f, k)
  RT = qadic[]
  for r = rt
    push!(RT, newton_lift(f, preimage(mk, r)))
    if length(RT) >= max_roots
      return RT
    end
  end
  return RT
end

function Hecke.roots(C::qAdicRootCtx, n::Int = 10)
  if isdefined(C, :R) && all(x -> x.N >= n, C.R)
    return [setprecision(x, n) for x = C.R]
  end
  lf = Hecke.factor_mod_pk(C.H, n)
  rt = qadic[]
  for Q = C.Q
    Q.prec_max = n
    for x = keys(lf)
      if degree(x) == degree(Q)
        append!(rt, roots(x, Q, max_roots = 1))
      end
    end
  end
  if isdefined(C, :R)
    st = qadic[]
    for r = C.R
      p = findfirst(x -> degree(parent(r)) == degree(parent(x)) && iszero(x-r), rt)
      push!(st, rt[p])
    end
    rt = st
  end
  C.R = rt
  return rt
end

#TODO: refine roots....

t = Hecke.create_accessors(AnticNumberField, Dict{Int, Tuple{qAdicRootCtx, Dict{nf_elem, Any}}}, get_handle())
global _get_nf_conjugate_data_qAdic = t[1]
global _set_nf_conjugate_data_qAdic = t[2]

mutable struct qAdicConj
  K::AnticNumberField
  C::qAdicRootCtx
  cache::Dict{nf_elem, Any}

  function qAdicConj(K::AnticNumberField, p::Int)
    D = _get_nf_conjugate_data_qAdic(K, false)
    global new_load
    if new_load 
      D = Dict{Int, Tuple{qAdicRootCtx, Dict{nf_elem, Any}}}()
      _set_nf_conjugate_data_qAdic(K, D)
      new_load = false
    end
    if D !== nothing
      if haskey(D, p)
        Dp = D[p]
        return new(K, Dp[1], Dp[2])
      end
    else
      D = Dict{Int, Tuple{qAdicRootCtx, Dict{nf_elem, Any}}}()
      _set_nf_conjugate_data_qAdic(K, D)
    end
    Zx = PolynomialRing(FlintZZ, cached = false)[1]
    C = qAdicRootCtx(Zx(K.pol), p)
    r = new()
    r.C = C
    r.K = K
    r.cache = Dict{nf_elem, Any}()
    D[p] = (C, r.cache)
    return r
  end
end

function Hecke.conjugates(a::nf_elem, C::qAdicConj, n::Int = 10)
  return _conjugates(a, C, n, x -> x, flat = false, all = true)
end
#TODO: implement a proper Frobenius - with caching of the frobenius_a element
function _conjugates(a::nf_elem, C::qAdicConj, n::Int, op::Function; flat::Bool = true, all::Bool = false)
  R = roots(C.C, n)
  @assert parent(a) == C.K
  Zx = PolynomialRing(FlintZZ, cached = false)[1]
  d = denominator(a)
  f = Zx(d*a)
  res = qadic[]
  for x = R
    a = op(inv(parent(x)(d))*f(x))::qadic
    push!(res, a)
    if all
      i = 2
      while i <= degree(parent(a))
        a = frobenius(a)
        push!(res, a)
        i += 1
      end
    end
  end
  if !flat
    return res
  end
  re = padic[]
  for x = res
    for i=1:degree(parent(x))
      push!(re, coeff(x, i-1))
    end
  end
  return matrix(parent(re[1]), 1, length(re), re)
end

function _log(a::qadic)
  q = prime(parent(a))^degree(parent(a))
  return log(a^(q-1))//(q-1)
  return log(a*inv(teichmuller(a)))
end

function Hecke.conjugates_log(a::nf_elem, C::qAdicConj, n::Int = 10)
  if haskey(C.cache, a)
    b = C.cache[a]
    if b[1,1].N == n
      return b
    end
  end
  return C.cache[a] = _conjugates(a, C, n, _log)
end

function Hecke.conjugates_log(a::FacElem{nf_elem, AnticNumberField}, C::qAdicConj, n::Int = 10)
  local res::Generic.MatSpaceElem{padic}
  first = true
  for (k, v) = a.fac
    try 
      y = conjugates_log(k, C, n)
      if first
        res = v*y
        first = false
      else
        res += v*y
      end
    catch e
      if isa(e, DivideError) || isa(e, DomainError)
        lp = prime_decomposition(maximal_order(parent(k)), C.C.p)
        @assert all(x -> Hecke.has_2_elem_normal(x[1]), lp)
        val = map(x -> valuation(k, x[1]), lp)
        pe = prod(lp[i][1].gen_two^val[i] for i = 1:length(lp) if val[i] != 0)
        aa = k//pe
        y = conjugates_log(aa, C, n)
        if first
          res = v*y
          first = false
        else
          res += v*y
        end
      else
        rethrow(e)
      end
    end
  end
  return res
end

function mult_syzygies_units(A::Array{FacElem{nf_elem, AnticNumberField}, 1})
  p = next_prime(100)
  K = base_ring(parent(A[1]))
  m = maximum(degree, keys(factor(K.pol, GF(p)).fac))
  while m > 4
    p = next_prime(p)
    m = maximum(degree, keys(factor(K.pol, GF(p)).fac))
  end
         #experimentally, the runtime is dominated by log
  u = FacElem{nf_elem, AnticNumberField}[]
  prec = 10

  r1, r2 = signature(K)
  r = r1+r2 -1
  n = degree(K)
  C = qAdicConj(K, p)
  la = conjugates_log(A[1], C, prec)
  lu = zero_matrix(base_ring(la), 0, n)
  uu = []
  for a = A
    while true
      @time la = conjugates_log(a, C, prec)
      if iszero(la)
        @time @assert verify_gamma([a], [fmpz(1)], fmpz(p)^prec)
        println("torsion found")
        break
      end
      lv = vcat(lu, la)
      #check_precision and change
      if false && any(x->precision(x) < prec, lv)
        println("loss of precision - not sure what to do")
        for i=1:rows(lv)
          for j = cols(lv) #seems to not do anything
            lv[i, j] = setprecision(lv[i, j], min_p)
            @assert precision(lv[i,j]) == min_p
          end
        end
      end
      @time k = Hecke.left_kernel_basis(lv)
      @assert length(k) < 2
      if length(k) == 0
        println("new ")
        push!(u, a)
        lu = vcat(lu, la)
        @assert length(u) <= r
      else # length == 1 extend the module
        s = fmpq[]
        for x = k[1]
          @time y = lift_reco(FlintQQ, x, reco = true)
          if y == nothing
            prec *= 2
            @show "increase prec to ", prec
            lu = vcat([conjugates_log(x, C, prec) for x = u])
            break
          end
          push!(s, y)
        end
        if length(s) < length(k[1])
          continue
        end
        d = reduce(lcm, map(denominator, s))
        gamma = fmpz[FlintZZ(x*d)::fmpz for x = s] 
        @assert reduce(gcd, gamma) == 1 # should be a primitive relation
        @time if !verify_gamma(push!(copy(u), a), gamma, fmpz(p)^prec)
          prec *= 2
          @show "increase prec to ", prec
          lu = vcat([conjugates_log(x, C, prec) for x = u])
          continue
        end
        @assert length(gamma) == length(u)+1
        gamma = vcat(gamma[1:length(u)], [0 for i=length(u)+1:r+length(uu)], [gamma[end]])
        push!(uu, (a, gamma))
      end
      break
    end
  end
  #=
    let u_1, .., u_n be units and
       <u_i | i> has rank s and 
        r_i in Z^n be such that
          prod u_i^r_i = 1  (OK, sum of the logs is zero)
          rank <r_i | i> = s as well
    so the r_i form a Q-basis for the relations.
    Essentially, the gamma of above are the r_i
    Let [H|0] = [r_i|i]*T be the hnf with trafo, so T in Gl(n, Z)
    Then
      <u_i|i> = <[u_i|i] T>
      [r_i|i] * [u_i|i]^t = 0 (by construction)
      [r_i|i] T inv(T) [u[i] | i] = 0
      [H | 0]   [v_i | i] = 0
      so, since H is triangular(!!) v_1, ... v_n-s = 0
      and <u_i |i> = <v_n-s+1, ..., v_n>
    
    for the case of n=s+1 this is mostly the "normal" construction.
    Note: as a side, the relations do not have to be primitive.
      If they are, (and n=s+1), then H = 1
  =#

  for i=1:length(uu)-1
    append!(uu[i][2], zeros(FlintZZ, length(uu[end][2])-length(uu[i][2])))
  end
  if length(uu) == 0
    @show uu
    U = matrix(FlintZZ, length(uu), length(uu[end][2]), reduce(vcat, [x[2] for x = uu]))
  else
    U = matrix(FlintZZ, length(uu), length(uu[end][2]), reduce(vcat, [x[2] for x = uu]))
  end
  _, U = hnf_with_transform(U')
  if false
    U = inv(U)
    V = sub(U, 1:rows(U), 1:cols(U)-length(u))
    U = sub(U, 1:rows(U), cols(U)-length(u)+1:cols(U))
    #U can be reduced modulo V...
    Z = zero_matrix(FlintZZ, cols(V), cols(U))
    I = identity_matrix(FlintZZ, cols(U)) * p^(2*prec)
    k = base_ring(A[1])
    A = [ Z V'; I U']
    l = lll(A)
    U = sub(l, cols(V)+1:rows(l), cols(U)+1:cols(l))
    U = lll(U)
  else
    U = lll(U')
  end
  return Hecke._transform(vcat(u, FacElem{nf_elem,AnticNumberField}[FacElem(k(1)) for i=length(u)+1:r], [x[1] for x = uu]), U')
end

function verify_gamma(a::Array{FacElem{nf_elem, AnticNumberField}, 1}, g::Array{fmpz, 1}, v::fmpz)
  #knowing that sum g[i] log(a[i]) == 0 mod v, prove that prod a[i]^g[i] is
  #torsion
  #= I claim N(1-a) > v^n for n the field degree:
   Let K be one of the p-adic fields involved, set b = a^g
   then log(K(b)) = 0 (v = p^l) by assumption
   so val(log(K(b))) >= l, but
   val(X) = 1/deg(K) val(norm(X)) for p-adics
   This is true for all completions involved, and sum degrees is n
 =#

  t = prod([a[i]^g[i] for i=1:length(a)])
  # t is either 1 or 1-t is large, norm(1-t) is div. by p^ln
  #in this case T2(1-t) is large, by the arguments above: T2>= (np^l)^2=:B
  # and, see the bottom, \|Log()\|_2^2 >= 1/4 arcosh((B-2)/2)^2
  B = ArbField(nbits(v)*2)(v)^2
  B = 1/2 *acosh((B-2)/2)^2
  p = Hecke.upper_bound(log(B)/log(parent(B)(2)), fmpz)
  @show "using", p, nbits(v)*2
  b = conjugates_arb_log(t, max(-Int(div(p, 2)), 2))
  global res = (B, b, t)
#  @show B , sum(x*x for x = b), istorsion_unit(t)[1]
  @assert (B > sum(x*x for x = b)) == istorsion_unit(t)[1]
  return B > sum(x*x for x = b)
end


function Hecke.prime(R::PadicField, i::Int)
  p = fmpz()
  ccall((:padic_ctx_pow_ui, :libflint), Cvoid, (Ref{fmpz}, Int, Ref{PadicField}), p, i, R)
  return p
end

function getUnit(a::padic)
  u = fmpz()
  ccall((:fmpz_set, :libflint), Cvoid, (Ref{fmpz}, Ref{Int}), u, a.u)
  return u, a.v, a.N
end

function lift_reco(::FlintRationalField, a::padic; reco::Bool = false)
  if reco
    u, v, N = getUnit(a)
    R = parent(a)
    fl, c, d = rational_reconstruction(u, prime(R, N-v))
    !fl && return nothing
    if false && 2*max(nbits(c), nbits(d)) > nbits(prime(R, N-v)) -20 #arbitrary 
      @show "bad"
      return nothing
    end
    @assert fl
    x = FlintQQ(c, d)
    if v < 0
      return x//prime(R, -v)
    else
      return x*prime(R, v)
    end
  else
    return lift(FlintQQ, a)
  end
end

function Hecke.FlintZZ(x::Rational{Int})
  @assert denominator(x) == 1
  return fmpz(numerator(x))
end

import Base.*

function *(A::fmpz_mat, B::MatElem{padic})
  return matrix(base_ring(B), A) * B
end

Hecke.uniformizer(Q::FlintQadicField) = Q(prime(Q))
Base.precision(Q::FlintQadicField) = Q.prec_max

Hecke.uniformizer(Q::FlintPadicField) = Q(prime(Q))
Base.precision(Q::FlintPadicField) = Q.prec_max

function expand(a::qadic)
  @assert valuation(a-1)>0
  i = 1
  Q = parent(a)
  pi = uniformizer(Q)
  x = qadic[]
  while true
    b = divexact((a-1), pi)
    b = setprecision(b, i)
    push!(x, b)
    b = setprecision(b, precision(Q))
    a = a*inv(1+pi*b)
    pi = pi^2
    i = 2*i
    if i > precision(Q)
      return x
    end
  end
end

Hecke.nrows(A::Array{T, 2}) where {T} = size(A)[1]
Hecke.ncols(A::Array{T, 2}) where {T} = size(A)[2]


import Base.^
^(a::qadic, b::qadic) = exp(b*log(a))
^(a::padic, b::padic) = exp(b*log(a))

################################################################################
#
# (q/p)adic integers
# 
# complete enough to support hnf
################################################################################
# CHECK precision!!!

struct QadicRing{T} <: Generic.Ring
  Q::T
end

function Base.show(io::IO, Q::QadicRing)
  println("Integers of ", Q.Q)
end

function Hecke.ring_of_integers(Q::FlintQadicField)
  return QadicRing{FlintQadicField}(Q)
end
#Hecke.integers(Q::FlintQadicField) = ring_of_integers(Q)

function Hecke.ring_of_integers(Q::FlintPadicField)
  return QadicRing{FlintPadicField}(Q)
end
#Hecke.integers(Q::FlintPadicField) = ring_of_integers(Q)

struct QadicRingElem{S} <: RingElem
  x::S
  P::QadicRing
  function QadicRingElem(a::qadic, P::QadicRing)
    r = new{qadic}(a, P)
  end
  function QadicRingElem(a::padic, P::QadicRing)
    r = new{padic}(a, P)
  end
end

function Base.show(io::IO, a::QadicRingElem)
  print(io, a.x)
end
  
import Base.*, Base.==, Base.+, Base.inv, Hecke.divexact, Hecke.canonical_unit,
       Base.-

*(a::QadicRingElem, b::QadicRingElem) = QadicRingElem(a.x*b.x, a.P)
+(a::QadicRingElem, b::QadicRingElem) = QadicRingElem(a.x+b.x, a.P)
-(a::QadicRingElem, b::QadicRingElem) = QadicRingElem(a.x-b.x, a.P)
-(a::QadicRingElem) = QadicRingElem(-a.x, a.P)
^(a::QadicRingElem, b::QadicRingElem) = QadicRingElem(a.x^b.x, a.P)
^(a::T, b::QadicRingElem{T}) where {T} = a^b.x

function inv(a::QadicRingElem) 
  valuation(a.x) == 0 || error("non unit")
  return QadicRingElem(inv(a.x), a.P)
end

==(a::QadicRingElem, b::QadicRingElem) = a.x == b.x 

function divexact(a::QadicRingElem, b::QadicRingElem)
  @assert !iszero(b.x)
  iszero(a) && return a
  valuation(a.x) >= valuation(b.x) || error("division not exact")
  return QadicRingElem(a.x//b.x, a.P)
end

function divrem(a::QadicRingElem, b::QadicRingElem)
  if valuation(a.x) < valuation(b.x)
    return setprecision(a.P(0), precision(a)), a 
  end
  q = divexact(a, b)
  return q, a-q*b
end

function Base.div(a::QadicRingElem, b::QadicRingElem)
  if valuation(a.x) < valuation(b.x)
    return setprecision(a.P(0), precision(a))
  end
  q = divexact(a, b)
  return q
end

Hecke.parent(a::QadicRingElem) = a.P
Hecke.elem_type(::Type{QadicRing{FlintPadicField}}) = QadicRingElem{padic}
Hecke.elem_type(::Type{QadicRing{FlintQadicField}}) = QadicRingElem{qadic}
Hecke.parent_type(::Type{QadicRingElem{padic}}) = QadicRing{FlintPadicField}
Hecke.parent_type(::Type{QadicRingElem{qadic}}) = QadicRing{FlintQadicField}

Hecke.zero(Q::QadicRing) = QadicRingElem(Q.Q(0), Q)
Hecke.one(Q::QadicRing) = QadicRingElem(Q.Q(1), Q)

(Q::QadicRing)(a::qadic) = QadicRingElem(a, Q)
(Q::QadicRing)(a::padic) = QadicRingElem(a, Q)
(Q::QadicRing)(a::QadicRingElem) = QadicRingElem(a.x, a.P)
(Q::QadicRing)(a::Int) = QadicRingElem(Q.Q(a), Q)
(Q::QadicRing)() = QadicRingElem(Q.Q(), Q)
(Q::FlintQadicField)(a::QadicRingElem{qadic}) = a.x
(Q::FlintPadicField)(a::QadicRingElem{padic}) = a.x
(Q::FlintQadicField)(a::padic) = Q(lift(a)) #TODO: do properly
Hecke.valuation(a::QadicRingElem) = valuation(a.x)
Hecke.isunit(a::QadicRingElem) = valuation(a) == 0
function Base.deepcopy_internal(a::QadicRingElem, dict::IdDict)
  return QadicRingElem(a.x, a.P)
end
function Hecke.canonical_unit(a::QadicRingElem)
  iszero(a.x) && return setprecision(a.P(1), precision(a))
  v = valuation(a.x)
  return QadicRingElem(inv(a.x//prime(a.P.Q)^v), a.P)
end

function Hecke.gcdx(a::QadicRingElem, b::QadicRingElem)
  if iszero(a)
    c = canonical_unit(b)
    return b*c, a, c
  end
  if iszero(b)
    c = canonical_unit(a)
    return a*c, c, b
  end
  if valuation(a.x) < valuation(b.x)
    c = canonical_unit(a)
    return a*c, c, setprecision(a.P(0), precision(a))
  else
    c = canonical_unit(b)
    return b*c, setprecision(b.P(0), precision(b)), c
  end
end

function Hecke.mul_red!(a::QadicRingElem, b::QadicRingElem, c::QadicRingElem, f::Bool = false)
  return b*c
end

function Hecke.mul!(a::QadicRingElem, b::QadicRingElem, c::QadicRingElem)
  return b*c
end

function Hecke.add!(a::QadicRingElem, b::QadicRingElem, c::QadicRingElem)
  return b+c
end

function Hecke.addeq!(a::QadicRingElem, b::QadicRingElem)
  return a+b
end

Base.iszero(a::QadicRingElem) = iszero(a.x)
Base.isone(a::QadicRingElem) = isone(a.x)

Base.precision(Q::QadicRing) = precision(Q.Q)
Base.precision(a::QadicRingElem) = precision(a.x)
function setprecision!(Q::QadicRing, n::Int) 
  setprecision!(Q.Q, n)
end

function Base.setprecision(a::QadicRingElem, n::Int)
  return a.P(setprecision(a.x, n))
end

function setprecision!(a::QadicRingElem, n::Int)
  setprecision!(a.x, n)
end

function Base.setprecision(a::Generic.MatSpaceElem{QadicRingElem{qadic}}, n::Int)
  return matrix(map(x -> setprecision(x, n), a.entries))
end

Hecke.base_ring(Q::QadicRing) = integers(base_ring(Q.Q))

#########################
#
#########################

mutable struct HenselCtxQadic
  f::PolyElem{qadic}
  lf::Array{PolyElem{qadic}, 1}
  la::Array{PolyElem{qadic}, 1}
  p::qadic
  n::Int
  #TODO: lift over subfields first iff poly is defined over subfield
  function HenselCtxQadic(f::PolyElem{qadic}, lfp::Array{fq_nmod_poly, 1})
    @assert sum(map(degree, lfp)) == degree(f)
    Q = base_ring(f)
    Qx = parent(f)
    K, mK = ResidueField(Q)
    i = 1
    la = Array{PolyElem{qadic}, 1}()
    n = length(lfp)
    while i < length(lfp)
      f1 = lfp[i]
      f2 = lfp[i+1]
      g, a, b = gcdx(f1, f2)
      @assert isone(g)
      push!(la, setprecision(change_base_ring(a, x->preimage(mK, x), Qx), 1))
      push!(la, setprecision(change_base_ring(b, x->preimage(mK, x), Qx), 1))
      push!(lfp, f1*f2)
      i += 2
    end
    return new(f, map(x->setprecision(change_base_ring(x, y->preimage(mK, y), Qx), 1), lfp), la, uniformizer(Q), n)
  end

  function HenselCtxQadic(f::PolyElem{qadic})
    Q = base_ring(f)
    K, mK = ResidueField(Q)
    fp = change_base_ring(f, mK)
    lfp = collect(keys(factor(fp).fac))
    return HenselCtxQadic(f, lfp)
  end
end

function Base.show(io::IO, C::HenselCtxQadic)
  println(io, "Lifting tree for $(C.f), with $(C.n) factors, currently up precision $(valuation(C.p))")
end

function Hecke.lift(C::HenselCtxQadic)
  i = length(C.lf)
  j = i-1
  p = C.p
  N = valuation(p)
  @show map(precision, coefficients(C.f)), N, precision(parent(p))
  @show mx = minimum(precision, coefficients(C.f))
  N2 = min(mx, 2*N)
  @show p = setprecision(p, N2)
  while j > 0
    if i==length(C.lf)
      f = setprecision(C.f, N2)
    else
      f = C.lf[i]
    end
    #formulae and names from the Flint doc
    h = C.lf[j]
    g = C.lf[j-1]
    b = C.la[j]
    a = C.la[j-1]
    setprecision!(h, N2)
    setprecision!(g, N2)
    setprecision!(a, N2)
    setprecision!(b, N2)

    fgh = (f-g*h)*inv(p)
    G = rem(fgh*b, g)*p+g
    H = rem(fgh*a, h)*p+h
    t = (1-a*G-b*H)*inv(p)
    B = rem(t*b, g)*p+b
    A = rem(t*a, h)*p+a
    if i < length(C.lf)
      C.lf[i] = G*H
    end
    C.lf[j-1] = G
    C.lf[j] = H
    C.la[j-1] = A
    C.la[j] = B
    i -= 1
    j -= 2
  end
  @show C.p.val = N2
end

function Hecke.factor(C::HenselCtxQadic)
  return C.lf[1:C.n]
end

function Hecke.precision(C::HenselCtxQadic)
  return valuation(C.p)
end

function Hecke.prime(C::HenselCtxQadic)
  return C.p
end

function lift_root(f::fmpz_poly, a::nf_elem, o::nf_elem, p::fmpz, n::Int)
  #f(a) = 0 mod p, o*f'(a) = 1 mod p, want f(a) = 0 mod p^n
  k = 1
  while k < n
    p *= p
    k *= 2

    pa = [one(a)]
    while length(pa) <= degree(f)
      push!(pa, pa[end]*a)
      mod_sym!(pa[end], p)
    end
    fa  = sum(coeff(f, i-1) * pa[i] for i=1:length(pa))
    fsa = sum(coeff(f, i) * i * pa[i] for i=1:length(pa)-1)  
    o = o*(2-fsa*o)
    a = a - fa*o
    mod_sym!(o, p)
    mod_sym!(a, p)
  end
  return a
end

function completion(K::AnticNumberField, P::NfOrdIdl)
  #non-unique!! will have deg(P) many
  p = minimum(P)
  C = qAdicConj(K, Int(p))
  g = conjugates(P.gen_two.elem_in_nf, C)
  @show map(x->valuation(x), g)
  i = findfirst(x->valuation(x) > 0, g)
  return completion(K, p, i)
end

completion(K::AnticNumberField, p::Integer, i::Int) = completion(K, fmpz(p), i)

function completion(K::AnticNumberField, p::fmpz, i::Int)
  C = qAdicConj(K, Int(p))
  @assert 0<i<= degree(K)

  ca = conjugates(gen(K), C)[i]
  function inj(a::nf_elem)
    return conjugates(a, C, precision(parent(ca)))[i]
  end
  # gen(K) -> conj(a, p)[i] -> a = sum a_i o^i
  # need o = sum o_i a^i
  R, mR = ResidueField(parent(ca))
  pa = [one(R), mR(ca)]
  d = degree(R)
  while length(pa) < d
    push!(pa, pa[end]*pa[2])
  end
  m = matrix(GF(p), d, d, [coeff(pa[i], j-1) for j=1:d for i=1:d])
  o = matrix(GF(p), d, 1, [coeff(gen(R), j-1) for j=1:d])
  s = solve(m, o)
  @assert m*s == o
  a = K()
  for i=1:d
    Hecke._num_setcoeff!(a, i-1, lift(s[i,1]))
  end
  f = defining_polynomial(parent(ca), FlintZZ)
  fso = inv(derivative(f)(gen(R)))
  o = matrix(GF(p), d, 1, [coeff(fso, j-1) for j=1:d])
  s = solve(m, o)
  b = K()
  for i=1:d
    Hecke._num_setcoeff!(b, i-1, lift(s[i,1]))
  end

  c = lift_root(f, a, b, p, 10)
  pc = fmpz(10)
  function lif(x::qadic)
    if iszero(x)
      return K(0)
    end
    if precision(x) > pc
      #XXX this changes (c, pc) inplace as a cache
      #probably should be done with a new map type that can
      #store c, pc on the map.
      d = lift_root(f, a, b, p, precision(x))
      ccall((:nf_elem_set, :libantic), Nothing, (Ref{nf_elem}, Ref{nf_elem}, Ref{AnticNumberField}), c, d, K)
      ccall((:fmpz_set_si, :libflint), Nothing, (Ref{fmpz}, Cint), pc, precision(x))
    elseif precision(x) < pc
      d = Hecke.mod_sym(c, p^precision(x))
    else
      d = c
    end
    n = x.length
    r = K(lift(coeff(x, n-1)))
    while n > 1
      n -= 1
      r = r*d + lift(coeff(x, n-1))
    end
    return r#*K(p)^valuation(x)
  end
  return parent(ca), MapFromFunc(inj, lif, K, parent(ca))
end

function defining_polynomial(Q::FlintQadicField, P::Hecke.Ring = base_ring(Q))
  Pt, t = PolynomialRing(P, cached = false)
  f = Pt()
  for i=0:Q.len-1
    j = unsafe_load(reinterpret(Ptr{Int}, Q.j), i+1)
    a = fmpz()
    ccall((:fmpz_set, :libflint), Nothing, (Ref{fmpz}, Int64), a, Q.a+i*sizeof(Ptr))
    setcoeff!(f, j, P(a))
  end
  return f
end

function defining_polynomial(Q::FqNmodFiniteField, P::Hecke.Ring = GF(characteristic(Q)))
  Pt, t = PolynomialRing(P, cached = false)
  f = Pt()
  for i=0:Q.len-1
    j = unsafe_load(reinterpret(Ptr{Int}, Q.j), i+1)
    a = fmpz()
    ccall((:fmpz_set, :libflint), Nothing, (Ref{fmpz}, Int64), a, Q.a+i*sizeof(Ptr))
    setcoeff!(f, j, P(a))
  end
  return f
end


function reco(a::NfAbsOrdElem, M, pM)
  m = matrix(FlintZZ, 1, degree(parent(a)), coordinates(a))
  m = m - matrix(FlintZZ, 1, degree(parent(a)), map(x -> round(fmpz, x//pM[2]), m*pM[1]))*M
  return parent(a)(collect(m))
end

function reco_inv(a::NfAbsOrdElem, M, pM)
  m = matrix(FlintZZ, 1, degree(parent(a)), coordinates(a))
  m = m - matrix(FlintZZ, 1, degree(parent(a)), map(x -> round(fmpz, x//pM[2]), m*pM[1]))*M
  return parent(a)(collect(m*pM[1]))
end

function reco(a::nf_elem, M, pM)
  m = matrix(FlintZZ, 1, degree(parent(a)), [FlintZZ(coeff(a, i)) for i=0:degree(parent(a))-1])
  m = m - matrix(FlintZZ, 1, degree(parent(a)), map(x -> round(fmpz, x//pM[2]), m*pM[1]))*M
  return parent(a)(parent(parent(a).pol)(collect(m)))
end


function zassenhaus(f::fmpz_poly, P::NfOrdIdl, N::Int)
  return zassenhaus(change_base_ring(f, nf(order(P))), P, N)
end

function zassenhaus(f::fmpq_poly, P::NfOrdIdl, N::Int)
  return zassenhaus(change_base_ring(f, nf(order(P))), P, N)
end

function zassenhaus(f::PolyElem{nf_elem}, P::NfOrdIdl, N::Int)
  K = base_ring(parent(f))
  C, mC = completion(K, P)
  setprecision!(C, N)
  H = HenselCtxQadic(change_base_ring(f, mC))
  while precision(H) < N
    lift(H)
  end

  M = lll(basis_mat(P^N))
  pM = pseudo_inv(M)

  lf = factor(H)
  zk = order(P)

  S = Set(map(x -> change_base_ring(x, y -> preimage(mC, y), parent(f)), lf))
  #TODO: test reco result for being small, do early abort
  #TODO: test selected coefficients first without computing the product
  #TODO: once a factor is found (need to enumerate by size!!!), remove stuff...
  #    : if f is the norm of a poly over a larger field, then every
  #      combination has to respect he prime splitting in the extension
  #      the norm(poly) is the prod of the local norm(poly)s
  #TODO: make subsets for Set
  #TODO: test reco result for being small, do early abort
  #TODO: test selected coefficients first without computing the product
  #TODO: once a factor is found (need to enumerate by size!!!), remove stuff...
  #add/use degree sets and search restrictions. Users might want restricted degrees
  for s = Hecke.subsets(S)
    if length(s) == 0
      continue
    end
    g = prod(s)
    println(g, " -> ", change_base_ring(g, x->reco(zk(x), M, pM)))
  end
end

###############################################
# generic for testing, used for qadics (and maybe padics
# if one chooses a deg 1 prime in the factoring)

#computes the top n coeffs of the product only
function mulhigh_n(a::PolyElem{T}, b::PolyElem{T}, n::Int) where {T}
  #sum a_i t^i and sum b_j t^j
  #want (i,j) s.th. i+j >= deg a + deg b - n
  r = parent(a)()
  for i=max(degree(a)-n, 0):degree(a)
    for j = max(degree(a) + degree(b) - n - i, 0):degree(b)
      setcoeff!(r, i+j, coeff(r, i+j) + coeff(a, i)*coeff(b, j))
    end
  end
  return r
end

function mulhigh_n(a::fmpz_poly, b::fmpz_poly, n::Int)
  c = parent(a)()
  #careful: as part of the interface, the coeffs 0 - (n-1) are random garbage
  ccall((:fmpz_poly_mulhigh_n, :libflint), Nothing, (Ref{fmpz_poly}, Ref{fmpz_poly}, Ref{fmpz_poly}, Cint), c, a, b, n)
  return c
end
function mulhigh(a::PolyElem{T}, b::PolyElem{T}, n::Int) where {T} 
  return mulhigh_n(a, b, degree(a) + degree(b) - n)
end

#assuming b divides a, compute the last n coeffs of the quotient
#will produce garbage otherwise
#div(a, b) mod x^n
function divexact_low(a::PolyElem{T}, b::PolyElem{T}, n::Int) where {T}
  r = parent(a)()
  a = truncate(a, n)
  b = truncate(b, n)
  for i=0:n-1
    q = divexact(constant_coefficient(a), constant_coefficient(b))
    setcoeff!(r, i, q)
    a = shift_right(a-q*b, 1)
    #truncate both a and b to n-i-1 (for generic polys one could just change the length)
  end
  return r
end

#computes the top coeffs starting with x^n
function divhigh(a::PolyElem{T}, b::PolyElem{T}, n::Int) where {T}
  r = parent(a)()
  n = degree(a) - degree(b) - n
  for i=0:n
    if degree(a) < degree(b)
      break
    end
    q = divexact(lead(a), lead(b))
    setcoeff!(r, degree(a) - degree(b), q)
    a = a-q*shift_left(b, degree(a) - degree(b)) # inplace, one operation would be cool
  end
  return r
end
###############################################
function cld_bound(f::PolyElem{nf_elem}, k::Array{Int, 1})
  @assert all(kk -> 0 <= kk < degree(f), k)
  Zx, x = PolynomialRing(FlintZZ, cached = false)
  g = Zx()
  for i=0:degree(f)
    setcoeff!(g, i, Hecke.upper_bound(sqrt(t2(coeff(f, i))), fmpz))
  end
  bb = fmpz[]
  for kk = k
    b = FlintZZ()
    ccall((:fmpz_poly_CLD_bound, :libflint), Nothing, (Ref{fmpz}, Ref{fmpz_poly}, Int64), b, g, kk)
    push!(bb, b)
  end
  return bb
end
cld_bound(f::PolyElem{nf_elem}, k::Int) = cld_bound(f, [k])[1]

function cld_bound(f::fmpz_poly, k::Int)
  @assert 0 <= k < degree(f)
  b = FlintZZ()
  ccall((:fmpz_poly_CLD_bound, :libflint), Nothing, (Ref{fmpz}, Ref{fmpz_poly}, Int64), b, f, k)
  return b
end
cld_bound(f::fmpz_poly, k::Array{Int, 1}) = map(x->cld_bound(f, x), k)

Base.log2(a::fmpz) = log2(BigInt(a))

function initial_prec(f::PolyElem{nf_elem}, p::Int, r::Int = degree(f))
  b = minimum(cld_bound(f, [0,degree(f)-2])) #deg(f)-1 will always be deg factor
  a = ceil(Int, (2.5*r*degree(base_ring(f))+log2(b) + log2(degree(f))/2)/log2(p))
  return a
end

function cld_data(H::HenselCtxQadic, up_to::Int, from::Int, mC, Mi)
  lf = factor(H)
  a = preimage(mC, zero(codomain(mC)))
  k = parent(a)
  N = degree(H.f)
  @assert 0<= up_to <= N  #up_tp: modulo x^up_tp
  @assert 0<= from <= N   #from : div by x^from
#  @assert up_to <= from

  M = zero_matrix(FlintZZ, length(lf), (1+up_to + N - from) * degree(k))

  lf = [divexact_low(mullow(derivative(x), H.f, up_to), x, up_to) for x = lf]

  NN = zero_matrix(FlintZZ, 1, degree(k))
  d = FlintZZ()
  for i=0:up_to
    for j=1:length(lf)
      c = preimage(mC, coeff(lf[j], i)) # should be an nf_elem
      elem_to_mat_row!(NN, 1, d, c)
      mul!(NN, NN, Mi) #base_change, Mi should be the inv-lll-basis-mat wrt field
      @assert isone(d)
      for h=1:degree(k)
        M[j, i*degree(k) + h] = NN[1, h]
      end
    end
  end
  lf = factor(H)
  lf = [divhigh(mulhigh(derivative(x), H.f, from), x, from) for x = lf]
  for i=from:N-1
    for j=1:length(lf)
      c = preimage(mC, coeff(lf[j], i)) # should be an nf_elem
      elem_to_mat_row!(NN, 1, d, c)
      mul!(NN, NN, Mi) #base_change, Mi should be the inv-lll-basis-mat wrt field
      @assert isone(d)
      for h=1:degree(k)
        M[j, (i-from+up_to)*degree(k) + h] = NN[1, h]
      end
    end
  end
  return M
end

function van_hoeij(f::fmpz_poly, P::NfOrdIdl, N::Int)
  return van_hoeij(change_base_ring(f, nf(order(P))), P, N)
end

function van_hoeij(f::fmpq_poly, P::NfOrdIdl, N::Int)
  return van_hoeij(change_base_ring(f, nf(order(P))), P, N)
end

mutable struct vanHoeijCtx
  H::HenselCtxQadic
  pr::Int
  Ml::fmpz_mat
  pMr::Tuple{fmpz_mat, fmpz}
  pM::Tuple{fmpz_mat, fmpz}
  C::FlintQadicField
  P::NfOrdIdl
  function vanHoeijCtx()
    return new()
  end
end

function grow_prec!(vH::vanHoeijCtx, pr::Int)
  while precision(vH.H) < pr
    lift(vH.H)
  end
  @show precision(vH.H.p), valuation(vH.H.p)
  @show vH.H.lf[1]

  vH.Ml = lll(basis_mat(vH.P^pr))
  vH.pMr = pseudo_inv(vH.Ml)
  F = FakeFmpqMat(vH.pMr)
  #M * basis_mat(zk) is the basis wrt to the field
  #(M*B)^-1 = B^-1 * M^-1, so I need basis_mat_inv(zk) * pM
  vH.pMr = (F.num, F.den)
  F = basis_mat_inv(order(vH.P)) * F
  vH.pM = (F.num, F.den)
end


function van_hoeij(f::PolyElem{nf_elem}, P::NfOrdIdl; prec_scale = 20)
  K = base_ring(parent(f))
  C, mC = completion(K, P)

  _, mK = ResidueField(order(P), P)
  mK = extend(mK, K)
  @show r = length(factor(change_base_ring(f, mK)))
  @show N = degree(f)

  setprecision!(C, 5)

  vH = vanHoeijCtx()
  vH.H = HenselCtxQadic(change_base_ring(f, mC))
  @show vH.H.lf[1], vH.H.p
  vH.C = C
  vH.P = P

  up_to = max(5, ceil(Int, N/10))
  from = N-up_to  #use 5 coeffs on either end
  up_to = min(up_to, N)
  from = min(from, N)
  from = max(up_to, from)
  b = cld_bound(f, vcat(0:up_to-1, from:N-1))

  # from Fieker/Friedrichs, still wrong here
  # needs to be larger than anticipated...
  c1, c2 = Hecke.norm_change_const(order(P))
  @show b = [ceil(Int, degree(K)/2/degree(P)*(log2(c1*c2) + 2*nbits(x)+ prec_scale)) for x = b]

  used = []
  really_used = []
  have = vcat(0:up_to-1, from:N-2)  #N-1 is always 1
  M = identity_matrix(FlintZZ, r)*2^prec_scale

  while true #the main loop
    #find some prec
    #to start with, I want at least half of the CLDs to be useful
    i= sort(b)[up_to] # minimal expo to recover CLD
    println("setting prec to $i, and lifting the info ...")
    setprecision!(codomain(mC), i)
    vH.H.f = change_base_ring(f, mC)
    @time grow_prec!(vH, i)

   
    av_bits = sum(nbits, vH.Ml)/degree(K)^2
    println("obtaining CLDs...")
    @time C = cld_data(vH.H, up_to, from, mC, vH.pM[1]) 

    # In the end, p-adic precision needs to be large enough to
    # cover some CLDs. If you want the factors, it also has to 
    # cover those. The norm change constants also come in ...
    # and the degree of P...

    # starting precision:
    # - large enough to recover factors (maybe)
    # - large enough to recover some CLD (definitely)
    # - + eps to give algo a chance.
    # Then take 10% of the CLD, small enough for the current precision
    # possibly figure out which CLD's are available at all

    # we want
    # I |  C/p^n
    # 0 |   I
    # true factors, in this lattice, are small (the lower I is the rounding)
    # the left part is to keep track of operations
    # by cld_bound, we know the expected upper size of the rounded legal entries
    # so we scale it by the bound. If all would be exact, the true factors would be zero...
    # 1st make integral:
    # I | C
    # 0 | p^n
    # scale:
    # I | C/lambda
    # 0 | p^n/lambda  lambda depends on the column
    # now, to limit damages re-write the rationals with den | 2^k (rounding)
    # I | D/2^k
    #   | X/2^k
    #make integral
    # 2^k | D
    #  0  | X   where X is still diagonal
    # is all goes like planned: lll with reduction will magically work...
    # needs (I think): fix a in Z_k, P and ideal. Then write a wrt. a LLL basis of P^k
    #  a = sum a^k_i alpha^k_i, a^k_i in Q, then for k -> infty, a^k_i -> 0
    #  (ineffective: write coeffs with Cramer's rule via determinants. The
    #  numerator has n-1 LLL-basis vectors and one small vector (a), thus the
    #  determinant is s.th. ^(n-1) and the coeff then ()^(n-1)/()^n should go to zero
    # lambda should be chosen, so that the true factors become < 1 by it
    # for the gradual feeding, we can also add the individual coefficients (of the nf_elems) individually


    # - apply transformations already done (by checking the left part of the matrix)
    # - scale, round
    # - call lll_with_removel
    # until done (whatever that means)
    # if unlucky: re-do Hensel and start over again, hopefull retaining some info
    # can happen if the CLD coeffs are too large for the current Hensel level
    st = 1
    while length(have) > length(used)
      if isodd(st)
        n = minimum(setdiff(have, used))
        push!(used, n)
      else
        n = maximum(setdiff(have, used))
        push!(used, n)
      end
      st += 1
      i = findfirst(x->x == n, have) #new data will be in block i of C
      println("trying to use coeff $n which is $i")
      if b[i] > precision(codomain(mC))
        @show "not enough precisino for CLD ", i
        continue
      end
      sz = floor(Int, degree(K)*av_bits/degree(P) - b[i])

      B = sub(C, 1:r, (i-1)*degree(K)+1:i*degree(K))
      @show i, maximum(nbits, B)
      
      T = sub(M, 1:nrows(M), 1:r)
      B = T*B   # T contains the prec_scale 
      mod_sym!(B, vH.pM[2]*fmpz(2)^prec_scale)
      @show maximum(nbits, B), nbits(vH.pM[2]), b[i]
      if sz + prec_scale >= nbits(vH.pM[2]) || sz < 0
        println("loss of precision for this col: ", sz, " ", nbits(pM[2]))
        continue
      else
        sz = nbits(vH.pM[2]) - 2 * prec_scale
      end
      push!(really_used, n)
      @show sz, nbits(vH.pM[2])
      ccall((:fmpz_mat_scalar_tdiv_q_2exp, :libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Cint), B, B, sz)
      s = max(0, sz - prec_scale)
      d = tdivpow2(vH.pM[2], s)
      M = [M B; zero_matrix(FlintZZ, ncols(B), ncols(M)) d*identity_matrix(FlintZZ, ncols(B))]
  #    @show map(nbits, Array(M))
      @show maximum(nbits, Array(M))
      @time l, M = lll_with_removal(M, r*fmpz(2)^(2*prec_scale) + div(r+1, 2)*N*degree(K))
      @show l, i# , map(nbits, Array(M))
  #    @show hnf(sub(M, 1:l, 1:r))
      @assert !iszero(sub(M, 1:l, 1:r))
      M = sub(M, 1:l, 1:ncols(M))
      d = Dict{fmpz_mat, Array{Int, 1}}()
      for l=1:r
        k = M[:, l]
        if haskey(d, k)
          push!(d[k], l)
        else
          d[k] = [l]
        end
      end
      @show values(d)
      if length(keys(d)) <= nrows(M)
        @show "BINGO", length(keys(d)), "factors"
        res = typeof(f)[]
        fail = []
        if length(keys(d)) == 1
          @show "irreducible!!!"
          return [f]
        end
        display(d)
        for v = values(d)
          #trivial test:
          a = prod(map(constant_coefficient, factor(vH.H)[v]))
          A = K(reco(order(P)(preimage(mC, a)), vH.Ml, vH.pMr))
          if denominator(divexact(constant_coefficient(f), A), order(P)) != 1
            push!(fail, v)
            @show "fail", v
            if length(fail) > 1
              break
            end
            continue
          end
          g = prod(factor(vH.H)[v])
          G = parent(f)([K(reco(order(P)(preimage(mC, coeff(g, l))), vH.Ml, vH.pMr)) for l=0:degree(g)])

          if !iszero(rem(f, G))
            push!(fail, v)
            @show "fail2", v
            if length(fail) > 1
              break
            end
            continue
          end
          @show "success", G
          push!(res, G)
        end
        if length(fail) == 1
          @show "only one reco failed, total success"
          return res
        end
        if length(res) < length(d)
          @show "... here we go again ..."
        else
          return res
        end
      end
    end
    @show used, have, really_used

    up_to = min(2*up_to, N)
    from = N-up_to 
    from = min(from, N)
    from = max(up_to, from)

    have = vcat(0:up_to-1, from:N-2)  #N-1 is always 1
    if length(have) <= length(really_used)
      error("too bad")
    end
    used = deepcopy(really_used)

    b = cld_bound(f, vcat(0:up_to-1, from:N-1))

    # from Fieker/Friedrichs, still wrong here
    # needs to be larger than anticipated...
    @show b = [ceil(Int, degree(K)/2/degree(P)*(log2(c1*c2) + 2*nbits(x)+ prec_scale)) for x = b]
  end #the big while
end

function Hecke.mod_sym!(M::fmpz_mat, B::fmpz)
  @assert !iszero(B)
  ccall((:fmpz_mat_scalar_smod, :libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{fmpz}), M, M, B)
end
Hecke.mod_sym!(M::fmpz_mat, B::Integer) = mod_sym!(M, fmpz(B))

function Hecke.mod_sym(M::fmpz_mat, B::fmpz)
  N = zero_matrix(FlintZZ, nrows(M), ncols(M))
  ccall((:fmpz_mat_scalar_smod, :libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{fmpz}), N, M, B)
  return N
end
Hecke.mod_sym(M::fmpz_mat, B::Integer) = mod_sym(M, fmpz(B))

function map!(f, M::fmpz_mat)
  for i=1:nrows(M)
    for j=1:ncols(M)
      M[i,j] = f(M[i,j])
    end
  end
end

#does not seem to be faster than the direct approach. (not modular)
#Magma is faster, which seems to suggest the direct resultant is
#even better (modular resultant)
# power series over finite fields are sub-par...or at least this usage
# fixed "most" of it...
function norm_mod(f::PolyElem{nf_elem}, Zx)
  p = Hecke.p_start
  K = base_ring(f)

  g = Zx(0)
  d = fmpz(1)

  while true
    p = next_prime(p)
    k = GF(p)
    me = modular_init(K, p)
    t = Hecke.modular_proj(f, me)
    tt = lift(Zx, Hecke.power_sums_to_polynomial(sum(map(x -> map(y -> k(coeff(trace(y), 0)), Hecke.polynomial_to_power_sums(x, degree(f)*degree(K))), t))))
    prev = g
    if isone(d)
      g = tt
      d = fmpz(p)
    else
      g, d = induce_crt(g, d, tt, fmpz(p), true)
    end
    if prev == g
      return g
    end
    if nbits(d) > 2000
      error("too bad")
    end
  end
end

new_load = true
function cc()
  global new_load = true
end

end

set_printing_mode(FlintPadicField, :terse)
#=
  Daniel:
  let a_i be a linear recurrence sequence or better
    sum_1^infty a_i x^-i = -f/g is rational, deg f<deg g < n/2
    run rational reconstruction on h := sum_0^n a_i x^(n-i) and x^n
    finding bh = a mod x^n (h = a/b mod x^n)
    then b = g and f = div(a-bh, x^n)
    establishing the link between rat-recon and Berlekamp Massey

=#    
