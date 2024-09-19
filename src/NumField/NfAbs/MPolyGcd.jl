function gcd(f::Hecke.Generic.MPoly{<:NumFieldElem}, g::Hecke.Generic.MPoly{<:NumFieldElem})
  R = parent(f)
  K = coefficient_ring(f)
  Kabs, KabstoK, KtoKabs = _absolute_simple_field_internal(K)
  fabs = map_coefficients(KtoKabs, f; cached = false)
  S = parent(fabs)
  gabs = map_coefficients(KtoKabs, g, parent = S)
  return map_coefficients(KabstoK, gcd(fabs, gabs), parent = R)
end

####################################################
# exported is the RecoCtx (and thus the rational_reconstruction functions)
# not exported are the helpers...

module RecoNF

using ..Hecke

import Hecke.Nemo

function basis_matrix(d::ZZRingElem, f::ZZPolyRingElem, k::AbsSimpleNumField)
  #assumes f is idl as above!!!
  #1st need to deconstruct f into the different degrees:
  #CRT of degree a>b and implies leading_coefficient(b) = 0 mod q, hence gcd's are my friend
  #claim: in this situation, the "obvious" method will produce a Howell form
  #tries to compute the basis matrix for the ideal <d, f(a)> where a = gen(k)
  #assumes deg f < deg k, d coprime to the conductor/ index/ everything
  de = []
  g = d
  N = zero_matrix(FlintZZ, degree(k), degree(k))
  dN = ZZRingElem(1)
  res = []
  f_orig = f
  d_orig = d
  for i=degree(f):-1:1
    if degree(f)<i
      continue
    end
    r = Base.gcd(coeff(f, i), g)
    #so I have <d/r, f> of degree i and
    #          <f, f mod r> of smaller degree
    n = div(g, r)
    c = invmod(leading_coefficient(f), n)
    fn = mod(c*f, n)
    @assert is_monic(fn)
    @assert degree(fn) == i
    if degree(f) == degree(k)
      M = matrix_space(FlintZZ, degree(k), degree(k))(n)
    else
      M = zero_matrix(FlintZZ, degree(k), degree(k))
      for j=1:i
        M[j,j] = n
      end
      for j=1:degree(fn)+1
        M[i+1, j] = coeff(fn, j-1)
      end
      t = gen(parent(fn))^i-fn
      for j=i+2:degree(k)
        t = t*gen(parent(fn))
        t -= leading_coefficient(t)*fn
        mod!(t, n)
        M[j,j] = 1
        for k=1:j-1
          M[j, k] = -coeff(t, k-1)
        end
      end
    end
    if dN == 1
      N = M
      dN = n
    else
      N, dN = induce_crt(N, dN, M, n)
    end
    f = mod(f, r)
    g = r
    if isone(g)
      break
    end
  end
  #TODO: implement the Fieker-Hofmann lifting step to avoid the hnf...
  N = Hecke._hnf_modular_eldiv(N, dN, :lowerleft)
  return N
end

export RecoCtx

mutable struct RecoCtx
  L::ZZMatrix  # should be LLL reduced, will do so on creation
  p1::ZZRingElem     # the "prime": L is the basis matrix of an ideal, p1 is the
               # minimum
  f::ZZPolyRingElem # the implicit ideal is <p1, f(gen(k))>
  LI::ZZMatrix #(Li, d) = pseudo_inv(L) - if set (integral = true)
  d::ZZRingElem
  k::AbsSimpleNumField
  new_data::Bool
  function RecoCtx(A::ZZMatrix, k::AbsSimpleNumField)
    r= new()
    r.k = k
    r.L = lll(A)
    r.p1 = det(A)
    r.new_data = false
    return r
  end
  function RecoCtx(k::AbsSimpleNumField)
    r = new()
    r.L = identity_matrix(FlintZZ, degree(k))
    r.p1 = ZZRingElem(1)
    r.k = k
    r.new_data = false
    return r
  end
end

function Base.push!(R::RecoCtx, p::ZZRingElem, f::ZZPolyRingElem)
  @assert gcd(R.p1, p) == 1

  if R.p1 == 1
    R.f = f
    R.p1 = p
  else
    R.f, R.p1 = induce_crt(R.f, R.p1, f, p)
  end
  R.new_data = true
end

function data_assure(R::RecoCtx)
  R.new_data || return

  R.L = lll(basis_matrix(R.p1, R.f, R.k))
  if isdefined(R, :LI) #to keep structure consistent
    R.LI, R.d = pseudo_inv(R.L)
  end
  R.new_data = false
  return R
end

function has_small_coeffs(a::AbsSimpleNumFieldElem, B::ZZRingElem)
  z = ZZRingElem()
  for i=0:degree(parent(a))-1
    Nemo.num_coeff!(z, a, i)
    if cmpabs(z, B) >0
      return false
    end
  end
  return true
end

function Hecke.induce_rational_reconstruction(a::Generic.MPoly{AbsSimpleNumFieldElem}, R::RecoCtx; integral::Bool = false)
  b = MPolyBuildCtx(parent(a))
  k = base_ring(a)
  d = k(2)
  if integral
    B = ZZRingElem(1)
  else
    B = abs(det(R.L))
    B = ZZRingElem(2)^div(nbits(B), 2*degree(k))
  end
  for i=1:length(a)
    if integral
      fl, c = rational_reconstruction(coeff(a, i), R, integral = integral)
      if !fl
        return fl, a
      end
    else
      #implicitly assumes elements have a common denominator
      fl, c = rational_reconstruction(coeff(a, i)*d, R, integral = true)
      if !fl || !has_small_coeffs(c, B)
        fl, c, dd = rational_reconstruction(coeff(a, i)*d, R, integral = false, split = true)
        !fl && return fl, a
        (has_small_coeffs(c, B) && has_small_coeffs(d*dd, B)) || return false, a
        d *= dd
      end
      c = c//d
    end
    push_term!(b, c, exponent_vector(a, i))
  end
  return true, finish(b)
end

#TODO: split needs to be a val-arg
function Hecke.rational_reconstruction(a::AbsSimpleNumFieldElem, R::RecoCtx; integral::Bool = false, split::Bool = false)
  data_assure(R)
  if integral
    if !isdefined(R, :LI)
      R.LI, R.d = pseudo_inv(R.L)
    end
    t = zero_matrix(FlintZZ, 1, degree(R.k))
    z = ZZRingElem()
    for i=1:degree(R.k)
      Nemo.num_coeff!(z, a, i-1)
      t[1, i] = z
    end
    s = t*R.LI
    for i=1:degree(R.k)
      s[1, i] = round(ZZRingElem, s[1, i], R.d)
    end
    tt = mul!(s, s, R.L)
    b = parent(a)()
    nb = div(3*nbits(R.d), 2)
    for i=1:degree(R.k)
      Hecke._num_setcoeff!(b, i-1, t[1, i]-tt[1, i])
      nb -= nbits(t[1, i] - tt[1, i])
    end
    return nb >= 0, b
  end
  n = degree(parent(a))
  Znn = matrix_space(FlintZZ, n, n)
  L = [ Znn(1) representation_matrix_q(a)[1] ; Znn(0) R.L]
  lll!(L)
  K = parent(a)
  d = Nemo.elem_from_mat_row(K, sub(L, 1:1, 1:n), 1, ZZRingElem(1))
  n = Nemo.elem_from_mat_row(K, sub(L, 1:1, n+1:2*n), 1, ZZRingElem(1))
  if split
    return true, n, d
  else
    return true, n//d
  end
end

end  #RecoNF module

using .RecoNF

module MPolyGcd

using Hecke
import Nemo, Nemo.zzModMPolyRingElem, Nemo.zzModMPolyRing
import AbstractAlgebra
import Hecke.RecoCtx

function Hecke.gcd(f::Hecke.Generic.MPoly{AbsSimpleNumFieldElem}, g::Hecke.Generic.MPoly{AbsSimpleNumFieldElem})
  # Recognize rational polynomials
  K = coefficient_ring(f)
  if all(is_rational, coefficients(f)) && all(is_rational, coefficients(g))
    fQQ = map_coefficients(QQ, f, cached = false)
    S = parent(fQQ)
    gQQ = map_coefficients(QQ, g, parent = S)
    gcdQQ = gcd(fQQ, gQQ)
    if is_one(gcdQQ)
      return one(parent(f))
    end
    return map_coefficients(K, gcdQQ, parent = parent(f))
  end

  return _gcd(f, g, :degree_one)
end

function _gcd(f::Hecke.Generic.MPoly{AbsSimpleNumFieldElem}, g::Hecke.Generic.MPoly{AbsSimpleNumFieldElem}, strategy::Symbol = :degree_one)
  # use :degree_one or :lazy
  Hecke.check_parent(f, g)
  @vprintln :MPolyGcd 1 "multivariate gcd of f with $(length(f)) and g with $(length(g)) terms over $(base_ring(f))"

  k = base_ring(f)
  ps = PrimesSet(Hecke.p_start, -1)
  fl, c = Hecke.is_cyclotomic_type(k)
  if fl
    @vprintln :MPolyGcd 2 "field is cyclotomic with conductor $c"
    ps = PrimesSet(Hecke.p_start, -1, c, 1)
  end
  fl, c = Hecke.is_quadratic_type(k)
  if fl && abs(c) < typemax(Int)
    @vprintln :MPolyGcd 2 "field is quadratic, using conductor $(4*c)"
    ps = PrimesSet(Hecke.p_start, -1, Int(4*c), 1)
  end
  return __gcd(f, g, ps, strategy)
end

function __gcd(f::Hecke.Generic.MPoly{AbsSimpleNumFieldElem}, g::Hecke.Generic.MPoly{AbsSimpleNumFieldElem}, ps::PrimesSet{Int}, strategy = :degree_one)
#  @show "gcd start"
  lazy = strategy == :lazy
  p = iterate(ps)[1]
  K = base_ring(f)
  max_stable = 2
  stable = max_stable

  if iszero(f)
    return g
  end
  if iszero(g)
    return f
  end

  # compute deflation and deflate
  shifta, defla = Generic.deflation(f)
  shiftb, deflb = Generic.deflation(g)
  shiftr = min.(shifta, shiftb)
  deflr = broadcast(gcd, defla, deflb)
  f = deflate(f, shifta, deflr)
  g = deflate(g, shiftb, deflr)

  d = ZZRingElem(1)
  gc = parent(f)()
  gd = parent(f)()
  Zx = Hecke.Globals.Zx
  R = RecoCtx(K)

  E = any_order(K)
  de = lcm(lcm(map(c -> denominator(c, E), coefficients(f))),
           lcm(map(c -> denominator(c, E), coefficients(g))))

  f*=de
  g*=de
  lI = E*E(leading_coefficient(f)) + E*E(leading_coefficient(g))
  gl = Hecke.short_elem(lI)
  gl *= evaluate(derivative(K.pol), gen(K))  # use Kronnecker basis

  fl = true
  cnt = 0
  while true
    p = iterate(ps, p)[1]
    cnt += 1
    if cnt > 1000
      error("ASDA")
    end
    @vprintln :MPolyGcd 2 "Main loop: using $p"
    if lazy
      @vtime :MPolyGcd 3 me = Hecke.modular_init(K, p, lazy = lazy)
    else
      @vtime :MPolyGcd 3 me = Hecke.modular_init(K, p, deg_limit = 1)
    end
    if isempty(me)
      continue
    end

    if lazy
      @vtime :MPolyGcd 3 fp = Hecke.modular_proj(fqPolyRepFieldElem, f, me)
      @vtime :MPolyGcd 3 gp = Hecke.modular_proj(fqPolyRepFieldElem, g, me)
      glp = Hecke.modular_proj(gl, me)
      _gcd_p = fqPolyRepMPolyRingElem[]
      local __g::fqPolyRepMPolyRingElem
      try
        __g = gcd(fp[1], gp[1])
      catch e
        if !(e isa ErrorException) || e.msg != "Problem in the Flint-Subsystem"
          rethrow(e)
        end
        continue
      end
      if length(__g) == 1 && iszero(exponent_vector(_g, 1))
        return inflate(one(parent(f)), shiftr, deflr)
      end
      push!(_gcd_p, glp[1]*__g)
      @vtime :MPolyGcd 3 tp = Hecke.modular_lift(_gcd_p, me)
    else
      @vtime :MPolyGcd 3 fp = Hecke.modular_proj(f, me)
      @vtime :MPolyGcd 3 gp = Hecke.modular_proj(g, me)
      glp = Hecke.modular_proj(gl, me)
      gcd_p = zzModMPolyRingElem[]
      @vtime :MPolyGcd 3 for i=1:length(fp)
        _g = gcd(fp[i], gp[i])
        if length(_g) == 1 && iszero(exponent_vector(_g, 1))
          return inflate(one(parent(f)), shiftr, deflr)
        end
        push!(gcd_p, coeff(glp[i], 0)*_g)
      end
      @vtime :MPolyGcd 3 tp = Hecke.modular_lift(gcd_p, me)
    end
    #gcd_p = [coeff(glp[i], 0)*gcd(fp[i], gp[i]) for i=1:length(fp)]
    if isone(d)
      d = ZZRingElem(p)
      gc = tp
      idl = lift(Zx, me.ce.pr[end])
      push!(R, d, idl)
      fl, gd = induce_rational_reconstruction(gc, R, integral = true)
      if fl && divides(f, gd)[1] && divides(g, gd)[1]
#          @show "gcd stop", nbits(d), length(gd), gd
#          @time fl, q = divides(f, gd)
#          @time q = div(f, gd)
#          @time q*gd == f
          gd*=inv(gl)
          @assert isone(leading_coefficient(gd))
          return inflate(gd, shiftr, deflr)
      end
      stable = max_stable
    else
      #TODO: instead of lifting "idl" and doing basis_matrix from
      #      scratch, do the basis_matrix for the new ideal and
      #      use CRT to combine them
      #TODO: explore combining LLL matrices to speed up LLL....
#TODO: deal with bad primes...

      push!(R, ZZRingElem(p), lift(Zx, me.ce.pr[end]))
      _check = any(let me = me, gd = gd, tp = tp; i -> (parent(me.ce.pr[end])(coeff(tp, i) - coeff(gd, i))) % me.ce.pr[end] != 0 end, 1:length(tp))

      if (!fl) || _check
        gc, d = induce_crt(gc, d, tp, ZZRingElem(p), true)
        fl, gd = induce_rational_reconstruction(gc, R, integral = true)
        stable = max_stable
      else
        d *= p
        stable -= 1
      end
        if fl && stable <= 0
          if divides(f, gd)[1] && divides(g, gd)[1]
#            @show "gcd stop", nbits(d), length(gd), gd
            gd*=inv(gl)
            @assert isone(leading_coefficient(gd))
            return inflate(gd, shiftr, deflr)
          else
            stable = max_stable
          end
        end
      #before I forget: gc is "the" gcd modulo <d, idl>
    end
  end
end

function Hecke.induce_crt(a::Hecke.Generic.MPoly{AbsSimpleNumFieldElem}, p::ZZRingElem, b::Hecke.Generic.MPoly{AbsSimpleNumFieldElem}, q::ZZRingElem, signed::Bool = false)
  pi = invmod(p, q)
  mul!(pi, pi, p)
  pq = p*q
  if signed
    pq2 = div(pq, 2)
  else
    pq2 = ZZRingElem(0)
  end
  z = zero(base_ring(a))

  #=
  c = (b-a)*pi+a
  mod!(c, pq)
  return c
  =#

  N = ngens(parent(a))

  ta = terms(a)
  tb = terms(b)
  c = MPolyBuildCtx(parent(a))
  aa = iterate(ta)
  if !(aa === nothing)   # allow a to be zero
    aa, sa = aa
  end
  bb = iterate(tb)
  if !(bb === nothing)   # also allow b to be zero
    bb, sb = bb
  end
#  @assert length(a) == length(b)
#  @assert ==(aa, bb, true) # leading terms must agree or else...
  while !(aa === nothing) && !(bb === nothing)
    if ==(aa.exps, bb.exps) #monomial equality
      push_term!(c, Hecke.induce_inner_crt(coeff(aa, 1), coeff(bb, 1), pi, pq, pq2), exponent_vector(aa, 1))
      aa = iterate(ta, sa)
      bb = iterate(tb, sb)
      aa === nothing && break
      aa, sa = aa
      bb === nothing && break
      bb, sb = bb
    elseif Generic.monomial_isless(aa.exps, 1, bb.exps, 1, N, parent(aa), UInt(0)) #aa < bb
      push_term!(c, Hecke.induce_inner_crt(z, coeff(bb, 1), pi, pq, pq2), exponent_vector(bb, 1))
      bb, sb = iterate(tb, sb)
      bb === nothing && break
      bb, sb = bb
    else
      push_term!(c, Hecke.induce_inner_crt(coeff(aa, 1), z, pi, pq, pq2), exponent_vector(aa, 1))
      aa = iterate(ta, sa)
      aa === nothing && break
      aa, sa = aa
    end
  end
  while !(aa === nothing)
    push_term!(c, Hecke.induce_inner_crt(coeff(aa, 1), z, pi, pq, pq2), exponent_vector(aa, 1))
    aa = iterate(ta, sa)
    if !aa === nothing
      aa, sa = aa
    end
  end
  while !(bb === nothing)
    push_term!(c, Hecke.induce_inner_crt(z, coeff(bb, 1), pi, pq, pq2), exponent_vector(bb, 1))
    bb = iterate(tb, sb)
    if !(bb === nothing)
      bb, sb = bb
    end
  end
  return finish(c), pq
end

function Hecke.induce_crt(a::ZZMatrix, p::ZZRingElem, b::ZZMatrix, q::ZZRingElem, signed::Bool = false)
  pi = invmod(p, q)
  mul!(pi, pi, p)
  pq = p*q
  if signed
    pq2 = div(pq, 2)
  else
    pq2 = ZZRingElem(0)
  end

  @assert size(a) == size(b)
  c = similar(a)
  for i=1:nrows(a)
    for j=1:ncols(a)
      c[i,j] = Hecke.inner_crt(a[i,j], b[i,j], pi, pq, pq2)
    end
  end
  return c, pq
end

function Hecke.modular_proj(f::Generic.MPoly{AbsSimpleNumFieldElem}, me::Hecke.modular_env)
  if !isdefined(me, :Kxy)
    me.Kxy = parent(f)
  else
    @assert me.Kxy === parent(f)
  end
  if !isdefined(me, :Kpxy)
    p = characteristic(me.Fpx)
    me.Kpxy, _ = polynomial_ring(base_ring(me.Fpx), ["$(x)_$p" for x = me.Kxy.S])
  end
  fp = [MPolyBuildCtx(me.Kpxy) for x = me.fld]
  s = length(me.fld)
  R = base_ring(me.Fpx)
  for (c, e) in zip(coefficients(f), exponent_vectors(f))
    cp = Hecke.modular_proj(c, me)
    for x = 1:s
      push_term!(fp[x], Hecke.zzModRingElem(coeff(cp[x], 0), R), e)
    end
  end
  return map(finish, fp)
end

function Hecke.modular_proj(::Type{fqPolyRepFieldElem}, a::Generic.MPoly{AbsSimpleNumFieldElem}, me::Hecke.modular_env)
  Kxy = parent(a)
  if !isdefined(me, :Kxy)
    me.Kxy = Kxy
  else
    @assert me.Kxy === parent(a)
  end
  vars = map(string, symbols(Kxy))
  s = length(me.fld)
  res = [MPolyBuildCtx(polynomial_ring(me.fld[i], vars)[1]) for i in 1:s]
  for (c, v) in zip(coefficients(a), exponent_vectors(a))
    cp = Hecke.modular_proj(c, me)
    for i in 1:s
      push_term!(res[i], deepcopy(cp[i]), v)
    end
  end
  map(finish, res)
end



function Hecke.modular_lift(g::Vector{zzModMPolyRingElem}, me::Hecke.modular_env)

  #TODO: no dict, but do s.th. similar to induce_crt
  d = Dict{Vector{Int}, Vector{Tuple{Int, zzModRingElem}}}()
  for i=1:length(g)
    for (c, e) = zip(coefficients(g[i]), exponent_vectors(g[i]))
      if Base.haskey(d, e)
        push!(d[e], (i, c))
      else
        d[e] = [(i, c)]
      end
    end
  end
  bt = MPolyBuildCtx(me.Kxy)

  for e = keys(d)
    for x=1:length(g)
      me.res[x] = zero!(me.res[x])
    end
    for (i, c) = d[e]
      me.res[i] = parent(me.res[i])(lift(c))
    end
    push_term!(bt, Hecke.modular_lift(me.res, me), e)
  end
  return finish(bt)

  bt = MPolyBuildCtx(me.Kxy)
  #TODO deal with different vectors properly (check induce_crt)
  @assert all(x->collect(exponent_vectors(g[1])) == collect(exponent_vectors(g[x])), 2:length(g))
  for i=1:length(g[1])
    for x=1:length(g)
      me.res[x] = parent(me.res[x])(lift(coeff(g[x], i)))
    end
    push_term!(bt, Hecke.modular_lift(me.res, me), exponent_vector(g[1], i))
  end
  return finish(bt)
end

function Hecke.modular_lift(g::Vector{T}, me::Hecke.modular_env) where T <: MPolyRingElem{fqPolyRepFieldElem}
  d = Dict{Vector{Int}, Vector{Tuple{Int, fqPolyRepFieldElem}}}()
  for i in 1:length(g)
    for (c, e) = Base.Iterators.zip(Generic.MPolyCoeffs(g[i]),
                                    Generic.MPolyExponentVectors(g[i]))
      if Base.haskey(d, e)
        push!(d[e], (i, c))
      else
        d[e] = [(i, c)]
      end
    end
  end
  bt = MPolyBuildCtx(me.Kxy)

  for e = keys(d)
    for i in 1:length(g)
      me.res[i] = zero!(me.res[i])
    end
    for (i, c) = d[e]
      me.res[i] = c
    end
    push_term!(bt, Hecke.modular_lift(me.res, me), e)
  end
  return finish(bt)
end


#=
import Base.//, Base.==

struct Term{T}
  f::T
  i::Int
  function Term(f::T, i::Int) where {T <: AbstractAlgebra.MPolyRingElem}
    return new{T}(f, i)
  end
end

function Base.show(io::IO, t::Term)
  print(io, "$(t.i)-th term of $(t.f)")
end

struct Terms{T}
  f::T
  function Terms(f::T) where {T <: AbstractAlgebra.MPolyRingElem}
    return new{T}(f)
  end
end

function Base.show(io::IO, t::Terms)
  print(io, "Iterator for the terms of $(t.f)")
end

function Base.iterate(T::Terms, st::Int = 0)
  st += 1
  if st > length(T.f)
    return nothing
  end
  return Term(T.f, st), st
end

Base.IteratorEltype(M::Terms) = Base.HasEltype()
Base.eltype(M::Terms{T}) where {T} = Term{T}

Base.IteratorSize(M::Terms) = Base.HasLength()
Base.length(M::Terms) = length(M.f)

function Base.lastindex(a::Terms)
  return length(a.f)
end

function Base.getindex(a::Terms, i::Int)
  return Term(a.f, i)
end

function Base.isless(f::Term, g::Term)
  R = parent(f.f)
  @assert R == parent(g.f)
  return AbstractAlgebra.Generic.monomial_isless(f.f.exps, f.i, g.f.exps, g.i, ngens(R), R, UInt(0))
end

function ==(f::Term, g::Term, monomial_only::Bool = false)
  R = parent(f.f)
  @assert R == parent(g.f)

  return AbstractAlgebra.Generic.monomial_cmp(f.f.exps, f.i, g.f.exps, g.i, ngens(R), R, UInt(0))==0 && (monomial_only || coeff(f.f, f.i) == coeff(g.f, g.i))
end

#=
function push_term!(M::MPolyBuildCtx{<:Generic.MPoly{T}}, t::Term{T}) where {T}
  push_term!(M, coeff(t.f, t.f.i), exponent_vector(t.f, t.f.i))
end
=#

function Hecke.coeff(t::Term)
  return coeff(t.f, t.i)
end

function Hecke.exponent_vector(t::Term)
  return exponent_vector(t.f, t.i)
end

function monomial(t::Term)
  m = parent(r.f)()
  set_exponent_vector!(m, 1, exponent_vector(t))
  setcoeff!(m, one(base_ring(m)))
  return m
end

function lead_term(f::AbstractAlgebra.MPolyRingElem)
  return Term(f, 1)
end

=#
#=TODO
  fit! for zzModMPolyRingElem
  coeff(fqPolyRepFieldElem) -> UInt (should be zzModRingElem)
  zzModMPolyRingElem -> fpMPolyRingElem? at least in Nemo
  set_coeff should accept UInt

  deal with bad primes (wrong expo vectors)
  reconstruction - and use it in the _hensel stuff elsewhere...
  deal with content

=#


end

