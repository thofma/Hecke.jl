add_verbose_scope(:MPolyGcd)

####################################################
# exported is the RecoCtx (and thus the rational_reconstruction functions)
# not exported are the helpers...

module RecoNF

using ..Hecke

import Hecke.Nemo

function basis_matrix(d::fmpz, f::fmpz_poly, k::AnticNumberField)
  #assumes f is idl as above!!!
  #1st need to deconstruct f into the different degrees:
  #CRT of degree a>b and implies leading_coefficient(b) = 0 mod q, hence gcd's are my friend
  #claim: in this situation, the "obvious" method will produce a Howell form
  #tries to compute the basis matrix for the ideal <d, f(a)> where a = gen(k)
  #assumes deg f < deg k, d coprime to the conductor/ index/ everything
  de = []
  g = d
  N = zero_matrix(FlintZZ, degree(k), degree(k))
  dN = fmpz(1)
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
      M = MatrixSpace(FlintZZ, degree(k), degree(k))(n)
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
  L::fmpz_mat  # should be LLL reduced, will do so on creation
  p1::fmpz     # the "prime": L is the basis matrix of an ideal, p1 is the
               # minimum
  f::fmpz_poly # the implicit ideal is <p1, f(gen(k))>
  LI::fmpz_mat #(Li, d) = pseudo_inv(L) - if set (integral = true)
  d::fmpz
  k::AnticNumberField
  new_data::Bool
  function RecoCtx(A::fmpz_mat, k::AnticNumberField)
    r= new()
    r.k = k
    r.L = lll(A)
    r.p1 = det(A)
    r.new_data = false
    return r
  end
  function RecoCtx(k::AnticNumberField)
    r = new()
    r.L = identity_matrix(FlintZZ, degree(k))
    r.p1 = fmpz(1)
    r.k = k
    r.new_data = false
    return r
  end
end

function Base.push!(R::RecoCtx, p::fmpz, f::fmpz_poly)
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
  if isdefined(R, :LI) #to keep stucture consistent
    R.LI, R.d = pseudo_inv(R.L)
  end
  R.new_data = false
  return R
end

function has_small_coeffs(a::nf_elem, B::fmpz)
  z = fmpz()
  for i=0:degree(parent(a))-1
    Nemo.num_coeff!(z, a, i)
    if cmpabs(z, B) >0
      return false
    end
  end
  return true
end

function Hecke.induce_rational_reconstruction(a::Generic.MPoly{nf_elem}, R::RecoCtx; integral::Bool = false)
  b = MPolyBuildCtx(parent(a))
  k = base_ring(a)
  d = k(2)
  if integral
    B = fmpz(1)
  else
    B = abs(det(R.L))
    B = fmpz(2)^div(nbits(B), 2*degree(k))
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
function Hecke.rational_reconstruction(a::nf_elem, R::RecoCtx; integral::Bool = false, split::Bool = false)
  data_assure(R)
  if integral
    if !isdefined(R, :LI)
      R.LI, R.d = pseudo_inv(R.L)
    end
    t = zero_matrix(FlintZZ, 1, degree(R.k))
    z = fmpz()
    for i=1:degree(R.k)
      Nemo.num_coeff!(z, a, i-1)
      t[1, i] = z
    end
    s = t*R.LI
    for i=1:degree(R.k)
      s[1, i] = round(fmpz, s[1, i], R.d)
    end
    tt = s*R.L
    b = parent(a)()
    nb = div(3*nbits(R.d), 2)
    for i=1:degree(R.k)
      Hecke._num_setcoeff!(b, i-1, t[1, i]-tt[1, i])
      nb -= nbits(t[1, i] - tt[1, i])
    end
    return nb >= 0, b
  end
  n = degree(parent(a))
  Znn = MatrixSpace(FlintZZ, n, n)
  L = [ Znn(1) representation_matrix_q(a)[1] ; Znn(0) R.L]
  lll!(L)
  K = parent(a)
  d = Nemo.elem_from_mat_row(K, sub(L, 1:1, 1:n), 1, fmpz(1))
  n = Nemo.elem_from_mat_row(K, sub(L, 1:1, n+1:2*n), 1, fmpz(1))
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
import Nemo, Nemo.nmod_mpoly, Nemo.NmodMPolyRing
import AbstractAlgebra
import Hecke.RecoCtx

function Hecke.gcd(f::Hecke.Generic.MPoly{nf_elem}, g::Hecke.Generic.MPoly{nf_elem})
  Hecke.check_parent(f, g)
  @vprint :MPolyGcd 1 "multivariate gcd of f with $(length(f)) and g with $(length(g)) terms over $(base_ring(f))\n"

  k = base_ring(f)
  ps = PrimesSet(Hecke.p_start, -1)
  fl, c = Hecke.is_cyclotomic_type(k)
  if fl
    @vprint :MPolyGcd 2 "field is cyclotomic with conductor $c\n"
    ps = PrimesSet(Hecke.p_start, -1, c, 1)
  end
  fl, c = Hecke.is_quadratic_type(k)
  if fl && abs(c) < typemax(Int)
    @vprint :MPolyGcd 2 "field is quadratic, using conductor $(4*c)\n"
    ps = PrimesSet(Hecke.p_start, -1, Int(4*c), 1)
  end
  return _gcd(f, g, ps)
end

function _gcd(f::Hecke.Generic.MPoly{nf_elem}, g::Hecke.Generic.MPoly{nf_elem}, ps::PrimesSet{Int})
#  @show "gcd start"
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

  d = fmpz(1)
  gc = parent(f)()
  gd = parent(f)()
  Zx = Hecke.Globals.Zx
  R = RecoCtx(K)

  de = lcm(lcm(map(denominator, coefficients(f))), lcm(map(denominator, coefficients(g))))
  f*=de
  g*=de
  E = equation_order(K)
  lI = E*E(leading_coefficient(f)) + E*E(leading_coefficient(g))
  gl = Hecke.short_elem(lI)
  gl *= evaluate(derivative(K.pol), gen(K))  # use Kronnecker basis

  fl = true
  while true
    p = iterate(ps, p)[1]
    @vprint :MPolyGcd 2 "Main loop: using $p\n"
    @vtime :MPolyGcd 3 me = Hecke.modular_init(K, p, deg_limit = 1)
    if isempty(me)
      continue
    end

    @vtime :MPolyGcd 3 fp = Hecke.modular_proj(f, me)
    @vtime :MPolyGcd 3 gp = Hecke.modular_proj(g, me)
    glp = Hecke.modular_proj(gl, me)
    gcd_p = nmod_mpoly[]
    @vtime :MPolyGcd 3 for i=1:length(fp)
      _g = gcd(fp[i], gp[i])
      if length(_g) == 1 && iszero(exponent_vector(_g, 1))
        return inflate(one(parent(f)), shiftr, deflr)
      end
      push!(gcd_p, coeff(glp[i], 0)*_g)
    end
    #gcd_p = [coeff(glp[i], 0)*gcd(fp[i], gp[i]) for i=1:length(fp)]
    @vtime :MPolyGcd 3 tp = Hecke.modular_lift(gcd_p, me)
    if d==1
      d = fmpz(p)
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

      push!(R, fmpz(p), lift(Zx, me.ce.pr[end]))
      if (!fl) || any(i->(parent(me.ce.pr[end])(coeff(tp, i) - coeff(gd, i))) % me.ce.pr[end] != 0, 1:length(tp))
        gc, d = induce_crt(gc, d, tp, fmpz(p), true)
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

function Hecke.induce_crt(a::Hecke.Generic.MPoly{nf_elem}, p::fmpz, b::Hecke.Generic.MPoly{nf_elem}, q::fmpz, signed::Bool = false)
  pi = invmod(p, q)
  mul!(pi, pi, p)
  pq = p*q
  if signed
    pq2 = div(pq, 2)
  else
    pq2 = fmpz(0)
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
    if !aa == nothing
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

function Hecke.induce_crt(a::fmpz_mat, p::fmpz, b::fmpz_mat, q::fmpz, signed::Bool = false)
  pi = invmod(p, q)
  mul!(pi, pi, p)
  pq = p*q
  if signed
    pq2 = div(pq, 2)
  else
    pq2 = fmpz(0)
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

function Hecke.modular_proj(f::Generic.MPoly{nf_elem}, me::Hecke.modular_env)
  if !isdefined(me, :Kxy)
    me.Kxy = parent(f)
  else
    @assert me.Kxy === parent(f)
  end
  if !isdefined(me, :Kpxy)
    p = characteristic(me.Fpx)
    me.Kpxy, _ = PolynomialRing(base_ring(me.Fpx), ["$(x)_$p" for x = me.Kxy.S])
  end
  fp = [MPolyBuildCtx(me.Kpxy) for x = me.fld]
  s = length(me.fld)
  for i=1:length(f)
    c = coeff(f, i)
    e = exponent_vector(f, i)
    cp = Hecke.modular_proj(c, me)
    R = base_ring(me.Fpx)
    for x = 1:s
      push_term!(fp[x], Hecke.nmod(coeff(cp[x], 0), R), e)
    end
  end
  return map(finish, fp)
end

function Hecke.modular_proj(::Type{fq_nmod}, a::Generic.MPoly{nf_elem}, me::Hecke.modular_env)
  Kxy = parent(a)
  if !isdefined(me, :Kxy)
    me.Kxy = Kxy
  else
    @assert me.Kxy === parent(a)
  end
  vars = map(string, symbols(Kxy))
  s = length(me.fld)
  res = [MPolyBuildCtx(PolynomialRing(me.fld[i], vars)[1]) for i in 1:s]
  for (c, v) in zip(coefficients(a), exponent_vectors(a))
    cp = Hecke.modular_proj(c, me)
    for i in 1:s
      push_term!(res[i], deepcopy(cp[i]), v)
    end
  end
  map(finish, res)
end



function Hecke.modular_lift(g::Vector{nmod_mpoly}, me::Hecke.modular_env)

  #TODO: no dict, but do s.th. similar to induce_crt
  d = Dict{Vector{Int}, Vector{Tuple{Int, Hecke.nmod}}}()
  for i=1:length(g)
    for (c, e) = Base.Iterators.zip(Generic.MPolyCoeffs(g[i]), Generic.MPolyExponentVectors(g[i]))
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

function Hecke.modular_lift(g::Vector{T}, me::Hecke.modular_env) where T <: MPolyElem{fq_nmod}
  d = Dict{Vector{Int}, Vector{Tuple{Int, fq_nmod}}}()
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


function Hecke.mod!(f::fmpz_poly, p::fmpz)
  for i=0:degree(f)
    setcoeff!(f, i, mod(coeff(f, i), p))
  end
end

function Hecke.mod(f::fmpz_poly, p::fmpz)
  g = parent(f)()
  for i=0:degree(f)
    setcoeff!(g, i, mod(coeff(f, i), p))
  end
  return g
end

function Hecke.mod_sym!(f::fmpz_poly, p::fmpz)
  for i=0:degree(f)
    setcoeff!(f, i, Hecke.mod_sym(coeff(f, i), p))
  end
end

#=
import Base.//, Base.==

struct Term{T}
  f::T
  i::Int
  function Term(f::T, i::Int) where {T <: AbstractAlgebra.MPolyElem}
    return new{T}(f, i)
  end
end

function Base.show(io::IO, t::Term)
  print(io, "$(t.i)-th term of $(t.f)")
end

struct Terms{T}
  f::T
  function Terms(f::T) where {T <: AbstractAlgebra.MPolyElem}
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

function lead_term(f::AbstractAlgebra.MPolyElem)
  return Term(f, 1)
end

=#
#=TODO
  fit! for nmod_mpoly
  coeff(fq_nmod) -> UInt (should be nmod)
  nmod_mpoly -> gfp_mpoly? at least in Nemo
  set_coeff should accept UInt

  deal with bad primes (wrong expo vectors)
  reconstruction - and use it in the _hensel stuff elsewhere...
  deal with content

=#


end

