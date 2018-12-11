module MPolyGcd

using Hecke
import Nemo, Nemo.nmod_mpoly, Nemo.NmodMPolyRing
import AbstractAlgebra
import Base.//

mutable struct MPolyBuildCtx{T}
  f::T
  function MPolyBuildCtx(R::T) where {T <: AbstractAlgebra.MPolyRing}
    r = new{elem_type(T)}()
    r.f = R()
    return r
  end
end

function show(io::IO, M::MPolyBuildCtx)
  print(io, "constructing a polynomial in ", parent(M.f))
end

function finish(M::MPolyBuildCtx{<:AbstractAlgebra.MPolyElem})
  M.f = sort_terms!(M.f)
  M.f = combine_like_terms!(M.f)
  return M.f
end

function push_term!(M::MPolyBuildCtx{<:AbstractAlgebra.MPolyElem}, c::RingElem, e::Vector{Int})
  l = length(M.f)+1
  set_exponent_vector!(M.f, l, e)
  setcoeff!(M.f, l, c)
end

function push_term!(M::MPolyBuildCtx{nmod_mpoly}, c::UInt, e::Vector{Int})
  ccall((:nmod_mpoly_push_term_ui_ui, :libflint), Nothing,
               (Ref{nmod_mpoly}, UInt, Ptr{Int}, Ref{NmodMPolyRing}),
               M.f, c, e, M.f.parent)
end

function Hecke.lead(f::AbstractAlgebra.MPolyElem)
  iszero(f) && error("zero poly")
  return coeff(f, 1)
end

function Hecke.coefficients(f::AbstractAlgebra.MPolyElem)
  return Hecke.PolyCoeffs(f)
end

function Base.iterate(PC::Hecke.PolyCoeffs{<:AbstractAlgebra.MPolyElem}, st::Int = 0)
  st += 1
  if st > length(PC.f)
    return nothing
  else
    return coeff(PC.f, st), st
  end
end

Base.length(M::Hecke.PolyCoeffs{<:AbstractAlgebra.MPolyElem}) = length(M.f)

//(f::AbstractAlgebra.MPolyElem{T}, g::T) where {T} = f*inv(g)
    
function gcd(f::Hecke.Generic.MPoly{nf_elem}, g::Hecke.Generic.MPoly{nf_elem})
  p = Hecke.p_start
  K = base_ring(f)
  max_stable = 2
  stable = max_stable

  d = fmpz(1)
  gc = parent(f)()
  gd = parent(f)()
  idl = FlintZZ["x"][1]()
  bm = zero_matrix(FlintZZ, degree(K), degree(K))

  #TODO: scale input to make it integral
  de = lcm(lcm(map(denominator, coefficients(f))), lcm(map(denominator, coefficients(g))))
  f*=de
  g*=de
  E = equation_order(K)
  lI =E*E(lead(f)) + E*E(lead(g))
  gl = Hecke.short_elem(lI)
  gl *= evaluate(derivative(K.pol), gen(K))  # use Kronnecker basis

  fl = true
  while true
    p = next_prime(p)
    me = Hecke.modular_init(K, p, deg_limit = 1)
    if isempty(me)
      continue
    end
    R = ResidueRing(FlintZZ, p)
    Rt, t = PolynomialRing(R, "t", cached = false)
    fp = Hecke.modular_proj(me, f)
    gp = Hecke.modular_proj(me, g)
    glp = Hecke.modular_proj(gl, me)
    gcd_p = [coeff(glp[i], 0)*Base.gcd(fp[i], gp[i]) for i=1:length(fp)]
    tp = Hecke.modular_lift(me, gcd_p)
    if d==1
      d = fmpz(p)
      gc = tp
      idl = lift(parent(idl), me.ce.pr[end])
      bm = lll(basis_matrix(fmpz(p), idl, K))
      R = RecoCtx(bm, K)
      fl, gd = rational_reconstruct(gc, R, true)
      stable = max_stable
    else
      #TODO: instead of lifting "idl" and doing basis_matrix from
      #      scratch, do the basis_matrix for the new ideal and
      #      use CRT to combine them
      #TODO: explore combining LLL matrices to speed up LLL....
#TODO: deal with bad primes...
      idl, _ = induce_crt(idl, d, lift(parent(idl), me.ce.pr[end]), fmpz(p))
      if (!fl) || any(i->(parent(me.ce.pr[end])(coeff(tp, i) - coeff(gd, i))) % me.ce.pr[end] != 0, 1:length(tp))
        gc, d = induce_crt(gc, d, tp, fmpz(p), true)
        R = RecoCtx(basis_matrix(d, idl, K), K)
        fl, gd = rational_reconstruct(gc, R, true)
        stable = max_stable
      else
        @show "stable"
        d *= p
        stable -= 1
        if stable <= 0 
          if divides(f, gd)[1] && divides(g, gd)[1]
            @show nbits(d)
            return gd
          else
            @show "divides failed"
            stable = max_stable
          end
        end
      end
      #before I forget: gc is "the" gcd modulo <d, idl>
    end
#    if nbits(d) > 2500
#      error("")
#    end
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

  @assert length(a) == length(b)
  @assert a.exps == b.exps
  c = parent(a)()
  for i=1:length(a)
    setcoeff!(c, i, Hecke.induce_inner_crt(coeff(a, i), coeff(b, i), pi, pq, pq2))
  end
  c.exps = deepcopy(a.exps)
  return c, pq
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
  for i=1:rows(a)
    for j=1:cols(a)
      c[i,j] = Hecke.inner_crt(a[i,j], b[i,j], pi, pq, pq2)
    end
  end
  return c, pq
end   

function Hecke.characteristic(R::PolyRing)
  return characteristic(base_ring(R))
end

function Hecke.modular_proj(me::Hecke.modular_env, f::Generic.MPoly{nf_elem})
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
    for x = 1:s
      push_term!(fp[x], coeff(cp[x], 0), e)
    end
  end
  return map(finish, fp)
end

function Hecke.modular_lift(me::Hecke.modular_env, g::Array{nmod_mpoly, 1})
  bt = MPolyBuildCtx(me.Kxy)
  #TODO deal with different vectors properly
  @assert all(x->exponent_vectors(g[1]) == exponent_vectors(g[x]), 2:length(g))
  for i=1:length(g[1])
    for x=1:length(g)
      me.res[x] = parent(me.res[x])(lift(coeff(g[x], i)))
    end
    push_term!(bt, Hecke.modular_lift(me.res, me), exponent_vector(g[1], i))
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

function basis_matrix(d::fmpz, f::fmpz_poly, k::AnticNumberField)
  #assumes f is idl as above!!!
  #1st need to deconstruct f into the different degrees:
  #CRT of degree a>b and implies lead(b) = 0 mod q, hence gcd's are my friend
  #claim: in this situation, the "obvious" method will produce a Howell form
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
    c = invmod(lead(f), n)
    fn = mod(c*f, n)
    @assert ismonic(fn)
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
        t -= lead(t)*fn
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

mutable struct RecoCtx
  L::fmpz_mat
  LI::fmpz_mat
  d::fmpz
  k::AnticNumberField
  function RecoCtx(A::fmpz_mat, k::AnticNumberField)
    r= new()
    r.k = k
    r.L = lll(A)
    return r
  end
end

function rational_reconstruct(a::Generic.MPoly{nf_elem}, R::RecoCtx, integral::Bool = false)
  b = MPolyBuildCtx(parent(a))
  for i=1:length(a)
    fl, c = rational_reconstruct(coeff(a, i), R, integral)
    if !fl
      return fl, a
    end
    push_term!(b, c, exponent_vector(a, i))
  end
  return true, finish(b)
end

function rational_reconstruct(a::nf_elem, R::RecoCtx, integral::Bool = false)
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
      s[1, i] = round(s[1, i]//R.d)
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
  L = [ Znn(1) representation_mat_q(a)[1] ; Znn(0) R.L]
  lll!(L)
  d = Nemo.elem_from_mat_row(K, sub(L, 1:1, 1:n), 1, fmpz(1))
  n = Nemo.elem_from_mat_row(K, sub(L, 1:1, n+1:2*n), 1, fmpz(1))
  return true, n//d
end


#=TODO
  fit! for nmod_mpoly
  coeff(fq_nmod) -> UInt (should be nmod)
  nmod_mpoly -> gfp_mpoly? at least in Nemo
  set_coeff should accept UInt

  why is Generic.gcd not monic?

  deal with bad primes (wrong expo vectors)
  reconstruction - and use it in the _hensel stuff elsewhere...
  deal with lead_coeff, content
  use Kronnecker rep do avoid dens.

=#

end

