
export rational_reconstruction, farey_lift, div, leading_coefficient,
       trailing_coefficient, constant_coefficient, factor_mod_pk,
       factor_mod_pk_init, hensel_lift, rres, rresx,
       coefficients

import Nemo: fmpz_mod_ctx_struct

function PolynomialRing(R::Ring; cached::Bool = false)
  return PolynomialRing(R, "x", cached = cached)
end

################################################################################
#
#  Content
#
################################################################################

function content(a::PolyElem{<: FieldElem})
  return one(base_ring(a))
end


function fmpz(a::Generic.Res{Nemo.fmpz})
  return a.data
end

function fmpz(a::Nemo.nmod)
  return fmpz(a.data)
end

function lift(::FlintIntegerRing, a::Generic.Res{Nemo.fmpz})
  return a.data
end

function (::FlintIntegerRing)(a::Generic.Res{Nemo.fmpz})
  return a.data
end

function lift(::FlintIntegerRing, a::Nemo.nmod)
  return fmpz(a.data)
end

function (::FlintIntegerRing)(a::Nemo.nmod)
  return fmpz(a.data)
end

if Nemo.version() > v"0.15.1"
  function fmpz(a::Nemo.fmpz_mod)
    return a.data
  end

  function lift(::FlintIntegerRing, a::Nemo.fmpz_mod)
    return a.data
  end

  function (::FlintIntegerRing)(a::Nemo.fmpz_mod)
    return a.data
  end
end

function div(f::PolyElem, g::PolyElem)
  q, r = divrem(f,g)
  return q
end

function rem(f::PolyElem, g::PolyElem)
  return mod(f, g)
end

function rem!(z::T, f::T, g::T) where T <: PolyElem
  z = rem(f, g)
  return z
end

@doc Markdown.doc"""
    induce_rational_reconstruction(a::fmpz_poly, M::fmpz) -> fmpq_poly

Apply `rational_reconstruction` to each coefficient of $a$, resulting
in either a fail (return (false, s.th.)) or (true, g) for some rational
polynomial $g$ s.th. $g \equiv a \bmod M$.
"""
function induce_rational_reconstruction(a::fmpz_poly, M::fmpz; parent=PolynomialRing(FlintQQ, parent(a).S, cached = false)[1])
  b = parent()
  for i=0:degree(a)
    fl, x,y = rational_reconstruction(coeff(a, i), M)
    if fl
      setcoeff!(b, i, x//y)
    else
      return false, b
    end
  end
  return true, b
end

function resultant(f::fmpz_poly, g::fmpz_poly, d::fmpz, nb::Int)
  z = fmpz()
  ccall((:fmpz_poly_resultant_modular_div, libflint), Nothing,
     (Ref{fmpz}, Ref{fmpz_poly}, Ref{fmpz_poly}, Ref{fmpz}, Int),
     z, f, g, d, nb)
  return z
end

function rem!(z::fq_nmod_poly, x::fq_nmod_poly, y::fq_nmod_poly)
  ccall((:fq_nmod_poly_rem, libflint), Nothing, (Ref{fq_nmod_poly}, Ref{fq_nmod_poly}, Ref{fq_nmod_poly}, Ref{FqNmodFiniteField}),
       z, x, y, base_ring(parent(x)))
  return z
end

function rem!(z::fq_poly, x::fq_poly, y::fq_poly)
  ccall((:fq_poly_rem, libflint), Nothing, (Ref{fq_poly}, Ref{fq_poly}, Ref{fq_poly}, Ref{FqPolyRing}),
       z, x, y, parent(x))
  return z
end

################################################################################
#
#  Modular composition
#
################################################################################

function compose_mod(x::fmpz_mod_poly, y::fmpz_mod_poly, z::fmpz_mod_poly)
  check_parent(x,y)
  check_parent(x,z)
  r = parent(x)()
  ccall((:fmpz_mod_poly_compose_mod, libflint), Nothing,
          (Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}, Ref{fmpz_mod_ctx_struct}), r, x, y, z, x.parent.base_ring.ninv)
  return r
end

function compose_mod_precomp(x::fmpz_mod_poly, A::fmpz_mat, z::fmpz_mod_poly, zinv::fmpz_mod_poly)
  r = parent(x)()
  ccall((:fmpz_mod_poly_compose_mod_brent_kung_precomp_preinv, libflint), Nothing,
        (Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}, Ref{fmpz_mat}, Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}, Ref{fmpz_mod_ctx_struct}), r, x, A, z, zinv, x.parent.base_ring.ninv)
  return r
end

function _inv_compose_mod(z::fmpz_mod_poly)
  r = reverse(z)
  ccall((:fmpz_mod_poly_inv_series_newton, libflint), Nothing,
        (Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}, Int, Ref{fmpz_mod_ctx_struct}), r, r, length(r), z.parent.base_ring.ninv)
  return r
end

function precomp_compose_mod(y::fmpz_mod_poly, z::fmpz_mod_poly)
  zinv = _inv_compose_mod(z)
  nr = Int(iroot(degree(z), 2)) + 1
  A = zero_matrix(FlintZZ, nr, degree(z))
  ccall((:fmpz_mod_poly_precompute_matrix, libflint), Nothing,
        (Ref{fmpz_mat}, Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}, Ref{fmpz_mod_ctx_struct}), A, y, z, zinv, y.parent.base_ring.ninv)
  return A, zinv
end

function my_compose_mod(x::fmpz_mod_poly, y::fmpz_mod_poly, z::fmpz_mod_poly)
  if degree(x) < degree(z)
    return compose_mod(x, y, z)
  end
  x1 = shift_right(x, degree(z))
  r1 = mulmod(my_compose_mod(x1, y, z), powermod(y, degree(z), z), z)
  x2 = truncate(x, degree(z))
  return r1 + compose_mod(x2, y, z)
end

function my_compose_mod_precomp(x::fmpz_mod_poly, A::fmpz_mat, z::fmpz_mod_poly, zinv::fmpz_mod_poly)

  if degree(x) < degree(z)
    res1 = compose_mod_precomp(x, A, z, zinv)
    return res1
  end

  #First, I compute x^degree(z) mod z
  #The rows of A contain the powers up to sqrt(degree(z))...
  Rx = parent(x)
  ind = nrows(A)
  q, r = divrem(degree(z), ind-1)
  yind = Rx(Nemo.fmpz_mod[base_ring(Rx)(A[ind, j]) for j = 1:ncols(A)])
  yind = powermod(yind, q, z)
  if !iszero(r)
    ydiff = Rx(Nemo.fmpz_mod[base_ring(Rx)(A[r+1, j]) for j = 1:ncols(A)])
    yind = mulmod(yind, ydiff, z)
  end
  x1 = shift_right(x, degree(z))
  res = mulmod(compose_mod_precomp(x1, A, z, zinv), yind, z)
  x2 = truncate(x, degree(z))
  add!(res, res, compose_mod_precomp(x2, A, z, zinv))
  return res
end

################################################################################
#
# Hensel
#
################################################################################
function factor_to_dict(a::fmpz_poly_factor)
  res = Dict{fmpz_poly,Int}()
  Zx,x = PolynomialRing(FlintZZ, "x", cached = false)
  for i in 1:a._num
    f = Zx()
    ccall((:fmpz_poly_set, libflint), Nothing, (Ref{fmpz_poly}, Ref{fmpz_poly_raw}), f, a.poly+(i-1)*sizeof(fmpz_poly_raw))
    res[f] = unsafe_load(a.exp, i)
  end
  return res
end

function factor_to_array(a::fmpz_poly_factor; parent::FmpzPolyRing = PolynomialRing(FlintZZ, "x", cached = false)[1])
  res = Vector{Tuple{fmpz_poly, Int}}()
  Zx = parent
  for i in 1:a._num
    f = Zx()
    ccall((:fmpz_poly_set, libflint), Nothing, (Ref{fmpz_poly}, Ref{fmpz_poly_raw}), f, a.poly+(i-1)*sizeof(fmpz_poly_raw))
    push!(res, (f, unsafe_load(a.exp, i)))
  end
  return res
end

function show(io::IO, a::fmpz_poly_factor)
  ccall((:fmpz_poly_factor_print, libflint), Nothing, (Ref{fmpz_poly_factor}, ), a)
end

function show(io::IO, a::HenselCtx)
  println(io, "factorisation of $(a.f) modulo $(a.p)^$(a.N)")
  if a.r == 1
    println(io, "irreducible, $(a.f)")
    return
  end
  if a.N > 0
    d = factor_to_dict(a.LF)
    println(io, "currently: $d")
  end
end

function start_lift(a::HenselCtx, N::Int)
  if a.r == 1
    return
  end
  a.prev = ccall((:_fmpz_poly_hensel_start_lift, libflint), UInt,
       (Ref{fmpz_poly_factor}, Ref{Int}, Ref{fmpz_poly_raw}, Ref{fmpz_poly_raw}, Ref{fmpz_poly}, Ref{Nemo.nmod_poly_factor}, Int),
       a.LF, a.link, a.v, a.w, a.f, a.lf, N)
  a.N = N
end

function continue_lift(a::HenselCtx, N::Int)
  if a.r == 1
    return
  end
  if a.N >= N
    return
  end
  a.prev = ccall((:_fmpz_poly_hensel_continue_lift, libflint), Int,
       (Ref{fmpz_poly_factor}, Ref{Int}, Ref{fmpz_poly_raw}, Ref{fmpz_poly_raw}, Ref{fmpz_poly}, UInt, UInt, Int, Ref{fmpz}),
       a.LF, a.link, a.v, a.w, a.f, a.prev, a.N, N, fmpz(a.p))
  a.N = N
end

@doc Markdown.doc"""
    factor_mod_pk(f::fmpz_poly, p::Int, k::Int) -> Dict{fmpz_poly, Int}

 For $f$ that is square-free modulo $p$, return the factorisation modulo $p^k$.
"""
function factor_mod_pk(f::fmpz_poly, p::Int, k::Int)
  H = HenselCtx(f, fmpz(p))
  if H.r == 1
    return Dict(H.f => 1)
  end
  start_lift(H, k)
  return factor_to_dict(H.LF)
end

@doc Markdown.doc"""
    factor_mod_pk_init(f::fmpz_poly, p::Int) -> HenselCtx

 For $f$ that is square-free modulo $p$, return a structure that allows to compute
 the factorisation modulo $p^k$ for any $k$.
"""
function factor_mod_pk_init(f::fmpz_poly, p::Int)
  H = HenselCtx(f, fmpz(p))
  return H
end

@doc Markdown.doc"""
    factor_mod_pk(H::HenselCtx, k::Int) -> RingElem

 Using the result of `factor_mod_pk_init`, return a factorisation modulo $p^k$.
"""
function factor_mod_pk(H::HenselCtx, k::Int)
  if H.r == 1
    return Dict(H.f => 1)
  end
  @assert k>= H.N
  if H.N == 0
    start_lift(H, k)
  else
    continue_lift(H, k)
  end
  return factor_to_dict(H.LF)
end

factor_mod_pk(H::HenselCtx) = factor_to_dict(H.LF)
factor_mod_pk(::Type{Array}, H::HenselCtx) = factor_to_array(H.LF, parent = parent(H.f))
length(H::HenselCtx) = H.LF._num

function degrees(H::HenselCtx)
  d = Int[]
  a = H.LF
  for i=1:a._num
    push!(d, Int(ccall((:fmpz_poly_degree, libflint), Clong, (Ref{fmpz_poly_raw}, ), a.poly+(i-1)*sizeof(fmpz_poly_raw))))
  end
  return d
end

function factor_mod_pk(::Type{Array}, H::HenselCtx, k::Int)
  if H.r == 1
    return [(H.f, 1)]
  end
  @assert k>= H.N
  if H.N == 0
    start_lift(H, k)
  else
    continue_lift(H, k)
  end
  return factor_to_array(H.LF, parent = parent(H.f))
end

#I think, experimentally, that p = Q^i, p1 = Q^j and j<= i is the condition to make it tick.
function hensel_lift!(G::fmpz_poly, H::fmpz_poly, A::fmpz_poly, B::fmpz_poly, f::fmpz_poly, g::fmpz_poly, h::fmpz_poly, a::fmpz_poly, b::fmpz_poly, p::fmpz, p1::fmpz)
  ccall((:fmpz_poly_hensel_lift, libflint), Nothing, (Ref{fmpz_poly}, Ref{fmpz_poly},  Ref{fmpz_poly},  Ref{fmpz_poly},  Ref{fmpz_poly},  Ref{fmpz_poly},  Ref{fmpz_poly}, Ref{fmpz_poly}, Ref{fmpz_poly}, Ref{fmpz}, Ref{fmpz}), G, H, A, B, f, g, h, a, b, p, p1)
end

@doc Markdown.doc"""
    hensel_lift(f::fmpz_poly, g::fmpz_poly, h::fmpz_poly, p::fmpz, k::Int) -> (fmpz_poly, fmpz_poly)

 Given $f = gh$ modulo $p$ for $g, h$ coprime modulo $p$, compute $G, H$ s.th. $f = GH mod p^k$ and
 $G = g mod p$, $H = h mod p$.
"""
function hensel_lift(f::fmpz_poly, g::fmpz_poly, h::fmpz_poly, p::fmpz, k::Int)
  Rx, x = PolynomialRing(GF(p, cached=false), cached=false)
  fl, a, b = gcdx(Rx(g), Rx(h))
  @assert isone(fl)
  @assert k>= 2
  ## if one of the cofactors is zero, this crashes.
  ## this can only happen if one of the factors is one. In this case, the other
  ## is essentially f and f would be a legal answer. Probably reduced mod p^k
  ## with all non-negative coefficients
  ## for now:
  @assert !iszero(a) && !iszero(b)
  a = lift(parent(g), a)
  b = lift(parent(g), b)
  G = parent(g)()
  H = parent(g)()
  A = parent(g)()
  B = parent(g)()
  g = deepcopy(g)
  h = deepcopy(h)

  # the idea is to have a good chain of approximations, ie.
  # to reach p^10, one should do p, p^2, p^3, p^5, p^10
  # rather than p, p^2, p^4, p^8, p^10
  # the chain has the same length, but smaller entries.
  l = Int[k]
  while k>1
    k = div(k+1, 2)
    push!(l, k)
  end
  ll = Int[]
  for i=length(l)-1:-1:1
    push!(ll, l[i] - l[i+1])
  end
  P = p
  for i in ll
    p1 = p^i
    hensel_lift!(G, H, A, B, f, g, h, a, b, P, p1)
    G, g = g, G
    H, h = h, H
    A, a = a, A
    B, b = b, B
    P *= p1
  end
  return g, h
end

@doc Markdown.doc"""
    hensel_lift(f::fmpz_poly, g::fmpz_poly, p::fmpz, k::Int) -> (fmpz_poly, fmpz_poly)

 Given $f$ and $g$ such that $g$ is a divisor of $f mod p$ and $g$ and $f/g$ are coprime, compute a hensel lift of $g modulo p^k$.
"""
function hensel_lift(f::fmpz_poly, g::fmpz_poly, p::fmpz, k::Int)
  @assert is_monic(g) #experimentally: otherwise, the result is bad...
  Rx, x = PolynomialRing(GF(p, cached=false), cached=false)
  if !is_monic(f)
    pk = p^k
    f *= invmod(leading_coefficient(f), pk)
    mod_sym!(f, pk)
  end
  @assert is_monic(f)
  q, r = divrem(Rx(f), Rx(g))
  @assert iszero(r)
  h = lift(parent(f), q)
  return hensel_lift(f, g, h, p, k)[1]
end

modulus(F::Generic.ResRing{fmpz}) = F.modulus

modulus(F::Generic.ResField{fmpz}) = F.modulus

function fmpq_poly_to_nmod_poly_raw!(r::nmod_poly, a::fmpq_poly)
  ccall((:fmpq_poly_get_nmod_poly, libflint), Nothing, (Ref{nmod_poly}, Ref{fmpq_poly}), r, a)
end

function fmpq_poly_to_gfp_poly_raw!(r::gfp_poly, a::fmpq_poly)
  ccall((:fmpq_poly_get_nmod_poly, libflint), Nothing, (Ref{gfp_poly}, Ref{fmpq_poly}), r, a)
end

function fmpq_poly_to_fmpz_mod_poly_raw!(r::fmpz_mod_poly, a::fmpq_poly, t1::fmpz_poly = fmpz_poly(), t2::fmpz = fmpz())
  ccall((:fmpq_poly_get_numerator, libflint), Nothing, (Ref{fmpz_poly}, Ref{fmpq_poly}), t1, a)
  ccall((:fmpz_mod_poly_set_fmpz_poly, libflint), Nothing, (Ref{fmpz_mod_poly}, Ref{fmpz_poly}, Ref{fmpz_mod_ctx_struct}), r, t1, r.parent.base_ring.ninv)
  ccall((:fmpq_poly_get_denominator, libflint), Nothing, (Ref{fmpz}, Ref{fmpq_poly}), t2, a)
  if !isone(t2)
    res = ccall((:fmpz_invmod, libflint), Cint, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), t2, t2, modulus(base_ring(r)))
    @assert res != 0
    ccall((:fmpz_mod_poly_scalar_mul_fmpz, libflint), Nothing, (Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}, Ref{fmpz}, Ref{fmpz_mod_ctx_struct}), r, r, t2, r.parent.base_ring.ninv)
  end
end

function fmpq_poly_to_gfp_fmpz_poly_raw!(r::gfp_fmpz_poly, a::fmpq_poly, t1::fmpz_poly = fmpz_poly(), t2::fmpz = fmpz())
  ccall((:fmpq_poly_get_numerator, libflint), Nothing, (Ref{fmpz_poly}, Ref{fmpq_poly}), t1, a)
  ccall((:fmpz_mod_poly_set_fmpz_poly, libflint), Nothing, (Ref{gfp_fmpz_poly}, Ref{fmpz_poly}, Ref{fmpz_mod_ctx_struct}), r, t1, r.parent.base_ring.ninv)
  ccall((:fmpq_poly_get_denominator, libflint), Nothing, (Ref{fmpz}, Ref{fmpq_poly}), t2, a)
  if !isone(t2)
    res = ccall((:fmpz_invmod, libflint), Cint, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), t2, t2, modulus(base_ring(r)))
    @assert res != 0
    ccall((:fmpz_mod_poly_scalar_mul_fmpz, libflint), Nothing, (Ref{gfp_fmpz_poly}, Ref{gfp_fmpz_poly}, Ref{fmpz}, Ref{fmpz_mod_ctx_struct}), r, r, t2, r.parent.base_ring.ninv)
  end
end

function fmpq_poly_to_nmod_poly(Rx::Nemo.NmodPolyRing, f::fmpq_poly)
  g = Rx()
  fmpq_poly_to_nmod_poly_raw!(g, f)
  return g
end

function fmpq_poly_to_gfp_poly(Rx::Nemo.GFPPolyRing, f::fmpq_poly)
  g = Rx()
  fmpq_poly_to_gfp_poly_raw!(g, f)
  return g
end

function fmpz_poly_to_nmod_poly_raw!(r::nmod_poly, a::fmpz_poly)
  ccall((:fmpz_poly_get_nmod_poly, libflint), Nothing,
                  (Ref{nmod_poly}, Ref{fmpz_poly}), r, a)

end

function fmpz_poly_to_gfp_poly_raw!(r::gfp_poly, a::fmpz_poly)
  ccall((:fmpz_poly_get_nmod_poly, libflint), Nothing,
                  (Ref{gfp_poly}, Ref{fmpz_poly}), r, a)

end

function fmpz_poly_to_nmod_poly(Rx::Nemo.NmodPolyRing, f::fmpz_poly)
  g = Rx()
  fmpz_poly_to_nmod_poly_raw!(g, f)
  return g
end

function fmpq_poly_to_fmpz_mod_poly(Rx::Nemo.FmpzModPolyRing, f::fmpq_poly)
  g = Rx()
  fmpq_poly_to_fmpz_mod_poly_raw!(g, f)
  return g
end

function fmpq_poly_to_gfp_fmpz_poly(Rx::Nemo.GFPFmpzPolyRing, f::fmpq_poly)
  g = Rx()
  fmpq_poly_to_gfp_fmpz_poly_raw!(g, f)
  return g
end

function fmpz_poly_to_fmpz_mod_poly_raw!(r::fmpz_mod_poly, a::fmpz_poly)
  ccall((:fmpz_poly_get_fmpz_mod_poly, libflint), Nothing,
        (Ref{fmpz_mod_poly}, Ref{fmpz_poly}, Ref{fmpz_mod_ctx_struct}), r, a, r.parent.base_ring.ninv)

end

function fmpz_poly_to_fmpz_mod_poly(Rx::Nemo.FmpzModPolyRing, f::fmpz_poly)
  g = Rx()
  fmpz_poly_to_fmpz_mod_poly_raw!(g, f)
  return g
end

################################################################################
#
#  Reduced resultant
#
################################################################################

@doc Markdown.doc"""
    rres(f::fmpz_poly, g::fmpz_poly) -> fmpz

The reduced resultant of $f$ and $g$,
that is a generator for the ideal $(f, g) \cap Z$.
"""
function rres(f::fmpz_poly, g::fmpz_poly)
  return rres_bez(f,g)
end

function rres_hnf(f::fmpz_poly, g::fmpz_poly)
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  s = Nemo.Generic.sylvester_matrix(f, g)
  h = hnf(s)
  return abs(h[nrows(h), ncols(h)])
end

function rres_bez(f::fmpz_poly, g::fmpz_poly)
  Nemo.check_parent(f, g)
  Qx = PolynomialRing(FlintQQ, "x", cached = false)[1]
  f1 = Qx(f)
  g1 = Qx(g)
  d, q, w = gcdx(f1, g1)
  if iszero(q) || iszero(w)
    if is_constant(f) || is_constant(g)
      if is_constant(f) && is_constant(g)
        return gcd(coeff(f, 0), coeff(g, 0))
      end
      if is_constant(f)
        if !isone(gcd(leading_coefficient(g), coeff(f, 0)))
          cg = content(g - coeff(g, 0))
          ann = divexact(coeff(f, 0), gcd(coeff(f, 0), cg))
          return gcd(coeff(f, 0), ann*coeff(g, 0))
        else
          return coeff(f, 0)
        end
      end
      if !isone(gcd(leading_coefficient(f), coeff(g, 0)))
        cf = content(f - coeff(f, 0))
        ann = divexact(coeff(g, 0), gcd(coeff(g, 0), cf))
        return gcd(coeff(g, 0), ann*coeff(f, 0))
      else
        return coeff(g, 0)
      end
    end
    return fmpz(0)
  end
  return lcm(denominator(q), denominator(w))
end

@doc Markdown.doc"""
    rresx(f::fmpz_poly, g::fmpz_poly) -> r, u, v

The reduced resultant, i.e. a generator for the intersect
of the ideal generated by $f$ and $g$ with the integers.
As well as polynomials $u$ and $v$ s.th. $r = uf+vg$,
$\deg u < \deg g$ and $\deg v < \deg f$.
"""
function rresx(f::fmpz_poly, g::fmpz_poly)
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  Qx = PolynomialRing(FlintQQ, "x", cached = false)[1]
  g, q, w = gcdx(Qx(f), Qx(g))
  l = lcm(denominator(q), denominator(w))
  Zx = parent(f)
  return l, Zx(l*q), Zx(l*w)
end




################################################################################
#
#  fmpq_poly with denominator 1 to fmpz_poly
#
################################################################################

function (a::FmpzPolyRing)(b::fmpq_poly)
  (!isone(denominator(b))) && error("Denominator has to be 1")
  z = a()
  ccall((:fmpq_poly_get_numerator, libflint), Nothing,
              (Ref{fmpz_poly}, Ref{fmpq_poly}), z, b)
  return z
end

##############################################################
# all of this should be in Nemo/AbstractAlgebra
#
#TODO:
# expand systematically for all finite fields
# and for fmpz/fmpq poly
# for fun: is_power(a::nf_elem)
#

function factor(f::fmpq_poly, R::T) where T <: Union{Nemo.FqNmodFiniteField, Nemo.GaloisField}
  Rt, t = PolynomialRing(R, "t", cached=false)
  return factor(Rt(f))
end

function roots(f::fmpq_poly, R::T) where T <: Union{Nemo.FqNmodFiniteField, Nemo.GaloisField}
  Rt, t = PolynomialRing(R, "t", cached=false)
  fp = PolynomialRing(FlintZZ, cached = false)[1](f*denominator(f))
  fpp = Rt(fp)
  return roots(fpp)
end

function roots(f::gfp_poly, K::FqNmodFiniteField)
  @assert characteristic(K) == characteristic(base_ring(f))
  Kx = PolynomialRing(K, cached = false)[1]
  coeffsff = Vector{elem_type(K)}(undef, degree(f)+1)
  for i=0:degree(f)
    coeffsff[i+1] = K(lift(coeff(f, i)))
  end
  ff = Kx(coeffsff)
  return roots(ff)
end

function roots(f::gfp_fmpz_poly, K::FqFiniteField)
  @assert characteristic(K) == characteristic(base_ring(f))
  Kx = PolynomialRing(K, cached = false)[1]
  coeffsff = Vector{fq}(undef, degree(f)+1)
  for i=0:degree(f)
    coeffsff[i+1] = K(lift(coeff(f, i)))
  end
  ff = Kx(coeffsff)
  return roots(ff)
end

function is_power(a::fq_nmod, m::Int)
  s = size(parent(a))
  if gcd(s-1, m) == 1
    return true, a^invmod(FlintZZ(m), s-1)
  end
  St, t = PolynomialRing(parent(a), "t", cached=false)
  f = t^m-a
  rt = roots(f)
  if length(rt) > 0
    return true, rt[1]
  else
    return false, a
  end
end

function roots(f::T) where T <: Union{fq_nmod_poly, fq_poly} # should be in Nemo and
                                    # made available for all finite fields I guess.
  q = size(base_ring(f))
  x = gen(parent(f))
  if degree(f) < q
    x = powermod(x, q, f)-x
  else
    x = x^Int(q)-x
  end
  f = gcd(f, x)
  l = factor(f).fac
  return elem_type(base_ring(f))[-divexact(constant_coefficient(x), leading_coefficient(x)) for x = keys(l) if degree(x)==1]
end


function setcoeff!(z::fq_nmod_poly, n::Int, x::fmpz)
   ccall((:fq_nmod_poly_set_coeff_fmpz, libflint), Nothing,
         (Ref{fq_nmod_poly}, Int, Ref{fmpz}, Ref{FqNmodFiniteField}),
         z, n, x, base_ring(parent(z)))
     return z
end

###############################################################################
#
#  Sturm sequence
#
###############################################################################

function _divide_by_content(f::fmpz_poly)
  p = primpart(f)
  if sign(leading_coefficient(f))== sign(leading_coefficient(p))
    return p
  else
    return -p
  end
end

function sturm_sequence(f::fmpz_poly)
  g = f
  h = _divide_by_content(derivative(g))
  seq = fmpz_poly[g,h]
  while true
    r = _divide_by_content(pseudorem(g,h))
    # r has the same sign as pseudorem(g, h)
    # To get a pseudo remainder sequence for the Sturm sequence,
    # we need r to be the pseudo remainder of |lc(b)|^(a - b + 1),
    # so we need some adjustment. See
    # https://en.wikipedia.org/wiki/Polynomial_greatest_common_divisor#Sturm_sequence_with_pseudo-remainders
    if leading_coefficient(h) < 0 && isodd(degree(g) - degree(h) + 1)
      r = -r
    end
    if r != 0
      push!(seq, -r)
      g, h = h, -r
    else
      break
    end
  end
  return seq
end

function _number_of_sign_changes(a::Vector{Int})
  nc = 0
  filter!(x -> x != 0, a)
  for i = 2:length(a)
    #if sign(a[i]) != sign(a[i-1])
    if a[i] != a[i-1]
      nc += 1
    end
  end
  return nc

end

# Number of positive roots

@doc Markdown.doc"""
    n_positive_roots(f::Union{fmpz_poly, fmpq_poly};
                     multiplicities::Bool = false) -> Int

Return the number of positive roots of $f$. If `multiplicities` is true,
than the roots are counted with multiplicities.
"""
function n_positive_roots(f::fmpz_poly; multiplicities::Bool = false)
  ff = Globals.Qx(f)
  if !multiplicities
    ffp = derivative(ff)
    g = gcd(ff, ffp)
    if isconstant(g)
      return _n_positive_roots_sf(f)
    else
      return n_positive_roots(divexact(ff, g))::Int
    end
  else
    res = 0
    for (g, e) in factor_squarefree(ff)
      res += n_positive_roots(g, multiplicities = false)::Int * e
    end
    return res
  end
end

function n_positive_roots(f::fmpq_poly; multiplicities::Bool = false)
  d = denominator(f)
  @assert d > 0
  g = Hecke.Globals.Zx(d * f)
  return n_positive_roots(g; multiplicities)
end

function _n_positive_roots_sf(f::fmpz_poly)
  @req !iszero(f) "Polynomial must be non-zero"

  # To use Sturm's theorem on (a, b], we need f(a) != 0
  # Here a = 0
  _, f = remove(f, gen(parent(f)))

  if isconstant(f)
    # f = x^n * a, so no positive root
    return 0
  end

  # Now f(a) != 0

  s = sturm_sequence(f)
  evinf = Int[sign(coeff(x, degree(x))) for x in s]
  ev0 = Int[sign(coeff(x, 0)) for x in s]
  return _number_of_sign_changes(ev0) - _number_of_sign_changes(evinf)
end

# Number of real roots
#
function n_real_roots(f::fmpz_poly)
  ff = Hecke.Globals.Qx(f)
  ffp = derivative(ff)
  g = gcd(ff, ffp)
  if isconstant(g)
    return _n_real_roots_sf(f)
  else
    return n_real_roots(divexact(ff, g))::Int
  end
end

function n_real_roots(f::fmpq_poly)
  d = denominator(f)
  @assert d > 0
  g = Hecke.Globals.Zx(d * f)
  return n_real_roots(g)
end

function _n_real_roots_sf(f::fmpz_poly)
  s = sturm_sequence(f)
  evinf = Int[numerator(sign(coeff(x, degree(x)))) for x in s]
  evminf = Int[((-1)^degree(x))*numerator(sign(coeff(x,degree(x)))) for x in s]
  return _number_of_sign_changes(evminf) - _number_of_sign_changes(evinf)
end

function n_real_roots(f::PolyElem{<:NumFieldElem}, P; sturm_sequence = PolyElem{nf_elem}[])
  if length(sturm_sequence) == 0
    s = Hecke.sturm_sequence(f)
  else
    s = sturm_sequence
  end

  evinf = Int[sign(coeff(x, degree(x)), P) for x in s]
  evminf = Int[((-1)^degree(s[i]))*evinf[i] for i in 1:length(s)]
  return _number_of_sign_changes(evminf) - _number_of_sign_changes(evinf)
end

@doc Markdown.doc"""
    n_positive_roots(f::PolyElem, P::InfPlc; multiplicities::Bool) -> true 

Return the number of positive roots of the polynomial $f$ at the real place $P$.
"""
function n_positive_roots(f::PolyElem{nf_elem}, P::InfPlc; multiplicities::Bool = false)
  fsq = factor_squarefree(f)
  p = 0
  for (g, e) in fsq
    p = p + _n_positive_roots_sqf(g, P) * (multiplicities ? e : 1)
  end
  return p
end

function _n_positive_roots_sqf(f::PolyElem{nf_elem}, P::InfPlc; start_prec::Int = 32)
  # We could do better this by not computing the roots.
  # We could just use the Sturm sequence as before.
  prec = start_prec
  while true
    coeffs = Vector{acb}(undef, length(f))
    c = evaluate(coeff(f, 0), P, prec)
    coeffs[1] = c
    C = parent(c)
    Cx, x = PolynomialRing(C, "x", cached = false)
    for i in 1:degree(f)
      coeffs[i + 1] = evaluate(coeff(f, i), P, prec)
    end
    g = Cx(coeffs)
    rts = real.(Hecke.roots(g))
    if any(contains_zero, rts)
      prec = 2 * prec
    else
      return count(is_positive, rts)
    end
  end
end

################################################################################
#
#  Squarefree factorization in characteristic 0
#
################################################################################

# This is Musser's algorithm
function factor_squarefree(f::PolyElem)
  @assert iszero(characteristic(base_ring(f)))
  res = Dict{typeof(f), Int}()
  if is_constant(f)
    return Fac(f, res)
  end
  c = leading_coefficient(f)
  f = divexact(f, c)
  di = gcd(f, derivative(f))
  if isone(di)
    res[f] = 1
    return Fac(one(parent(f)), res)
  end
  ei = divexact(f, di)
  i = 1
  while !is_constant(ei)
    eii = gcd(di, ei)
    dii = divexact(di, eii)
    if degree(eii) != degree(ei)
      res[divexact(ei, eii)] = i
    end
    i = i +1
    di = dii
    ei = eii
  end
  return Fac(parent(f)(c), res)
end


function factor_equal_deg(x::gfp_poly, d::Int)
  if degree(x) == d
    return gfp_poly[x]
  end
  fac = Nemo.gfp_poly_factor(x.mod_n)
  ccall((:nmod_poly_factor_equal_deg, libflint), UInt,
          (Ref{Nemo.gfp_poly_factor}, Ref{gfp_poly}, Int),
          fac, x, d)
  res = Vector{gfp_poly}(undef, fac.num)
  for i in 1:fac.num
    f = parent(x)()
    ccall((:nmod_poly_factor_get_nmod_poly, libflint), Nothing,
            (Ref{gfp_poly}, Ref{Nemo.gfp_poly_factor}, Int), f, fac, i-1)
    res[i] = f
  end
  return res
end

function factor_equal_deg(x::gfp_fmpz_poly, d::Int)
  if degree(x) == d
    return gfp_fmpz_poly[x]
  end
  fac = Nemo.gfp_fmpz_poly_factor(base_ring(x))
  ccall((:fmpz_mod_poly_factor_equal_deg, libflint), UInt,
        (Ref{Nemo.gfp_fmpz_poly_factor}, Ref{gfp_fmpz_poly}, Int, Ref{fmpz_mod_ctx_struct}),
          fac, x, d, x.parent.base_ring.ninv)
  res = Vector{gfp_fmpz_poly}(undef, fac.num)
  for i in 1:fac.num
    f = parent(x)()
    ccall((:fmpz_mod_poly_factor_get_fmpz_mod_poly, libflint), Nothing,
          (Ref{gfp_fmpz_poly}, Ref{Nemo.gfp_fmpz_poly_factor}, Int, Ref{fmpz_mod_ctx_struct}), f, fac, i-1, x.parent.base_ring.ninv)
    res[i] = f
  end
  return res
end

################################################################################
#
#  Squarefree factorization for fmpq_poly
#
################################################################################

@doc Markdown.doc"""
    factor_squarefree(x::fmpq_poly)

Returns the squarefree factorization of $x$.
"""
function factor_squarefree(x::fmpq_poly)
   res, z = _factor_squarefree(x)
   return Fac(parent(x)(z), res)
end

function _factor_squarefree(x::fmpq_poly)
   res = Dict{fmpq_poly, Int}()
   y = fmpz_poly()
   ccall((:fmpq_poly_get_numerator, libflint), Nothing,
         (Ref{fmpz_poly}, Ref{fmpq_poly}), y, x)
   fac = Nemo.fmpz_poly_factor()
   ccall((:fmpz_poly_factor_squarefree, libflint), Nothing,
              (Ref{Nemo.fmpz_poly_factor}, Ref{fmpz_poly}), fac, y)
   z = fmpz()
   ccall((:fmpz_poly_factor_get_fmpz, libflint), Nothing,
            (Ref{fmpz}, Ref{Nemo.fmpz_poly_factor}), z, fac)
   f = fmpz_poly()
   for i in 1:fac.num
      ccall((:fmpz_poly_factor_get_fmpz_poly, libflint), Nothing,
            (Ref{fmpz_poly}, Ref{Nemo.fmpz_poly_factor}, Int), f, fac, i - 1)
      e = unsafe_load(fac.exp, i)
      res[parent(x)(f)] = e
   end
   return res, fmpq(z, denominator(x))

end

function charpoly_mod(M::Generic.Mat{nf_elem}; integral::Bool = false, normal::Bool = false, proof::Bool = true)
  K = base_ring(M)
  p = p_start
  Kt, t = PolynomialRing(K, cached = false)
  f = Kt()
  f_last = f
  d = fmpz(1)
  stable = 5
  max_stable = 5
  while true
    p = next_prime(p)
    me = modular_init(K, p)
    if normal && length(me.fld) < degree(K)
      continue
    end
    t = Hecke.modular_proj(M, me)
    if !isdefined(me, :fldx)
      me.fldx = [PolynomialRing(x, "_x", cached=false)[1] for x = me.fld]
      me.Kx = Kt
    end

    fp = map(i-> charpoly(me.fldx[i], t[i]), 1:length(t))
    gp= Hecke.modular_lift(fp, me)
    if iszero(f)
      f = gp
    else
      f, d = induce_crt(f, d, gp, fmpz(p), true)
      if integral
        fl = true
        gg = f
      else
        fl, gg = induce_rational_reconstruction(f, d)
      end

      if fl && gg == f_last
        stable -= 1
        if stable <= 0
          break
        end
      else
        stable = max_stable
      end
      f_last = gg
    end
  end
  if !proof
    return f_last
  end
  error("Proof not implemented")
end
#=
function cyclic_generators(A::MatElem{T}) where {T <: FieldElem}
  b = matrix(base_ring(A), 0, nrows(A), [])
  g = matrix(base_ring(A), 0, nrows(A), [])
  while nrows(b) < nrows(A)
    if nrows(g) == 0
      g = zero_matrix(base_ring(A), 1, nrows(A))
      g[1,1] = 1
    else
      i = findfirst(j-> b[j,j] == 0, 1:nrows(b))
      if i == nothing
        i = nrows(b)+1
      end
      g = vcat(g, zero_matrix(base_ring(A), 1, nrows(A)))
      g[nrows(g), i] = 1
    end
    b = extend_cyclic_subspace(A::MatElem{T}, b::MatElem{T}, g)
    if nrows(b) == nrows(A)
      return g
    end
  end
end

function extend_cyclic_subspace(A::MatElem{T}, b::MatElem{T}, g) where {T <: FieldElem}
  while true
    g = vcat(g, g*A)
    cleanvect(b, g) #currently does only single rows...
    i = findfirst(i->is_zero_row(g, i), 1:nrows(g))
    if i != nothing
      b = vcat(b, view(g, 1:i-1, 1:ncols(g)))
      rk, b = rref!(b)
      @assert rk == nrows(b)
      return b
    end
    A *= A
  end
end
function cyclic_subspace(A::MatElem{T}, b::MatElem{T}) where {T <: FieldElem}
  b = deepcopy!(b)
  rk, b = rref!(b)
  bv = view(b, 1:rk, 1:ncols(b))
  if rk == 0 || rk == ncols(b)
    return bv
  end
  while true
    b2 = bv*A
    b = vcat(bv, b2)
    rk_new, b = rref!(b)
    if rk_new == rk
      return bv
    end
    rk= rk_new
    bv = view(b, 1:rk, 1:ncols(b))
    if rk == ncols(b)
      return bv
    end
    A *= A
  end
end
=#
#=
  plan for proof:
    if f is irreducible (or at least square-free), then there are
      (many) primes p s.th. f is square-free mod p
    then that means there are vectors b s.th. the
    space <M^i b | i> = everyhting, at least mod p, so in general.
    Now f(M)b = 0 implies f(M) = 0.

    if f is known to be integral, then one can use arb to compute the
      complex version and use this to derive bounds...

    There are also bounds on the coefficients which are sometimes tight
=#

function mulhigh_n(a::fmpz_poly, b::fmpz_poly, n::Int)
  c = parent(a)()
  #careful: as part of the interface, the coeffs 0 - (n-1) are random garbage
  ccall((:fmpz_poly_mulhigh_n, libflint), Nothing, (Ref{fmpz_poly}, Ref{fmpz_poly}, Ref{fmpz_poly}, Cint), c, a, b, n)
  return c
end
function mulhigh(a::PolyElem{T}, b::PolyElem{T}, n::Int) where {T}
  return mulhigh_n(a, b, degree(a) + degree(b) - n)
end


function roots(f::fmpz_poly, ::FlintRationalField; max_roots::Int = degree(f))
  if degree(f) < 1
    return fmpq[]
  end
  if degree(f) == 1
    return fmpq[-constant_coefficient(f)//leading_coefficient(f)]
  end

  g = gcd(f, derivative(f))
  if isone(g)
    h = f
  else
    h = divexact(f, g)
  end
  if degree(h) == 1
    return fmpq[-constant_coefficient(h)//leading_coefficient(h)]
  end
  h = primpart(h)

  global p_start
  p = p_start
  bd = leading_coefficient(h)+maximum(abs, coefficients(h))
  while true
    p = next_prime(p)
    k = GF(p)
    hp = change_base_ring(k, h)
    if !is_squarefree(hp)
      continue
    end
    k = ceil(Int, log(bd)/log(p))
    Hp = factor_mod_pk(h, p, k)
    pk = fmpz(p)^k
    r = fmpq[mod_sym(-constant_coefficient(x)*leading_coefficient(h), pk)//leading_coefficient(h) for x = keys(Hp) if degree(x) == 1]
    return [x for x = r if iszero(f(x)) ]
  end
end

function roots(f::fmpz_poly; max_roots::Int = degree(f))
  r = roots(f, FlintQQ, max_roots = max_roots)
  return fmpz[FlintZZ(x) for x = r if denominator(x) == 1]
end

function roots(f::fmpq_poly; max_roots::Int = degree(f))
  Zx, x = PolynomialRing(FlintZZ, cached = false)
  g = Zx(denominator(f)*f)
  return roots(g, FlintQQ)
end

function roots(f::Union{fmpz_poly, fmpq_poly}, R::AcbField, abs_tol::Int=R.prec, initial_prec::Int...)
  lf = factor(f)
  return map(R, vcat([_roots(g, abs_tol, initial_prec...) for g = keys(lf.fac) if degree(g) > 0]...))
end

function (f::acb_poly)(x::acb)
  return evaluate(f, x)
end

function factor(f::Union{fmpz_poly, fmpq_poly}, R::AcbField, abs_tol::Int=R.prec, initial_prec::Int...)
  g = factor(f)
  d = Dict{acb_poly, Int}()
  Rt, t = PolynomialRing(R, String(var(parent(f))), cached = false)
  for (k,v) = g.fac
    for r = roots(k, R)
      d[t-r] = v
    end
  end
  return Fac(Rt(g.unit), d)
end

function roots(f::Union{fmpz_poly, fmpq_poly}, R::ArbField, abs_tol::Int=R.prec, initial_prec::Int...)
  g = factor(f)
  r = elem_type(R)[]
  C = AcbField(precision(R))
  for k = keys(g.fac)
    s, _ = signature(k)
    rt = roots(k, C)
    append!(r, map(real, rt[1:s]))
  end
  return r
end

function factor(f::Union{fmpz_poly, fmpq_poly}, R::ArbField, abs_tol::Int=R.prec, initial_prec::Int...)
  g = factor(f)
  d = Dict{arb_poly, Int}()
  Rx, x = PolynomialRing(R, String(var(parent(f))), cached = false)
  C = AcbField(precision(R))
  for (k,v) = g.fac
    s, t = signature(k)
    r = roots(k, C)
    for i=1:s
      d[x-real(r[i])] = v
    end
    for i=1:t
      a = r[s+2*i-1]
      b = r[s+2*i]
      d[x^2-(real(a)+real(b))*x + real(a*b)] = v
    end
  end
  return Fac(Rx(g.unit), d)
end

################################################################################
#
#  Prefactorization discriminant relative case
#
################################################################################


function gcd_with_failure(a::Generic.Poly{T}, b::Generic.Poly{T}) where T
  if length(a) > length(b)
    (a, b) = (b, a)
  end
  if !is_invertible(leading_coefficient(a))[1]
    return leading_coefficient(a), a
  end
  if !is_invertible(leading_coefficient(b))[1]
    return leading_coefficient(b), a
  end
  while !iszero(a)
    (a, b) = (mod(b, a), a)
    if !iszero(a) && !is_invertible(leading_coefficient(a))[1]
      return leading_coefficient(a), a
    end
  end
  d = leading_coefficient(b)
  return one(parent(d)), divexact(b, d)
end

function mod(f::AbstractAlgebra.PolyElem{T}, g::AbstractAlgebra.PolyElem{T}) where {T <: RingElem}
  check_parent(f, g)
  if length(g) == 0
    throw(DivideError())
  end
  if length(f) >= length(g)
    f = deepcopy(f)
    b = leading_coefficient(g)
    g = inv(b)*g
    c = base_ring(f)()
    while length(f) >= length(g)
      l = -leading_coefficient(f)
      for i = 1:length(g)
        c = mul!(c, coeff(g, i - 1), l)
        u = coeff(f, i + length(f) - length(g) - 1)
        u = addeq!(u, c)
        f = setcoeff!(f, i + length(f) - length(g) - 1, u)
      end
      set_length!(f, normalise(f, length(f) - 1))
    end
  end
  return f
end
Nemo.normalise(f::fmpz_poly, ::Int) = degree(f)+1
Nemo.set_length!(f::fmpz_poly, ::Int) = nothing

function Base.divrem(f::AbstractAlgebra.PolyElem{T}, g::AbstractAlgebra.PolyElem{T}) where {T <: RingElem}
  check_parent(f, g)
  if length(g) == 0
     throw(DivideError())
  end
  if length(f) < length(g)
     return zero(parent(f)), f
  end
  f = deepcopy(f)
  binv = inv(leading_coefficient(g))
  g = divexact(g, leading_coefficient(g))
  qlen = length(f) - length(g) + 1
  q = zero(parent(f))
  fit!(q, qlen)
  c = zero(base_ring(f))
  while length(f) >= length(g)
     q1 = leading_coefficient(f)
     l = -q1
     q = setcoeff!(q, length(f) - length(g), q1*binv)
     for i = 1:length(g)
        c = mul!(c, coeff(g, i - 1), l)
        u = coeff(f, i + length(f) - length(g) - 1)
        u = addeq!(u, c)
        f = setcoeff!(f, i + length(f) - length(g) - 1, u)
     end
     set_length!(f, normalise(f, length(f) - 1))
  end
  return q, f
end


@doc Markdown.doc"""
    fmpz_poly_read!(a::fmpz_poly, b::String) -> fmpz_poly

Use flint's native read function to obtain the polynomial in the file with name `b`.
"""
function fmpz_poly_read!(a::fmpz_poly, b::String)
  f = ccall((:fopen, :libc), Ptr{Nothing}, (Cstring, Cstring), b, "r")
  ccall((:fmpz_poly_fread, libflint), Nothing, (Ptr{Nothing}, Ref{fmpz}), f, a)
  ccall((:fclose), Nothing, (Ptr{Nothing}, ), f)
  return a
end

@doc Markdown.doc"""
    mahler_measure_bound(f::fmpz_poly) -> fmpz

A upper bound on the Mahler measure of `f`.
The Mahler measure is the product over the roots of absolute value at least `1`.
"""
function mahler_measure_bound(f::fmpz_poly)
  return root(sum([coeff(f, i)^2 for i=0:degree(f)])-1, 2)+1
end

function prod1(a::Vector{T}; inplace::Bool = false) where T <: PolyElem
  if length(a) == 1
    return deepcopy(a[1])
  end
  if length(a) == 2
    if inplace
      r = mul!(a[1], a[1], a[2])
      return r
    else
      return a[1]*a[2]
    end
  end
  nl = div(length(a), 2)
  if isodd(length(a))
    nl += 1
  end
  anew = Vector{T}(undef, nl)
  for i = 1:length(anew)-1
    if inplace
      anew[i] = mul!(a[2*i-1], a[2*i-1], a[2*i])
    else
      anew[i] = a[2*i-1]*a[2*i]
    end
  end
  if isodd(length(a))
    anew[end] = a[end]
  else
    if inplace
      anew[end] = mul!(a[end-1], a[end-1], a[end])
    else
      anew[end] = a[end]*a[end-1]
    end
  end
  return prod1(anew, inplace = true)
end

################################################################################
#
#  Random polynomial
#
################################################################################

@doc Markdown.doc"""
    Base.rand(Rt::PolyRing{T}, n::Int) where T <: ResElem{fmpz} -> PolyElem{T}

Find a random polynomial of degree=$n$.
"""
function Base.rand(Rt::PolyRing{T}, n::Int) where T <: ResElem{fmpz}
    f = Rt()
    R = base_ring(Rt)
    for i = 0:n
        setcoeff!(f, i, rand(R))
    end
    return f
end
