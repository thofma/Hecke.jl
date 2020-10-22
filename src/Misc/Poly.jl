
export rational_reconstruction, farey_lift, div, valence, leading_coefficient,
       trailing_coefficient, constant_coefficient, factor_mod_pk,
       factor_mod_pk_init, hensel_lift, rres, rresx,
       coefficients, polynomial

function PolynomialRing(R::Ring; cached::Bool = false)
  return PolynomialRing(R, "x", cached = cached)
end

function PolynomialRing(R::FlintRationalField, a::Symbol; cached::Bool = true)
  Qx = FmpqPolyRing(R, a, cached)
  return Qx, gen(Qx)
end

function PolynomialRing(R::FlintIntegerRing, a::Symbol; cached::Bool = true)
  Zx = FmpzPolyRing(a, cached)
  return Zx, gen(Zx)
end

################################################################################
#
#  Dense polynomial types
#
################################################################################

dense_poly_type(::Type{arb}) = arb_poly

dense_poly_type(::Type{acb}) = acb_poly

dense_poly_type(::Type{fq}) = fq_poly

dense_poly_type(::Type{fq_nmod}) = fq_nmod_poly

dense_poly_type(::Type{gfp_elem}) = gfp_poly

dense_poly_type(::Type{Generic.ResF{fmpz}}) = gfp_fmpz_poly

dense_poly_type(::Type{fmpz}) = fmpz_poly

dense_poly_type(::Type{fmpq}) = fmpq_poly

dense_poly_type(::Type{nmod}) = nmod_poly

dense_poly_type(::Type{Generic.Res{fmpz}}) = fmpz_mod_poly

dense_poly_type(::Type{T}) where {T} = Generic.Poly{T}

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

  function lift(a::Nemo.fmpz_mod)
    return a.data
  end

  function lift(a::Nemo.gfp_fmpz_elem)
    return a.data
  end
end

function div(f::PolyElem, g::PolyElem)
  q, r = divrem(f,g)
  return q
end

function div(f::PolyElem{T}, g::T) where T
  return div(f, parent(f)(g))
end

function rem(f::PolyElem, g::PolyElem)
  return mod(f, g)
end

function ismonic(a::PolyElem)
  return isone(lead(a))
end

@doc Markdown.doc"""
    valence(f::PolyElem) -> RingElem

 The last non-zero coefficient of $f$.
"""
function valence(f::PolyElem)
  for i=0:degree(f)
    c = coeff(f, i)
    if !iszero(c)
      return c
    end
  end
  return c
end

@doc Markdown.doc"""
    leading_coefficient(f::PolyElem) -> RingElem

 The last leading coefficient of $f$.
"""
leading_coefficient(f::PolyElem) = lead(f)

@doc Markdown.doc"""
    trailing_coefficient(f::PolyElem) -> RingElem
    constant_coefficient(f::PolyElem) -> RingElem

 The constant coefficient of $f$.
"""
function trailing_coefficient(f::PolyElem)
  if iszero(f)
    return base_ring(f)(0)
  end
  return coeff(f, 0)
end

@doc Markdown.doc"""
    induce_rational_reconstruction(a::fmpz_poly, M::fmpz) -> fmpq_poly
Apply `rational_reconstruction` to each coefficient of $a$, resulting
in either a fail (return (false, s.th.)) or (true, g) for some rational
polynomial $g$ s.th. $g \equiv a \bmod M$.
"""
function induce_rational_reconstruction(a::fmpz_poly, M::fmpz)
  b = PolynomialRing(FlintQQ, parent(a).S, cached = false)[1]()
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


const constant_coefficient = trailing_coefficient

function resultant(f::fmpz_poly, g::fmpz_poly, d::fmpz, nb::Int)
  z = fmpz()
  ccall((:fmpz_poly_resultant_modular_div, libflint), Nothing,
     (Ref{fmpz}, Ref{fmpz_poly}, Ref{fmpz_poly}, Ref{fmpz}, Int),
     z, f, g, d, nb)
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
          (Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}), r, x, y, z)
  return r
end

function compose_mod_precomp(x::fmpz_mod_poly, A::fmpz_mat, z::fmpz_mod_poly, zinv::fmpz_mod_poly)
  r = parent(x)()
  ccall((:fmpz_mod_poly_compose_mod_brent_kung_precomp_preinv, libflint), Nothing,
    (Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}, Ref{fmpz_mat}, Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}), r, x, A, z, zinv)
  return r
end

function _inv_compose_mod(z::fmpz_mod_poly)
  r = reverse(z)
  ccall((:fmpz_mod_poly_inv_series_newton, libflint), Nothing,
      (Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}, Int), r, r, length(r))
  return r
end

function precomp_compose_mod(y::fmpz_mod_poly, z::fmpz_mod_poly)
  zinv = _inv_compose_mod(z)
  nr = Int(root(degree(z), 2)) + 1
  A = zero_matrix(FlintZZ, nr, degree(z))
  ccall((:fmpz_mod_poly_precompute_matrix, libflint), Nothing,
          (Ref{fmpz_mat}, Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}), A, y, z, zinv)
  return A, zinv
end

function my_compose_mod(x::fmpz_mod_poly, y::fmpz_mod_poly, z::fmpz_mod_poly)
  if degree(x) < degree(z)
    return compose_mod(x, y, z)
  end
  x1 = shift_right(x, degree(z))
  r1 = mulmod(my_compose_mod(x1, y, z), powmod(y, degree(z), z), z)
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
  yind = powmod(yind, q, z)
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
#  Random polynomial
#
################################################################################

@doc Markdown.doc"""
    Base.rand(Rt::PolyRing{T}, n::Int) where T <: ResElem{S} where S <: Union{fmpz, Integer} -> PolElem{T}
Find a random polynomial of degree=$n$.
"""
function Base.rand(Rt::PolyRing{T}, n::Int) where T <: ResElem{S} where S <: Union{fmpz, Integer}
  f = Rt()
  R = base_ring(Rt)
  for i=0:n
    setcoeff!(f, i, rand(R))
  end
  return f
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

function factor_to_array(a::fmpz_poly_factor)
  res = Array{Tuple{fmpz_poly, Int}, 1}()
  Zx,x = PolynomialRing(FlintZZ, "x", cached = false)
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
factor_mod_pk(::Type{Array}, H::HenselCtx) = factor_to_array(H.LF)
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
  return factor_to_array(H.LF)
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
  Rx, x = PolynomialRing(GF(p, cached=false), cached=false)
  h = lift(parent(f), div(Rx(f), Rx(g)))
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
  ccall((:fmpz_mod_poly_set_fmpz_poly, libflint), Nothing, (Ref{fmpz_mod_poly}, Ref{fmpz_poly}), r, t1)
  ccall((:fmpq_poly_get_denominator, libflint), Nothing, (Ref{fmpz}, Ref{fmpq_poly}), t2, a)
  if !isone(t2)
    res = ccall((:fmpz_invmod, libflint), Cint, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), t2, t2, modulus(base_ring(r)))
    @assert res != 0
    ccall((:fmpz_mod_poly_scalar_mul_fmpz, libflint), Nothing, (Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}, Ref{fmpz}), r, r, t2)
  end
end

function fmpq_poly_to_gfp_fmpz_poly_raw!(r::gfp_fmpz_poly, a::fmpq_poly, t1::fmpz_poly = fmpz_poly(), t2::fmpz = fmpz())
  ccall((:fmpq_poly_get_numerator, libflint), Nothing, (Ref{fmpz_poly}, Ref{fmpq_poly}), t1, a)
  ccall((:fmpz_mod_poly_set_fmpz_poly, libflint), Nothing, (Ref{gfp_fmpz_poly}, Ref{fmpz_poly}), r, t1)
  ccall((:fmpq_poly_get_denominator, libflint), Nothing, (Ref{fmpz}, Ref{fmpq_poly}), t2, a)
  if !isone(t2)
    res = ccall((:fmpz_invmod, libflint), Cint, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), t2, t2, modulus(base_ring(r)))
    @assert res != 0
    ccall((:fmpz_mod_poly_scalar_mul_fmpz, libflint), Nothing, (Ref{gfp_fmpz_poly}, Ref{gfp_fmpz_poly}, Ref{fmpz}), r, r, t2)
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
                  (Ref{fmpz_mod_poly}, Ref{fmpz_poly}), r, a)

end

function fmpz_poly_to_fmpz_mod_poly(Rx::Nemo.FmpzModPolyRing, f::fmpz_poly)
  g = Rx()
  fmpz_poly_to_fmpz_mod_poly_raw!(g, f)
  return g
end

################################################################################
#
#  Deflate and inflate
#
################################################################################

@doc Markdown.doc"""
    inflate(f::PolyElem, n::Int64) -> PolyElem
Given a polynomial $f$ in $x$, return $f(x^n)$, i.e. multiply
all exponents by $n$.
"""
function inflate(x::PolyElem, n::Int64)
  y = parent(x)()
  for i=0:degree(x)
    setcoeff!(y, n*i, coeff(x, i))
  end
  return y
end

@doc Markdown.doc"""
    deflate(f::PolyElem, n::Int64) -> PolyElem
Given a polynomial $f$ in $x^n$, write it as a polynomial in $x$, i.e. divide
all exponents by $n$.
"""
function deflate(x::PolyElem, n::Int64)
  y = parent(x)()
  for i=0:div(degree(x), n)
    setcoeff!(y, i, coeff(x, n*i))
  end
  return y
end

@doc Markdown.doc"""
    deflate(x::PolyElem) -> PolyElem
Deflate the polynomial $f$ maximally, i.e. find the largest $n$ s.th.
$f$ can be deflated by $n$, i.e. $f$ is actually a polynomial in $x^n$.
"""
function deflate(x::PolyElem)
  g = 0
  for i=0:degree(x)
    if coeff(x, i) != 0
      g = gcd(g, i)
      if g==1
        return x, 1
      end
    end
  end
  return deflate(x, g), g
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
    if isconstant(f) || isconstant(g)
      if isconstant(f) && isconstant(g)
        return gcd(coeff(f, 0), coeff(g, 0))
      end
      if isconstant(f)
        if !isone(gcd(lead(g), coeff(f, 0)))
          cg = content(g - coeff(g, 0))
          ann = divexact(coeff(f, 0), gcd(coeff(f, 0), cg))
          return gcd(coeff(f, 0), ann*coeff(g, 0))
        else
          return coeff(f, 0)
        end
      end
      if !isone(gcd(lead(f), coeff(g, 0)))
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


struct PolyCoeffs{T <: RingElem}
  f::T
end

function coefficients(f::PolyElem)
  return PolyCoeffs(f)
end

function Base.iterate(PC::PolyCoeffs{<:PolyElem}, st::Int = -1)
  st += 1
  if st > degree(PC.f)
    return nothing
  else
    return coeff(PC.f, st), st
  end
end

Base.IteratorEltype(M::PolyElem) = Base.HasEltype()
Base.eltype(M::PolyElem{T}) where {T} = T

Base.IteratorSize(M::PolyCoeffs{<:PolyElem}) = Base.HasLength()
Base.length(M::PolyCoeffs{<:PolyElem}) = degree(M.f)+1

function Base.lastindex(a::PolyCoeffs{<:PolyElem})
  return degree(a.f)
end

function Base.getindex(a::PolyCoeffs{<:PolyElem}, i::Int)
  return coeff(a.f, i)
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

################################################################################
#
#  Power sums
#
################################################################################

@doc Markdown.doc"""
    polynomial_to_power_sums(f::PolyElem{T}, n::Int=degree(f)) -> Array{T, 1}
Uses Newton (or Newton-Girard) formulas to compute the first $n$
power sums from the coefficients of $f$.
"""
function polynomial_to_power_sums(f::PolyElem{T}, n::Int=degree(f)) where T <: FieldElem
  d = degree(f)
  R = base_ring(f)
  S = PowerSeriesRing(R, n+1, "gen(S)", cached = false, model =:capped_absolute)[1]
  #careful: converting to power series and derivative do not commute
  #I also don't quite get this: I thought this was just the log,
  #but it isn't
  A = S()
  B = S()
  fit!(A, d)
  fit!(B, d+1)
#  A.val = B.val = 0
  for i=1:d
    c = coeff(f, i)
    setcoeff!(A, d-i, i*c)
    setcoeff!(B, d-i, c)
  end
  setcoeff!(B, d, coeff(f, 0))
  A.prec = n+1
  B.prec = n+1

#  @show A, B
#  A = S([coeff(reverse(derivative(f)), i) for i=0:d-1], d, n+1, 0)
#  B = S([coeff(reverse(f), i) for i=0:d], d+1, n+1, 0)
  L = A*inv(B)
#  s = T()
  s = T[coeff(L, i) for i=1:n]
  return s
end

#plain vanilla recursion
function polynomial_to_power_sums(f::PolyElem{T}, n::Int=degree(f)) where T
  if n == 0
    return elem_type(base_ring(f))[]
  end
  d = degree(f)
  R = base_ring(f)
  E = T[(-1)^i*coeff(f, d-i) for i=0:min(d, n)] #should be the elementary symm.
  while length(E) <= n
    push!(E, R(0))
  end
  P = T[]

  push!(P, E[1+1])
  for k=2:n
    push!(P, (-1)^(k-1)*k*E[k+1] + sum((-1)^(k-1+i)*E[k-i+1]*P[i] for i=1:k-1))
  end
  return P
end

@doc Markdown.doc"""
    power_sums_to_polynomial(P::Array{T, 1}) -> PolyElem{T}
Uses the Newton (or Newton-Girard) identities to obtain the polynomial
coefficients (the elementary symmetric functions) from the power sums.
"""
function power_sums_to_polynomial(P::Array{T, 1}) where T <: FieldElem
  d = length(P)
  R = parent(P[1])
  S = PowerSeriesRing(R, d, "gen(S)")[1] #, model = :capped_absolute)[1]
  s = S(P, length(P), d, 0)

  r = -integral(s)
  r1 = exp(r)
  #=
  if false
    r = S(T[R(1), -P[1]], 2, 2, 0)
    la = [d+1]
    while la[end]>1
      push!(la, div(la[end]+1, 2))
    end
    n = length(la)-1
    while n > 0
      set_precision!(r, la[n])
      rr = derivative(r)*inv(r)
      md = -(rr+s)
      m = S([R(1)], 1, la[n], 0)+integral(md)
      r *= m
      n -= 1
    end
    println("new exp $r")
  end
  =#
  @assert iszero(valuation(r1))
  Rx, x = PolynomialRing(R, cached = false)
  return Rx([Nemo.polcoeff(r1, d-i) for i=0:d])
end

function power_sums_to_polynomial(P::Array{T, 1}) where T
  E = T[one(parent(P[1]))]
  R = parent(P[1])
  last_non_zero = 0
  for k=1:length(P)
    push!(E, divexact(sum((-1)^(i-1)*E[k-i+1]*P[i] for i=1:k), R(k)))
    if E[end] != 0
      last_non_zero = k
    end
  end
  E = E[1:last_non_zero+1]
  d = length(E) #the length of the resulting poly...
  for i=1:div(d, 2)
    E[i], E[d-i+1] = (-1)^(d-i)*E[d-i+1], (-1)^(i-1)*E[i]
  end
  if isodd(d)
    E[div(d+1, 2)] *= (-1)^div(d, 2)
  end
  
  return PolynomialRing(R, cached = false)[1](E)
end

##############################################################
# all of this should be in Nemo/AbstractAlgebra
#
#TODO:
# expand systematically for all finite fields
# and for fmpz/fmpq poly
# for fun: ispower(a::nf_elem)
#




function factor(f::PolyElem, R::Field)
  Rt = PolynomialRing(R, "t", cached = false)[1]
  f1 = change_base_ring(R, f, parent = Rt)
  return factor(f1)
end

function factor(f::fmpq_poly, R::T) where T <: Union{Nemo.FqNmodFiniteField, Nemo.GaloisField}
  Rt, t = PolynomialRing(R, "t", cached=false)
  return factor(Rt(f))
end

#TODO: better signature? better name?
function factor(f::FracElem, R::Ring)
  fn = factor(R(numerator(f)))
  fd = factor(R(denominator(f)))
  fn.unit = divexact(fn.unit, fd.unit)
  for (k,v) = fd.fac
    if Base.haskey(fn.fac, k)
      fn.fac[k] -= v
    else
      fn.fac[k] = -v
    end
  end
  return fn
end

function roots(f::PolyElem, R::Field)
  Rt = PolynomialRing(R, "t", cached = false)[1]
  f1 = change_base_ring(R, f, parent = Rt)
  return roots(f1)
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
    coeffsff[i] = K(lift(coeff(f, i)))
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

function ispower(a::fq_nmod, m::Int)
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
    x = powmod(x, q, f)-x
  else
    x = x^Int(q)-x
  end
  f = gcd(f, x)
  l = factor(f).fac
  return elem_type(base_ring(f))[-divexact(trailing_coefficient(x), leading_coefficient(x)) for x = keys(l) if degree(x)==1]
end

# generic fall back
# ...
function roots(f::PolyElem)
  lf = factor(f)
  rts = Vector{elem_type(base_ring(f))}()
  for (p, e) in lf
    if degree(p) == 1
      push!(rts, -divexact(trailing_coefficient(p), leading_coefficient(p)))
    end
  end
  return rts
end

function ispower(a::RingElem, n::Int)
  if isone(a) || iszero(a)
    return true, a
  end
  if isone(-a) && isodd(n)
    return true, a
  end
  R = parent(a)
  Rt, t = PolynomialRing(R, "t", cached = false)
  r = roots(t^n-a)
  if length(r) == 0
    return false, a
  else
    return true, r[1]
  end
end

function ispower(a::PolyElem, n::Int)
  #not the best algorithm... but it works generically
  #probably a equal-degree-factorisation would be good + some more gcd's
  #implement some Newton-type algo?
  degree(a) % n == 0 || return false, a
  fl, x = ispower(leading_coefficient(a), n)
  fl || return false, a
  f = factor(a)
  all(i -> i % n == 0, values(f.fac)) || return false, a
  return true, x*prod(p^div(k, n) for (p,k) = f.fac)
end

function root(a::RingElem, n::Int)
  fl, b = ispower(a, n)
  fl || error("element does not have a $n-th root")
  return b
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

#See Wikipedia as a reference
function _divide_by_content(f::fmpz_poly)

  p = primpart(f)
  if sign(lead(f))== sign(lead(p))
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
    if r != 0
      push!(seq, -r)
      g, h = h, -r
    else
      break
    end
  end
  return seq

end

function _number_changes(a::Array{Int,1})

  nc = 0
  filter!(x -> x != 0, a)
  for i = 2:length(a)
    if sign(a[i]) != sign(a[i-1])
      nc += 1
    end
  end
  return nc

end

function number_positive_roots(f::fmpz_poly)

  s = sturm_sequence(f)
  evinf = Int[sign(coeff(x, degree(x))) for x in s]
  ev0 = Int[sign(coeff(x,0)) for x in s]
  return _number_changes(ev0)-_number_changes(evinf)

end

function number_real_roots(f::fmpz_poly)
  s = sturm_sequence(f)
  evinf = Int[sign(coeff(x, degree(x))) for x in s]
  evminf = Int[((-1)^degree(x))*sign(coeff(x,degree(x))) for x in s]
  return _number_changes(evminf)-_number_changes(evinf)
end

function sturm_sequence(f::PolyElem{<:FieldElem})
  g = f
  h = derivative(g)
  #h = _divide_by_content(derivative(g))
  seq = typeof(f)[g,h]
  while true
    #r = _divide_by_content(pseudorem(g,h))
    r = rem(g, h)
    if r != 0
      push!(seq, -r)
      g, h = h, -r
    else 
      break
    end
  end
  return seq

end

function number_real_roots(f::PolyElem{<:NumFieldElem}, P; sturm_sequence = PolyElem{nf_elem}[])
  if length(sturm_sequence) == 0
    s = Hecke.sturm_sequence(f)
  else
    s = sturm_sequence
  end

  evinf = Int[sign(coeff(x, degree(x)), P) for x in s]
  evminf = Int[((-1)^degree(s[i]))*evinf[i] for i in 1:length(s)]
  return _number_changes(evminf) - _number_changes(evinf)
end

function number_positive_roots(f::PolyElem{nf_elem}, P::InfPlc)
  fsq = factor_squarefree(f)
  p = 0
  for (g, e) in fsq
    p = p + _number_positive_roots_sqf(g, P) * e
  end
  return p
end

function _number_positive_roots_sqf(f::PolyElem{nf_elem}, P::InfPlc; start_prec::Int = 32)
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
      return count(ispositive, rts)
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
  c = lead(f)
  f = divexact(f, c)
  res = Dict{typeof(f), Int}()
  di = gcd(f, derivative(f))
  if isone(di)
    res[f] = 1
    return Fac(one(parent(f)), res)
  end
  ei = divexact(f, di)
  i = 1
  while !isconstant(ei)
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
  fac = Nemo.gfp_fmpz_poly_factor(x.mod_n)
  ccall((:fmpz_mod_poly_factor_equal_deg, libflint), UInt,
          (Ref{Nemo.gfp_fmpz_poly_factor}, Ref{gfp_fmpz_poly}, Int),
          fac, x, d)
  res = Vector{gfp_fmpz_poly}(undef, fac.num)
  for i in 1:fac.num
    f = parent(x)()
    ccall((:fmpz_mod_poly_factor_get_nmod_poly, libflint), Nothing,
            (Ref{gfp_fmpz_poly}, Ref{Nemo.gfp_fmpz_poly_factor}, Int), f, fac, i-1)
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
    i = findfirst(i->iszero_row(g, i), 1:nrows(g))
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
  ccall((:fmpz_poly_mulhigh_n, libflint), Nothing, (Ref{fmpz_poly}, Ref{fmpz_poly}, Ref{fmpz_poly}, Cint), c, a, b, n)
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
    b = truncate(b, n-i-1)
    #truncate both a and b to n-i-1 (for generic polys one could just change the length)
  end
  return r
end

#computes the top coeffs starting with x^n
function divhigh(a::PolyElem{T}, b::PolyElem{T}, n0::Int) where {T}
  r = parent(a)()
  n = degree(a) - degree(b) - n0
  Hecke.fit!(r, degree(a) - degree(b))
  a = deepcopy(a)
  k = degree(a) - n0
  da = degree(a)
  for i=0:n
    if degree(a) < degree(b)
      break
    end
    q = divexact(coeff(a, da), lead(b))
    setcoeff!(r, da - degree(b), q)
    for j=da:-1:max(k, da - degree(b))
      setcoeff!(a, j, coeff(a, j)-q*coeff(b, j-da+degree(b)))
    end
    da -= 1
#    a = a-q*shift_left(b, degree(a) - degree(b)) # inplace, one operation would be cool
  end
  if iszero(r)
    #set_length(, -1) fails
    return r
  end
  Hecke.set_length!(r, Hecke.normalise(r, length(r) - 1))
  return r
end


function roots(f::fmpz_poly, ::FlintRationalField; max_roots::Int = degree(f))
  if degree(f) < 1
    return fmpq[]
  end
  if degree(f) == 1
    return fmpq[-trailing_coefficient(f)//lead(f)]
  end

  g = gcd(f, derivative(f))
  if isone(g)
    h = f
  else
    h = divexact(f, g)
  end
  if degree(h) == 1
    return fmpq[-trailing_coefficient(h)//lead(h)]
  end
  h = primpart(h)

  global p_start
  p = p_start
  bd = lead(h)+maximum(abs, coefficients(h))
  while true
    p = next_prime(p)
    k = GF(p)
    hp = change_base_ring(k, h)
    if !issquarefree(hp)
      continue
    end
    k = ceil(Int, log(bd)/log(p))
    Hp = factor_mod_pk(h, p, k)
    pk = fmpz(p)^k
    r = fmpq[mod_sym(-trailing_coefficient(x)*lead(h), pk)//lead(h) for x = keys(Hp) if degree(x) == 1]
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
  return _roots(f, abs_tol, initial_prec...)
end

function (f::acb_poly)(x::acb)
  return evaluate(f, x)
end

function polynomial(A::Array{T, 1}) where {T <: RingElem}
  P = parent(A[1])
  @assert all(x->parent(x) == P, A)
  Pt, t = PolynomialRing(P, cached = false)
  return Pt(A)
end

function polynomial(R::Ring, A::Array{T, 1}) where {T <: RingElem}
  return polynomial(map(R, A))
end

function polynomial(R::Ring, A::Array{T, 1}) where {T <: Integer}
  return polynomial(map(R, A))
end

function polynomial(R::Ring, A::Array{T, 1}) where {T <: Rational}
  return polynomial(map(R, A))
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
  if !isinvertible(lead(a))[1]
    return lead(a), a
  end
  if !isinvertible(lead(b))[1]
    return lead(b), a
  end
  while !iszero(a)
    (a, b) = (mod(b, a), a)
    if !iszero(a) && !isinvertible(lead(a))[1]
      return lead(a), a
    end
  end
  d = lead(b)
  return one(parent(d)), divexact(b, d)
end

function mod(f::AbstractAlgebra.PolyElem{T}, g::AbstractAlgebra.PolyElem{T}) where {T <: RingElem}
  check_parent(f, g)
  if length(g) == 0
    throw(DivideError())
  end
  if length(f) >= length(g)
    f = deepcopy(f)
    b = lead(g)
    g = inv(b)*g
    c = base_ring(f)()
    while length(f) >= length(g)
      l = -lead(f)
      for i = 1:length(g) - 1
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

function Base.divrem(f::AbstractAlgebra.PolyElem{T}, g::AbstractAlgebra.PolyElem{T}) where {T <: RingElem}
  check_parent(f, g)
  if length(g) == 0
     throw(DivideError())
  end
  if length(f) < length(g)
     return zero(parent(f)), f
  end
  f = deepcopy(f)
  binv = inv(lead(g))
  g = divexact(g, lead(g))
  qlen = length(f) - length(g) + 1
  q = parent(f)()
  fit!(q, qlen)
  c = base_ring(f)()
  while length(f) >= length(g)
     q1 = lead(f)
     l = -q1
     q = setcoeff!(q, length(f) - length(g), q1*binv)
     for i = 1:length(g) - 1
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
