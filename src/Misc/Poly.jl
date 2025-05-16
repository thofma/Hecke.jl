import Nemo: fmpz_mod_ctx_struct



@doc raw"""
    induce_rational_reconstruction(a::ZZPolyRingElem, M::ZZRingElem) -> QQPolyRingElem

Apply `rational_reconstruction` to each coefficient of $a$, resulting
in either a fail (return (false, s.th.)) or (true, g) for some rational
polynomial $g$ s.th. $g \equiv a \bmod M$.
"""
function induce_rational_reconstruction(a::ZZPolyRingElem, M::ZZRingElem; parent=polynomial_ring(QQ, parent(a).S, cached = false)[1])
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



################################################################################
#
#  Modular composition
#
################################################################################

function compose_mod(x::ZZModPolyRingElem, y::ZZModPolyRingElem, z::ZZModPolyRingElem)
  check_parent(x,y)
  check_parent(x,z)
  r = parent(x)()
  ccall((:fmpz_mod_poly_compose_mod, libflint), Nothing,
          (Ref{ZZModPolyRingElem}, Ref{ZZModPolyRingElem}, Ref{ZZModPolyRingElem}, Ref{ZZModPolyRingElem}, Ref{fmpz_mod_ctx_struct}), r, x, y, z, x.parent.base_ring.ninv)
  return r
end

function compose_mod_precomp(x::ZZModPolyRingElem, A::ZZMatrix, z::ZZModPolyRingElem, zinv::ZZModPolyRingElem)
  r = parent(x)()
  ccall((:fmpz_mod_poly_compose_mod_brent_kung_precomp_preinv, libflint), Nothing,
        (Ref{ZZModPolyRingElem}, Ref{ZZModPolyRingElem}, Ref{ZZMatrix}, Ref{ZZModPolyRingElem}, Ref{ZZModPolyRingElem}, Ref{fmpz_mod_ctx_struct}), r, x, A, z, zinv, x.parent.base_ring.ninv)
  return r
end

function _inv_compose_mod(z::ZZModPolyRingElem)
  r = reverse(z)
  ccall((:fmpz_mod_poly_inv_series, libflint), Nothing,
        (Ref{ZZModPolyRingElem}, Ref{ZZModPolyRingElem}, Int, Ref{fmpz_mod_ctx_struct}), r, r, length(r), z.parent.base_ring.ninv)
  return r
end

function precomp_compose_mod(y::ZZModPolyRingElem, z::ZZModPolyRingElem)
  zinv = _inv_compose_mod(z)
  nr = Int(iroot(degree(z), 2)) + 1
  A = zero_matrix(ZZ, nr, degree(z))
  ccall((:fmpz_mod_poly_precompute_matrix, libflint), Nothing,
        (Ref{ZZMatrix}, Ref{ZZModPolyRingElem}, Ref{ZZModPolyRingElem}, Ref{ZZModPolyRingElem}, Ref{fmpz_mod_ctx_struct}), A, y, z, zinv, y.parent.base_ring.ninv)
  return A, zinv
end

function my_compose_mod(x::ZZModPolyRingElem, y::ZZModPolyRingElem, z::ZZModPolyRingElem)
  if degree(x) < degree(z)
    return compose_mod(x, y, z)
  end
  x1 = shift_right(x, degree(z))
  r1 = mulmod(my_compose_mod(x1, y, z), powermod(y, degree(z), z), z)
  x2 = truncate(x, degree(z))
  return r1 + compose_mod(x2, y, z)
end

function my_compose_mod_precomp(x::ZZModPolyRingElem, A::ZZMatrix, z::ZZModPolyRingElem, zinv::ZZModPolyRingElem)

  if degree(x) < degree(z)
    res1 = compose_mod_precomp(x, A, z, zinv)
    return res1
  end

  #First, I compute x^degree(z) mod z
  #The rows of A contain the powers up to sqrt(degree(z))...
  Rx = parent(x)
  ind = nrows(A)
  q, r = divrem(degree(z), ind-1)
  yind = Rx(Nemo.ZZModRingElem[base_ring(Rx)(A[ind, j]) for j = 1:ncols(A)])
  yind = powermod(yind, q, z)
  if !iszero(r)
    ydiff = Rx(Nemo.ZZModRingElem[base_ring(Rx)(A[r+1, j]) for j = 1:ncols(A)])
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
  res = Dict{ZZPolyRingElem,Int}()
  Zx,x = polynomial_ring(ZZ, "x", cached = false)
  for i in 1:a._num
    f = Zx()
    ccall((:fmpz_poly_set, libflint), Nothing, (Ref{ZZPolyRingElem}, Ref{fmpz_poly_raw}), f, a.poly+(i-1)*sizeof(fmpz_poly_raw))
    res[f] = unsafe_load(a.exp, i)
  end
  return res
end

function factor_to_array(a::fmpz_poly_factor; parent::ZZPolyRing = polynomial_ring(ZZ, "x", cached = false)[1])
  res = Vector{Tuple{ZZPolyRingElem, Int}}()
  Zx = parent
  for i in 1:a._num
    f = Zx()
    ccall((:fmpz_poly_set, libflint), Nothing, (Ref{ZZPolyRingElem}, Ref{fmpz_poly_raw}), f, a.poly+(i-1)*sizeof(fmpz_poly_raw))
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
       (Ref{fmpz_poly_factor}, Ref{Int}, Ref{fmpz_poly_raw}, Ref{fmpz_poly_raw}, Ref{ZZPolyRingElem}, Ref{Nemo.nmod_poly_factor}, Int),
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
       (Ref{fmpz_poly_factor}, Ref{Int}, Ref{fmpz_poly_raw}, Ref{fmpz_poly_raw}, Ref{ZZPolyRingElem}, UInt, UInt, Int, Ref{ZZRingElem}),
       a.LF, a.link, a.v, a.w, a.f, a.prev, a.N, N, ZZRingElem(a.p))
  a.N = N
end

@doc raw"""
    factor_mod_pk(f::ZZPolyRingElem, p::Int, k::Int) -> Dict{ZZPolyRingElem, Int}

 For $f$ that is square-free modulo $p$, return the factorisation modulo $p^k$.
"""
function factor_mod_pk(f::ZZPolyRingElem, p::Int, k::Int)
  H = HenselCtx(f, ZZRingElem(p))
  if H.r == 1
    return Dict(H.f => 1)
  end
  start_lift(H, k)
  return factor_to_dict(H.LF)
end

@doc raw"""
    factor_mod_pk_init(f::ZZPolyRingElem, p::Int) -> HenselCtx

 For $f$ that is square-free modulo $p$, return a structure that allows to compute
 the factorisation modulo $p^k$ for any $k$.
"""
function factor_mod_pk_init(f::ZZPolyRingElem, p::Int)
  H = HenselCtx(f, ZZRingElem(p))
  return H
end

@doc raw"""
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
function hensel_lift!(G::ZZPolyRingElem, H::ZZPolyRingElem, A::ZZPolyRingElem, B::ZZPolyRingElem, f::ZZPolyRingElem, g::ZZPolyRingElem, h::ZZPolyRingElem, a::ZZPolyRingElem, b::ZZPolyRingElem, p::ZZRingElem, p1::ZZRingElem)
  ccall((:fmpz_poly_hensel_lift, libflint), Nothing, (Ref{ZZPolyRingElem}, Ref{ZZPolyRingElem},  Ref{ZZPolyRingElem},  Ref{ZZPolyRingElem},  Ref{ZZPolyRingElem},  Ref{ZZPolyRingElem},  Ref{ZZPolyRingElem}, Ref{ZZPolyRingElem}, Ref{ZZPolyRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}), G, H, A, B, f, g, h, a, b, p, p1)
end

@doc raw"""
    hensel_lift(f::ZZPolyRingElem, g::ZZPolyRingElem, h::ZZPolyRingElem, p::ZZRingElem, k::Int) -> (ZZPolyRingElem, ZZPolyRingElem)

 Given $f = gh$ modulo $p$ for $g, h$ coprime modulo $p$, compute $G, H$ s.th. $f = GH mod p^k$ and
 $G = g mod p$, $H = h mod p$.
"""
function hensel_lift(f::ZZPolyRingElem, g::ZZPolyRingElem, h::ZZPolyRingElem, p::ZZRingElem, k::Int)
  Rx, x = polynomial_ring(Native.GF(p, cached=false), cached=false)
  fl, a, b = gcdx(Rx(g), Rx(h))
  @assert isone(fl)
  @assert k>= 2
  ## if one of the cofactors is zero, this crashes.
  ## this can only happen if one of the factors is one. In this case, the other
  ## is essentially f and f would be a legal answer. Probably reduced mod p^k
  ## with all non-negative coefficients
  ## for now:
  if is_one(g)
    h = mod(h, p^k)
    return g, h
  elseif is_one(h)
    g = mod(g, p^k)
    return g, h
  end

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

@doc raw"""
    hensel_lift(f::ZZPolyRingElem, g::ZZPolyRingElem, p::ZZRingElem, k::Int) -> (ZZPolyRingElem, ZZPolyRingElem)

 Given $f$ and $g$ such that $g$ is a divisor of $f mod p$ and $g$ and $f/g$ are coprime, compute a hensel lift of $g modulo p^k$.
"""
function hensel_lift(f::ZZPolyRingElem, g::ZZPolyRingElem, p::ZZRingElem, k::Int)
  @assert is_monic(g) #experimentally: otherwise, the result is bad...
  Rx, x = polynomial_ring(Native.GF(p, cached=false), cached=false)
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


################################################################################
#
#  Reduced resultant
#
################################################################################

@doc raw"""
    reduced_resultant(f::ZZPolyRingElem, g::ZZPolyRingElem) -> ZZRingElem

The reduced resultant of $f$ and $g$,
that is a generator for the ideal $(f, g) \cap Z$.
"""
function reduced_resultant(f::ZZPolyRingElem, g::ZZPolyRingElem)
  return rres_bez(f,g)
end

function rres_hnf(f::ZZPolyRingElem, g::ZZPolyRingElem)
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  s = Nemo.Generic.sylvester_matrix(f, g)
  h = hnf(s)
  return abs(h[nrows(h), ncols(h)])
end

function rres_bez(f::ZZPolyRingElem, g::ZZPolyRingElem)
  Nemo.check_parent(f, g)
  Qx = polynomial_ring(QQ, "x", cached = false)[1]
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
    return ZZRingElem(0)
  end
  return lcm(denominator(q), denominator(w))
end

@doc raw"""
    rresx(f::ZZPolyRingElem, g::ZZPolyRingElem) -> r, u, v

The reduced resultant, i.e. a generator for the intersect
of the ideal generated by $f$ and $g$ with the integers.
As well as polynomials $u$ and $v$ s.th. $r = uf+vg$,
$\deg u < \deg g$ and $\deg v < \deg f$.
"""
function rresx(f::ZZPolyRingElem, g::ZZPolyRingElem)
  Nemo.check_parent(f, g)
  @assert typeof(f) == typeof(g)
  Qx = polynomial_ring(QQ, "x", cached = false)[1]
  g, q, w = gcdx(Qx(f), Qx(g))
  l = lcm(denominator(q), denominator(w))
  Zx = parent(f)
  return l, Zx(l*q), Zx(l*w)
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

@doc raw"""
    n_positive_roots(f::Union{ZZPolyRingElem, QQPolyRingElem};
                     multiplicities::Bool = false) -> Int

Return the number of positive roots of $f$. If `multiplicities` is true,
than the roots are counted with multiplicities.
"""
function n_positive_roots(f::ZZPolyRingElem; multiplicities::Bool = false)
  ff = Globals.Qx(f)
  if !multiplicities
    ffp = derivative(ff)
    g = gcd(ff, ffp)
    if is_constant(g)
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

function n_positive_roots(f::QQPolyRingElem; multiplicities::Bool = false)
  d = denominator(f)
  @assert d > 0
  g = Hecke.Globals.Zx(d * f)
  return n_positive_roots(g; multiplicities)
end

function _n_positive_roots_sf(f::ZZPolyRingElem)
  @req !iszero(f) "Polynomial must be non-zero"

  # To use Sturm's theorem on (a, b], we need f(a) != 0
  # Here a = 0
  _, f = remove(f, gen(parent(f)))

  if is_constant(f)
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
function n_real_roots(f::ZZPolyRingElem)
  ff = Hecke.Globals.Qx(f)
  ffp = derivative(ff)
  g = gcd(ff, ffp)
  if is_constant(g)
    return _n_real_roots_sf(f)
  else
    return n_real_roots(divexact(ff, g))::Int
  end
end

function n_real_roots(f::QQPolyRingElem)
  d = denominator(f)
  @assert d > 0
  g = Hecke.Globals.Zx(d * f)
  return n_real_roots(g)
end

function _n_real_roots_sf(f::ZZPolyRingElem)
  s = sturm_sequence(f)
  evinf = Int[numerator(sign(coeff(x, degree(x)))) for x in s]
  evminf = Int[((-1)^degree(x))*numerator(sign(coeff(x,degree(x)))) for x in s]
  return _number_of_sign_changes(evminf) - _number_of_sign_changes(evinf)
end

function n_real_roots(f::PolyRingElem{<:NumFieldElem}, P; sturm_sequence = PolyRingElem{AbsSimpleNumFieldElem}[])
  if length(sturm_sequence) == 0
    s = Hecke.sturm_sequence(f)
  else
    s = sturm_sequence
  end

  evinf = Int[sign(coeff(x, degree(x)), P) for x in s]
  evminf = Int[((-1)^degree(s[i]))*evinf[i] for i in 1:length(s)]
  return _number_of_sign_changes(evminf) - _number_of_sign_changes(evinf)
end

@doc raw"""
    n_positive_roots(f::PolyRingElem, P::InfPlc; multiplicities::Bool) -> true

Return the number of positive roots of the polynomial $f$ at the real place $P$.
"""
function n_positive_roots(f::PolyRingElem{AbsSimpleNumFieldElem}, P::NumFieldEmb; multiplicities::Bool = false)
  fsq = factor_squarefree(f)
  p = 0
  for (g, e) in fsq
    p = p + _n_positive_roots_sqf(g, P) * (multiplicities ? e : 1)
  end
  return p
end

function _n_positive_roots_sqf(f::PolyRingElem{AbsSimpleNumFieldElem}, P::NumFieldEmb; start_prec::Int = 32)
  # We could do better this by not computing the roots.
  # We could just use the Sturm sequence as before.
  prec = start_prec
  while true
    prec > 2^10 && error("Something wrong here")
    coeffs = Vector{AcbFieldElem}(undef, length(f))
    c = evaluate(coeff(f, 0), P, prec)
    coeffs[1] = c
    C = parent(c)
    Cx, x = polynomial_ring(C, "x", cached = false)
    for i in 1:degree(f)
      coeffs[i + 1] = evaluate(coeff(f, i), P, prec)
    end
    g = Cx(coeffs)
    try
      rts = roots(g, initial_prec = div(prec, 2))
    catch e
      e isa ErrorException && startswith(e.msg, "unable to isolate all roots") || rethrow()
      prec *= 2
      continue
    end
    rts = real.(rts)
    if any(contains_zero, rts)
      prec = 2 * prec
    else
      return count(is_positive, rts)
    end
  end
end

################################################################################
#
#  Squarefree factorization for QQPolyRingElem
#
################################################################################

function charpoly_mod(M::Generic.Mat{AbsSimpleNumFieldElem}; integral::Bool = false, normal::Bool = false, proof::Bool = true)
  K = base_ring(M)
  p = p_start
  Kt, t = polynomial_ring(K, cached = false)
  f = Kt()
  f_last = f
  d = ZZRingElem(1)
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
      me.fldx = [polynomial_ring(x, "_x", cached=false)[1] for x = me.fld]
      me.Kx = Kt
    end

    fp = map(i-> charpoly(me.fldx[i], t[i]), 1:length(t))
    gp= Hecke.modular_lift(fp, me)
    if iszero(f)
      f = gp
    else
      f, d = induce_crt(f, d, gp, ZZRingElem(p), true)
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
    space <M^i b | i> = everything, at least mod p, so in general.
    Now f(M)b = 0 implies f(M) = 0.

    if f is known to be integral, then one can use arb to compute the
      complex version and use this to derive bounds...

    There are also bounds on the coefficients which are sometimes tight
=#

function roots(::QQField, f::ZZPolyRingElem; max_roots::Int=degree(f))
  if degree(f) < 1
      return QQFieldElem[]
  end
  if degree(f) == 1
      return QQFieldElem[-constant_coefficient(f)//leading_coefficient(f)]
  end

  g = gcd(f, derivative(f))
  if isone(g)
      h = f
  else
      h = divexact(f, g)
  end
  if degree(h) == 1
      return QQFieldElem[-constant_coefficient(h)//leading_coefficient(h)]
  end
  h = primpart(h)

  global p_start
  p = p_start
  bd = leading_coefficient(h) + maximum(abs, coefficients(h))
  while true
      p = next_prime(p)
      k = GF(p)
      hp = change_base_ring(k, h)
      if !is_squarefree(hp)
          continue
      end
      k = ceil(Int, log(bd) / log(p))
      Hp = factor_mod_pk(h, p, k)
      pk = ZZRingElem(p)^k
      r = QQFieldElem[mod_sym(-constant_coefficient(x) * leading_coefficient(h), pk) // leading_coefficient(h) for x = keys(Hp) if degree(x) == 1]
      return [x for x = r if iszero(f(x))]
  end
end

function roots(f::ZZPolyRingElem; max_roots::Int=degree(f))
  r = roots(QQ, f, max_roots=max_roots)
  return ZZRingElem[ZZ(x) for x = r if denominator(x) == 1]
end

function roots(f::QQPolyRingElem; max_roots::Int=degree(f))
  Zx, x = polynomial_ring(ZZ, cached = false)
  g = Zx(denominator(f)*f)
  return roots(QQ, g)
end

function roots(R::AcbField, f::Union{ZZPolyRingElem, QQPolyRingElem}, abs_tol::Int=R.prec, initial_prec::Int...)
  lf = factor(f)
  return map(R, reduce(vcat, [_roots(g, abs_tol, initial_prec...) for g = keys(lf.fac) if degree(g) > 0]))
end

function roots(x::RealPolyRingElem)
  rt = roots(map_coefficients(ComplexField(), x), isolate_real=true)
  return real.(filter(isreal, rt))
end

function _roots(f::QQPolyRingElem, ::PosInf; prec::Int=64)
  g = squarefree_part(f)
  all_rts = _roots(g, prec)
  # real.(filter(...)) leads to worse type inference
  rl_rts = map(real, (filter(isreal, all_rts)))
  compl_rts = filter(x -> !isreal(x) && is_positive(imag(x)), all_rts)
  @assert length(rl_rts) + 2 * length(compl_rts) == degree(g)
  return all_rts, rl_rts, compl_rts
end

function factor(R::AcbField, f::Union{ZZPolyRingElem, QQPolyRingElem}, abs_tol::Int=R.prec, initial_prec::Int...)
  g = factor(f)
  d = Dict{AcbPolyRingElem, Int}()
  Rt, t = polynomial_ring(R, var(parent(f)), cached = false)
  for (k,v) = g.fac
    for r = roots(R, k)
      d[t-r] = v
    end
  end
  return Fac(Rt(g.unit), d)
end

function factor(R::ComplexField, f::Union{ZZPolyRingElem, QQPolyRingElem}, abs_tol::Int=precision(R), initial_prec::Int...)
  g = factor(f)
  Rt, t = polynomial_ring(R, var(parent(f)), cached = false)
  d = Dict{typeof(t), Int}()
  for (k,v) = g.fac
    for r = roots(R, k)
      d[t-r] = v
    end
  end
  return Fac(Rt(g.unit), d)
end

function roots(R::ArbField, f::Union{ZZPolyRingElem, QQPolyRingElem}, abs_tol::Int=R.prec, initial_prec::Int...)
  g = factor(f)
  r = elem_type(R)[]
  C = AcbField(precision(R))
  for k = keys(g.fac)
    s, _ = signature(k)
    rt = roots(C, k)
    append!(r, map(real, rt[1:s]))
  end
  return r
end

function factor(R::Union{RealField, ArbField}, f::Union{ZZPolyRingElem, QQPolyRingElem}, abs_tol::Int=precision(R), initial_prec::Int...)
  g = factor(f)
  Rx, x = polynomial_ring(R, var(parent(f)), cached = false)
  d = Dict{typeof(x), Int}()
  if isa(R, RealField)
    C = ComplexField()
  else
    C = AcbField(precision(R))
  end

  for (k,v) = g.fac
    s, t = signature(k)
    r = roots(C, k)
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


@doc raw"""
    fmpz_poly_read!(a::ZZPolyRingElem, b::String) -> ZZPolyRingElem

Use flint's native read function to obtain the polynomial in the file with name `b`.
"""
function fmpz_poly_read!(a::ZZPolyRingElem, b::String)
  f = ccall((:fopen, :libc), Ptr{Nothing}, (Cstring, Cstring), b, "r")
  ccall((:fmpz_poly_fread, libflint), Nothing, (Ptr{Nothing}, Ref{ZZRingElem}), f, a)
  ccall((:fclose), Nothing, (Ptr{Nothing}, ), f)
  return a
end

@doc raw"""
    mahler_measure_bound(f::ZZPolyRingElem) -> ZZRingElem

A upper bound on the Mahler measure of `f`.
The Mahler measure is the product over the roots of absolute value at least `1`.
"""
function mahler_measure_bound(f::ZZPolyRingElem)
  return root(sum([coeff(f, i)^2 for i=0:degree(f)])-1, 2)+1
end

function prod1(a::Vector{T}; inplace::Bool = false) where T <: PolyRingElem
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
#  Cyclotomic polynomial
#
################################################################################

@doc raw"""
    cyclotomic_polynomial(n::Int, R::PolyRing{T} = Hecke.Globals.Zx) where T
                                                                  -> PolyRingElem{T}

Return the `n`-th cyclotomic polynomial as an element of `R`. If `R` is not
specified, return the `n`-th cyclotomic polynomial over the integers.

# Examples

```jldoctest
julia> F, _ = finite_field(5)
(Prime field of characteristic 5, 0)

julia> Ft, _ = F["t"]
(Univariate polynomial ring in t over F, t)

julia> cyclotomic_polynomial(15, Ft)
t^8 + 4*t^7 + t^5 + 4*t^4 + t^3 + 4*t + 1

julia> cyclotomic_polynomial(9)
x^6 + x^3 + 1

julia> typeof(ans)
ZZPolyRingElem
```
"""
function cyclotomic_polynomial(n::Int, R::PolyRing{T} = Hecke.Globals.Zx) where T
  @req n > 0 "n must be positive"
  x = gen(Hecke.Globals.Zx)
  p = Hecke.cyclotomic(n, x)
  return map_coefficients(base_ring(R), p, parent = R)::PolyRingElem{T}
end

@doc raw"""
    is_cyclotomic_polynomial_with_data(p::PolyRingElem{T}) where T -> Bool, Int

Return a tuple containing whether `p` is cyclotomic and which cyclotomic polynomial it is.

# Examples

```jldoctest
julia> _, b = cyclotomic_field_as_cm_extension(12)
(Relative number field of degree 2 over maximal real subfield of cyclotomic field of order 12, z_12)

julia> is_cyclotomic_polynomial_with_data(minpoly(b))
(false, -1)

julia> is_cyclotomic_polynomial_with_data(absolute_minpoly(b))
(true, 12)
```
"""
function is_cyclotomic_polynomial_with_data(p::PolyRingElem{T}) where T
  n = degree(p)
  R = parent(p)::PolyRing{T}
  for k in union(euler_phi_inv(n), [1])
    if p == cyclotomic_polynomial(k, R)
      return (true, k)
    end
  end
  return (false, -1)
end

@doc raw"""
    is_cyclotomic_polynomial(p::PolyRingElem{T}) where T -> Bool

Return whether `p` is cyclotomic.

# Examples

```jldoctest
julia> _, b = cyclotomic_field_as_cm_extension(12)
(Relative number field of degree 2 over maximal real subfield of cyclotomic field of order 12, z_12)

julia> is_cyclotomic_polynomial(minpoly(b))
false

julia> is_cyclotomic_polynomial(absolute_minpoly(b))
true
```
"""
is_cyclotomic_polynomial(p::PolyRingElem{T}) where T = is_cyclotomic_polynomial_with_data(p)[1]

################################################################################
#
#  Lazy Factorization
#
################################################################################

"""
    lazy_factor(poly)

Return iterator over the irreducible factors of a minimal polynomial.
"""
lazy_factor(poly::PolyRingElem) = _lazy_factor(poly, base_ring(parent(poly)))
_lazy_factor(poly::PolyRingElem, ::FinField) =
  (f for (sqf, _) in factor_squarefree(poly) for g in FactorsOfSquarefree(sqf) for (f, _) in factor(g))
_lazy_factor(poly::PolyRingElem, ::Ring) =
  (f for (sqf, _) in factor_squarefree(poly) for (f, _) in factor(sqf))

"""
    FactorsOfSquarefree(poly)

Iterator that turns a squarefree polynomial in smaller factors.
"""
struct FactorsOfSquarefree{T<:PolyRingElem}
  orderOfBaseRing :: Int
  x :: T
  poly :: T

  function FactorsOfSquarefree(poly::T) where T <:PolyRingElem
    Kx = poly.parent
    return new{T}(order(Kx.base_ring), gen(Kx), poly)
  end
end

function Base.iterate(
    a::FactorsOfSquarefree{T},
    (p, exp)::Tuple{T,Int} = (a.poly, 0)
  ) where T<:PolyRingElem
  isone(p) && return nothing
  exp += 1
  exponent = ZZ(a.orderOfBaseRing) ^ exp
  f = gcd(powermod(a.x, exponent, p) - a.x, p)
  p = divexact(p, f)
  return (f, (p, exp))
end

Base.IteratorSize(::Type{FactorsOfSquarefree{T}}) where T = Base.SizeUnknown()
Base.eltype(::Type{FactorsOfSquarefree{T}}) where T = T

################################################################################
#
#  Right division with remainder
#
################################################################################

# Conventions follow Ore, "Theory of Non-Commutative Polynomials", 1933

function divrem_right(f::NCPolyRingElem, g::NCPolyRingElem)
  check_parent(f, g)
  @req !is_zero(g) "Divisor must be non-zero"
  # we are looing for q, r with f = q*g + r, so g is always a right divisors
  b = leading_coefficient(g)
  q = zero(f)
  R = parent(f)
  while degree(f) >= degree(g)
    n = degree(f) - degree(g)
    c = shift_left(R(divexact_right(leading_coefficient(f), b)), n)
    q += c
    @assert degree(f - c * g) < degree(f)
    f = f - c * g
  end
  return q, f
end

function gcd_right(f::NCPolyRingElem, g::NCPolyRingElem)
  check_parent(f, g)
  while !iszero(g)
    _, r = divrem_right(f, g)
    f, g = g, r
  end
  return f
end
