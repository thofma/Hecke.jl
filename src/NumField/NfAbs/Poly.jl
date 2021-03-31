###########################################################################
#
#  Chinese remaindering
#
################################################################################

@doc Markdown.doc"""
    induce_crt(a::Generic.Poly{nf_elem}, p::fmpz, b::Generic.Poly{nf_elem}, q::fmpz) -> Generic.Poly{nf_elem}, fmpz

Given polynomials $a$ defined modulo $p$ and $b$ modulo $q$, apply the CRT
to all coefficients recursively.
Implicitly assumes that $a$ and $b$ have integral coefficients (i.e. no
denominators).
"""
function induce_crt(a::Generic.Poly{nf_elem}, p::fmpz, b::Generic.Poly{nf_elem}, q::fmpz, signed::Bool = false)
  c = parent(a)()
  pi = invmod(p, q)
  mul!(pi, pi, p)
  pq = p*q
  if signed
    pq2 = div(pq, 2)
  else
    pq2 = fmpz(0)
  end
  for i=0:max(degree(a), degree(b))
    setcoeff!(c, i, induce_inner_crt(coeff(a, i), coeff(b, i), pi, pq, pq2))
  end
  return c, pq
end

@doc Markdown.doc"""
    induce_rational_reconstruction(a::Generic.Poly{nf_elem}, M::fmpz) -> bool, Generic.Poly{nf_elem}

Apply rational reconstruction to the coefficients of $a$. Implicitly assumes
the coefficients to be integral (no checks done)
returns true iff this is successful for all coefficients.
"""
function induce_rational_reconstruction(a::Generic.Poly{nf_elem}, M::fmpz)
  b = parent(a)()
  for i=0:degree(a)
    fl, x = rational_reconstruction(coeff(a, i), M)
    if fl
      setcoeff!(b, i, x)
    else
      return false, b
    end
  end
  return true, b
end

################################################################################
#
#  GCD
#
################################################################################

@doc Markdown.doc"""
    gcd(a::Generic.Poly{nf_elem}, b::Generic.Poly{nf_elem}) -> Generic.Poly{nf_elem}

Computes the greatest common divisor of $f$ and $g$ using a modular algorithm.
"""
function gcd(a::Generic.Poly{nf_elem}, b::Generic.Poly{nf_elem}, test_sqfr::Bool = false)
  # modular kronnecker assumes a, b !=n 0
  if iszero(a)
    if iszero(b)
      return b
    else
      return  inv(leading_coefficient(b))*b
    end
  elseif iszero(b)
    return inv(leading_coefficient(a))*a
  end
  if min(degree(a), degree(b)) >= 6 || degree(base_ring(a)) > 5 || test_sqfr
    g = gcd_modular_kronnecker(a, b, test_sqfr)
    test_sqfr && return g
    return inv(leading_coefficient(g))*g  # we want it monic...
  else
    return gcd_euclid(a, b)
  end
end

################################################################################
#
#  Modular GCD
#
################################################################################

# There is some weird type instability
function gcd_modular(a::Generic.Poly{nf_elem}, b::Generic.Poly{nf_elem})
  # naive version, kind of
  # polys should be integral
  # rat recon maybe replace by known den if poly integral (Kronnecker)
  # if not monic, scale by gcd
  # remove content?
  a = a*(1//leading_coefficient(a))
  b = b*(1//leading_coefficient(b))
  global p_start
  p = p_start
  K = base_ring(parent(a))
  @assert parent(a) == parent(b)
  g = zero(a)
  d = fmpz(1)
  while true
    p = next_prime(p)
    me = modular_init(K, p)
    t = Hecke.modular_proj(a, me)
    fp = deepcopy(t)::Array{fq_nmod_poly, 1}  # bad!!!
    gp = Hecke.modular_proj(b, me)
    gp = [gcd(fp[i], gp[i]) for i=1:length(gp)]::Array{fq_nmod_poly, 1}
    gc = Hecke.modular_lift(gp, me)::Generic.Poly{nf_elem}
    if isone(gc)
      return parent(a)(1)
    end
    if d == 1
      g = gc
      d = fmpz(p)
    else
      if degree(gc) < degree(g)
        g = gc
        d = fmpz(p)
      elseif degree(gc) > degree(g)
        continue
      else
        g, d = induce_crt(g, d, gc, fmpz(p))
      end
    end
    fl, gg = induce_rational_reconstruction(g, d)
    if fl  # not optimal
      r = mod(a, gg)
      if iszero(r)
        r = mod(b, gg)
        if iszero(r)
          return gg
        end
      end
    end
  end
end


function _preproc_pol(a::Generic.Poly{nf_elem}, b::Generic.Poly{nf_elem})
  a1 = a*(1//leading_coefficient(a))
  da = Base.reduce(lcm, [denominator(coeff(a1, i)) for i=0:degree(a)])
  b1 = b*(1//leading_coefficient(b))
  db = Base.reduce(lcm, [denominator(coeff(b1, i)) for i=0:degree(b)])
  d = gcd(da, db)
  a2 = a1*da
  b2 = b1*db
  Kt = parent(a)
  K = base_ring(Kt)
  if isdefining_polynomial_nice(K)
    fsa = evaluate(derivative(K.pol), gen(K))*d
  else
    E = any_order(K)
    cd = codifferent(E)
    fsa = short_elem(colon(1*E, numerator(cd))*denominator(cd))*d
  end
  return a2, b2, fsa
end

function gcd_euclid(a::AbstractAlgebra.PolyElem{nf_elem}, b::AbstractAlgebra.PolyElem{nf_elem})
   check_parent(a, b)
   if length(a) > length(b)
      (a, b) = (b, a)
   end
   while !iszero(a)
      (a, b) = (mod(b, a), a)
   end
   d = leading_coefficient(b)
   return divexact(b, d)
end


#similar to gcd_modular, but avoids rational reconstruction by controlling
#a/the denominator
function gcd_modular_kronnecker(a::Generic.Poly{nf_elem}, b::Generic.Poly{nf_elem}, test_sqfr::Bool = false)
  # rat recon maybe replace by known den if poly integral (Kronnecker)
  # if not monic, scale by gcd
  # remove content?
  @assert parent(a) == parent(b)
  a, b, fsa = _preproc_pol(a, b)
  Kt = parent(a)
  K = base_ring(Kt)
  #now gcd(a, b)*fsa should be in the equation order...
  global p_start
  p = p_start

  g = zero(Kt)
  d = fmpz(1)
  last_g = zero(Kt)
  while true
    p = next_prime(p)
    F = GF(p, cached = false)
    Fx = PolynomialRing(F, "x", cached = false)[1]
    Fp = Fx(K.pol)
    if !issquarefree(Fp)
      continue
    end
    fs = factor_shape(Fp)
    if any(x -> x > 4, keys(fs))
      continue
    end
    local me, fp, gp, fsap
    try
      me = modular_init(K, p)
      fp = deepcopy(Hecke.modular_proj(a, me))  # bad!!!
      gp = Hecke.modular_proj(b, me)
      fsap = Hecke.modular_proj(fsa, me)
    catch ee
      if typeof(ee) != Hecke.BadPrime
        rethrow(ee)
      end
      continue
    end
    gp = fq_nmod_poly[fsap[i] * gcd(fp[i], gp[i]) for i=1:length(gp)]
    gc = Hecke.modular_lift(gp, me)
    if isconstant(gc)
      return one(Kt)
    end
    if test_sqfr
      return zero(Kt)
    end
    if isone(d)
      g = gc
      d = fmpz(p)
    else
      if degree(gc) < degree(g)
        g = gc
        d = fmpz(p)
      elseif degree(gc) > degree(g)
        continue
      else
        g, d = induce_crt(g, d, gc, fmpz(p), true)
      end
    end
    if g == last_g && iszero(mod(a, g)) && iszero(mod(b, g))
      return divexact(g, leading_coefficient(g))
    else
      last_g = g
    end
  end
end

################################################################################
#
#  Modular extended GCD
#
################################################################################

#seems to be faster than gcdx - if problem large enough.
#rational reconstructio is expensive - enventually
#TODO: figure out the denominators in advance. Resultants?

function gcdx_modular(a::Generic.Poly{nf_elem}, b::Generic.Poly{nf_elem})
  a = a*(1//leading_coefficient(a))
  b = b*(1//leading_coefficient(b))
  global p_start
  p = p_start
  K = base_ring(parent(a))
  @assert parent(a) == parent(b)
  g = zero(a)
  d = fmpz(1)
  last_g = parent(a)(0)
  while true
    p = next_prime(p)
    me = modular_init(K, p)
    fp = deepcopy(Hecke.modular_proj(a, me))  # bad!!!
    gp = Hecke.modular_proj(b, me)
    ap = similar(gp)
    bp = similar(gp)
    for i=1:length(gp)
      gp[i], ap[i], bp[i] = gcdx(fp[i], gp[i])
    end
    gc = Hecke.modular_lift(gp, me)
    aa = Hecke.modular_lift(ap, me)
    bb = Hecke.modular_lift(bp, me)
    if d == 1
      g = gc
      ca = aa
      cb = bb
      d = fmpz(p)
    else
      if degree(gc) < degree(g)
        g = gc
        ca = aa
        cb = bb
        d = fmpz(p)
      elseif degree(gc) > degree(g)
        continue
      else
        g, dd = induce_crt(g, d, gc, fmpz(p))
        ca, dd = induce_crt(ca, d, aa, fmpz(p))
        cb, d = induce_crt(cb, d, bb, fmpz(p))
      end
    end
    fl, ccb = Hecke.induce_rational_reconstruction(cb, d)
    if fl
      fl, cca = Hecke.induce_rational_reconstruction(ca, d)
    end
    if fl
      fl, gg = Hecke.induce_rational_reconstruction(g, d)
    end
    if fl
      r = mod(a, g)
      if iszero(r)
        r = mod(b, g)
        if iszero(r) && ((cca*a + ccb*b) == gg)
          return gg, cca, ccb
        end
      end
    end
  end
end

#similar to gcd_modular, but avoids rational reconstruction by controlling
#a/the denominator using resultant. Faster than above, but still slow.
#mainly due to the generic resultant. Maybe use only deg-1-primes??
#fact: g= gcd(a, b) and 1= gcd(a/g, b/g) = u*(a/g) + v*(b/g)
#then u*res(a/g, b/g) is mathematically integeral, same for v
#scaling by f'(a) makes it i nthe equation order
#
# missing/ next attempt:
#  write invmod using lifting
#  write gcdx using lifting (lin/ quad)
#  try using deg-1-primes only (& complicated lifting)
#
function gcdx_mod_res(a::Generic.Poly{nf_elem}, b::Generic.Poly{nf_elem})
  @assert parent(a) == parent(b)
  a = a*(1//leading_coefficient(a))
  da = Base.reduce(lcm, [denominator(coeff(a, i)) for i=0:degree(a)])
  b = b*(1//leading_coefficient(b))
  db = Base.reduce(lcm, [denominator(coeff(a, i)) for i=0:degree(a)])
  d = gcd(da, db)
  a = a*da
  b = b*db
  Kt = parent(a)
  K = base_ring(Kt)
  fsa = change_base_ring(K, derivative(K.pol), parent = Kt)*d
  #now gcd(a, b)*fsa should be in the equation order...
  global p_start
  p = p_start
  g = zero(parent(a))
  d = fmpz(1)
  r = zero(K)
  fa = zero(parent(a))
  fb = zero(parent(b))
  last_g = (parent(a)(0), parent(a)(0), parent(a)(0), parent(a)(0))

  while true
    p = next_prime(p)
    me = modular_init(K, p)
    fp = deepcopy(Hecke.modular_proj(a, me))  # bad!!!
    gp = (Hecke.modular_proj(b, me))
    fsap = (Hecke.modular_proj(fsa, me))
    g_ = similar(fp)
    fa_ = similar(fp)
    fb_ = similar(fp)
    r_ = Array{fq_nmod}(length(fp))
    for i=1:length(gp)
      g_[i], fa_[i], fb_[i] = gcdx(fp[i], gp[i])
      r_[i] = resultant(div(fp[i], g_[i]), div(gp[i], g_[i]))
      g_[i] *= fsap[i]
      fa_[i] *= (fsap[i]*r_[i])
      fb_[i] *= (fsap[i]*r_[i])
    end
    rc = Hecke.modular_lift(r_, me)
    gc = Hecke.modular_lift(g_, me)
    fac = Hecke.modular_lift(fa_, me)
    fbc = Hecke.modular_lift(fb_, me)
    if d == 1
      g = gc
      r = rc
      fa = fac
      fb = fbc
      d = fmpz(p)
    else
      if degree(gc) < degree(g)
        g = gc
        r = rc
        fa = fac
        fb = fbc
        d = fmpz(p)
      elseif degree(gc) > degree(g)
        continue
      else
        g, d1 = induce_crt(g, d, gc, fmpz(p), true)
        fa, d1 = induce_crt(fa, d, fac, fmpz(p), true)

        r = Hecke.induce_inner_crt(r, rc, d*invmod(d, fmpz(p)), d1, div(d1, 2))
        fb, d = induce_crt(fb, d, fbc, fmpz(p), true)

      end
    end
    if (g, r, fa, fb) == last_g
      if g*r == fa*a + fb*b
        return g*r, fa, fb ## or normalise to make gcd monic??
      else
        last_g = (g, r, fa, fb)
      end
    else
      last_g = (g, r, fa, fb)
    end
  end
end

################################################################################
#
#  Equality modulo rational integer
#
################################################################################

function eq_mod(a::Generic.Poly{nf_elem}, b::Generic.Poly{nf_elem}, d::fmpz)
  e = degree(a) == degree(b)
  K= base_ring(parent(a))
  i=0
  while e && i<= degree(a)
    j = 0
    while e && j<degree(K)
      e = e && (numerator(coeff(coeff(a, i), j)) - numerator(coeff(coeff(b, i), j))) % d == 0
      j += 1
    end
    i += 1
  end
  return e
end

################################################################################
#
#  Predicates
#
################################################################################

function issquarefree(x::Generic.Poly{nf_elem})
  return isone(gcd(x, derivative(x), true))
end

################################################################################
#
#  Some weird conversion
#
################################################################################

function nf_poly_to_xy(f::PolyElem{Nemo.nf_elem}, Qxy::PolyRing, Qx::PolyRing)
  K = base_ring(f)
  Qy = parent(K.pol)
  y = gen(Qx)

  res = zero(Qxy)
  for i=degree(f):-1:0
    res *= y
    res += change_base_ring(Qx, Qy(coeff(f, i)), parent = Qxy)
  end
  return res
end

################################################################################
#
#  Modular resultant
#
################################################################################

function resultant_mod(f::Generic.Poly{nf_elem}, g::Generic.Poly{nf_elem})
  global p_start
  p = p_start
  K = base_ring(parent(f))
  @assert parent(f) == parent(g)
  r = K()
  d = fmpz(1)
  last_r = K()
  first = true
  while true
    p = next_prime(p)
    me = modular_init(K, p)
    fp = deepcopy(Hecke.modular_proj(f, me))  # bad!!!
    gp = Hecke.modular_proj(g, me)
    rp = Array{fq_nmod}(undef, length(gp))
    for i=1:length(gp)
      rp[i] = resultant(fp[i], gp[i])
    end
    rc = Hecke.modular_lift(rp, me)
    if d == 1
      r = rc
      d = fmpz(p)
    else
      r, d = induce_crt(r, d, rc, fmpz(p))
    end
    fl, ccb = Hecke.rational_reconstruction(r, d)
    if fl
      if first
        first = false
        last_r = ccb
#        println("first: $ccb")
      else
        if ccb == last_r
          return ccb
        else
#      println("fail2: $ccb")
          last_r = ccb
        end
      end
    else
#      println("fail")
    end
  end
end



function landau_mignotte_bound(f::PolyElem{nf_elem})
  Zx, x = PolynomialRing(FlintZZ, cached = false)
  g = Zx()
  for i=0:degree(f)
    setcoeff!(g, i, Hecke.upper_bound(sqrt(t2(coeff(f, i))), fmpz))
  end
  b = fmpz()
  ccall((:fmpz_poly_factor_mignotte, libflint), Nothing, (Ref{fmpz}, Ref{fmpz_poly}), b, g)
  return b
end



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
    ccall((:fmpz_poly_CLD_bound, libflint), Nothing, (Ref{fmpz}, Ref{fmpz_poly}, Int64), b, g, kk)
    push!(bb, b)
  end
  return bb
end
cld_bound(f::PolyElem{nf_elem}, k::Int) = cld_bound(f, [k])[1]

function cld_bound(f::fmpz_poly, k::Int)
  @assert 0 <= k < degree(f)
  b = FlintZZ()
  ccall((:fmpz_poly_CLD_bound, libflint), Nothing, (Ref{fmpz}, Ref{fmpz_poly}, Int64), b, f, k)
  return b
end
cld_bound(f::fmpz_poly, k::Array{Int, 1}) = map(x->cld_bound(f, x), k)
