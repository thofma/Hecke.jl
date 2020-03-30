################################################################################
#
#  NfOrd/Hensel.jl : Hensel lifting for simple absolute number fields
#
# This file is part of Hecke.
#
# Copyright (c) 2015, 2016: Claus Fieker, Tommy Hofmann
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
# * Redistributions of source code must retain the above copyright notice, this
#   list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright notice,
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
#
# (C) 2019 Claus Fieker, Tommy Hofmann, Carlo Sircana
#
################################################################################

# TODO/missing:
#  assertion on the lifting
#  filtering of the roots (maybe we don't want all?)
#  find all/ one/ few roots
#  break down in various modules:
#  - find powers of ideal
#  - find LLL/HNF basis
#  - lifting?
#  use ResRing(Poly) instead of doing % pgg?
#  an open variant where k is increased until we have a root?
#
#missing: different (better) handling for x^n-a
# possibly based on https://scicomp.stackexchange.com/questions/18846/newton-iteration-for-cube-root-without-division
#
# g = x^-n -a^(n-1), and r = root(g), then r = a^(-(n-1)/n), hence
#                                         ar = a^(-(n-1)/n + 1) = a^(1/n)
# Here, the Newton-iteration is easy: (b = a^(n-1))
# g = x^-n - b, => g' = -nx^(-n-1)
#Newton: r -> r-g(r)/g'(r) = r - (r^(-n) -b)/(-n r^(-n-1))
#                          = r - r/(-n) - b/n r^(n+1)
#                          = r(1+1/n) - b/n r^(n+1)
# no division! and no double iteration
# however, for reconstruction: we don't want r (which is non-integral)
# but ar which is...


################################################################################
#
#  Helper functions
#
################################################################################

Base.isless(x::arb, y::arb) = x < y

function lift(R::NmodPolyRing, a::fq_nmod)
  f = R()
  for i=0:degree(parent(a))-1
    setcoeff!(f, i, _get_coeff_raw(a, i))
  end
  return f
end

function lift(R::GFPPolyRing, a::fq_nmod)
  f = R()
  for i=0:degree(parent(a))-1
    setcoeff!(f, i, _get_coeff_raw(a, i))
  end
  return f
end

function (Zx::FmpzPolyRing)(a::nf_elem) 
  b = Zx()
  @assert denominator(a) == 1
  if degree(parent(a)) == 1
    # If the number field is linear, then a.elem_length is not properly
    # initialized, that is, it could be anything.
    setcoeff!(b, 0, numerator(coeff(a, 0)))
  else
    for i=0:a.elem_length
      setcoeff!(b, i, numerator(coeff(a, i)))
    end
  end
  return b
end

################################################################################
#
#  Root computation via Hensel lifting
#
################################################################################

# General comments
# ispure means that f = X^deg(f) + coeff(f, 0)
# isnormal means that if there are either no or all roots

function _roots_hensel(f::Generic.Poly{nf_elem};
                       max_roots::Int = degree(f),
                       ispure::Bool = false,
                       isnormal::Bool = false,
                       root_bound::Vector{fmpz} = fmpz[])
  # f must be squarefree
  # I should check that
  K::AnticNumberField = base_ring(f)

  if iszero(trailing_coefficient(f))
    rs = nf_elem[zero(K)]
    f = div(f, gen(parent(f)))
  else
    rs = nf_elem[]
  end

  if length(rs) >= max_roots
    return rs
  end

  n = degree(K)
  deg = degree(f)

  # First we find a prime ideal such that f is squarefree modulo P 
  # (The discriminant of f has only finitely many divisors).

  p = degree(f)+1
  deg_p = 1

  good_deg_p = 0

  good_p = p

  found = false

  local factor_of_g::gfp_poly

  local good_fp::fq_nmod_poly

  current_num_rmodp = degree(f) + 1

  not_better = 1

  coeffs_f = Vector{elem_type(base_ring(f))}(undef, length(f))

  if n >= 10
    STABILIZED = 2
  else
    STABILIZED = 0
  end

  if !ispure
    for i in 0:degree(f)
      coeffs_f[i + 1] = coeff(f, i)
    end
  end

  while !found
    p = next_prime(p)
    
    Rp = Nemo.GF(p, cached=false)
    Rpt, t = PolynomialRing(Rp, "t", cached=false)
    gp = Rpt(K.pol)
    if iszero(discriminant(gp))
      continue
    end

    lp = factor(gp).fac

    #set up the mod p data:
    #need FiniteField as I need to factor (roots)
    # I want to find a residue field with less roots
    for gp_factor in keys(lp)
      deg_p = degree(gp_factor)

      S = FqNmodFiniteField(gp_factor, :z, false)
      ST, T = PolynomialRing(S, "T", cached=false)

      if ispure
        red_coeff1 = Vector{fq_nmod}(undef, length(f))
        red_coeff1[length(f)] = S(1)
        for i = 2:length(f)-1
          red_coeff1[i] = zero(S) 
        end
        red_coeff1[1] = S(Rpt(coeff(f, 0)))
        fp = ST(red_coeff1)
      else
        red_coeff = Vector{fq_nmod}(undef, length(f))
        for i in 1:length(f)
          red_coeff[i] = S(Rpt(coeffs_f[i]))
        end
        fp = ST(red_coeff)
      end

      if !issquarefree(fp)
        continue
      end
      num_rmodp = degree(gcd(fp, powmod(T, fmpz(p)^deg_p, fp) - T))

      if num_rmodp == 0
        return nf_elem[]
      end

      if isnormal && num_rmodp < degree(f)
        return nf_elem[]
      end

      if num_rmodp < current_num_rmodp || (num_rmodp == current_num_rmodp && deg_p > good_deg_p)
        good_p = p
        factor_of_g = gp_factor
        current_num_rmodp = num_rmodp
        good_fp = fp
        good_deg_p = deg_p
      else
        not_better = not_better + 1
      end

      if not_better >= STABILIZED
        found = true
        break
      end
    end
  end

  # compute the lifting exponent a la Friedrich-Fieker

  E = EquationOrder(K)
  r1, r2 = signature(E) 

  gsa = derivative(K.pol)(gen(K))
  gsa_con = conjugates_arb(gsa, 32)

  if length(root_bound) > 0
    @assert length(root_bound) == r1 + r2
    bound_root = Vector{arb}(undef, r1 + r2)
    for i in 1:(r1 + r2)
      bound_root[i] = root_bound[i] * abs(gsa_con[i])
    end
  elseif ispure
    conj = __conjugates_arb(coeff(f, 0), 32)
    R = parent(conj[1])
    a_con = [R(abs_upper_bound(abs(e), fmpz)) for e in conj]

    bound_root = Vector{arb}(undef, r1 + r2)

    for i in 1:r1+r2
      bound_root[i] = root(abs(a_con[i]), degree(f)) * abs(gsa_con[i])
    end
  else
    bound_root = Vector{arb}(undef, r1 + r2)

    CC = AcbField(64, cached = false)
    CCt, t = PolynomialRing(CC, "t", cached=false)
    conjugates_of_coeffs = Vector{acb}[ conjugates_arb(c, 32) for c in coeffs_f ]

    for i in 1:r1+r2
      g = CCt(acb[ conjugates_of_coeffs[j + 1][i] for j in 0:degree(f) ])
      bound_root[i] = roots_upper_bound(g) * abs(gsa_con[i])
    end
  end
  ss = _lifting_expo(good_p, good_deg_p, E, bound_root)
  rts = _hensel(f, factor_of_g, good_fp, Int(ss), max_roots = max_roots - length(rs), ispure = ispure)
  return vcat(rs, rts)
end

################################################################################
#
#  Main lifting functions
#
################################################################################

function _hensel(f::Generic.Poly{nf_elem},
                 fac_pol_mod_p::gfp_poly,
                 fp::fq_nmod_poly, k::Int;
                 max_roots::Int = degree(f),
                 ispure::Bool = false,
                 isnormal::Bool = false)
  # Let f be a polynomial over a number field K with defining polynomial g.
  # This function expects
  # fac_pol_mod_p = factor of g mod p corresponding to a prime ideal P of K
  # fp = f mod P, the reduction of f modulo P
  # k = lifting exponent
  # This function lifts the roots of f mod P to P^k and reconstructs them.
  
  # f is pure if and only if f = x^deg(f) + coeff(f, 0)

  @assert max_roots > 0

  caching = degree(base_ring(f)) > 20

  if caching
    # Setup the caching
    _cache = _get_prime_data_lifting(base_ring(f))
    _p = Int(characteristic(base_ring(fac_pol_mod_p)))
    if haskey(_cache, _p)
      _cache_p = _cache[_p]
      @vprint :Saturate 1 "Hitting the cache for the prime $(_p)\n"
      fac_pol_mod_p.parent = parent(first(keys(_cache_p)))
      if haskey(_cache_p, fac_pol_mod_p)
        @vprint :Saturate 1 "  Hitting the cache for the prime ideal\n"
        _cache_lll = _cache_p[fac_pol_mod_p]
      else
        @vprint :Saturate 1 "  Not hitting the cache for the prime ideal\n"
        _cache_lll = Dict()
        _cache_p[fac_pol_mod_p] = _cache_lll
      end
    else
      @vprint :Saturate 1 "No hitting the cache for the prime $(_p)\n"
      _cache_p = Dict()
      _cache_lll = Dict()
      _cache_p[fac_pol_mod_p] = _cache_lll
      _cache[_p] = _cache_p
    end
  end

  k = max(k, 2)

  # We want normalized PR's
  if caching
    new_k = Int(round(fmpz(k)//10^flog(fmpz(k), 10))) * 10^flog(fmpz(k), 10)
    new_k < k ? new_k = (1 + Int(round(fmpz(new_k)//10^flog(fmpz(new_k), 10)))) * 10^flog(fmpz(new_k), 10) : new_k = new_k
    k = new_k
  end

  Rp = base_ring(fac_pol_mod_p)
  Rpt = parent(fac_pol_mod_p)
  t = gen(Rpt)
  p = Int(characteristic(Rp))

  #assumes f squarefree
  #assumes constant_coefficient(f) != 0
  
  ZX, X = PolynomialRing(FlintZZ, "X", cached = false)
  K = base_ring(f)

  #to avoid embarrasment...

  #find the prime ideal - as I don't want to use orders, this is 
  #fun (computing a max order just for this is wasteful)
  #fun fact: if g = prod g_i mod p^k, then P_i^k = <p^k, g_i>
  #so instead of powering, and simplify and such, lets write it down
  if degree(fac_pol_mod_p) != degree(K)
    g1 = lift(ZX, fac_pol_mod_p)
    gg = hensel_lift(ZX(K.pol), g1, fmpz(p), k)
  else
    gg = ZX(K.pol)
  end
  # now for all i<= k, <p^i, K(gg)+p^i> is a normal presentation for
  #                                     the prime ideal power.
  #later we'll get the HNF matrix for selected powers as well

  #set up the mod p data:
  #need FiniteField as I need to factor (roots)

  rt = roots(fp)

  # Do something else in the pure case
  if ispure
    rt = eltype(rt)[inv(x^(degree(f)-1)) for x = rt]
  end

  # Now if we are in the normal case and want max_roots, we only have
  # to lift max_roots 
  
  if isnormal
    rt = eltype(rt)[1:max(max_roots, degree(f))]
  end

  #we're going to lift the roots - and for efficiency 1/f'(rt) as well:
  fps = derivative(fp)
  irt = eltype(rt)[inv(fps(x)) for x in rt]

  # this is in the finite field, but now I need it in the res. ring.
  # in ZX for ease of transport.
  RT = fmpz_poly[lift(ZX, lift(Rpt, x)) for x = rt]
  IRT = fmpz_poly[lift(ZX, lift(Rpt, x)) for x = irt]

  #the den: ala Kronnecker:
  den = ZX(derivative(K.pol)(gen(K)))
  iden = inv(derivative(K.pol)(gen(K)))

  ##for the result, to check for stabilising

  res = nf_elem[zero(K) for x = RT]
  rs = nf_elem[]

  #we'll be working in (Z/p^k)[t]/gg

  #an "optimal" lifting chain:
  pr = Int[k]
  while k>1
    k = div(k+1, 2)
    push!(pr, k)
  end
  pr = reverse(pr)

  ##lets start:
  
  
  f_coeff_ZX = Vector{fmpz_poly}(undef, length(f))
  if !ispure
    for j in 0:degree(f)
      f_coeff_ZX[j + 1] = ZX(coeff(f, j))
    end
  end

  # Keep a bit array to keep track of what we have to still lift
  roots_to_lift = trues(length(rt))

  n = degree(K)
  M = zero_matrix(FlintZZ, n, n)
  local Mi::fmpz_mat
  local d::fmpz
  ttt = 0.0
  for i=2:length(pr)
    pp = fmpz(p)^pr[i]
    Q = ResidueRing(FlintZZ, pp, cached=false)
    Qt, t = PolynomialRing(Q, "t", cached=false)

    #possibly this should be done with max precision and then adjusted down
    #the poly mod P^??
    if !ispure
      fpp = fmpz_mod_poly[Qt(f_coeff_ZX[k + 1]) for k=0:degree(f)]
    end

    #we need to evaluate fp and fp' at the roots (later)
    #given that we evaluate "by hand" we don't need polynomials

    pgg = Qt(gg) #we'll do the reductions by hand - possibly not optimal

    if caching && haskey(_cache_lll, pr[i])
      M, Mi, d = _cache_lll[pr[i]]::Tuple{fmpz_mat, fmpz_mat, fmpz}
    elseif ttt > 50.0
      Mold = M
      Miold = Mi
      dold = d
      M = zero_matrix(FlintZZ, n, n)
      #the lattice for reco:
      #zero!(M)
      for j = 1:degree(pgg)
        M[j, j] = pp
      end
      coeffarr = Vector{elem_type(Q)}(undef, degree(pgg))
      for j = 1:degree(pgg)-1
        coeffarr[j] = zero(Q)
      end
      coeffarr[degree(pgg)] = one(Q)
      pt = Qt(coeffarr)
      for j=degree(pgg)+1:n
        pt = shift_left(pt, 1)
        rem!(pt, pt, pgg)
        M[j,j] = 1
        for k=0:degree(pt)
          M[j, k+1] = -lift(coeff(pt, k))
        end
      end
      @vtime :Saturate 1 begin
        Ms_1 = M*Miold
	@assert divides(content(Ms_1), dold)[1]
	Ms_1 = divexact(Ms_1, dold)
        U1 = lll(Ms_1)
        M = U1*Mold
        M = lll(M)
        Mi, d = pseudo_inv(M)
        if caching
          _cache_lll[pr[i]] = (M, Mi, d)
        end
      end
    else
      M = zero_matrix(FlintZZ, n, n)
      #the lattice for reco:
      #zero!(M)
      for j = 1:degree(pgg)
        M[j, j] = pp
      end
      coeffarr = Vector{elem_type(Q)}(undef, degree(pgg))
      for j = 1:degree(pgg)-1
        coeffarr[j] = zero(Q)
      end
      coeffarr[degree(pgg)] = one(Q)
      pt = Qt(coeffarr)
      for j=degree(pgg)+1:n
        pt = shift_left(pt, 1)
        rem!(pt, pt, pgg)
        M[j,j] = 1
        for k=0:degree(pt)
          M[j, k+1] = -lift(coeff(pt, k))
        end
      end
      #this is (or should be) the HNF basis for P^??
      ttt = @elapsed M = lll(M)
      @vprint :Saturate 1 "Time for LLL: $(ttt) \n"
      Mi, d = pseudo_inv(M)
      if caching
        _cache_lll[pr[i]] = (M, Mi, d)
      end
    end

    if ispure
      ap = Qt((-coeff(f, 0)))
      bp = powmod(ap, degree(f)-1, pgg)
      minv = invmod(fmpz(degree(f)), pp)
    end

    for j=1:length(RT)
      if !roots_to_lift[j]
        continue
      end
      #to eval fp and the derivative, we pre-compute the powers of the
      #evaluation point - to save on large products...

      if !ispure
        pow = fmpz_mod_poly[Qt(1), Qt(RT[j])]
        while length(pow) <= degree(f)+1
          push!(pow, pow[2]*pow[end] % pgg)
        end

        eval_f = pow[1] * fpp[1]
        for k in 2:length(fpp)
          eval_f = eval_f +  pow[k] * fpp[k]
        end
        eval_f = eval_f % pgg

        #eval_f = sum(pow[k] * fp[k] for k=1:length(fp)) % pgg
        eval_fs = pow[1] * fpp[2]
        for k in 3:length(fpp)
          eval_fs = eval_fs + pow[k-1] *(k-1)*fpp[k]
        end
        eval_fs = eval_fs % pgg
        #eval_fs = sum(pow[k-1] *(k-1)*fp[k] for k=2:length(fp)) % pgg

        #double lift:
        #IRT = invmod(fp'(rt), p^k)
        # using x -> x(2-xy) to compute the inverse of y
        IRT[j] = lift(ZX, Qt(IRT[j])*(Qt(2-IRT[j]*eval_fs) % pgg) %pgg)
        #RT = rt mod p^k normal Newton
        # using x -> x-fp(x)//fp'(x) = x-fp(x) * IRT
        RT[j] = lift(ZX, Qt(pow[2] - eval_f*Qt(IRT[j])) % pgg)

        #before the reconstruction, we need to scale by den
        cf = lift(ZX, Qt(RT[j]*den) % pgg)
      else
        RTjp = Qt(RT[j])
        RT[j] = lift(ZX, (RTjp*(1+minv) - bp*minv* powmod(RTjp, degree(f)+1, pgg)) % pgg)

        #before the reconstruction, we need to scale by den and by a
        cf = lift(ZX, (Qt(RT[j]*den) % pgg)*ap % pgg)
      end

      ve = matrix(FlintZZ, 1, n, [coeff(cf, k) for k=0:n-1])
      _ve = ve*Mi
      mu = matrix(FlintZZ, 1, n,  [ round(fmpz, _ve[1, k]//d) for k=1:n])
      ve = ve - mu*M
      z = ZX()
      for kk=1:n
        setcoeff!(z, kk-1, ve[1, kk])
      end
      zz = K(z)*iden
      if res[j] == zz || i == length(pr)
        if (!ispure && iszero(f(zz))) || (ispure && zz^degree(f) == -coeff(f, 0))
          push!(rs, zz)
          if length(rs) >= max_roots
            return rs
          end
          roots_to_lift[j] = false
        end
        # I lifted to the end and one root did not lift to a root of f
        # and f is normal. Then there are no roots.
        if i == length(pr) && isnormal
          return nf_elem[]
        end
      else
        res[j] = zz
      end
    end
  end

  return rs
end

function _hensel(f::Generic.Poly{nf_elem}, p::Int, k::Int; max_roots::Int = degree(f))
  # Let f be a polynomial over a number field K
  # This function expects
  # p = prime number
  # k = lifting exponent
  # This function lifts the roots of f mod P to P^k and reconstructs them,
  # where P is a prime ideal with smallest degree over p

  K = base_ring(f)
  k = max(k, 2)
  Rp = GF(p, cached=false)
  Rpt, t = PolynomialRing(Rp, "t", cached=false)
  gp = Rpt(K.pol)
  lp = factor(gp).fac
  lpfac = first(keys(lp))

  for lpfac in keys(lp)
    if issquarefree(lpfac)
      break
    end
  end
  
  S = FqNmodFiniteField(lpfac, :z, false)
  ST, T = PolynomialRing(S,"T", cached=false)
  fp = ST([S(Rpt(coeff(f, i))) for i=0:degree(f)])

  return _hensel(f, lpfac, fp, k, max_roots = max_roots)
end

################################################################################
#
#  Computation of the lifting exponent
#
################################################################################

function _lifting_expo(p::Int, deg_p::Int, O::NfOrd, bnd::Array{arb, 1})
  # return _lifting_expo_using_logbound(p, deg_p, O, arb[log(a) for a in bnd])
  # compute the lifting exponent a la Friedrich-Fieker
  # bnd has upper bounds on |x^{(i)}| 1<= i <= r1+r2 as arbs
  # we're using a prime ideal above p of intertia degree deg_p
  # O is the order where the result will be reconstructed in

  (c1, c2) = norm_change_const(O)
  r1, r2 = signature(O)
  R = parent(bnd[1])
  bd = zero(R)
  n = degree(O)
  #so   |x|_mink  <= c_1 |x|_coeff
  #and  |x|_coeff <= c_2 |x|_mink

  for i in 1:r1
    bd += bnd[i]^2
  end

  for i=1:r2
    bd += 2*bnd[i+r1]^2
  end

  boundt2 = max(bd, one(R))

  # Tommy: log(...) could contain a ball, which contains zero
  tmp = R(abs_upper_bound(R(c1)*R(c2)*boundt2*exp((R(n*(n-1))//2 + 2)*log(R(2)))//n, fmpz))

  # CF: there is a prob, in the paper wrt LLL bounds on |x| or |x|^2....
  boundk = R(n)*log(tmp)//(2*deg_p*log(R(p)))

  ss = abs_upper_bound(boundk, fmpz)
  return ss
end

#identical to hasroot - which one do we want?
function ispower(a::NfOrdElem, n::Int)
  fl, r = ispower(nf(parent(a))(a), n, isintegral = true)
  return fl, parent(a)(r)
end
