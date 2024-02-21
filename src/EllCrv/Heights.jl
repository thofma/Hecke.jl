################################################################################
#
#             EllipticCurve/Heights.jl : Height functions on elliptic curves
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
# (C) 2016 Tommy Hofmann
# (C) 2016 Robin Ammon
# (C) 2016 Sofia Brenner
# (C) 2022 Jeroen Hanselman
#
################################################################################

################################################################################
#
#  Naive Height
#
################################################################################

function naive_height_coordinate(x::QQFieldElem, prec::Int = 100)
  attempt = 1
  p = numerator(x)
  q = denominator(x)
  r = max(abs(p), abs(q))

  while true
    R = ArbField(attempt*prec, cached = false)
    result = log(R(r))
    if radiuslttwopower(result, -prec)
      expand!(result, -prec)
      @assert radiuslttwopower(result, -prec)
      return result
    end
    attempt = 2*attempt
  end
end

@doc raw"""
    naive_height(P::EllipticCurvePoint{QQFieldElem}, prec) -> ArbFieldElem

Return the naive height of a point $P$ on an elliptic curve defined over
$\mathbb{Q}$.
"""
function naive_height(P::EllipticCurvePoint{QQFieldElem}, prec::Int = 100)
  return naive_height_coordinate(P[1], prec)
end

function naive_height_coordinate(x::AbsSimpleNumFieldElem, prec::Int = 100)
  attempt = 1

  K = parent(x)
  OK = ring_of_integers(K)

  q = K(denominator(x))

  N = norm(ideal(OK, x) + 1*OK)

  deg = degree(K)

  while true
    R = ArbField(attempt*prec, cached = false)

    #Non-archimedean contribution
    result = -log(N)

    #Archimedean contribution (Mahler measure)
    for v in real_places(K)
      s = abs(evaluate(x, _embedding(v), attempt*prec))
      result = result + log(max(s, one(R)))
    end

    for v in complex_places(K)
      s = abs(evaluate(x, _embedding(v), attempt*prec))
      result = result + 2*log(max(s, one(R)))
    end

    result = result//deg

    if radiuslttwopower(result, -prec)
      expand!(result, -prec)
      @assert radiuslttwopower(result, -prec)
      return result
    end
    attempt = 2*attempt
  end
end

@doc raw"""
    naive_height(P::EllipticCurvePoint{AbsSimpleNumFieldElem}, prec) -> ArbFieldElem

Return the naive height of a point $P$ on an elliptic curve defined over
a number field.
"""
function naive_height(P::EllipticCurvePoint{AbsSimpleNumFieldElem}, prec::Int = 100)
  return naive_height_coordinate(P[1], prec)
end


################################################################################
#
#  Local Height at finite prime
#
################################################################################

# Equal to Magma command with Renormalization := true flag.
# In Magma the default is to add a factor of (1/6)log Δv at every place.

#TODO: Fine-tune precision

@doc raw"""
    local_height(P::EllipticCurvePoint{QQFieldElem}, p::IntegerUnion, prec::Int) -> ArbField

Computes the local height of a point $P$ on an elliptic curve defined over
$\mathbf{Q}$ at $p$. The number $p$ must be a prime or $0$. In the latter case,
the height at the infinite place is returned.
"""
function local_height(P::EllipticCurvePoint{QQFieldElem}, p, prec::Int = 100)

  if !is_finite(P)
    return zero(ArbField(prec, cached = false))
  end

  if p == 0
    return _real_height(P, prec)
  end

  @req p > 0 && is_prime(p) "p must be 0 or a non-negative prime"

  E = parent(P)
  F, phi = minimal_model(E)

  P = phi(P)

  p = FlintZZ(p)

  x = P[1]
  y = P[2]

  a1, a2, a3, a4, a6 = map(numerator, a_invariants(F))

  b2, b4, b6, b8, c4, c6 = get_b_c_integral(F)

  delta = discriminant(E)

  A = 3*x^2 + 2*a2*x + a4 - a1*y
  B = 2*y + a1*x + a3 # = psi2(P)
  C = 3*x^4 + b2 * x^3 + 3*b4*x^2 + 3*b6*x + b8 # = psi3(P)

  # L always QQ
  # N always ZZ
  # M always QQ

  if (!iszero(A) && valuation(A, p) <= 0) || (!iszero(B) && valuation(B, p) <= 0)
    if !iszero(x)
      L = QQ(max(0, -valuation(x, p)))
    else
      L = zero(QQ)
    end
  elseif (!iszero(c4) && valuation(c4, p) == 0)
    N = ZZ(valuation(delta, p)) # work with ZZRingElem to avoid overflow
    if iszero(B)
      M = N//2
    else
      M = min(QQ(valuation(B, p)), N//2)
    end
    L = M*(M - N)//N
  elseif (iszero(C) || (!iszero(C) && !iszero(B) && valuation(C, p) >= 3*valuation(B, p)))
    L = ZZ(-2*valuation(B, p))//3
  else
    L = ZZ(-valuation(C, p))//4
  end

  attempt = 2

  while true
    R = ArbField(attempt*prec, cached = false)
    result = L*log(R(p))

    !radiuslttwopower(result, -prec) && (attempt *= 2; continue)

    if radiuslttwopower(result, -prec)
      expand!(result, -prec)
      @assert radiuslttwopower(result, -prec)
      return result
    end
    #attempt = 2*attempt
  end
end

function local_height(P::EllipticCurvePoint{AbsSimpleNumFieldElem}, pIdeal::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, prec::Int = 100)

  if !is_finite(P)
    return zero(ArbField(prec, cached = false))
  end

  #if p == 0
  #  return _real_height(P, prec)
  #end

  @req #=p > 0 &&=# is_prime(pIdeal) "p must be 0 or a non-negative prime"

  E = parent(P)
  K = base_field(E)
  OK = ring_of_integers(K)
  F, phi = minimal_model(E, pIdeal)

  res_degree = norm(pIdeal)
  p = minimum(pIdeal)

  P = phi(P)

  x = P[1]
  y = P[2]

  a1, a2, a3, a4, a6 = map(numerator, a_invariants(F))

  b2, b4, b6, b8 = map(OK, b_invariants(E))
  c4, c6 = map(OK, c_invariants(E))

  delta = discriminant(E)

  A = 3*x^2 + 2*a2*x + a4 - a1*y
  B = 2*y + a1*x + a3 # = psi2(P)
  C = 3*x^4 + b2 * x^3 + 3*b4*x^2 + 3*b6*x + b8 # = psi3(P)

  # L always QQ
  # N always ZZ
  # M always QQ

  if (!iszero(A) && valuation(A, pIdeal) <= 0) || (!iszero(B) && valuation(B, pIdeal) <= 0)
    if !iszero(x)
      L = QQ(max(0, -valuation(x, pIdeal)))
    else
      L = zero(QQ)
    end
  elseif (!iszero(c4) && valuation(c4, pIdeal) == 0)
    N = ZZ(valuation(delta, pIdeal)) # work with ZZRingElem to avoid overflow
    if iszero(B)
      M = N//2
    else
      M = min(QQ(valuation(B, pIdeal)), N//2)
    end
    L = M*(M - N)//N
  elseif (iszero(C) || (!iszero(C) && !iszero(B) && valuation(C, pIdeal) >= 3*valuation(B, pIdeal)))
    L = ZZ(-2*valuation(B, pIdeal))//3
  else
    L = ZZ(-valuation(C, pIdeal))//4
  end

  attempt = 2

  while true
    R = ArbField(attempt*prec, cached = false)
    result = L*log(R(res_degree))
    # Weighted as in Silverman? Then //(ramification_index(pIdeal)*degree(residue_field(OK, pIdeal)[1]))

    !radiuslttwopower(result, -prec) && (attempt *= 2; continue)

    if radiuslttwopower(result, -prec)
      expand!(result, -prec)
      @assert radiuslttwopower(result, -prec)
      return result
    end
    #attempt = 2*attempt
  end
end

function local_height(P::EllipticCurvePoint{AbsSimpleNumFieldElem}, v::InfPlc, prec = 100)
  return archimedean_height(P, v, prec)
end

################################################################################
#
#  Archimedean Height
#
################################################################################

#Precision is given in bits (as Real Field also works this way), but maybe this should be changed. In Magma precision is given in decimals

function _real_height(P::EllipticCurvePoint{QQFieldElem}, prec = 100)
  attempt = 3
  d = ceil(Int, prec*log(10,2))

  E = parent(P)
  F = E
  #F = minimal_model(E)
  #phi = isomorphism(E, F)

  #P = phi(P)

  a1, a2, a3, a4, a6 = map(numerator,(a_invariants(F)))

  b2, b4, b6, b8 = get_b_integral(F)
  H = max(ZZ(4), abs(b2), 2*abs(b4), 2*abs(b6), abs(b8))
  _b2 = b2-12
  _b4 = b4-b2+6
  _b6 = b6-2*b4+b2-4
  _b8 = b8-3*b6+3*b4-b2+3

  # We are looking for h.
  # We want to compute a term f with |f - h| < 2^prec.
  # We know that if f = \sum_{i=1}^N a_i, then |f - h| < 2^-prec.
  # The problem is that the computation of f itself introduces
  # round off errors. So we choose N such that
  # |f - h| < 2^-(prec + 1) and compute f' such that |f' - f| < 2^-(prec + 1)
  # Then |f' - h| < 2^-prec.

  # Silvermans bound (Theorem 4.2) for the error term R(N) asserts that if
  # N >= 5/3 * d + ... things independent of d, then
  # then |R(N)| < 1/2 * 10^-d
  # But our precision is with respect to 2, so we have
  # N >= 5/3 * log(2)/log((10) + things independent of prec
  # We use a low precision to get an upper bound on the right hand side

  Rc = ArbField(53, cached = false)

  wprec = prec + 1

  N = ceil(Int,
            Rc(5)/3 * log(Rc(2))/log(Rc(10)) * (wprec + 1) + Rc(1)/2 +
            Rc(3)/4 * log(Rc(7) + Rc(4)/3 * log(Rc(H)) +
                                 Rc(1)/3 * log(max(Rc(1), inv(Rc(discriminant(E))))))
          )

  while true
    R = ArbField(attempt*wprec)
    x = R(P[1])
    y = R(P[2])

    if abs(x)<0.5
      t = 1/(x+1)
      beta = 0
    elseif abs(x) >= 0.5
      t = 1/x
      beta = 1
    else
      attempt = 2 * attempt
      continue
    end

    mu = -log(abs(t))
    f = ZZ(1)//1

    for n in 0:N
      f = f//4
      if beta==1
        w = b6*t^4+2*b4*t^3+b2*t^2+4*t
        z = 1-b4*t^2-2*b6*t^3-b8*t^4
        zw = z+w
      else
        w = _b6*t^4+2*_b4*t^3+_b2*t^2+4*t
        z = 1-_b4*t^2-2*_b6*t^3-_b8*t^4
        zw = z-w
      end
      if abs(w) <= 2*abs(z)
        mu = mu+f*log(abs(z))
        t = w/z
      else
        mu = mu+f*log(abs(zw))
        t = w/zw
        beta = 1-beta
      end
    end

    !(isfinite(mu)  && radiuslttwopower(mu, wprec)) && (attempt *= 2; continue)

    # Algorithm is only precise up to wprec bits
    error_arf = arf_struct(0, 0, 0, 0)
    ccall((:arf_set_si_2exp_si, libarb), Nothing,
        (Ref{arf_struct}, Int, Int), error_arf, Int(1), Int(-wprec))
    ccall((:arb_add_error_arf, libarb), Nothing,
            (Ref{ArbFieldElem}, Ref{arf_struct}), mu, error_arf)
    ccall((:arf_clear, libarb), Nothing, (Ref{arf_struct}, ), error_arf)
    expand!(mu, -prec)
    @assert radiuslttwopower(mu, prec)
    return mu
  end
end

function archimedean_height(P::EllipticCurvePoint{AbsSimpleNumFieldElem}, _v::InfPlc, prec = 100)
  v = _embedding(_v)
  attempt = 3
  d = ceil(Int, prec*log(10,2))

  E = parent(P)
  F = E
  #F = minimal_model(E)
  #phi = isomorphism(E, F)

  #P = phi(P)

  a1, a2, a3, a4, a6 = map(numerator,(a_invariants(F)))
  R = ArbField(prec)
  b2, b4, b6, b8 = map(t -> evaluate(t, v,  prec), get_b_integral(F))
  H = max(R(4), abs(b2), 2*abs(b4), 2*abs(b6), abs(b8))

  # We are looking for h.
  # We want to compute a term f with |f - h| < 2^prec.
  # We know that if f = \sum_{i=1}^N a_i, then |f - h| < 2^-prec.
  # The problem is that the computation of f itself introduces
  # round off errors. So we choose N such that
  # |f - h| < 2^-(prec + 1) and compute f' such that |f' - f| < 2^-(prec + 1)
  # Then |f' - h| < 2^-prec.

  # Silvermans bound (Theorem 4.2) for the error term R(N) asserts that if
  # N >= 5/3 * d + ... things independent of d, then
  # then |R(N)| < 1/2 * 10^-d
  # But our precision is with respect to 2, so we have
  # N >= 5/3 * log(2)/log((10) + things independent of prec
  # We use a low precision to get an upper bound on the right hand side

  Rc = ArbField(53, cached = false)

  wprec = prec + 1

  abs_disc = abs(evaluate(discriminant(E), v, 53))

  N = ceil(Int,
            Rc(5)/3 * log(Rc(2))/log(Rc(10)) * (wprec + 1) + Rc(1)/2 +
            Rc(3)/4 * log(Rc(7) + Rc(4)/3 * log(Rc(H)) +
                                 Rc(1)/3 * log(max(Rc(1), inv(Rc(abs_disc)))))
          )

  while true
    newprec = attempt*wprec
    b2, b4, b6, b8 = map(t -> evaluate(t, v, newprec), get_b_integral(F))

    _b2 = b2-12
    _b4 = b4-b2+6
    _b6 = b6-2*b4+b2-4
    _b8 = b8-3*b6+3*b4-b2+3

    x = evaluate(P[1], v, newprec)
    y = evaluate(P[2], v, newprec)

    if abs(x)<0.5
      t = 1/(x+1)
      beta = 0
    elseif abs(x) >= 0.5
      t = 1/x
      beta = 1
    else
      attempt = 2 * attempt
      continue
    end

    mu = -log(abs(t))
    f = ZZ(1)//1

    for n in 0:N
      f = f//4
      if beta==1
        w = b6*t^4+2*b4*t^3+b2*t^2+4*t
        z = 1-b4*t^2-2*b6*t^3-b8*t^4
        zw = z+w
      else
        w = _b6*t^4+2*_b4*t^3+_b2*t^2+4*t
        z = 1-_b4*t^2-2*_b6*t^3-_b8*t^4
        zw = z-w
      end
      if abs(w) <= 2*abs(z)
        mu = mu+f*log(abs(z))
        t = w/z
      else
        mu = mu+f*log(abs(zw))
        t = w/zw
        beta = 1-beta
      end
    end

    !(isfinite(mu)  && radiuslttwopower(mu, wprec)) && (attempt *= 2; continue)

    # Algorithm is only precise up to wprec bits
    error_arf = arf_struct(0, 0, 0, 0)
    ccall((:arf_set_si_2exp_si, libarb), Nothing,
        (Ref{arf_struct}, Int, Int), error_arf, Int(1), Int(-wprec))
    ccall((:arb_add_error_arf, libarb), Nothing,
            (Ref{ArbFieldElem}, Ref{arf_struct}), mu, error_arf)
    ccall((:arf_clear, libarb), Nothing, (Ref{arf_struct}, ), error_arf)
    expand!(mu, -prec)
    @assert radiuslttwopower(mu, prec)
    return mu
  end
end


################################################################################
#
#  Néron-Tate Height
#
################################################################################

@doc raw"""
    neron_tate_height(P::EllipticCurvePoint{T}, prec::Int) -> ArbFieldElem
      where T<:Union{QQFieldElem, AbsSimpleNumFieldElem}

Compute the Néron-Tate height (or canonical height) of a point $P$ on an
elliptic curve defined over $\mathbb{Q}$.
"""
function neron_tate_height(P::EllipticCurvePoint{T}, prec::Int = 100) where T<:Union{QQFieldElem, AbsSimpleNumFieldElem}
  return canonical_height(P, prec)
end

@doc raw"""
    canonical_height(P::EllipticCurvePoint{QQFieldElem}, prec::Int) -> ArbFieldElem

Compute the Néron-Tate height (or canonical height) of a point $P$ on an
elliptic curve defined over $\mathbb{Q}$.
"""
function canonical_height(P::EllipticCurvePoint{QQFieldElem}, prec = 100)
  attempt = 1

  while true
    R = ArbField(attempt*prec, cached = false)
    E = P.parent
    disc = discriminant(E)
    d = (denominator(P[1]))
    h = local_height(P, 0, attempt*prec) + log(R(d))
    plist = bad_primes(E)

    for p in plist
      if !divides(d,p)[1]
       h = h + local_height(P,p, attempt*prec)
      end
    end
    if radiuslttwopower(h, -prec)
      expand!(h, -prec)
      @assert radiuslttwopower(h, -prec)
      return h
    else
      attempt = 2*attempt
    end
  end
end

@doc raw"""
    canonical_height(P::EllipticCurvePoint{AbsSimpleNumFieldElem}, prec::Int) -> ArbFieldElem

Compute the Néron-Tate height (or canonical height) of a point $P$ on an
elliptic curve defined over a number field
"""
function canonical_height(P::EllipticCurvePoint{AbsSimpleNumFieldElem}, prec = 100)
  attempt = 1
  K = base_field(parent(P))
  OK = ring_of_integers(K)
  while true
    R = ArbField(attempt*prec, cached = false)
    E = P.parent
    disc = discriminant(E)

    #d should be the norm of J where I/J = P[1]*OK is the unique decomposition
    #of prime integer ideals
    d = (denominator(P[1]*OK))
    h = log(d)

    for v in real_places(K)
      h = h + local_height(P, v, attempt*prec)
    end

    for v in complex_places(K)
      h = h + 2*local_height(P, v, attempt*prec)
    end


    plist = bad_primes(E)

    #Removed the divides check
    for p in plist
      h = h + local_height(P,p, attempt*prec)
    end

    h = h//degree(K)

    if radiuslttwopower(h, -prec)
      expand!(h, -prec)
      @assert radiuslttwopower(h, -prec)
      return h
    else
      attempt = 2*attempt
    end
  end
end

@doc raw"""
    height_pairing(P::EllipticCurvePoint{T},Q::EllipticCurvePoint{T}, prec::Int)
      -> ArbField where T<:Union{QQFieldElem, AbsSimpleNumFieldElem}

Compute the height pairing of two points $P$ and $Q$ of an
elliptic curve defined over a number field. It is defined by
$h(P,Q) = (h(P + Q) - h(P) -h(Q))/2$ where $h$ is the canonical height.
"""
function height_pairing(P::EllipticCurvePoint{T}, Q::EllipticCurvePoint{T}, prec::Int = 100) where T<:Union{QQFieldElem, AbsSimpleNumFieldElem}
  attempt = 1
  while true
    wprec = attempt * prec
    result = (canonical_height(P + Q, wprec) - canonical_height(P, wprec))
    result = (result - canonical_height(Q, wprec))/2

    !radiuslttwopower(result, -prec) && (attempt *= 2; continue)

    expand!(result, -prec)
    @assert radiuslttwopower(result, -prec)
    return result
  end
end

@doc raw"""
    regulator(S::Vector{EllipticCurvePoint{T}}, prec = 100) -> ArbField

Return the determinant of the height pairing matrix of a given
set of points $S$ on an elliptic curve over a number field.
"""
function regulator(S::Vector{EllipticCurvePoint{T}}, prec::Int = 100) where T<:Union{QQFieldElem, AbsSimpleNumFieldElem}
  attempt = 2

  while true
    wprec = attempt * prec
    r = length(S)
    M = zero_matrix(ArbField(attempt*prec), r, r)

    for i in 1:r
      for j in 1:r
        M[i, j] = height_pairing(S[i], S[j], wprec)
      end
    end

    result = det(M)

    !radiuslttwopower(result, -prec) && (attempt *= 2; continue)

    expand!(result, -prec)
    return result
  end
end

################################################################################
#
#  Height bounds
#
################################################################################

#Base on Height Difference Bounds for elliptic curves over number fields by
#Cremona, Prickett and Siksek.

# In Magma the lower bound is sometimes different from our lower bound.  The
# reason for this is that at the time of writing this the Magma implementation
# always seems to include 1 and -1 in S and S2 in their version of
# CPS_dvev_real. Even if f(1) and f(-1) are <0.
# In the original CPS paper (and in the implementation in Sage, which
# unfortunately doesn't compute a lower bound) this does not happen, which
# means that Magma's implementation is probably slightly wrong and that their
# lower bounds are considerably less sharp.

@doc raw"""
    CPS_height_bounds(E::EllipticCurve) -> ArbFieldElem, ArbFieldElem

Given an elliptic curve over a number field or rational field, return a tuple
`a, b` giving bounds for the difference between the naive and the canonical
height of an elliptic curve E. We have `a <= naive_height(P) -
canonical_height(P) <= b` for all rational points `P` of `E`.
"""
function CPS_height_bounds(E::EllipticCurve{T}) where T<:Union{QQFieldElem, AbsSimpleNumFieldElem}
  # This is just a working precision
  prec = 110
  P = bad_primes(E)
  K = base_field(E)
  d = degree(K)

  Rv = real_places(K)
  Cv = complex_places(K)

  dv_arch = ev_arch = zero(ArbField(prec, cached = false))

  for v in Rv
    dv, ev = CPS_dvev_real(E, v, prec)
    dv_arch += log(dv)
    ev_arch += log(ev)
  end

  for v in Cv
    dv, ev = CPS_dvev_complex(E, v, prec)
    dv_arch += 2*log(dv)
    ev_arch += 2*log(ev)
  end

  non_arch_contribution = sum([CPS_non_archimedean(E, v, prec) for v in P])//d
  return 1//(3*d) * dv_arch, 1//(3*d) * ev_arch + non_arch_contribution
end

function CPS_non_archimedean(E::EllipticCurve{T}, v, prec::Int = 100) where T
  OK = ring_of_integers(base_field(E))
  Ep, K, f, c = tates_algorithm_local(E, v)
  k = K.ksymbol

  Rc = ArbField(prec, cached = false)

  # See Table 1 in Cremona, Prickett, Siksek Height Difference Bounds For Elliptic Curves
  # over Number Fields for the values of av depending on
  # the Kodaira symbol and the Tamagawa number
  if c == 1
    av = 0
  elseif k > 4
    m = k - 4
    if iseven(m)
      av = m//4
    else
      av = (m^2 - 1)//(4*m)
    end
  elseif k == 3
    av = 1//2
  elseif k == 4
    av = 2//3
  elseif k == -1
    av = 1
  elseif k < -4
    if c == 2
      av = 1
    elseif c == 4
      m = k + 4
      av = (m + 4)//4
    end
  elseif k == -4
    av = 4//3
  elseif k == -3
    av = 3//2
  end

  D = discriminant(E)
  Dv = discriminant(Ep)
  qv = norm(v)
  disc_ord = valuation(D//Dv, v)
  return (Rc(av) + Rc(Rc(disc_ord)//6))*log(qv)
end

function CPS_dvev_real(E::EllipticCurve{T}, v::V, prec::Int = 100) where T where V<:Union{InfPlc, PosInf}
  Rc = ArbField(prec)
  C = AcbField(prec)
  K = base_field(E)
  Kx, x = polynomial_ring(K, "x")

  b2, b4, b6, b8 = b_invariants(E)

  f = 4*x^3 + b2*x^2 + 2*b4*x + b6
  df = 12*x^2 +2*b2*x + 2*b4
  g = x^4 - b4*x^2 -2*b6*x - b8
  dg = 4*x^3 - 2*b4*x -2*b6

  F = b6*x^4 + 2*b4*x^3 + b2*x^2 + 4*x
  G = -b8*x^4 - 2*b6*x^3 - b4*x^2 + 1
  dF = 4*b6*x^3 + 6*b4*x^2 + 2*b2*x + 4
  dG = -4*b8*x^3 - 6*b6*x^2 - 2*b4*x

  S = vcat(_roots(f, v, prec = prec)[2], _roots(g, v, prec = prec)[2], _roots(f + g, v, prec = prec)[2],  _roots(f - g, v, prec = prec)[2], _roots(df, v, prec = prec)[2], _roots(dg, v, prec = prec)[2], Rc(1), Rc(-1))

  S2 = vcat(_roots(F, v, prec = prec)[2], _roots(G, v, prec = prec)[2], _roots(F + G, v, prec = prec)[2],  _roots(F - G, v, prec = prec)[2], _roots(dF, v, prec = prec)[2], _roots(dG, v, prec = prec)[2], Rc(1), Rc(-1))

  Rx, x = polynomial_ring(Rc, "x")

  b2R, b4R, b6R, b8R = map(real, map(t -> evaluate(t, _embedding(v), prec), b_invariants(E)))

  fR = 4*x^3 + b2R*x^2 + 2*b4R*x + b6R
  gR = x^4 - b4R*x^2 -2*b6R*x - b8R
  FR = b6R*x^4 + 2*b4R*x^3 + b2R*x^2 + 4*x
  GR = -b8R*x^4 - 2*b6R*x^3 - b4R*x^2 + 1

  test_fg = function(x::ArbFieldElem)

    fx = evaluate(fR, x)

    return abs(x)<= 1 && (fx > Rc(0) || contains(fx, zero(Rc)))
  end

  filter!(test_fg, S)
  fglist = map(s -> max(abs(evaluate(fR,s)), abs(evaluate(gR,s))), S)

  test_FG = function(x::ArbFieldElem)
  Fx = evaluate(FR, x)
    return abs(x)<= 1 && (Fx > 0 ||contains(Fx, zero(Rc)))
  end

  filter!(test_FG, S2)

  FGlist = map(s -> max(abs(evaluate(FR,s)), abs(evaluate(GR,s))), S2)

  e_v = inv(minimum(vcat(fglist, FGlist)))
  d_v = inv(maximum(vcat(fglist, FGlist)))

  return d_v, e_v
end


function CPS_dvev_complex(E::EllipticCurve{T}, v::V, prec::Int = 100) where T where V<:Union{InfPlc, PosInf}

  Rc = ArbField(prec)
  C = AcbField(prec)
  K = base_field(E)
  Rx, x = polynomial_ring(C, "x")

  b2, b4, b6, b8 = map(t -> evaluate(t, _embedding(v), prec), b_invariants(E))

  f = 4*x^3 + b2*x^2 + 2*b4*x + b6
  g = x^4 - b4*x^2 -2*b6*x - b8
  F = b6*x^4 + 2*b4*x^3 + b2*x^2 + 4*x
  G = -b8*x^4 - 2*b6*x^3 - b4*x^2 + 1

  E_fg = function (u::AcbFieldElem, eta::ArbFieldElem)
    fsum = sum([eta^i//factorial(i)*abs(derivative(f, i)(u)) for i in (1:3)])
    gsum = sum([eta^i//factorial(i)*abs(derivative(g, i)(u)) for i in (1:4)])
    return max(fsum, gsum)
  end

  E_FG = function (u::AcbFieldElem, eta::ArbFieldElem)
    Fsum = sum([eta^i//factorial(i)*abs(derivative(F, i)(u)) for i in (1:4)])
    Gsum = sum([eta^i//factorial(i)*abs(derivative(G, i)(u)) for i in (1:4)])
    return max(Fsum, Gsum)
  end


  M = [(m, n) for m in (-10:10) for n in (-10:10)]
  filter!(t -> t[1]^2 + t[2]^2 <= 100, M)
  M = map(t -> divexact((t[1]) + t[2]*onei(C), 10), M)

  H_fg = [max(abs(f(z)), abs(g(z))) for z in M]
  H_FG = [max(abs(F(z)), abs(G(z))) for z in M]

  # minimum and maximum of Vector{ArbFieldElem} are bugged, even reduec(min/max, ...)
  alpha_start_fg = H_fg[1]
  beta_start_fg = H_fg[1]
  for x in H_fg
    alpha_start_fg = _min(alpha_start_fg, x)
    beta_start_fg = _max(beta_start_fg, x)
  end

  alpha_start_FG = H_FG[1]
  beta_start_FG = H_FG[1]
  for x in H_FG
    alpha_start_FG = _min(alpha_start_FG, x)
    beta_start_FG = _max(beta_start_FG, x)
  end

  #Determines precision. Choosing a smaller mu makes the function a lot slower as
  #alpha_bound converges very slowly. When I tested different values it took 0.5s for
  #0.001 and 45s for 0.00001 for the same curve. Smaller mu only marginally improves the bound
  #so it is probably fine. We seem to get the same results as Magma.
  mu = Rc(0.001)
  a = -one(Rc)
  r = 2*one(Rc)

  approx_ev = inv(min(refine_alpha_bound(f, g, E_fg, mu, a, a, r, alpha_start_fg, prec),
    refine_alpha_bound(F, G, E_FG, mu, a, a, r, alpha_start_FG, prec)))
  approx_dv = inv(min(refine_beta_bound(f, g, E_fg, mu, a, a, r, beta_start_fg,prec),
    refine_beta_bound(F, G, E_FG, mu, a, a, r, beta_start_FG, prec)))
  return approx_dv, approx_ev
end

function refine_alpha_bound(P::PolyRingElem, Q::PolyRingElem, E,  mu::ArbFieldElem, a::ArbFieldElem, b::ArbFieldElem, r::ArbFieldElem, alpha_bound::ArbFieldElem, prec)

  C = AcbField(prec, cached = false)
  Rc = ArbField(prec, cached = false)
  i = onei(C)

  #We consider a square [a, a + r] x [b*i, (b + r) * i] in C
  corners = [a + b*i, a + r + b*i, a + (b + r)*i, a + r + (b + r)*i]
  filter!(t -> abs(t) <= 1, corners)

  #The supremum of h(u) is attained on the unit disk, so we
  #stop if the square doesn't intersect with the disk.
  #This happens exactly when none of the corners lie inside
  #the unit disk. The only exception is at the start
  #when r = 2 and the unit circle is contained in the square
  if isempty(corners) && r!= 2
    return alpha_bound
  end

  if abs(a + r//2 + (b + r//2)*i) <= 1
    u = a + r//2 + (b + r//2)*i
    eta = r//sqrt(Rc(2))
  else
    u = corners[1]
    eta = r*sqrt(Rc(2))
  end

  hu = max(abs(P(u)), abs(Q(u)))
  if hu - E(u, eta) > alpha_bound*exp(-mu)
    return alpha_bound
  end

  alpha_bound = min(alpha_bound, hu)

  #Subdiving the initial square into four squares and computing alpha_bound there
  alpha_bound = refine_alpha_bound(P, Q, E, mu, a, b, r//2, alpha_bound, prec)
  alpha_bound = refine_alpha_bound(P, Q, E, mu, a, b + r//2, r//2, alpha_bound, prec)
  alpha_bound = refine_alpha_bound(P, Q, E, mu, a + r//2, b, r//2, alpha_bound, prec)
  alpha_bound = refine_alpha_bound(P, Q, E, mu, a + r//2, b + r//2, r//2, alpha_bound, prec)

  return alpha_bound
end



function refine_beta_bound(P::PolyRingElem, Q::PolyRingElem, E,  mu::ArbFieldElem, a::ArbFieldElem, b::ArbFieldElem, r::ArbFieldElem, beta_bound::ArbFieldElem, prec)

  C = AcbField(prec, cached = false)
  Rc = ArbField(prec, cached = false)
  i = onei(C)

  #We consider a square [a, a + r] x [b*i, (b + r) * i] in C
  corners = [a + b*i, a + r + b*i, a + (b + r)*i, a + r + (b + r)*i]
  filter!(t -> abs(t) < 1, corners)

  #The supremum of h(u) is attained on the boundary, so we
  #stop if the square doesn't intersect with the boundary.
  #This happens exactly when none of the corners lie either inside
  #or outside the unit sphere. The only exception is at the start
  #when r =2 and the unit disk is contained in the square
  if (isempty(corners) || length(corners) == 4) && r!= 2
    return beta_bound
  end

  if abs(a + r//2 + (b + r//2)*i) <= 1
    u = a + r//2 + (b + r//2)*i
    eta = r//sqrt(Rc(2))
  else
    u = corners[1]
    eta = r*sqrt(Rc(2))
  end

  hu = max(abs(P(u)), abs(Q(u)))

  if hu - E(u, eta) < beta_bound*exp(mu)
    return beta_bound
  end

  beta_bound = max(beta_bound, hu)

  #Subdiving the initial square into four squares and computing alpha_bound there
  beta_bound = refine_beta_bound(P, Q, E, mu, a, b, r//2, beta_bound, prec)
  beta_bound = refine_beta_bound(P, Q, E, mu, a, b + r//2, r//2, beta_bound, prec)
  beta_bound = refine_beta_bound(P, Q, E, mu, a + r//2, b, r//2, beta_bound, prec)
  beta_bound = refine_beta_bound(P, Q, E, mu, a + r//2, b + r//2, r//2, beta_bound, prec)

  return beta_bound
end
