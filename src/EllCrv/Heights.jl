################################################################################
#
#             EllCrv/Heights.jl : Height functions on elliptic curves
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

export local_height, canonical_height, naive_height, height_pairing, regulator,
       neron_tate_height

################################################################################
#
#  Naive Height
#
################################################################################

@doc Markdown.doc"""
    naive_height(P::EllCrvPt{fmpq}, prec) -> arb

Return the naive height of a point $P$ on an elliptic curve defined over
$\mathbb{Q}$.
"""
function naive_height(P::EllCrvPt{fmpq}, prec::Int = 100)
  attempt = 1
  x = P[1]
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

@doc Markdown.doc"""
    naive_height(P::EllCrvPt{nf_elem}, prec) -> arb

Return the naive height of a point $P$ on an elliptic curve defined over
a number field.
"""
function naive_height(P::EllCrvPt{nf_elem}, prec::Int = 100)
  attempt = 1
  
  K = base_field(parent(P))
  OK = ring_of_integers(K)
  
  x = P[1]
  q = K(denominator(x))
  
  N = norm(ideal(OK, x) + 1*OK)
  
  deg = degree(K)

  while true
    R = ArbField(attempt*prec, cached = false)
    
    #Non-archimedean contribution
    result = -log(N)
    
    #Archimedean contribution (Mahler measure)
    for v in real_places(K)
      s = abs(evaluate(x, v, attempt*prec))
      result = result + log(max(s, one(R)))
    end
    
    for v in complex_places(K)
      s = abs(evaluate(x, v, attempt*prec))
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

################################################################################
#
#  Local Height at finite prime
#
################################################################################

# Equal to Magma command with Renormalization := true flag.
# In Magma the default is to add a factor of (1/6)log Δv at every place.

#TODO: Fine-tune precision

@doc Markdown.doc"""
    local_height(P::EllCrvPt{fmpq}, p::IntegerUnion, prec::Int) -> ArbField

Computes the local height of a point $P$ on an elliptic curve defined over
$\mathbf{Q}$ at $p$. The number $p$ must be a prime or $0$. In the latter case,
the height at the infinite place is returned.
"""
function local_height(P::EllCrvPt{fmpq}, p, prec::Int = 100)

  if !is_finite(P)
    return zero(ArbField(prec, cached = false))
  end

  if p == 0
    return _real_height(P, prec)
  end

  @req p > 0 && isprime(p) "p must be 0 or a non-negative prime"

  E = parent(P)
  F, phi = minimal_model(E)

  P = phi(P)

  p = FlintZZ(p)
    
  x = P[1]
  y = P[2]

  a1, a2, a3, a4, a6 = map(numerator, a_invars(F))

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
    N = ZZ(valuation(delta, p)) # work with fmpz to avoid overflow
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

function local_height(P::EllCrvPt{nf_elem}, pIdeal::NfOrdIdl, prec::Int = 100)

  if !is_finite(P)
    return zero(ArbField(prec, cached = false))
  end

  #if p == 0
  #  return _real_height(P, prec)
  #end

  @req #=p > 0 &&=# isprime(pIdeal) "p must be 0 or a non-negative prime"

  E = parent(P)
  K = base_field(E)
  OK = ring_of_integers(K)
  F, phi = minimal_model(E, pIdeal)
  
  res_degree = norm(pIdeal)
  p = minimum(pIdeal)

  P = phi(P)
    
  x = P[1]
  y = P[2]

  a1, a2, a3, a4, a6 = map(numerator, a_invars(F))

  b2, b4, b6, b8 = map(OK, b_invars(E))
  c4, c6 = map(OK, c_invars(E))

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
    N = ZZ(valuation(delta, pIdeal)) # work with fmpz to avoid overflow
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
    # Weighted as in Silverman? Then //(ramification_index(pIdeal)*degree(ResidueField(OK, pIdeal)[1]))

    !radiuslttwopower(result, -prec) && (attempt *= 2; continue)

    if radiuslttwopower(result, -prec)
      expand!(result, -prec)
      @assert radiuslttwopower(result, -prec)
      return result
    end
    #attempt = 2*attempt
  end
end

function local_height(P::EllCrvPt{nf_elem}, v::InfPlc, prec = 100)
  return archimedean_height(P, v, prec)
end

################################################################################
#
#  Archimedean Height
#
################################################################################

#Precision is given in bits (as Real Field also works this way), but maybe this should be changed. In Magma precision is given in decimals

function _real_height(P::EllCrvPt{fmpq}, prec = 100)
  attempt = 3
  d = ceil(Int, prec*log(10,2))

  E = parent(P)
  F = E
  #F = minimal_model(E)
  #phi = isomorphism(E, F)

  #P = phi(P)

  a1, a2, a3, a4, a6 = map(numerator,(a_invars(F)))

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
            (Ref{arb}, Ref{arf_struct}), mu, error_arf)
    ccall((:arf_clear, libarb), Nothing, (Ref{arf_struct}, ), error_arf)
    expand!(mu, -prec)
    @assert radiuslttwopower(mu, prec)
    return mu
  end
end

function archimedean_height(P::EllCrvPt{nf_elem}, v::InfPlc, prec = 100)
  attempt = 3
  d = ceil(Int, prec*log(10,2))

  E = parent(P)
  F = E
  #F = minimal_model(E)
  #phi = isomorphism(E, F)

  #P = phi(P)

  a1, a2, a3, a4, a6 = map(numerator,(a_invars(F)))
  R = ArbField(prec)
  b2, b4, b6, b8 = map(t -> evaluate(t, v, prec), get_b_integral(F))
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
            (Ref{arb}, Ref{arf_struct}), mu, error_arf)
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

@doc Markdown.doc"""
    neron_tate_height(P::EllCrvPt{T}, prec::Int) -> arb 
      where T<:Union{fmpq, nf_elem}

Compute the Néron-Tate height (or canonical height) of a point $P$ on an
elliptic curve defined over $\mathbb{Q}$.
"""
function neron_tate_height(P::EllCrvPt{T}, prec::Int = 100) where T<:Union{fmpq, nf_elem}
  return canonical_height(P, prec)
end

@doc Markdown.doc"""
    canonical_height(P::EllCrvPt{fmpq}, prec::Int) -> arb

Compute the Néron-Tate height (or canonical height) of a point $P$ on an
elliptic curve defined over $\mathbb{Q}$.
"""
function canonical_height(P::EllCrvPt{fmpq}, prec = 100)
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

@doc Markdown.doc"""
    canonical_height(P::EllCrvPt{nf_elem}, prec::Int) -> arb

Compute the Néron-Tate height (or canonical height) of a point $P$ on an
elliptic curve defined over a number field
"""
function canonical_height(P::EllCrvPt{nf_elem}, prec = 100)
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

@doc Markdown.doc"""
    height_pairing(P::EllCrvPt{T},Q::EllCrvPt{T}, prec::Int) 
      -> ArbField where T<:Union{fmpq, nf_elem}

Compute the height pairing of two points $P$ and $Q$ of an
elliptic curve defined over a number field. It is defined by 
$h(P,Q) = (h(P + Q) - h(P) -h(Q))/2$ where $h$ is the canonical height.
"""
function height_pairing(P::EllCrvPt{T}, Q::EllCrvPt{T}, prec::Int = 100) where T<:Union{fmpq, nf_elem}
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

@doc Markdown.doc"""
    regulator(S::Vector{EllCrvPt{T}}, prec = 100) -> ArbField

Return the determinant of the height pairing matrix of a given
set of points $S$ on an elliptic curve over a number field.
"""
function regulator(S::Vector{EllCrvPt{T}}, prec::Int = 100) where T<:Union{fmpq, nf_elem}
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

