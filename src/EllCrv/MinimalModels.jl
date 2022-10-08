################################################################################
#
#             EllCrv/MinimalModels.jl : Minimal models and global minimal models
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

export minimal_model, has_global_minimal_model, semi_global_minimal_model, minimal_discriminant,
       global_minimality_class, tidy_model

################################################################################
#
#  Algorithm of Laska-Kraus-Connel
#
################################################################################

# algorithm of Laska-Kraus-Connell
@doc Markdown.doc"""
    laska_kraus_connell(E::EllCrv{fmpz}) -> Array{Nemo.fmpz}

Given an elliptic curve over $\mathbf Q$ with integral model, this returns an
isomorphic elliptic curve over $\mathbf Q$ with minimal discriminant.
"""
function laska_kraus_connell(E::EllCrv{fmpq})
  a1, a2, a3, a4, a6 = map(numerator,(a_invars(E)))

  b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

  delta = divexact(c4^3 - c6^2, 1728)

  u = fmpz(1)
  g = gcd(c6^2, delta)

  fac = factor(g)

  for (p, ord) in fac
    d = div(ord, 12)
    if p == 2
      a = divexact(c4, 2^(4*d))
      a = mod(a, 16)
      if a > 8
        a = a - 16
      end

      b = divexact(c6, 2^(6*d))
      b = mod(b, 32)
      if b > 16
        b = b - 32
      end

      if (mod(b, 4) != 3) && !((a == 0) && ((b == 0) || (b == 8)))
        d = d - 1

      end

    elseif p == 3
      ord1 = valuation(c6, 3)

      if (ord1 == 6*d + 2)
        d = d - 1

      end
    end
    u = u * p^d
  end

  c4 = divexact(c4, u^4)
  c6 = divexact(c6, u^6)

  b2 = mod(-c6, 12)
  if b2 > 6
      b2 = b2 - 12
  end

  b4 = divexact(b2^2 - c4, 24)
  b6 = divexact(-b2^3 + 36*b2*b4 - c6, 216)

  na1 = mod(b2, 2)
  na2 = divexact(b2 - na1, 4)
  na3 = mod(b6, 2)
  na4 = divexact(b4 - na1*na3, 2)
  na6 = divexact(b6 - na3, 4)


  return EllipticCurve([na1, na2, na3, na4, na6])::EllCrv{fmpq}
end

################################################################################
#
#  Local Minimal models
#
################################################################################

@doc Markdown.doc"""
    minimal_model(E::EllCrv{fmpq}, p::Int) -> EllCrv{fmpq},
      EllCrvIso{fmpq}, EllCrvIso{fmpq}

Returns a model of $E$, which is minimal at $p$. It is assumed that $p$
is prime.
"""
function minimal_model(E::EllCrv{fmpq}, p::Int)
  Ep = tates_algorithm_local(E, p)[1]
  phi = isomorphism(E, Ep)
  return Ep, phi, inv(phi)
end

@doc Markdown.doc"""
    minimal_model(E::EllCrv{nf_elem}, p::NfOrdIdl) -> EllCrv{nf_elem},
      EllCrvIso{nf_elem}, EllCrvIso{nf_elem}

Returns a model of $E$, which is minimal at $p$. It is assumed that $p$
is a prime ideal.
"""
function minimal_model(E::EllCrv{nf_elem}, p::NfOrdIdl)
  Ep = tates_algorithm_local(E, p)
  Ep = Ep[1]
  phi = isomorphism(E, Ep)
  return Ep, phi, inv(phi)
end


@doc Markdown.doc"""
    tidy_model(E::EllCrv{fmpq}) -> EllCrv{fmpq}

Given an elliptic curve with minimal model, this functions returns an
isomorphic curve with reduced minimal model, that is, $a_1, a_3 \in \{0, 1\}$
and $a_2 \in \{-1,0,1\}$.
"""
function tidy_model(E::EllCrv{fmpq})

  a1, a2, a3, a4, a6 = map(numerator,(a_invars(E)))

  if mod(a1, 2) == 0
    s = -divexact(a1, 2)
  else
    s = -divexact(a1 - 1, 2)
  end

  if mod(-a2 + s*a1 + s^2, 3) == 0
    r = divexact(-a2 + s*a1 + s^2, 3)
  elseif mod(-a2 + s*a1 + s^2, 3) == 1
    r = divexact(-1 - a2 + s*a1 + s^2, 3)
  else
    r = divexact(1 - a2 + s*a1 + s^2, 3)
  end

  if mod(-a3 - r*a1, 2) == 0
    t = divexact(-a3 - r*a1, 2)
  else
    t = divexact(1 - a3 - r*a1, 2)
  end

  E = transform_rstu(E, [r, s, t, 1])[1]

  return E
end

################################################################################
#
#  (Semi-) Global Minimal models
#
################################################################################

@doc Markdown.doc"""
    minimal_model(E::EllCrv{fmpq}) -> EllCrv{fmpq}

Returns the reduced global minimal model of $E$.
"""
function minimal_model(E::EllCrv{fmpq})
  F = laska_kraus_connell(E)
  phi = isomorphism(E, F)
  return F, phi, inv(phi)
end

@doc Markdown.doc"""
    minimal_model(E::EllCrv{nf_elem}) -> EllCrv, EllCrvIso, EllCrvIso

Returns the reduced global minimal model if it exists.
"""
function minimal_model(E::EllCrv{nf_elem})
  if has_global_minimal_model(E)
    F, phi,phi_inv, I = semi_global_minimal_model(E)
    return F, phi, phi_inv
  end
  error("The curve E has no global minimal model.")
end

@doc Markdown.doc"""
    has_global_minimal_model(E::EllCrv{T}) -> Bool where T<:Union{fmpq, nf_elem}

Return true when a global minimal model for E exists.
"""
function has_global_minimal_model(E::EllCrv{fmpq})
  return true
end

function has_global_minimal_model(E::EllCrv{nf_elem})
  return is_principal(global_minimality_class(E))[1]
end

@doc Markdown.doc"""
    global_minimalirt_class(E::EllCrv{nf_elem}) -> NfOrdIdl

Return the element in the ideal class group that forms the obstruction for
E not having a minimal model
"""
function global_minimality_class(E::EllCrv{nf_elem})
  K = base_field(E)
  OK = ring_of_integers(K)
  Cl, phi = class_group(K)
  if order(Cl) == 1
    return 1*OK
  end

  D = discriminant(E)
  P = bad_primes(E)
  v = Int[valuation(discriminant(tates_algorithm_local(E, p)[1]),p) for p in P]
  I = prod([P[i]^(divexact((valuation(D, P[i]) - v[i]),12)) for i in (1:length(P))]; init = 1*OK)
  return I
end

# The semi-minimal model is inspired by the SageMath implementation

@doc Markdown.doc"""
    semi_global_minimal_model(E::EllCrv{nf_elem}, p::NfOrdIdl) -> EllCrv, EllCrvIso, EllCrvIso, NfOrdIdl

Return a semi global minimal model and the unique prime at which the model is non-minimal.
"""
function semi_global_minimal_model(E::EllCrv{nf_elem})
  OK = ring_of_integers(base_field(E))
  G, mG = class_group(OK)
  if false #order(G) == 1
    # This is wrong, unless one forces Tate's algorithm to use the generator
    # as the uniformizer
    I = 1*OK
    P = bad_primes(E)
    F = E
    for p in P
      F = minimal_model(F, p)[1]
    end
  else
    F, I = _semi_global_minimal_model(E)
  end

  F = rescale_curve(F)
  F = reduce_model(F)

  phi = isomorphism(E, F)
  return F, phi, inv(phi), I
end

function _semi_global_minimal_model(E::EllCrv{T}) where T <:nf_elem
  I = global_minimality_class(E)
  K = base_field(E)
  OK = ring_of_integers(K)
  c4, c6 = c_invars(E)

  if is_principal(I)[1]
    P0 = 1*OK
    u = one(OK)
  else
    C, mC = class_group(OK)
    bound = 1000
    found = false
    mCI = mC\I
    while !found
      for P in prime_ideals_up_to(OK, bound)
        if mC\P == mCI
          P0 = P
          fl, u = is_principal(I*inv(P))
          found = true
          @assert fl
          I = I//P0
          break
        end
      end
      bound = 2*bound
    end
  end
  fl, u = is_principal(I)
  rc4 = OK(c4//u^4)
  rc6 = OK(c6//u^6)

  Emin = check_kraus_conditions_global(rc4, rc6)
  return Emin, P0
end

function c4c6_model(c4, c6)
  return EllipticCurve([-c4//48, -c6//864])
end

function check_kraus_conditions_global(c4::NfOrdElem, c6::NfOrdElem)
  OK = parent(c4)

  #Find b2 values for all the primes dividing 3
  OK3 = 3*OK
  Plist3 = prime_ideals_over(OK, 3)
  dat = Tuple{Bool, NfOrdElem}[check_kraus_conditions_at_3(c4, c6, P) for P in Plist3]
  if !all(Bool[d[1] for d in dat])
    return false, EllipticCurve(OK.nf, [0, 0, 0, 0, 0], false)
  end

  #We are fine at all primes dividing 3 now. We need to combine the b2
  #values to get a single residue class for b2 mod 3

  b2list = [d[2] for d in dat]
  P3list = [P^valuation(OK3, P) for P in Plist3]
  b2 = mod(crt(b2list ,P3list), OK3)

  #Check all primes dividing 2 and get a value of a1 for each of them. Then use
  #crt to combine them into a single a1 mod 2. Then use these to obtain local a3
  #and combine those to get global a1, a3

  OK2 = 2*OK
  Plist2 = prime_ideals_over(OK, 2)
  dat = [check_kraus_conditions_at_2(c4, c6, P) for P in Plist2]
  if !all(Bool[d[1] for d in dat])
    return false, EllipticCurve(OK.nf, [0, 0, 0, 0, 0], false)
  end

  #We are fine at all primes dividing 2 now. We need to combine the a1
  #values to get the residue class of a1 mod 2

  P2list = [P^valuation(OK2, P) for P in Plist2]
  a1list = [d[2] for d in dat]
  a1 = crt(a1list, P2list)

  #Needed  for when we combine with the primes above 3 to get a global transformation
  if !(a1 in OK3)
    a1 = 3*a1
  end

  dat = [check_kraus_conditions_at_2(c4, c6, P, a1) for P in Plist2]
  a3list = [d[3] for d in dat]
  a3 = crt(a3list, P2list)

  #We now combine the local transformations at 2 and 3 to find an
  #(r, s, t, u)- transformation from [0, 0, 0, -c4//48, -c6//864] to
  #a global integral model

  #This transformation needs to be of the form
  #(r, s, t, u) = (a1^2//12, a1//2, a3//2, 1) * (r2, 0, 0, 1) with 2-integral r2
  #(r, s, t, u) = (b2//12, 0, 0, 0) * (r3, s3, t3, 1) with 3-integral r3, s3, t3
  #Above we made sure that a1 = 0 mod(3). If this is the case then a solution is given by

  #r2 = (b2 - a1^2)//3,
  #r3 = (b2 - a1^2)//4
  #s3 = a1//2
  #t3 = (a1*r2 + a3)//2
  #
  #The condition a1 = 0 mod(3) ensures that t3 is 3-integral.

  s = a1//2
  r = b2//3 - s^2
  t = s*(b2 - a1^2)//3 +a3//2

  return transform_rstu(c4c6_model(c4, c6), [r, s, t, 1])[1]
end

function check_kraus_conditions_at_2(c4::NfOrdElem, c6::NfOrdElem, P::NfOrdIdl, a1::NfOrdElem)
  @req P.gen_one == 2 "Prime ideal needs to be above 2"
  OK = parent(c4)
  e = ramification_index(P)
  P2 = P^e

  c4v = valuation(c4, P)

  if c4v == 0
    return check_kraus_at_2_0(c4, c6, P, a1)
  end
  if c4v >= 4*e
    return check_kraus_at_2_gt4e(c4, c6, P, a1)
  end

  return check_kraus_at_2_remainder(c4, c6, P, [a1])
end

function check_kraus_conditions_at_2(c4::NfOrdElem, c6::NfOrdElem, P::NfOrdIdl)
  @req P.gen_one == 2 "Prime ideal needs to be above 2"
  OK = parent(c4)
  e = ramification_index(P)
  P2 = P^e
  c4v = valuation(c4, P)
  if c4v == 0
    test, t = sqrt_mod_4(-c6, P)
    if !test
      return false, zero(OK), zero(OK)
    end
    a1 = make_integral(c4//t, P, e)
    return check_kraus_at_2_0(c4, c6, P, a1)
  end

  if c4v >= 4*e
    a1 = zero(OK)
    return check_kraus_at_2_gt4e(c4, c6, P, a1)
  end

  G, phi = abelian_group(ResidueRing(OK, P2))
  as = [lift(phi(g)) for g in G]
  return check_kraus_at_2_remainder(c4, c6, P, as)

end

function check_kraus_at_2_0(c4, c6, P, a1)
  e = ramification_index(P)
  a13 = a1^3
  a3 = make_integral((c6 + a13^2)//(4*a13), P, 2*e)
  return true, a1, a3
end

function check_kraus_at_2_gt4e(c4, c6, P, a1)
  OK = parent(c4)
  test, a3 = sqrt_mod_4(divexact(c6, 8), P)
  if test
    return true, a1, a3
  else
    return false, zero(OK), zero(OK)
  end
end

function check_kraus_at_2_remainder(c4, c6, P, as)
  OK = parent(c4)
  e = ramification_index(P)
  for a1 in as
    Px = -a1^6 + 3*a1^2*c4 + 2*c6
    if valuation(Px, P) >= 4*e
      test, a3 = sqrt_mod_4(divexact(Px, 16), P)
      if test
        a1sq = a1^2
        if valuation(4*a1sq*Px - (a1sq^2 - c4)^2, P) >= 8*e
          return true, a1, a3
        end
      end
    end
  end
  return false, zero(OK), zero(OK)
end

function check_kraus_conditions_at_3(c4::NfOrdElem, c6::NfOrdElem, P::NfOrdIdl)
  @req P.gen_one == 3 "Prime ideal needs to be above 3"
  OK = ring_of_integers(parent(c4))
  e = ramification_index(P)
  P3 = P^e

  if valuation(c4, P) == 0
    b2 = mod(invmod(-c6*c4, P), P)
    return true, b2
  end

  if valuation(c6, P) >= 3*e
    b2 = zero(OK)
    return true, b2
  end

  G, phi = abelian_group(ResidueRing(OK, P3))
  for g in G
    x = lift(phi(g))
    if valuation(x*c4 + c6, P) >= e
      if valuation(x*(x^2 - 3*c4) - 2*c6, P) >= 3*e
        return true, x
      end
    end
  end
  return false, zero(OK)
end

@doc Markdown.doc"""
    minimal_discriminant(E::EllCrv{fmpq}) -> fmpq

Return the minimal discriminant ideal D_min of E. If E has a global minimal model
this is equal to the ideal generated by discriminant(E_min).
"""
function minimal_discriminant(E::EllCrv{fmpq})
  P = bad_primes(E)
  v = Int[valuation(discriminant(tates_algorithm_local(E, p)[1]),p) for p in P]
  I = prod([P[i]^(v[i]) for i in (1:length(P))]; init = one(fmpq))
end

@doc Markdown.doc"""
    minimal_discriminant(E::EllCrv{nf_elem}) -> NfOrdIdl

Return the minimal discriminant ideal D_min of E. If E has a global minimal model
this is equal to the ideal generated by discriminant(E_min).
"""
function minimal_discriminant(E::EllCrv{nf_elem})
  K = base_field(E)
  OK = ring_of_integers(K)
  P = bad_primes(E)
  v = Int[valuation(discriminant(tates_algorithm_local(E, p)[1]),p) for p in P]
  I = prod([P[i]^(v[i]) for i in (1:length(P))]; init = 1*OK)
end

################################################################################
#
#  Making prettier models
#
################################################################################

function reduce_model(E::EllCrv{T}) where T
  @req is_integral_model(E) "E has to be an integral model."
  OK = ring_of_integers(base_field(E))
  a1, a2, a3, a4, a6 = map(OK, a_invars(E))
  s = mod(-a1, 2)
  r = mod(-a2 + s*a1 + s^2, 3)
  t = mod(-a3 - r*a1, 2)
  return transform_rstu(E, [r, s, t, one(OK)])[1]
end

#Reduce a model of a curve by rescaling with units
function rescale_curve(E::EllCrv{T}) where T <: nf_elem
  K = base_field(E)
  r1, r2 = signature(K)
  if r1 + r2 == 1
    return E
  end

  OK = ring_of_integers(K)
  G, mG = unit_group_fac_elem(OK)
  us = map(mG, gens(G)[2:ngens(G)])
  prec = 500
  while true
    prec = 2 * prec
    C = ArbField(prec, cached = false)
    m = length(us)
    U = _conj_log_mat(us, prec)
    A = U * transpose(U)
    local Ainv
    try
      Ainv = inv(A)
    catch e
      if !(e isa ErrorException && e.msg == "Matrix cannot be inverted numerically")
        continue
      else
        rethrow(e)
      end
    end

    c4, c6 =c_invars(E)
    c4s = conjugates_arb(c4)
    c6s = conjugates_arb(c6)

    degs = [i <= r1 ? 1 : 2 for i in 1:ncols(U)]

    v = matrix(base_ring(U), ncols(U), 1, [log(abs(c4s[i])^(1//4) + abs(c6s[i])^(1//6))*degs[i] for i in 1:ncols(U)])
    w = -Ainv * U * v
    local es
    try
      es = round(fmpz_mat, w)
    catch e
      if !(e isa InexactError)
        continue
      else
        rethrow(e)
      end
    end
    u = evaluate(prod([us[i]^es[i] for i in 1:m]; init = one(K)))
    F = transform_rstu(E, [0, 0, 0, 1//u])[1]
    return F
  end
end

#Given an element a in a number field
#Return b integral such that b is congruent to a modulo P^e
function make_integral(a::nf_elem, P::NfOrdIdl, e::Int)
  Pe = P^e
  OK = order(P)
  G, phi = abelian_group(ResidueRing(OK, Pe))
  for g in G
    b = lift(phi(g))
    if valuation(a - b, P) >= e
      return b
    end
  end
  error("Cannot lift a to O_K mod P^e)")
end

function sqrt_mod_4(x::NfOrdElem, P::NfOrdIdl)
  e = ramification_index(P)
  P2 = P^e
  OK = parent(x)
  G, phi = abelian_group(ResidueRing(OK, P2))
  for g in G
    r = lift(phi(g))
    if valuation(r^2 - x, P) >= 2*e
      return true, r
    end
  end
  return false, zero(OK)
end

