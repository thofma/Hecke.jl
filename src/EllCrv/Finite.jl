################################################################################
#
#          EllCrv/Finite.jl : Elliptic curves over finite fields
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
#
################################################################################

export hasse_interval, order, order_via_bsgs, order_via_legendre,
       order_via_schoof, rand, elem_order_bsgs

################################################################################
#
#  Random point
#
################################################################################

Random.gentype(::Type{EllCrv{T}}) where {T} = EllCrvPt{T}

# only works for short form
@doc Markdown.doc"""
    rand(E::EllCrv) -> EllCrvPt
Returns a random point on the elliptic curve $E$ defined over a finite field.
It is assumed that $E$ is given in short form.
"""
function rand(rng::AbstractRNG, Esp::Random.SamplerTrivial{<:EllCrv})
  E = Esp[]
  R = base_field(E)

  if E.short == false
    error("does not work for long form")
  end

  while true
  # choose random x-coordinate and check if it is a square in F_q
  # if not, choose new x-coordinate
    x = rand(rng, R)
    square = x^3 + E.coeff[1]*x + E.coeff[2]

    a = issquare(square)
    if a[1] == true # square is a square in F_q, so have found point on the curve
      y = a[2]
      P = E([x, y])
      return P
    end
  end
end

################################################################################
#
# Order via Legendre symbol
#
################################################################################

# Th. 4.14
@doc Markdown.doc"""
    order_via_legendre(E::EllCrv{Generic.Res{fmpz}) -> fmpz

Calculates the number of points on an elliptic curve $E$ over a finite field
$\mathbf Z/p\mathbf Z$ using the Legendre symbol. It is assumed that $p$ is
prime.
"""
function order_via_legendre(E::EllCrv{T}) where {T <: Union{nmod, Generic.Res{fmpz}}}
  R = base_field(E)
  p = characteristic(R)
  q = order(R)
  grouporder = FlintZZ(0)

  p == 0 && error("Base field must be finite")

  if p != q
    error("Finite field must have degree 1")
  end

  if E.short == false
    E = short_weierstrass_model(E)[1]
  end

  x = FlintZZ(0)

  while x < p
    C = x^3 + (E.coeff[1])*x + (E.coeff[2])
    Cnew = C.data # convert to fmpz
    a = jacobi_symbol(Cnew, p) # can be used to compute (C/F_p) since p prime
    grouporder = grouporder + a
    x = x + 1
  end

  grouporder = grouporder + p + 1
  return grouporder
end

################################################################################
#
#  Hasse inverval
#
################################################################################

@doc Markdown.doc"""
    hasse_interval(E::EllCrv) -> Array{fmpz, 1}

Given an elliptic curve $E$ over a finite field $\mathbf F$, returns an array
`[l, b]` > of integers, such that $l \leq \#E(\mathbf F) \leq b$ using
Hasse's theorem.
"""
function hasse_interval(E::EllCrv)
  R = base_field(E)
  characteristic(R) == 0 && error("Base field must be finite")
  q = order(R)
  s = isqrtrem(q)[1] # sqrt(q) rounded down

  l = q + 1 - 2*(s + 1)
  b = q + 1 + 2*(s + 1)

  return [l, b]
end

# section 4.3.4
@doc Markdown.doc"""
    elem_order_bsgs(P::EllCrvPt) -> fmpz

Calculates the order of a point $P$ on an elliptic curve given over a finite
field using BSGS.
"""
function elem_order_bsgs(P::EllCrvPt)
  R = base_field(P.parent)
  p = characteristic(R)
  p == 0 && error("Base field must be finite")
  q = order(R) # R = F_q

  # step 1
  Q = Int(q + 1) * P

  # step 2
  m = Int( ceil(Int(q)^(1//4)) )

  list_points = []
  for j = 0:m
    S = j*P
    push!(list_points, S)
  end

  # step 3
  k = -m
  H = (2*m)*P
  M = FlintZZ(0) # initialize M, so that it is known after the while loop

  while k < m + 1
    Snew = Q + (k*H)

    i = 1
    while i < m + 2 # is there a match?
      if Snew == list_points[i]
        M = q + 1 + (2*m*k) - (i-1)

        if M != 0
          i = m + 2 # leave both while loops
          k = m + 1
        else
          i = i + 1 # search on if M == 0
        end

      elseif Snew == -(list_points[i])
        M = q + 1 + (2*m*k) + (i-1) # step 4

        if M != 0
          i = m + 2 # leave both while loops
          k = m + 1
        else
          i = i + 1 # search on if M == 0
        end
      else
        i = i + 1
      end
    end

    k = k + 1
  end

  # step 5
  gotostep5 = true
  while gotostep5
    fac = factor(M)
    primefactors = []
    for i in fac
      push!(primefactors, i[1])
    end
    r = length(primefactors)

    # step 6
    i = 1
    while i < (r + 1)
      T = Int(divexact(M, primefactors[i]))*P
      if T.isinfinite == true
        M = divexact(M, primefactors[i])
        i = r + 2  # leave while-loop
      else
        i = i + 1
      end
    end

    if i == r + 1  # then (M/p_i)P != oo for all i
      gotostep5 = false
    end
  end

  return M
end

@doc Markdown.doc"""
    order(P::EllCrvPt) -> fmpz

Given a point on an elliptic curve over a finite field, returns the order
of this point.
"""
order(P::EllCrvPt) = elem_order_bsgs(P)

################################################################################
#
#  Order via BSGS
#
################################################################################

@doc Markdown.doc"""
    order_via_bsgs(E::EllCrv) -> Array{fmpz, 1}

Calculates candidates for the number of points on an elliptic curve $E$ given
over a finite field $\mathbf F_q$, using the baby step giant step method. If
$q$ prime, $q > 229$, then the order is determined uniquely by this algorithm.
It is assumed that the characteristic is not 2.
"""
function order_via_bsgs(E::EllCrv)
  R = base_field(E)
  p = characteristic(R)
  p == 0 && error("Base field must be finite")

  q = order(R)

  if (p == 2)
    error("Characteristic must not be 2")
  end

  if E.short == false
    E = short_weierstrass_model(E)[1]
  end

  Nposs = FlintZZ(1)
  h = hasse_interval(E)
  l = h[1]
  b = h[2]

  counter = 0
  runwhile = true

  # if Nposs is greater than interval length, there is only one multiple of
  # Nposs in the interval, so stop
  # Also, if lcm does not change in 10(?) consecutive loops, leave while loop
  while (Nposs <= (b-l)) && (runwhile == true)

    P = rand(E)
    ord = elem_order_bsgs(P)

    if lcm(ord, Nposs) == Nposs
      counter = counter + 1
    else
      Nposs = lcm(ord, Nposs)
      counter = 0
    end

    if counter > 10 # maybe take another criterion
      runwhile = false
    end

  end

  if runwhile == false # could not determine group order uniquely
    candidates = fmpz[]
    Ncand = divrem(l, Nposs)[1]*Nposs
    if Ncand != 0
      push!(candidates, Ncand)
    end

    Ncand = Ncand + Nposs

    while Ncand < b # compute all possible group orders using Hasse's theorem
      push!(candidates, Ncand)
      Ncand = Ncand + Nposs
    end

    output = candidates

  else # group order is determined
    N = (divrem(l+1, Nposs)[1] + 1) * Nposs
    output = [N]
  end

  if (p == q) && (p > 229) && (length(output) != 1)
  # group order is uniquely determined, but by quadratic twist

    d = R(0)
    boolie = true
    while boolie # get a quadratic non-residue mod p
      d = rand(R)
      if issquare(d)[1] == false
        boolie = false
      end
    end

    Eprime = EllipticCurve([E.coeff[1]*d^2, E.coeff[2]*d^3]) # quadratic twist
    bb = order_via_bsgs(Eprime)[1]
    output = [2*p + 2 - bb]
  end

  return output
end

################################################################################
#
#  Schoof's algorithm
#
################################################################################

function fn_from_schoof(E::EllCrv, n::Int, x)

  R = base_field(E)
  S, y = PolynomialRing(parent(x),"y")

  f = psi_poly_field(E, n, x, y)

 # println("f: $f, $(degree(f))")

  g = x^3 + E.coeff[1]*x + E.coeff[2]

  if isodd(n)
    return replace_all_squares(f, g)
  else
    return replace_all_squares(divexact(f, y), g)
  end
end

@doc Markdown.doc"""
    order_via_schoof(E::EllCrv) -> fmpz

Given an elliptic curve $E$ over a finite field $\mathbf F$,
this function computes the order of $E(\mathbf F)$ using Schoof's algorithm
The characteristic must not be $2$ or $3$.
"""
function order_via_schoof(E::EllCrv)
  R = base_field(E)
  q = order(R)
  p = characteristic(R)

  if (p == 2) || (p == 3) || (p == 0)
    error("Characteristic must not be 2 or 3 or 0")
  end

  if E.short == false
    E = short_weierstrass_model(E)[1]
  end

  # step 1: get suitable set S of prime numbers
  sqrt_q = isqrtrem(q)[1]
  S = prime_set(4*(sqrt_q + 1), p)

  L = length(S)
  product = 1

  # step 2: compute t (mod l) for every l in S
  t_mod_l = []
  for i = 1:L
    a = S[i]
    push!(t_mod_l, t_mod_prime(S[i], E))
    product = product * S[i]
  end

  # step 3: use chinese remainder theorem to get value of t
  t = 0
  for i = 1:L
    n_i = div(product, S[i])
    B = ResidueRing(FlintZZ, S[i], cached = false)
    M_i = inv(B(n_i))
    M_i = M_i.data
    t = t + (M_i * n_i * t_mod_l[i])
  end

  t = mod(t, product)
  if t > product//2
    t = t - product
  end

  return (q + 1 - t)::fmpz
end

#prime_set(M::Nemo.fmpz, char::Nemo.fmpz) -> Array{Nemo.fmpz}
#  returns a set S of primes with:
# 1) char not contained in S
# 2) product of elements in S is greater than M
function prime_set(M, char)
  S = Nemo.fmpz[]

  p = 1
  product = 1

  while product < M
    p = next_prime(p)

    if p != char
      push!(S,p)
      product = product * p
    end
  end

  return S
end

# t_mod_prime(l::Nemo.fmpz, E::EllCrv) -> Nemo.fmpz
# determines the value of t modulo some prime l (used in Schoof's algorithm)
function t_mod_prime(l, E)
  R = base_field(E)
  q = order(R)
  q_int = Int(q)
  l = Int(l)

  S, x = PolynomialRing(R, "x")
  T, y = PolynomialRing(S, "y")
  Z = GF(l, cached = false)

  f = x^3 + E.coeff[1]*x + E.coeff[2]
  fl = fn_from_schoof(E, l, x)
  U = ResidueRing(S, fl)

  PsiPoly = [] # list of psi-polynomials
  for i = -1:(l + 1)
    push!(PsiPoly, psi_poly_field(E,i,x,y)) # Psi[n] is now found in PsiPoly[n+2]
  end

  Fnschoof = [] # list of the fn- functions # Psi[n] is now found in PsiPoly[n+2]
  for i = -1:(l + 1)
    push!(Fnschoof, fn_from_schoof(E,i,x))
  end

  # case where l == 2. value of t mod l determined by some gcd, see p. 124
  if l == 2
    x_q = powmod(x, q_int, f)
    ggt = gcd(f, x_q - x)
    if ggt == 1
      t = FlintZZ(1)
    else
      t = FlintZZ(0)
    end

    return t
  end

  # case where l != 2
  k = Int(mod(q, l)) # reduce q mod l
  k_mod = Z(k)

  fk = Fnschoof[k+2]
  fkme = Fnschoof[k+1]
  fkpe = Fnschoof[k+3]
  fkpz = Fnschoof[k+4]

  # is there a nonzero P = (x,y) in E[l] with phi^2(P) == +-kP ?
  if mod(k,2) == 0
    g = U( (powmod(x, q_int^2, fl) - x) * fk^2 * f + fkme * fkpe).data
    ggT = gcd(g, fl)
  else
    g = U( (powmod(x, q_int^2, fl) - x) * fk^2 + fkme * fkpe * f).data
    ggT = gcd(g, fl)
  end

  if ggT != 1 # case 1
    if jacobi_symbol(FlintZZ(k), FlintZZ(l)) == -1
      return FlintZZ(0)
    else
      # need square root of q (mod l)
      w = issquare(k_mod)[2]
      if w.data < 0
        w = w + l
      end
      w_int = Int(w.data)

      fw = Fnschoof[w_int+2]
      fwme = Fnschoof[w_int+1]
      fwpe = Fnschoof[w_int+3]

      if mod(w_int, 2) == 0
        g = U((powmod(x,q_int,fl) - x) * fw^2*f + fwme*fwpe).data # reduce mod fl
        ggT = gcd(g, fl)
      else
        g = U((powmod(x,q_int,fl) - x) * fw^2 + fwme*fwpe*f).data
        ggT = gcd(g, fl)
      end

      if ggT == 1
        return FlintZZ(0)
      else
        fwmz = Fnschoof[w_int]
        fwpz = Fnschoof[w_int+4]

        if mod(w_int, 2) == 0
          g = U(4 * powmod(f,div(q_int + 3, 2),fl)*fw^3 - (fwpz * fwme^2) + (fwmz*fwpe^2)).data
          ggT2 = gcd(g, fl)
        else
          g = U(4 * powmod(f,div(q_int - 1, 2),fl)*fw^3 - (fwpz * fwme^2) + (fwmz*fwpe^2)).data
          ggT2 = gcd(g, fl)
        end

        if ggT2 == 1
          return -2*fmpz(w.data)
        else
          return 2*fmpz(w.data)
        end
      end
    end
  else # case 2
    Fkmz = PsiPoly[k]
    Fkme = PsiPoly[k+1]
    Fk = PsiPoly[k+2]
    Fkpe = PsiPoly[k+3]
    Fkpz = PsiPoly[k+4]

    alpha = Fkpz*psi_power_mod_poly(k-1,E,x,y,2,fl) - Fkmz*psi_power_mod_poly(k+1,E,x,y,2,fl) - 4*powmod(f,div(q_int^2+1,2),fl)*psi_power_mod_poly(k,E,x,y,3,fl)
    beta = ((x - powmod(x, (q_int^2), fl))*psi_power_mod_poly(k,E,x,y,2,fl)- Fkme*Fkpe)*4*y*Fk

    tau = 1
    while tau < l

      ftaumz = PsiPoly[tau]
      ftaume = PsiPoly[tau+1]
      ftau = PsiPoly[tau+2]
      ftaupe = PsiPoly[tau+3]
      ftaupz = PsiPoly[tau+4]

      fntaumz = Fnschoof[tau]
      fntaume = Fnschoof[tau+1]
      fntaupe = Fnschoof[tau+3]
      fntaupz = Fnschoof[tau+4]

      gammahelp = powmod(fntaupz*fntaume^2- fntaumz * fntaupe^2,q_int,fl)

      if mod(tau, 2) == 0
        gamma = y * powmod(f,div(q_int-1,2),fl) * gammahelp
      else
        gamma = powmod(f,q_int,fl) * gammahelp
      end

      monster1 = ((Fkme*Fkpe - psi_power_mod_poly(k,E,x,y,2,fl)*(powmod(x, q_int^2, fl) + powmod(x, q_int, fl) + x)) * beta^2 + psi_power_mod_poly(k,E,x,y,2,fl)*alpha^2) * psi_power_mod_poly(tau,E,x,y,2*q_int,fl) + psi_power_mod_poly(tau-1, E, x,y,q_int,fl)*psi_power_mod_poly(tau+1, E, x,y,q_int, fl)*beta^2*psi_power_mod_poly(k,E,x,y,2,fl)

      if divrem(degree(monster1), 2)[2] == 1
        monster1 = divexact(monster1, y)
      end

      monster1_1 = replace_all_squares_modulo(monster1, f, fl)
      monster1_2 = U(monster1_1).data # monster1_1 reduced

      if monster1_2 != 0
        tau = tau + 1
      else
        monster2 = 4*y*powmod(f,div(q_int-1,2),fl)*psi_power_mod_poly(tau,E,x,y,3*q_int,fl) * (alpha * (((2*powmod(x, q_int^2, fl) + x) * psi_power_mod_poly(k,E,x,y,2,fl) - Fkme*Fkpe )*beta^2 - alpha^2*psi_power_mod_poly(k,E,x,y,2,fl)) - y*powmod(f,div(q_int^2-1,2),fl)*beta^3 * Fk^2) - beta^3*psi_power_mod_poly(k,E,x,y,2,fl)*gamma

        if divrem(degree(monster2), 2)[2] == 1
          monster2 = divexact(monster2, y)
        end

        monster2_1 = replace_all_squares_modulo(monster2, f,fl)
        monster2_2 = U(monster2_1).data # monster2_1 mod fl

        if monster2_2 != 0
          tau = tau + 1
        else
          return tau
        end
      end
    end
  end
end

# computes psi_n^power mod g
function psi_power_mod_poly(n, E, x, y, power, g)

    fn = fn_from_schoof(E, n, x)
    f = x^3 + E.coeff[1]*x + E.coeff[2]
    p = powmod(fn,power,g)

    if mod(n, 2) == 0
        if mod(power, 2) == 0
            p1 = powmod(f, div(power, 2), g)
        else
            p1 = powmod(f, div(power - 1, 2), g) * y
        end
    else p1 = 1
    end

    return p * p1
end

#special_order2(E::EllCrv{NemoResidue}) -> Nemo.fmpz
#> counts points on an elliptic curve E given over F_2
function _special_order2(E)
  R = base_field(E) # should be Z/2Z
  ord = FlintZZ(1)

  for i = 0:1
    for j = 0:1
      if ison_curve(E, [R(i), R(j)])
        ord = ord + 1
      end
    end
  end

  return ord
end


#special_order3(E::EllCrv{NemoResidue}) -> Nemo.fmpz
# counts points on an elliptic curve E given over F_3
function _special_order3(E)
  R = base_field(E) # should be Z/3Z
  ord = FlintZZ(1)

  for i = 0:2
    for j = 0:2
      if ison_curve(E, [R(i), R(j)])
        ord = ord + 1
      end
    end
  end

  return ord
end

################################################################################
#
#  Point counting
#
################################################################################

@doc Markdown.doc"""
    order(E::EllCrv{NemoResidue}) -> Nemo.fmpz

Given an elliptic curve $E$ over a finite field $\mathbf F$, computes
$\#E(\mathbf F)$.
"""
function order(E::EllCrv)
  R = base_field(E)
  p = characteristic(R)
  q = order(R)

  p == 0 && error("Characteristic must be nonzero")

  # char 2
  if p == 2
    if q > 2
      error("Don't have algorithm for char = 2 and not F_2") # legendre is the only algorithm that can deal with char = 2, but q must be equal to p
    else
      return _special_order2(E)
    end
  end

  # char 3
  if p == 3
    if q > 3
      error("Don't have algorithm for char = 3 and not F_3")
    else
      return _special_order3(E)
    end
  end

  A = order_via_bsgs(E)
  if length(A) == 1
    return A[1]
  end
  return order_via_schoof(E) # bsgs may only return candidate list
end
