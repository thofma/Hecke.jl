################################################################################
#
#             EllCrv/QQ.jl : Minimal models and local information
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

export laska_kraus_connell, minimal_model, tates_algorithm_global, tates_algorithm_local, tidy_model,
       torsion_points, torsion_structure, torsion_bound, tamagawa_number, tamagawa_numbers,
       kodaira_symbol, kodaira_symbols, reduction_type, modp_reduction

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
#  Tates algorithm
#
################################################################################

# Tate's algorithm over number fields, see Cremona, p. 66, Silverman p. 366
@doc Markdown.doc"""
    tates_algorithm_local(E::EllCrv{nf_elem}, pIdeal:: NfOrdIdl) 
    -> EllipticCurve{nf_elem}, String, fmpz, fmpz, Bool

Returns a tuple $(\tilde E, K, m, f, c, s)$, where $\tilde E$ is a 
minimal model for $E$ at the prime ideal $p$, $K$ is the Kodaira symbol,
$f$ is the conductor valuation at $p$, $c$ is the local Tamagawa number 
at $p$ and s is false if and only if $E$ has non-split 
multiplicative reduction.
"""
function tates_algorithm_local(E::EllCrv{nf_elem},pIdeal:: NfOrdIdl)

  #Assumption: Coefficients of E are in DVR with maximal ideal pIdeal of K.

  #Check if we have generators
  p = pIdeal.gen_one
  uniformizer = pIdeal.gen_two
  R = ring_of_integers(base_field(E))

  a1, a2, a3, a4, a6 = map(R,(a_invars(E)))

  b2, b4, b6, b8 = map(R,(b_invars(E)))
  c4, c6 = map(R,(c_invars(E)))

  delta = discriminant(E)
  delta = numerator(delta)

  n = valuation(delta, pIdeal)

  # test for type I0
  if n == 0
    return (E, "I0", FlintZZ(0), FlintZZ(1), true)::Tuple{EllCrv{nf_elem}, String, fmpz, fmpz, Bool}
  end

  
  # Maybe smods?
  # change coordinates so that p | a3, a4, a6
  if p == 2
    if mod(b2, pIdeal) == 0
      r = pth_root_mod(a4, pIdeal)
      t = mod(r*(r*(r + a2) + a4) + a6, pIdeal)
    else
      temp = invmod(a1, pIdeal)
      r = temp*a3
      t = temp*(a4 + r^2)
    end

  elseif p == 3
    if mod(b2, pIdeal) == 0
      r = pth_root_mod(-b6, pIdeal)
    else
      r = -invmod(b2, pIdeal)*b4
    end

    t = a1*r + a3
  else
    if mod(c4, pIdeal) == 0
      r = - invmod(FlintZZ(12), p)*b2
    else
      r = - invmod(FlintZZ(12)*c4, pIdeal)*(c6 + b2 * c4)
    end
      t = - invmod(FlintZZ(2), p)* (a1*r + a3)
      r = mod(R(r), pIdeal)
      t = mod(R(t), pIdeal)
  end

  trans = transform_rstu(E, [r, 0, t, 1])
  E = trans[1]

  a1, a2, a3, a4, a6 = map(R,(a_invars(E)))
  b2, b4, b6, b8 = map(R,(b_invars(E)))
  c4, c6 = map(R,(c_invars(E)))
  
  split = true
  # test for types In, II, III, IV
  if mod(c4, pIdeal) != 0
    if quadroots(1, a1, -a2, pIdeal)
      cp = FlintZZ(n)
    elseif mod(n, 2) == 0
      cp = FlintZZ(2)
      split = false
    else
      cp = FlintZZ(1)
      split = false
    end

    Kp = "I$(n)"
    fp = FlintZZ(1)
    

    return (E, Kp, fp, cp, split)::Tuple{EllCrv{nf_elem}, String, fmpz, fmpz, Bool}
  end

  if mod(a6, pIdeal^2) != 0
    Kp = "II"
    fp = FlintZZ(n)
    cp = FlintZZ(1)
    return (E, Kp, fp, cp, true)::Tuple{EllCrv{nf_elem}, String, fmpz, fmpz, Bool}
  end

  if mod(b8, pIdeal^3) != 0
    Kp = "III"
    fp = FlintZZ(n-1)
    cp = FlintZZ(2)
    return (E, Kp, fp, cp, true)::Tuple{EllCrv{nf_elem}, String, fmpz, fmpz, Bool}
  end

  if mod(b6, pIdeal^3) != 0
    if quadroots(1, divexact(a3, uniformizer), divexact(-a6, uniformizer^2), pIdeal)
      cp = FlintZZ(3)
    else
      cp = FlintZZ(1)
    end
    Kp = "IV"
    fp = FlintZZ(n - 2)
    return (E, Kp, fp, cp, true)::Tuple{EllCrv{nf_elem}, String, fmpz, fmpz, Bool}
  end

  # change coordinates so that p | a1, a2; p^2 | a3, a4; p^3 | a6
  # Taking square roots ok?
  if p == 2
    s = pth_root_mod(a2, pIdeal)
    t = uniformizer * pth_root(divexact(a6, uniformizer^2), pIdeal)
  elseif p ==3
    s = a1
    t = a3
  else
    s = -a1 * invmod(FlintZZ(2), p)
    t = -a3 * invmod(FlintZZ(2), p)
  end

  trans = transform_rstu(E, [0, s, t, 1])
  E = trans[1]

  a1, a2, a3, a4, a6 = map(R,(a_invars(E)))

  # set up auxililary cubic T^3 + bT^2 + cT + d
  b = divexact(a2, uniformizer)
  c = divexact(a4, uniformizer^2)
  d = divexact(a6, uniformizer^3)
  w = 27*d^2 - b^2*c^2 + 4*b^3*d - 18*b*c*d + 4*c^3
  x = 3*c - b^2
  # test for distinct roots: type I0*
  if mod(w, pIdeal) != 0
    Kp = "I0*"
    fp = FlintZZ(n - 4)
    cp = 1 + nrootscubic(b, c, d, pIdeal)
    return (E, Kp, fp, cp, true)::Tuple{EllCrv{nf_elem}, String, fmpz, fmpz, Bool}

  # test for double root: type Im*
  elseif mod(x, pIdeal) != 0
    # change coordinates so that the double root is T = 0
    if p == 2
      r = pth_root_mod(c, pIdeal)
    elseif p == 3
      r = c*inv_mod(b, pIdeal)
    else
      r = (b*c - 9*d) * invmod(FlintZZ(2)*x, pIdeal)
    end

    r = uniformizer * mod(r, pIdeal)

    trans = transform_rstu(E, [r, 0, 0, 1])
    E = trans[1]

    a1, a2, a3, a4, a6 = map(numerator,(a_invars(E)))

    # make a3, a4, a6 repeatedly more divisible by p
    m = 1
    mx = uniformizer^2
    my = uniformizer^2
    cp = FlintZZ(0)
    while cp == 0
      xa2 = R(divexact(a2, uniformizer))
      xa3 = R(divexact(a3, my))
      xa4 = R(divexact(a4, uniformizer*mx))
      xa6 = R(divexact(a6, mx*my))
      if mod(xa3^2 + 4*xa6, pIdeal) !=  0
        if quadroots(1, xa3, -xa6, pIdeal)
          cp = FlintZZ(4)
        else
          cp = FlintZZ(2)
        end

      else
        if p == 2
          t = my * pth_root_mod(xa6, pIdeal)
        else
          t = my * mod(R(-xa3*invmod(FlintZZ(2), p)), pIdeal)
        end

        trans = transform_rstu(E, [0, 0, t, 1])
        E = trans[1]

        a1, a2, a3, a4, a6 = map(numerator,(a_invars(E)))

        my = my*uniformizer
        m = m + 1
        xa2 = R(divexact(a2, uniformizer))
        xa3 = R(divexact(a3, my))
        xa4 = R(divexact(a4, uniformizer*mx))
        xa6 = R(divexact(a6, mx*my))

        if mod(xa4^2 - 4*xa2*xa6, pIdeal) != 0
          if quadroots(xa2, xa4, xa6, pIdeal)
            cp = FlintZZ(4)
          else
            cp = FlintZZ(2)
          end

        else
          if p == 2
            r = mx * pth_root_mod(xa6*inv_mod(xa2), pIdeal)
          else
            r = mx * mod(-xa4 * invmod(2*xa2, pIdeal), pIdeal)
          end

          trans = transform_rstu(E, [r, 0, 0, 1])
          E = trans[1]

          a1, a2, a3, a4, a6 = map(numerator,(a_invars(E)))

          mx = mx*uniformizer
          m = m + 1
        end
      end
    end

    fp = n - m - 4
    Kp = "I$(m)*"

    return (E, Kp, FlintZZ(fp), FlintZZ(cp), true)::Tuple{EllCrv{nf_elem}, String, fmpz, fmpz, Bool}

  else
    # Triple root case: types II*, III*, IV* or non-minimal
    # change coordinates so that the triple root is T = 0
    if p == 2
      r = b
    elseif p == 3
      r = pth_root_mod(-d, 3)
    else
      r = -b * invmod(FlintZZ(3), p)
    end

    r = p * mod(r, pIdeal)

    trans = transform_rstu(E, [r, 0, 0, 1])
    E = trans[1]

    a1, a2, a3, a4, a6 = map(numerator,(a_invars(E)))
    
    x3 = divexact(a3, uniformizer^2)
    x6 = divexact(a6, uniformizer^4)

    # Test for type IV*
    if mod(x3^2 + 4* x6, pIdeal) != 0
      if quadroots(1, x3, -x6, pIdeal)
        cp = FlintZZ(3)
      else
        cp = FlintZZ(1)
      end
      Kp = "IV*"
      fp = FlintZZ(n - 6)

      return (E, Kp, fp, FlintZZ(cp), true)::Tuple{EllCrv{nf_elem}, String, fmpz, fmpz, bool}
    else
      if p == 2
        t = -uniformizer^2 * pth_root_mod(x6, pIdeal)
      else
        t = uniformizer^2 * mod(x3 * invmod(FlintZZ(2), p), pIdeal)
      end


      trans = transform_rstu(E, [0, 0, t, 1])
      E = trans[1]

      a1, a2, a3, a4, a6 = map(numerator,(a_invars(E)))

      # Test for types III*, II*
      if mod(a4, uniformizer^4) != 0
        Kp = "III*"
        fp = FlintZZ(n - 7)
        cp = FlintZZ(2)
        

        return (E, Kp, fp, FlintZZ(cp), true)::Tuple{EllCrv{nf_elem}, String, fmpz, fmpz, Bool}
      elseif mod(a6, uniformizer^6) != 0
        Kp = "II*"
        fp = FlintZZ(n - 8)
        cp = FlintZZ(1)

        return (E, Kp, fp, FlintZZ(cp))::Tuple{EllCrv{nf_elem}, String,  fmpz, fmpz, Bool}
      else
        E = transform_rstu(E, [0, 0, 0, uniformizer])[1]
        return tates_algorithm_local(E, pIdeal)::Tuple{EllCrv{nf_elem}, String, fmpz, fmpz, Bool}
      end
    end
  end
end

@doc Markdown.doc"""
    tates_algorithm_local(E::EllCrv{fmpq}, p:: Int) 
    -> EllipticCurve{fmpq}, String, fmpz, fmpz, Bool

Returns a tuple $(\tilde E, K, f, c, s)$, where $\tilde E$ is a 
minimal model for $E$ at the prime ideal $p$, $K$ is the Kodaira symbol,
$f$ is the conductor valuation at $p$, $c$ is the local Tamagawa number 
at $p$ and s is false if and only if $E$ has non-split 
multiplicative reduction.
"""
function tates_algorithm_local(E::EllCrv{fmpq}, p)

  p = FlintZZ(p)

  a1, a2, a3, a4, a6 = map(numerator,(a_invars(E)))

  b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

  delta = discriminant(E)
  delta = numerator(delta)

  n = valuation(delta, p)

  # test for type I0
  if n == 0
    return (E, "I0", FlintZZ(0), FlintZZ(1), true)::Tuple{EllCrv{fmpq}, String, fmpz, fmpz, Bool}
  end

  # change coordinates so that p | a3, a4, a6
  if p == 2
    if mod(b2, p) == 0
      r = smod(a4, p)
      t = smod(r*(1 + a2 + a4) + a6, p)
    else
      r = smod(a3, p)
      t = smod(r + a4, p)
    end

  elseif p == 3
    if mod(b2, p) == 0
      r = smod(-b6, p)
    else
      r = smod(-b2*b4, p)
    end

    t = smod(a1*r + a3, p)
  else
    if mod(c4, p) == 0
      r = - invmod(FlintZZ(12), p)*b2
    else
      r = - invmod(FlintZZ(12)*c4, p)*(c6 + b2*c4)
    end
      t = - invmod(FlintZZ(2), p)* (a1*r + a3)
      r = smod(r, p)
      t = smod(t, p)
  end

  trans = transform_rstu(E, [r, 0, t, 1])
  E = trans[1]

  a1, a2, a3, a4, a6 = map(numerator,(a_invars(E)))

  b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)


  split = true
  # test for types In, II, III, IV
  if mod(c4, p) != 0
    if quadroots(1, a1, -a2, p)
      cp = FlintZZ(n)
    elseif mod(n, 2) == 0
      cp = FlintZZ(2)
      split = false
    else
      cp = FlintZZ(1)
      split = false
    end

    Kp = "I$(n)"
    fp = FlintZZ(1)

    return (E, Kp, fp, cp, split)::Tuple{EllCrv{fmpq}, String, fmpz, fmpz, Bool}
  end

  if mod(a6, p^2) != 0
    Kp = "II"
    fp = FlintZZ(n)
    cp = FlintZZ(1)
    return (E, Kp, fp, cp, true)::Tuple{EllCrv{fmpq}, String, fmpz, fmpz, Bool}
  end

  if mod(b8, p^3) != 0
    Kp = "III"
    fp = FlintZZ(n-1)
    cp = FlintZZ(2)
    return (E, Kp, fp, cp, true)::Tuple{EllCrv{fmpq}, String, fmpz, fmpz, Bool}
  end

  if mod(b6, p^3) != 0
    if quadroots(1, divexact(a3, p), divexact(-a6, p^2), p)
      cp = FlintZZ(3)
    else
      cp = FlintZZ(1)
    end
    Kp = "IV"
    fp = n - 2
    return (E, Kp, FlintZZ(fp), cp, true)::Tuple{EllCrv{fmpq}, String, fmpz, fmpz, Bool}
  end

  # change coordinates so that p | a1, a2; p^2 | a3, a4; p^3 | a6
  if p == 2
    s = smod(a2, 2)
    t = 2 * smod(divexact(a6, 4), 2)
  else
    s = -a1 * invmod(FlintZZ(2), p)
    t = -a3 * invmod(FlintZZ(2), p)
  end

  trans = transform_rstu(E, fmpz[0, s, t, 1])
  E = trans[1]

  a1, a2, a3, a4, a6 = map(numerator,(a_invars(E)))

  b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

  # set up auxililary cubic T^3 + bT^2 + cT + d
  b = divexact(a2, p)
  c = divexact(a4, p^2)
  d = divexact(a6, p^3)
  w = 27*d^2 - b^2*c^2 + 4*b^3*d - 18*b*c*d + 4*c^3
  x = 3*c - b^2

  # test for distinct roots: type I0*
  if mod(w, p) != 0
    Kp = "I0*"
    fp = FlintZZ(n - 4)
    cp = 1 + nrootscubic(b, c, d, p)
    return (E, Kp, fp, FlintZZ(cp), true)::Tuple{EllCrv{fmpq}, String, fmpz, fmpz, Bool}

  # test for double root: type Im*
  elseif mod(x, p) != 0

    # change coordinates so that the double root is T = 0
    if p == 2
      r = c
    elseif p == 3
      r = b*c
    else
      r = (b*c - 9*d) * invmod(FlintZZ(2)*x, p)
    end

    r = p * smod(r, p)

    trans = transform_rstu(E, [r, 0, 0, 1])
    E = trans[1]

    a1, a2, a3, a4, a6 = map(numerator,(a_invars(E)))

    b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

    # make a3, a4, a6 repeatedly more divisible by p
    m = 1
    mx = p^2
    my = p^2
    cp = FlintZZ(0)

    while cp == 0
      xa2 = divexact(a2, p)
      xa3 = divexact(a3, my)
      xa4 = divexact(a4, p*mx)
      xa6 = divexact(a6, mx*my)

      if mod(xa3^2 + 4*xa6, p) !=  0
        if quadroots(1, xa3, -xa6, p)
          cp = FlintZZ(4)
        else
          cp = FlintZZ(2)
        end

      else
        if p == 2
          t = my * xa6
        else
          t = my * smod(-xa3*invmod(FlintZZ(2), p), p)
        end

        trans = transform_rstu(E, [0, 0, t, 1])
        E = trans[1]

        a1, a2, a3, a4, a6 = map(numerator,(a_invars(E)))

        b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

        my = my*p
        m = m + 1
        xa2 = divexact(a2, p)
        xa3 = divexact(a3, my)
        xa4 = divexact(a4, p*mx)
        xa6 = divexact(a6, mx*my)

        if mod(xa4^2 - 4*xa2*xa6, p) != 0
          if quadroots(xa2, xa4, xa6, p)
            cp = FlintZZ(4)
          else
            cp = FlintZZ(2)
          end

        else
          if p == 2
            r = mx * smod(xa6*xa2, 2)
          else
            r = mx * smod(-xa4 * invmod(2*xa2, p), p)
          end

          trans = transform_rstu(E, [r, 0, 0, 1])
          E = trans[1]

          a1, a2, a3, a4, a6 = map(numerator,(a_invars(E)))

          b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

          mx = mx*p
          m = m + 1
        end
      end
    end

    fp = n - m - 4
    Kp = "I$(m)*"

    return (E, Kp, FlintZZ(fp), FlintZZ(cp), true)::Tuple{EllCrv{fmpq}, String, fmpz, fmpz, Bool}

  else
    # Triple root case: types II*, III*, IV* or non-minimal
    # change coordinates so that the triple root is T = 0
    if p == 3
      rp = -d
    else
      rp = -b * invmod(FlintZZ(3), p)
    end

    r = p * smod(rp, p)

    trans = transform_rstu(E, [r, 0, 0, 1])
    E = trans[1]

    a1, a2, a3, a4, a6 = map(numerator,(a_invars(E)))

    b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

    x3 = divexact(a3, p^2)
    x6 = divexact(a6, p^4)

    # Test for type IV*
    if mod(x3^2 + 4* x6, p) != 0
      if quadroots(1, x3, -x6, p)
        cp = FlintZZ(3)
      else
        cp = FlintZZ(1)
      end
      Kp = "IV*"
      fp = FlintZZ(n - 6)

      return (E, Kp, fp, FlintZZ(cp), true)::Tuple{EllCrv{fmpq}, String, fmpz, fmpz, Bool}
    else
      if p == 2
        t = x6
      else
        t = x3 * invmod(FlintZZ(2), p)
      end

      t = -p^2 * smod(t, p)

      trans = transform_rstu(E, [0, 0, t, 1])
      E = trans[1]

      a1, a2, a3, a4, a6 = map(numerator,(a_invars(E)))

      b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

      # Test for types III*, II*
      if mod(a4, p^4) != 0
        Kp = "III*"
        fp = FlintZZ(n - 7)
        cp = FlintZZ(2)

        return (E, Kp, fp, FlintZZ(cp), true)::Tuple{EllCrv{fmpq}, String, fmpz, fmpz, Bool}
      elseif mod(a6, p^6) != 0
        Kp = "II*"
        fp = FlintZZ(n - 8)
        cp = FlintZZ(1)

        return (E, Kp, fp, FlintZZ(cp), true)::Tuple{EllCrv{fmpq}, String, fmpz, fmpz, Bool}
      else
        E = transform_rstu(E, [0, 0, 0, p])[1]
        return tates_algorithm_local(E, p)::Tuple{EllCrv{fmpq}, String, fmpz, fmpz, Bool}
      end
    end
  end
end


@doc Markdown.doc"""
    tates_algorithm_global(E::EllCrv{fmpq}) -> EllCrv{fmpq}

Return a global reduced minimal model for $E$ using Tate's algorithm.
"""
function tates_algorithm_global(E::EllCrv{fmpq})
  delta = abs(numerator(discriminant(E)))
  fac = factor(delta)

  p_list = [i[1] for i in fac]
  p_list = sort(p_list)

  output = []

  # apply tates algorithm successively for all primes dividing the discriminant
  for p in p_list
    E = tates_algorithm_local(E, p)[1]
  end

  # reduce coefficients (see tidy_model)
  E = tidy_model(E)

  return E::EllCrv{fmpq}
end

@doc Markdown.doc"""
    tamagawa number(E::EllCrv{fmpq}, p::Int) -> fmpz

Return the local Tamagawa number for E at p.
"""
function tamagawa_number(E::EllCrv{fmpq},p)
  return tates_algorithm_local(E,p)[4]
end

@doc Markdown.doc"""
    tamagawa numbers(E::EllCrv{fmpq}) -> Vector{(fmpz, fmpz)}

Return the sequence of Tamagawa numbers for $E$ at all the 
bad primes $p$ of $E$.
"""
function tamagawa_numbers(E::EllCrv{fmpq})
  badp = bad_primes(E)
  return [tamagawa_number(E,p) for p in badp]
end

@doc Markdown.doc"""
    kodaira_symbol(E::EllCrv{fmpq}, p::Int) -> String

Return the reduction type of E at p using a Kodaira symbol.
"""
function kodaira_symbol(E::EllCrv{fmpq},p)
  return tates_algorithm_local(E,p)[2]
end

@doc Markdown.doc"""
    kodaira_symbols(E::EllCrv{fmpq}, p::Int) -> Vector{(fmpz, String)}

Return the reduction types of E at all bad primes as a sequence of
Kodaira symbols
"""
function kodaira_symbols(E::EllCrv{fmpq})
  badp = bad_primes(E)
  return [kodaira_symbol(E,p) for p in badp]
end

@doc Markdown.doc"""
    tamagawa number(E::EllCrv{fmpq}, p::NfOrdIdl) -> fmpz

Return the local Tamagawa number for E at p.
"""
function tamagawa_number(E::EllCrv{nf_elem},p::NfOrdIdl)
  return tates_algorithm_local(E,p)[4]
end

@doc Markdown.doc"""
    tamagawa numbers(E::EllCrv{fmpq}) -> Vector{(NfOrdIdl, fmpz)}

Return the sequence of Tamagawa numbers for $E$ at all the bad 
prime ideals $p$ of $E$.
"""
function tamagawa_numbers(E::EllCrv{nf_elem})
  badp = bad_primes(E)
  return [tamagawa_number(E,p) for p in badp]
end

@doc Markdown.doc"""
    kodaira_symbol(E::EllCrv{nf_elem}, p::NfOrdIdl) 
      -> String

Return the reduction type of E at the prime ideal p using
a Kodaira symbol.
"""
function kodaira_symbol(E::EllCrv{nf_elem},p::NfOrdIdl)
  return tates_algorithm_local(E,p)[2]
end

@doc Markdown.doc"""
    kodaira_symbols(E::EllCrv{nf_elem}, p::NfOrdIdl) 
      -> Vector{(NfOrdIdl, String)}

Return the reduction types of E at all bad primes as a sequence of 
Kodaira symbols.
"""
function kodaira_symbols(E::EllCrv{nf_elem})
  badp = bad_primes(E)
  return [kodaira_symbol(E,p) for p in badp]
end

@doc Markdown.doc"""
    reduction_type(E::EllCrv{fmpq}, p::fmpz) -> String

Return the reduction type of E at p. It can either be good, additive,
split multiplicative or nonsplit mutiplicative.
"""
function reduction_type(E::EllCrv{fmpq}, p)
  Ep, Kp, f, c, split = tates_algorithm_local(E, p)
  
  if Kp=="I0"
    return "Good"
  end
  
  if match(r"(I)([0-9]*)", Kp).match == Kp
    if split
      return "Split multiplicative"
    else
      return "Nonsplit multiplicative"
    end
  end
 
 return "Additive"
  
end
  
@doc Markdown.doc"""
    reduction_type(E::EllCrv{nf_elem}, p::NfOrdIdl) -> String

Return the reduction type of E at the prime ideal p. 
It can either be good, additive, split multiplicative or 
nonsplit mutiplicative.
"""
function reduction_type(E::EllCrv{nf_elem}, p::NfOrdIdl)
  Ep, Kp, f, c, split = tates_algorithm_local(E, p)
  
  if Kp=="I0"
    return "Good"
  end
  
  if match(r"(I)([0-9]*)", Kp).match == Kp
    if split
      return "Split multiplicative"
    else
      return "Nonsplit multiplicative"
    end
  end
 
 return "Additive"
  
end
  
  

################################################################################
#
#  Minimal model(s)
#
################################################################################

@doc Markdown.doc"""
    minimal_model(E::EllCrv{fmpq}) -> EllCrv{fmpq}

Returns the reduced global minimal model of $E$.
"""
function minimal_model(E::EllCrv{fmpq})
  return tates_algorithm_global(E)
end

@doc Markdown.doc"""
    minimal_model(E::EllCrv{fmpq}, p::Int) -> EllCrv{fmpq}

Returns a model of $E$, which is minimal at $p$. It is assumed that $p$
is prime.
"""
function minimal_model(E::EllCrv{fmpq}, p::Int)
  Ep = tates_algorithm_local(E, p)
  return Ep
end

@doc Markdown.doc"""
    minimal_model(E::EllCrv{fmpq}, p::NfOrdIdl) -> EllCrv{fmpq}

Returns a model of $E$, which is minimal at $p$. It is assumed that $p$
is a prime ideal.
"""
function minimal_model(E::EllCrv{fmpq}, p::NfOrdIdl)
  Ep = tates_algorithm_local(E, p)
  return Ep
end


@doc Markdown.doc"""
    tidy_model(E::EllCrv{fmpz}) -> EllCrv{fmpz}

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
#  Conductor
#
################################################################################

@doc Markdown.doc"""
    conductor(E::EllCrv{fmpq}) -> fmpz

Return the conductor of $E$ over QQ.
"""
function conductor(E::EllCrv{fmpq})
  badp = bad_primes(E)

  result = 1
  for p in badp 
    result = result*(p^tates_algorithm_local(E,p)[3])
  end
  return result
end 

@doc Markdown.doc"""
    conductor(E::EllCrv{nf_elem}) -> Nf)rdIdl

Return conductor of $E$ over a number field as an ideal.
"""
function conductor(E::EllCrv{nf_elem})
  badp = bad_primes(E)

  result = 1
  for p in badp 
    result = result*(p^tates_algorithm_local(E,p)[3])
  end
  return result
end 

#Magma returns the primes that divide the minimal discriminant
@doc Markdown.doc"""
    bad_primes(E::EllCrv{fmpq}) -> Vector{fmpz}

Return a list of the primes that divide the discriminant of $E$.
"""
function bad_primes(E::EllCrv{fmpq})

  d = ZZ(discriminant(E))
  L = factor(d)
  return [p for (p,e) in L]
end

@doc Markdown.doc"""
    bad_primes(E::EllCrv{fmpq}) -> Vector{NfOrdIdl}

Return a list of prime ideals that divide the discriminant of $E$.
"""
function bad_primes(E::EllCrv{nf_elem})
  R = ring_of_integers(base_field(E))
  d = R(discriminant(E))
  L = factor(d*R)
  return [p for (p,e) in L]
end

################################################################################
#
#  Reduction
#
################################################################################

#Magma also returns reduction map
@doc Markdown.doc"""
    bad_primes(E::EllCrv{nf_elem}, p::NfOrdIdl) -> EllCrv

Return the reduction of $E$ modulo the prime ideal p if p has good reduction
"""
function modp_reduction(E::EllCrv{nf_elem}, p::NfOrdIdl)
  if !isprime(p)
    throw(DomainError(p,"p is not a prime ideal"))
  end
  
  if p in bad_primes(E)
    throw(DomainError(p,"E has bad reduction at p"))
  end
  
  K, phi = ResidueField(order(p),p)
  
  a1, a2, a3, a4, a6 = map(phi,map(order(p), a_invars(E))) 
  
  return EllipticCurve(K, [a1, a2, a3, a4, a6])
  
end

################################################################################
#
#  Integral invariants
#
################################################################################

# this needs to be rewritten
@doc Markdown.doc"""
    get_b_integral(E::EllCrv{fmpz}) -> Nemo.fmpz

Computes the invariants $b2$, $b4$, $b6$, $b8$ of an elliptic curve $E$ with integer coefficients.
"""
function get_b_integral(E)
  a1, a2, a3, a4, a6 = map(numerator,(a_invars(E)))

  b2 = a1^2 + 4*a2
  b4 = a1*a3 + 2*a4
  b6 = a3^2 + 4*a6
  b8 = a1^2*a6 - a1*a3*a4 + 4*a2*a6 + a2*a3^2 - a4^2

  return b2,b4,b6,b8
end

@doc Markdown.doc"""
    get_b_c_integral(E::EllCrv{fmpz}) -> Nemo.fmpz

Computes the invariants $b2$, $b4$, $b6$, $b8$, $c4$, $c6$ of an elliptic curve $E$ with integer coefficients.
"""
function get_b_c_integral(E)
    b2, b4, b6, b8 = get_b_integral(E)

    c4 = b2^2 - 24*b4
    c6 = -b2^3 + 36*b2*b4 - 216*b6

    return b2,b4,b6,b8,c4,c6
end
