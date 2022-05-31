################################################################################
#
#             EllCrv/LocalData.jl : Computing local data for elliptic curves
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

export tates_algorithm_global, tates_algorithm_local, tidy_model,
       tamagawa_number, tamagawa_numbers, kodaira_symbol, kodaira_symbols, 
       reduction_type, modp_reduction, bad_primes, KodairaSymbol
       
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
  K = base_field(E)
  a1, a2, a3, a4, a6 = a_invars(E)

  b2, b4, b6, b8 = b_invars(E)
  c4, c6 = c_invars(E)

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
      t = pth_root_mod(r*(r*(r + a2) + a4) + a6, pIdeal)
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
      r = mod(r, pIdeal)
      t = mod(t, pIdeal)
  end

  trans = transform_rstu(E, [r, 0, t, 1])
  E = trans[1]

  a1, a2, a3, a4, a6 = a_invars(E)
  b2, b4, b6, b8 = b_invars(E)
  c4, c6 = c_invars(E)

  split = true
  # test for types In, II, III, IV
  if mod(c4, pIdeal) != 0
    if quadroots(one(K), a1//1, -a2//1, pIdeal)
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
  if a6!= 0 && valuation(a6, pIdeal) < 2
    Kp = "II"
    fp = FlintZZ(n)
    cp = FlintZZ(1)
    return (E, Kp, fp, cp, true)::Tuple{EllCrv{nf_elem}, String, fmpz, fmpz, Bool}
  end

  if b8!= 0 && valuation(b8, pIdeal) < 3
    Kp = "III"
    fp = FlintZZ(n-1)
    cp = FlintZZ(2)
    return (E, Kp, fp, cp, true)::Tuple{EllCrv{nf_elem}, String, fmpz, fmpz, Bool}
  end

  if b6!= 0 && valuation(b6, pIdeal) < 3
    if quadroots(one(K), a3//uniformizer, -a6//uniformizer^2, pIdeal)
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
    t = uniformizer * pth_root_mod(a6//uniformizer^2, pIdeal)
  elseif p ==3
    s = a1
    t = a3
  else
    s = -a1 * invmod(FlintZZ(2), p)
    t = -a3 * invmod(FlintZZ(2), p)
  end

  trans = transform_rstu(E, [0, s, t, 1])
  E = trans[1]

  a1, a2, a3, a4, a6 = a_invars(E)

  # set up auxililary cubic T^3 + bT^2 + cT + d
  b = mod(a2//uniformizer, pIdeal)
  c = mod(a4//uniformizer^2, pIdeal)
  d = mod(a6//uniformizer^3, pIdeal)
  w = 27*d^2 - b^2*c^2 + 4*b^3*d - 18*b*c*d + 4*c^3
  x = 3*c - b^2
  # test for distinct roots: type I0*
  if mod(w, pIdeal) != 0
    Kp = "I0*"
    fp = FlintZZ(n - 4)
    cp = 1 + nrootscubic(b//1, c//1, d//1, pIdeal)
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

    a1, a2, a3, a4, a6 = a_invars(E)

    # make a3, a4, a6 repeatedly more divisible by p
    m = 1
    mx = uniformizer^2
    my = uniformizer^2
    cp = FlintZZ(0)
    while cp == 0
      xa2 = mod(a2//uniformizer, pIdeal)
      xa3 = mod(a3//my, pIdeal)
      xa4 = mod(a4//(uniformizer*mx), pIdeal)
      xa6 = mod(a6//(mx*my), pIdeal)
      if mod(xa3^2 + 4*xa6, pIdeal) !=  0
        if quadroots(one(K), xa3//1, -xa6//1, pIdeal)
          cp = FlintZZ(4)
        else
          cp = FlintZZ(2)
        end

      else
        if p == 2
          t = my * pth_root_mod(xa6, pIdeal)
        else
          t = my * mod(-xa3*invmod(FlintZZ(2), p), pIdeal)
        end

        trans = transform_rstu(E, [0, 0, t, 1])
        E = trans[1]

        a1, a2, a3, a4, a6 = map(numerator,(a_invars(E)))

        my = my*uniformizer
        m = m + 1
        xa2 = mod(a2//uniformizer, pIdeal)
        xa3 = mod(a3//my, pIdeal)
        xa4 = mod(a4//(uniformizer*mx), pIdeal)
        xa6 = mod(a6//(mx*my), pIdeal)

        if mod(xa4^2 - 4*xa2*xa6, pIdeal) != 0
          if quadroots(xa2//1, xa4//1, xa6//1, pIdeal)
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

          a1, a2, a3, a4, a6 = a_invars(E)

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
      r = pth_root_mod(-d, pIdeal)
    else
      r = -b * invmod(FlintZZ(3), p)
    end

    r = uniformizer * mod(r, pIdeal)

    trans = transform_rstu(E, [r, 0, 0, 1])
    E = trans[1]

    a1, a2, a3, a4, a6 = map(numerator,(a_invars(E)))

    x3 = a3//uniformizer^2
    x6 = a6//uniformizer^4

    # Test for type IV*
    if mod(x3^2 + 4*x6, pIdeal) != 0
      if quadroots(one(K), x3//1, -x6//1, pIdeal)
        cp = FlintZZ(3)
      else
        cp = FlintZZ(1)
      end
      Kp = "IV*"
      fp = FlintZZ(n - 6)

      return (E, Kp, fp, FlintZZ(cp), true)::Tuple{EllCrv{nf_elem}, String, fmpz, fmpz, Bool}
    else
      if p == 2
        t = -uniformizer^2 * pth_root_mod(x6, pIdeal)
      else
        t = uniformizer^2 * mod(-x3 * invmod(FlintZZ(2), p), pIdeal)
      end

      trans = transform_rstu(E, [0, 0, t, 1])
      E = trans[1]

      a1, a2, a3, a4, a6 = a_invars(E)

      # Test for types III*, II*
      if a4!=0 && valuation(a4, pIdeal) < 4
        Kp = "III*"
        fp = FlintZZ(n - 7)
        cp = FlintZZ(2)
        return (E, Kp, fp, FlintZZ(cp), true)::Tuple{EllCrv{nf_elem}, String, fmpz, fmpz, Bool}

      elseif a6!= 0 && valuation(a6, pIdeal) < 6
        Kp = "II*"
        fp = FlintZZ(n - 8)
        cp = FlintZZ(1)

        return (E, Kp, fp, FlintZZ(cp), true)::Tuple{EllCrv{nf_elem}, String,  fmpz, fmpz, Bool}
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



struct KodairaSymbol
  ksymbol::Int
  
  function KodairaSymbol(n::Int)
    K = new(n)
    return K
  end
  
  function KodairaSymbol(K::String)
    if K=="I0"
      return KodairaSymbol(1)
    elseif K=="I0*"
      return KodairaSymbol(-1)
    elseif K=="II"
      return KodairaSymbol(2)
    elseif K=="II*"
      return KodairaSymbol(-2)
    elseif K=="III"
      return KodairaSymbol(3)
    elseif K=="III*"
      return KodairaSymbol(-3)
    elseif K=="IV"
      return KodairaSymbol(4)
    elseif K=="IV*"
      return KodairaSymbol(-4)
    end
    
    n = lastindex(K)
    
    if K[n]=='*'
      return KodairaSymbol(-4 - parse(Int, K[2:n-1]))
    else
      return KodairaSymbol(4 + parse(Int, K[2:n]))
    end  
  end
  
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
    conductor(E::EllCrv{nf_elem}) -> NfOrdIdl

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
  return sort([p for (p,e) in L])
end

@doc Markdown.doc"""
    bad_primes(E::EllCrv{fmpq}) -> Vector{NfOrdIdl}

Return a list of prime ideals that divide the discriminant of $E$.
"""
function bad_primes(E::EllCrv{nf_elem})
  OK = ring_of_integers(base_field(E))
  d = OK(discriminant(E))
  L = factor(d*OK)
  return [p for (p,e) in L]
end

################################################################################
#
#  Reduction
#
################################################################################

#Magma also returns reduction map
@doc Markdown.doc"""
    modp_reduction(E::EllCrv{nf_elem}, p::NfOrdIdl) -> EllCrv

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


