################################################################################
#
#             EllipticCurve/LocalData.jl : Computing local data for elliptic curves
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
#  Tates algorithm
#
################################################################################

# Tate's algorithm over number fields, see Cremona, p. 66, Silverman p. 366
@doc raw"""
    tates_algorithm_local(E::EllipticCurve{AbsSimpleNumFieldElem}, p:: AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
    -> EllipticCurve{AbsSimpleNumFieldElem}, String, ZZRingElem, ZZRingElem, Bool

Returns a tuple $(\tilde E, K, m, f, c, s)$, where $\tilde E$ is a minimal
model for $E$ at the prime ideal $p$, $K$ is the Kodaira symbol, $f$ is the
conductor valuation at $p$, $c$ is the local Tamagawa number at $p$ and `s` is
false if and only if $E$ has non-split multiplicative reduction.
"""
function tates_algorithm_local(E, P)
  return _tates_algorithm(E, P)
end

# internal version
# extend this for global fields

function _tates_algorithm(E::EllipticCurve{AbsSimpleNumFieldElem}, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  OK = order(P)
  F, _mF = residue_field(OK, P)
  mF = extend(_mF, nf(OK))
  _val(x) = iszero(x) ? inf : valuation(x, P)
  _lift(y) = mF\y
  _red(x) = mF(x)
  _redmod(x) = mF\(mF(x))
  _invmod(x) = mF\(inv(mF(x)))
  pi = uniformizer(P)
  return __tates_algorithm_generic(E, OK, _val, _redmod, _red, _lift, _invmod, pi)
end

function _tates_algorithm(E::EllipticCurve{<:AbstractAlgebra.Generic.RationalFunctionFieldElem}, ::typeof(degree))
  K = base_field(E)
  R = base_ring(K.fraction_field)
  Kl = localization(K, degree)
  F, _mF = residue_field(Kl, Kl(1//gen(K)))
  mF = x -> _mF(Kl(x))
  _val = x -> iszero(x) ? inf : degree(denominator(x)) - degree(numerator(x))
  _res = mF
  _mod = x -> K(preimage(_mF, (_res(x))))
  _invmod = x -> K(preimage(_mF, inv(_res(x))))
  _uni = 1//gen(K)
  _lift = x -> K(preimage(_mF, x))
  return __tates_algorithm_generic(E, R, _val, _mod, _res, _lift, _invmod, _uni)
end

function _tates_algorithm(E::EllipticCurve{<:AbstractAlgebra.Generic.RationalFunctionFieldElem}, f::PolyRingElem)
  @req is_irreducible(f) "Polynomial must be irreducible"
  R = parent(f)
  K = base_field(E)
  @assert R === base_ring(K.fraction_field)
  F, _mF = residue_field(R, f)
  mF = x -> _mF(numerator(x))/_mF(denominator(x))
  _val = x -> iszero(x) ? inf : valuation(numerator(x), f) - valuation(denominator(x), f)
  _res = mF
  _mod = x -> K(preimage(_mF, (_res(x))))
  _invmod = x -> K(preimage(_mF, inv(_res(x))))
  _uni = K(f)
  _lift = x -> K(preimage(_mF, x))
  return __tates_algorithm_generic(E, R, _val, _mod, _res, _lift, _invmod, _uni)
end

function _tates_algorithm(E::EllipticCurve{<:AbstractAlgebra.Generic.RationalFunctionFieldElem}, x)
  K = base_field(E)
  @assert parent(x) === K
  t = gen(K)
  if is_one(denominator(x))
    return _tates_algorithm(E, numerator(x))
  else
    @assert x == 1//t
    return _tates_algorithm(E, degree)
  end
end

function _tates_algorithm(E::EllipticCurve{QQFieldElem}, _p::IntegerUnion)
  p = ZZ(_p)
  F = GF(p, cached = false)
  _invmod = x -> QQ(lift(ZZ, inv(F(x))))
  _uni = p
  return __tates_algorithm_generic(E, ZZ, x -> is_zero(x) ? inf : valuation(x, p), x -> smod(x, p), x -> F(x), x -> QQ(lift(x)), _invmod, p)
end

function __tates_algorithm_generic(E, R, _val, _redmod, _red, _lift, _invmod, pi)
  #K = base_field(E)
  #OK = maximal_order(K)
  #F, _mF = residue_field(OK, P)
  #mF = extend(_mF, K)

  K = base_field(E)
  F = parent(_red(one(K)))
  p = characteristic(F)
  pis2 = p == 2
  pis3 = p == 3
  ## divisibility check
  _pdiv(x) = _val(x) > 0
  # p/2
  onehalfmodp = p == 0 ? QQ(1//2) : (pis2 ? ZZ(0) : invmod(ZZ(2), ZZ(p)))
  # root mod P
  _rootmod(x, e) = begin
    fl, y = is_power(_red(x), e)
    if fl
      @assert y^e == _red(x)
    end
    return fl ? _lift(y) : zero(x)
  end

  Fx, = polynomial_ring(F, cached = false)
  # check if root exists of quadratic polynomial in F
  _hasroot(a, b, c) = length(roots(Fx(_red.([c, b, a])))) > 0
  # number of roots of monic cubic (a = 1)
  _nrootscubic(b, c, d) = length(roots(Fx(_red.([d, c, b, one(b)]))))

  a1, a2, a3, a4, a6 = a_invariants(E)

  if minimum(_val(ai) for ai in [a1, a2, a3, a4, a6] if !iszero(ai)) < 0
    # Non-integral at P, lets make integral
    e = 0
    if !iszero(a1)
      e = max(e, -_val(a1))
    end
    if !iszero(a2)
      e = max(e, ceil(Int, -_val(a2)//2))
    end
    if !iszero(a3)
      e = max(e, ceil(Int, -_val(a3)//3))
    end
    if !iszero(a4)
      e = max(e, ceil(Int, -_val(a4)//4))
    end
    if !iszero(a6)
      e = max(e, ceil(Int, -_val(a6)//6))
    end

    pie = pi^e
    a1 = a1 * pie
    a2 = a2 * pie^2
    a3 = a3 * pie^3
    a4 = a4 * pie^4
    a6 = a6 * pie^6
  end

  # Now the model is P-integral

  while true
    E = elliptic_curve(K, [a1, a2, a3, a4, a6])
    b2, b4, b6, b8 = b_invariants(E)
    c4, c6 = c_invariants(E)
    delta = discriminant(E)
    vD = _val(delta)
    if vD == 0 # Good reduction
      return (E, KodairaSymbol("I0"), FlintZZ(0), FlintZZ(1), true)::Tuple{typeof(E), KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
    end

    # change coords so that p|a3,a4,a6
    if pis2
      if _pdiv(b2)
        r = _rootmod(a4, 2)
        t = _rootmod(((r + a2)*r + a4)*r + a6, 2)
      else
        a1inv = _invmod(a1)
        r = a1inv * a3
        t = a1inv*(a4 + r^2)
      end
    else
      if pis3
        r = _pdiv(b2) ? _rootmod(-b6, 3) : (-_invmod(b2)*b4)
        t = a1 * r + a3
      else
        r = _pdiv(c4) ? (-_invmod(K(12))*b2) : (-_invmod(12*c4)*(c6 + b2*c4))
        t = -onehalfmodp*(a1*r + a3)
      end
    end
    r = _redmod(r)
    t = _redmod(t)

    # transform and update invariants
    E, = transform_rstu(E, [r, 0, t, 1])
    a1, a2, a3, a4, a6 = a_invariants(E)
    b2, b4, b6, b8 = b_invariants(E)

    @assert minimum(_val(ai) for ai in [a1, a2, a3, a4, a6] if !iszero(ai)) >= 0
    # Model is still p-Integral, good!

    @assert _val(a3) != 0
    @assert _val(a4) != 0
    @assert _val(a6) != 0

    # Test for In, II, III, IV

    if !_pdiv(c4) # Type In
      split = _hasroot(one(K), a1, -a2)
      if split
        cp = FlintZZ(vD)
      else
        if mod(vD, 2) == 0
          cp = FlintZZ(2)
        else
          cp = FlintZZ(1)
        end
      end
      Kp = KodairaSymbol("I$(vD)")
      fp = FlintZZ(1)
      return (E, Kp, fp, cp, split)::Tuple{typeof(E), KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
    end

    if _val(a6) < 2 # Type II
      Kp = KodairaSymbol("II")
      fp = FlintZZ(vD)
      cp = FlintZZ(1)
      return (E, Kp, fp, cp, true)::Tuple{typeof(E), KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
    end

    if _val(b8) < 3 # Type III
      Kp = KodairaSymbol("III")
      fp = FlintZZ(vD - 1)
      cp = FlintZZ(2)
      return (E, Kp, fp, cp, true)::Tuple{typeof(E), KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
    end

    if _val(b6) < 3 # Type IV
      cp = _hasroot(one(K), a3//pi, -a6//pi^2) ? ZZ(3) : ZZ(1)
      Kp = KodairaSymbol("IV")
      fp = FlintZZ(vD - 2)
      return (E, Kp, fp, cp, true)::Tuple{typeof(E), KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
    end

    # Change coords so that p|a1,a2, p^2|a3,a4, p^3|a6

    if pis2
      s = _rootmod(a2, 2)
      t = pi * _rootmod(a6//pi^2, 2)
    elseif pis3
      s = a1
      t = a3
    else
      s = -a1 * onehalfmodp
      t = -a3 * onehalfmodp
    end

    # transform and update invariants
    E, = transform_rstu(E, [0, s, t, 1])
    a1, a2, a3, a4, a6 = a_invariants(E)
    b2, b4, b6, b8 = b_invariants(E)
    c4, c6 = c_invariants(E)

    @assert _val(a1) > 0
    @assert _val(a2) > 0
    @assert _val(a3) >= 2
    @assert _val(a4) >= 2
    @assert _val(a6) >= 3

    # Test P-integrality
    @assert minimum(_val(ai) for ai in [a1, a2, a3, a4, a6] if !iszero(ai)) >= 0

    # Analyse roots of the cubic T^3  + bT^2  + cT^2 + d = 0, where
    # b = a2/p, c = a4/p^2, d = a6/p^3

    b = a2//pi
    c = a4//pi^2
    d = a6//pi^3
    w = 27*d^2 - b^2*c^2 + 4*b^3*d - 18*b*c*d + 4*c^3
    x = 3*c - b^2

    sw = _pdiv(w) ? (_pdiv(x) ? 3 : 2) : 1

    if sw == 1 # w != 0 mod P
      # Three distinct roots, so type I*0
      Kp = KodairaSymbol("I0*")
      fp = FlintZZ(vD - 4)
      cp = ZZ(1 + _nrootscubic(b, c, d))
      return (E, Kp, fp, cp, true)::Tuple{typeof(E), KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
    elseif sw == 2
      # One double root, so type I*m for some m
      # Change coords so that the double root is T = 0 mod p

      if pis2
        r = _rootmod(c, 2)
      else
        if pis3
          r = c * _invmod(b)
        else
          r = (b*c - 9 * d) * _invmod(2*x)
        end
      end
      r = pi * _redmod(r)

      E, = transform_rstu(E, [r, 0, 0, 1])
      a1, a2, a3, a4, a6 = a_invariants(E)
      b2, b4, b6, b8 = b_invariants(E)
      c4, c6 = c_invariants(E)

      ix = 3
      iy = 3
      mx = pi^2
      my = pi^2
      done = false
      while !done
        at2 = a2//pi
        a3t = a3//my
        a4t = a4//(pi * mx)
        a6t = a6//(mx * my)
        if _pdiv(a3t^2 + 4*a6t)
          if pis2
            t = my * _rootmod(a6t, 2)
          else
            t = my * _redmod(-a3t * onehalfmodp)
          end
          E, = transform_rstu(E, [0, 0, t, 1])
          a1, a2, a3, a4, a6 = a_invariants(E)
          b2, b4, b6, b8 = b_invariants(E)
          my = my * pi
          iy = iy + 1
          a2t = a2//pi
          a3t = a3//my
          a4t = a4//(pi * mx)
          a6t = a6//(mx * my)
          if _pdiv(a4t^2 - 4*a6t*a2t)
            if pis2
              r = mx * _rootmod(a6t * _invmod(a2t), 2)
            else
              r = mx * _redmod(-a4t * _invmod(2*a2t))
            end
            E, = transform_rstu(E, [r, 0, 0, 1])
            a1, a2, a3, a4, a6 = a_invariants(E)
            b2, b4, b6, b8 = b_invariants(E)
            mx = mx * pi
            ix = ix + 1
            # Stay in the loop
          else
            cp = _hasroot(a2t, a4t, a6t) ? 4 : 2
            done = true
          end
        else
          cp = _hasroot(one(K), a3t, -a6t) ? 4 : 2
          done = true
        end
      end
      m = ix + iy - 5
      fp = vD - m - 4
      Kp = KodairaSymbol("I$(m)*")
      return (E, Kp, FlintZZ(fp), FlintZZ(cp), true)::Tuple{typeof(E), KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
    elseif sw == 3
      # Triple root
      # Change coordinates so that T = 0 mod p
      if pis2
        r = b
      else
        if pis3
          r = _rootmod(-d, 3)
        else
          r = -b * _invmod(K(3))
        end
      end
      r = pi * _redmod(r)
      E, = transform_rstu(E, [r, 0, 0, 1])
      a1, a2, a3, a4, a6 = a_invariants(E)
      b2, b4, b6, b8 = b_invariants(E)
      @assert minimum(_val(ai) for ai in [a1, a2, a3, a4, a6] if !iszero(ai)) >= 0
      # Cubic after transform must have triple root at 0"
      @assert !(_val(a2) < 2 || _val(a4) < 3 || _val(a6) < 4)

      a3t = a3//pi^2
      a6t = a6//pi^4

      # Test for Type IV*
      if !_pdiv(a3t^2 + 4*a6t)
        cp = _hasroot(one(K), a3t, -a6t) ? 3 : 1
        Kp = KodairaSymbol("IV*")
        fp = FlintZZ(vD - 6)
        return (E, Kp, fp, FlintZZ(cp), true)::Tuple{typeof(E), KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
      end

      # Change coordinates so that p^3|a3, p^5|a6
      if pis2
        t = -pi^2 * _rootmod(a6t, 2)
      else
        t = pi^2 * _redmod(-a3t * onehalfmodp)
      end
      E, = transform_rstu(E, [0, 0, t, 1])
      a1, a2, a3, a4, a6 = a_invariants(E)
      b2, b4, b6, b8 = b_invariants(E)

      # Test for types III*, II*

      if _val(a4) < 4 # Type III*
        Kp = KodairaSymbol("III*")
        fp = FlintZZ(vD - 7)
        cp = FlintZZ(2)
        return (E, Kp, fp, FlintZZ(cp), true)::Tuple{typeof(E), KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
      end

      if _val(a6) < 6 # Type II*
        Kp = KodairaSymbol("II*")
        fp = FlintZZ(vD - 8)
        cp = FlintZZ(1)
        return (E, Kp, fp, FlintZZ(cp), true)::Tuple{typeof(E), KodairaSymbol,  ZZRingElem, ZZRingElem, Bool}
      end

      # Non-minimal equation, dividing out
      a1 = a1//pi
      a2 = a2//pi^2
      a3 = a3//pi^3
      a4 = a4//pi^4
      a6 = a6//pi^6
    end
  end
end

@doc raw"""
    tates_algorithm_local(E::EllipticCurve{QQFieldElem}, p:: Int)
    -> elliptic_curve{QQFieldElem}, String, ZZRingElem, ZZRingElem, Bool

Returns a tuple $(\tilde E, K, f, c, s)$, where $\tilde E$ is a
minimal model for $E$ at the prime ideal $p$, $K$ is the Kodaira symbol,
$f$ is the conductor valuation at $p$, $c$ is the local Tamagawa number
at $p$ and s is false if and only if $E$ has non-split
multiplicative reduction.
"""
function tates_algorithm_local(E::EllipticCurve{QQFieldElem}, p)

  p = FlintZZ(p)

  a1, a2, a3, a4, a6 = map(numerator,(a_invariants(E)))

  b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

  delta = discriminant(E)
  delta = numerator(delta)

  n = valuation(delta, p)

  # test for type I0
  if n == 0
    return (E, KodairaSymbol("I0"), FlintZZ(0), FlintZZ(1), true)::Tuple{EllipticCurve{QQFieldElem}, KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
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

  a1, a2, a3, a4, a6 = map(numerator,(a_invariants(E)))

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

    Kp = KodairaSymbol("I$(n)")
    fp = FlintZZ(1)

    return (E, Kp, fp, cp, split)::Tuple{EllipticCurve{QQFieldElem}, KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
  end

  if mod(a6, p^2) != 0
    Kp = KodairaSymbol("II")
    fp = FlintZZ(n)
    cp = FlintZZ(1)
    return (E, Kp, fp, cp, true)::Tuple{EllipticCurve{QQFieldElem}, KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
  end

  if mod(b8, p^3) != 0
    Kp = KodairaSymbol("III")
    fp = FlintZZ(n-1)
    cp = FlintZZ(2)
    return (E, Kp, fp, cp, true)::Tuple{EllipticCurve{QQFieldElem}, KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
  end

  if mod(b6, p^3) != 0
    if quadroots(1, divexact(a3, p), divexact(-a6, p^2), p)
      cp = FlintZZ(3)
    else
      cp = FlintZZ(1)
    end
    Kp = KodairaSymbol("IV")
    fp = n - 2
    return (E, Kp, FlintZZ(fp), cp, true)::Tuple{EllipticCurve{QQFieldElem}, KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
  end

  # change coordinates so that p | a1, a2; p^2 | a3, a4; p^3 | a6
  if p == 2
    s = smod(a2, 2)
    t = 2 * smod(divexact(a6, 4), 2)
  else
    s = -a1 * invmod(FlintZZ(2), p)
    t = -a3 * invmod(FlintZZ(2), p)
  end

  trans = transform_rstu(E, ZZRingElem[0, s, t, 1])
  E = trans[1]

  a1, a2, a3, a4, a6 = map(numerator,(a_invariants(E)))

  b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

  # set up auxililary cubic T^3 + bT^2 + cT + d
  b = divexact(a2, p)
  c = divexact(a4, p^2)
  d = divexact(a6, p^3)
  w = 27*d^2 - b^2*c^2 + 4*b^3*d - 18*b*c*d + 4*c^3
  x = 3*c - b^2

  # test for distinct roots: type I0*
  if mod(w, p) != 0
    Kp = KodairaSymbol("I0*")
    fp = FlintZZ(n - 4)
    cp = 1 + nrootscubic(b, c, d, p)
    return (E, Kp, fp, FlintZZ(cp), true)::Tuple{EllipticCurve{QQFieldElem}, KodairaSymbol, ZZRingElem, ZZRingElem, Bool}

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

    a1, a2, a3, a4, a6 = map(numerator,(a_invariants(E)))

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

        a1, a2, a3, a4, a6 = map(numerator,(a_invariants(E)))

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

          a1, a2, a3, a4, a6 = map(numerator,(a_invariants(E)))

          b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

          mx = mx*p
          m = m + 1
        end
      end
    end

    fp = n - m - 4
    Kp = KodairaSymbol("I$(m)*")

    return (E, Kp, FlintZZ(fp), FlintZZ(cp), true)::Tuple{EllipticCurve{QQFieldElem}, KodairaSymbol, ZZRingElem, ZZRingElem, Bool}

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

    a1, a2, a3, a4, a6 = map(numerator,(a_invariants(E)))

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
      Kp = KodairaSymbol("IV*")
      fp = FlintZZ(n - 6)

      return (E, Kp, fp, FlintZZ(cp), true)::Tuple{EllipticCurve{QQFieldElem}, KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
    else
      if p == 2
        t = x6
      else
        t = x3 * invmod(FlintZZ(2), p)
      end

      t = -p^2 * smod(t, p)

      trans = transform_rstu(E, [0, 0, t, 1])
      E = trans[1]

      a1, a2, a3, a4, a6 = map(numerator,(a_invariants(E)))

      b2, b4, b6, b8, c4, c6 = get_b_c_integral(E)

      # Test for types III*, II*
      if mod(a4, p^4) != 0
        Kp = KodairaSymbol("III*")
        fp = FlintZZ(n - 7)
        cp = FlintZZ(2)

        return (E, Kp, fp, FlintZZ(cp), true)::Tuple{EllipticCurve{QQFieldElem}, KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
      elseif mod(a6, p^6) != 0
        Kp = KodairaSymbol("II*")
        fp = FlintZZ(n - 8)
        cp = FlintZZ(1)

        return (E, Kp, fp, FlintZZ(cp), true)::Tuple{EllipticCurve{QQFieldElem}, KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
      else
        E = transform_rstu(E, [0, 0, 0, p])[1]
        return tates_algorithm_local(E, p)::Tuple{EllipticCurve{QQFieldElem}, KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
      end
    end
  end
end


@doc raw"""
    tates_algorithm_global(E::EllipticCurve{QQFieldElem}) -> EllipticCurve{QQFieldElem}

Return a global reduced minimal model for $E$ using Tate's algorithm.
"""
function tates_algorithm_global(E::EllipticCurve{QQFieldElem})
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

  return E::EllipticCurve{QQFieldElem}
end

function tates_algorithm_global(E::T) where T<: EllipticCurve{ <:AbstractAlgebra.Generic.RationalFunctionFieldElem{<:FieldElem,<:PolyRingElem}}

  R = base_ring(base_field(E).fraction_field)

  delta = factor(R, discriminant(E))

  for (p,_) in delta
    E = tates_algorithm_local(E,p)[1]
  end

  return E::T
end


struct KodairaSymbol
  ksymbol::Int

  function KodairaSymbol(n::Int)
    @req n!= 0 "0 does not correspond to any Kodaira symbol."
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

    if K[1]!='I'
      error("String does not represent a valid Kodaira symbol.")
    end

    n = lastindex(K)

    if K[n]=='*'
      m = parse(Int, K[2:n-1])
      return KodairaSymbol(-4 - m)
    else
      m = parse(Int, K[2:n])
      return KodairaSymbol(4 + m)
    end

    error("String does not represent a valid Kodaira symbol.")

  end
end

################################################################################
#
#  Equality of Kodaira symbols
#
################################################################################

@doc raw"""
    ==(K1::KodairaSymbol, K2::KodairaSymbol) -> Bool

Return true if $K1$ and $K2$ are the same Kodaira symbol.
"""
function ==(K1::KodairaSymbol, K2::KodairaSymbol)
  return K1.ksymbol == K2.kymbol
end


@doc raw"""
    ==(K::KodairaSymbol, s::String) -> Bool

Return true if K is corresponds to the Kodaira symbol given by the string.
Valid inputs are : I0, II, III, IV and In where n is a positive integer,
I0*, II*, III*, IV* and In* where n is a positive integer.

Instead of substituting n for an integer one may also check against the generic types 'In'
or 'In*' to test if the Kodaira symbol is of that type.
"""
function ==(K::KodairaSymbol, s::String)
   if s == "I0"
      return K.ksymbol == 1
    elseif s == "I0*"
      return K.ksymbol == -1
    elseif s == "II"
      return K.ksymbol == 2
    elseif s == "II*"
      return K.ksymbol == -2
    elseif s == "III"
      return K.ksymbol == 3
    elseif s == "III*"
      return K.ksymbol == -3
    elseif s == "IV"
      return K.ksymbol == 4
    elseif s == "IV*"
      return K.ksymbol == -4
    elseif s == "In"
      return K.ksymbol > 4
    elseif s == "In*"
      return K.ksymbol < -4
    end

    if s[1] != 'I'
      error("String does not represent a valid Kodaira symbol.")
    end

    n = lastindex(s)

    if s[n]=='*'
      m = parse(Int, s[2:n-1])
      return K.ksymbol == -4 - m
    else
      m = parse(Int, s[2:n])
      return K.ksymbol == 4 + m
    end

    error("String does not represent a valid Kodaira symbol.")
end


function show(io::IO, K::KodairaSymbol)
  m = K.ksymbol

  if m == 1
    print(io, "I0")
  elseif m == -1
    print(io, "I0*")
  elseif m == 2
    print(io, "II")
  elseif m == -2
    print(io, "II*")
  elseif m == 3
    print(io, "III")
  elseif m == -3
    print(io, "III*")
  elseif m == 4
    print(io, "IV")
  elseif m == -4
    print(io, "IV*")
  end

  if m > 4
    m = m - 4
    print(io, "I$(m)")
  elseif m < -4
    m = m + 4
    m = -m
    print(io, "I$(m)*")
  end
end


function ==(s::String, K::KodairaSymbol)
  return K == s
end

@doc raw"""
    tamagawa number(E::EllipticCurve{QQFieldElem}, p::Int) -> ZZRingElem

Return the local Tamagawa number for E at p.
"""
function tamagawa_number(E::EllipticCurve{QQFieldElem},p)
  return tates_algorithm_local(E,p)[4]
end

@doc raw"""
    tamagawa numbers(E::EllipticCurve{QQFieldElem}) -> Vector{(ZZRingElem, ZZRingElem)}

Return the sequence of Tamagawa numbers for $E$ at all the
bad primes $p$ of $E$.
"""
function tamagawa_numbers(E::EllipticCurve{QQFieldElem})
  badp = bad_primes(E)
  return [tamagawa_number(E,p) for p in badp]
end

@doc raw"""
    kodaira_symbol(E::EllipticCurve{QQFieldElem}, p::Int) -> String

Return the reduction type of E at p using a Kodaira symbol.
"""
function kodaira_symbol(E::EllipticCurve{QQFieldElem},p)
  return tates_algorithm_local(E,p)[2]
end

@doc raw"""
    kodaira_symbols(E::EllipticCurve{QQFieldElem}, p::Int) -> Vector{(ZZRingElem, String)}

Return the reduction types of E at all bad primes as a sequence of
Kodaira symbols
"""
function kodaira_symbols(E::EllipticCurve{QQFieldElem})
  badp = bad_primes(E)
  return [kodaira_symbol(E,p) for p in badp]
end

@doc raw"""
    tamagawa number(E::EllipticCurve{QQFieldElem}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> ZZRingElem

Return the local Tamagawa number for E at p.
"""
function tamagawa_number(E::EllipticCurve{AbsSimpleNumFieldElem},p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  return tates_algorithm_local(E,p)[4]
end

@doc raw"""
    tamagawa numbers(E::EllipticCurve{QQFieldElem}) -> Vector{(AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, ZZRingElem)}

Return the sequence of Tamagawa numbers for $E$ at all the bad
prime ideals $p$ of $E$.
"""
function tamagawa_numbers(E::EllipticCurve{AbsSimpleNumFieldElem})
  badp = bad_primes(E)
  return [tamagawa_number(E,p) for p in badp]
end

@doc raw"""
    kodaira_symbol(E::EllipticCurve{AbsSimpleNumFieldElem}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
      -> String

Return the reduction type of E at the prime ideal p using
a Kodaira symbol.
"""
function kodaira_symbol(E::EllipticCurve{AbsSimpleNumFieldElem},p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  return tates_algorithm_local(E,p)[2]
end

@doc raw"""
    kodaira_symbols(E::EllipticCurve{AbsSimpleNumFieldElem}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
      -> Vector{(AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, String)}

Return the reduction types of E at all bad primes as a sequence of
Kodaira symbols.
"""
function kodaira_symbols(E::EllipticCurve{AbsSimpleNumFieldElem})
  badp = bad_primes(E)
  return [kodaira_symbol(E,p) for p in badp]
end

@doc raw"""
    reduction_type(E::EllipticCurve{QQFieldElem}, p::ZZRingElem) -> String

Return the reduction type of E at p. It can either be good, additive,
split multiplicative or nonsplit mutiplicative.
"""
function reduction_type(E::EllipticCurve{QQFieldElem}, p)
  Ep, Kp, f, c, split = tates_algorithm_local(E, p)

  if Kp=="I0"
    return "Good"
  end

  if Kp.ksymbol > 4
    if split
      return "Split multiplicative"
    else
      return "Nonsplit multiplicative"
    end
  end

 return "Additive"

end

@doc raw"""
    reduction_type(E::EllipticCurve{AbsSimpleNumFieldElem}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> String

Return the reduction type of E at the prime ideal p.
It can either be good, additive, split multiplicative or
nonsplit mutiplicative.
"""
function reduction_type(E::EllipticCurve{AbsSimpleNumFieldElem}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  Ep, Kp, f, c, split = tates_algorithm_local(E, p)

  if Kp=="I0"
    return "Good"
  end

  if Kp.ksymbol > 4
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

@doc raw"""
    conductor(E::EllipticCurve{QQFieldElem}) -> ZZRingElem

Return the conductor of $E$ over QQ.
"""
function conductor(E::EllipticCurve{QQFieldElem})
  badp = bad_primes(E)

  result = 1
  for p in badp
    result = result*(p^tates_algorithm_local(E,p)[3])
  end
  return result
end

@doc raw"""
    conductor(E::EllipticCurve{AbsSimpleNumFieldElem}) -> AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}

Return conductor of $E$ over a number field as an ideal.
"""
function conductor(E::EllipticCurve{AbsSimpleNumFieldElem})
  badp = bad_primes(E)

  result = 1
  for p in badp
    result = result*(p^tates_algorithm_local(E,p)[3])
  end
  return result
end

#Magma returns the primes that divide the minimal discriminant
@doc raw"""
    bad_primes(E::EllipticCurve{QQFieldElem}) -> Vector{ZZRingElem}

Return a list of the primes that divide the discriminant of $E$.
"""
function bad_primes(E::EllipticCurve{QQFieldElem})

  d = ZZ(discriminant(E))
  L = factor(d)
  return sort([p for (p,e) in L])
end

@doc raw"""
    bad_primes(E::EllipticCurve{QQFieldElem}) -> Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}

Return a list of prime ideals that divide the discriminant of $E$.
"""
function bad_primes(E::EllipticCurve{AbsSimpleNumFieldElem})
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
@doc raw"""
    modp_reduction(E::EllipticCurve{AbsSimpleNumFieldElem}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> EllipticCurve

Return the reduction of $E$ modulo the prime ideal p if p has good reduction
"""
function modp_reduction(E::EllipticCurve{AbsSimpleNumFieldElem}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  if !is_prime(p)
    throw(DomainError(p,"p is not a prime ideal"))
  end

  if p in bad_primes(E)
    throw(DomainError(p,"E has bad reduction at p"))
  end

  K, phi = residue_field(order(p),p)

  a1, a2, a3, a4, a6 = map(phi,map(order(p), a_invariants(E)))

  return elliptic_curve(K, [a1, a2, a3, a4, a6])

end

################################################################################
#
#  Integral invariants
#
################################################################################

# this needs to be rewritten
@doc raw"""
    get_b_integral(E::EllipticCurve{ZZRingElem}) -> Nemo.ZZRingElem

Computes the invariants $b2$, $b4$, $b6$, $b8$ of an elliptic curve $E$ with integer coefficients.
"""
function get_b_integral(E)
  a1, a2, a3, a4, a6 = map(numerator,(a_invariants(E)))

  b2 = a1^2 + 4*a2
  b4 = a1*a3 + 2*a4
  b6 = a3^2 + 4*a6
  b8 = a1^2*a6 - a1*a3*a4 + 4*a2*a6 + a2*a3^2 - a4^2

  return b2,b4,b6,b8
end

@doc raw"""
    get_b_c_integral(E::EllipticCurve{ZZRingElem}) -> Nemo.ZZRingElem

Computes the invariants $b2$, $b4$, $b6$, $b8$, $c4$, $c6$ of an elliptic curve $E$ with integer coefficients.
"""
function get_b_c_integral(E)
    b2, b4, b6, b8 = get_b_integral(E)

    c4 = b2^2 - 24*b4
    c6 = -b2^3 + 36*b2*b4 - 216*b6

    return b2,b4,b6,b8,c4,c6
end
