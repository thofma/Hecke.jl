################################################################################
#
#             EllipticCurve/LocalData.jl : Computing local data for elliptic curves
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
  return __tates_algorithm_generic(E, ZZ, x -> is_zero(x) ? inf : valuation(x, p), x -> smod(x, p), x -> F(x), x -> QQ(lift(ZZ, x)), _invmod, p)
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
      return (E, KodairaSymbol("I0"), ZZ(0), ZZ(1), true)::Tuple{typeof(E), KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
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
        cp = ZZ(vD)
      else
        if mod(vD, 2) == 0
          cp = ZZ(2)
        else
          cp = ZZ(1)
        end
      end
      Kp = KodairaSymbol("I$(vD)")
      fp = ZZ(1)
      return (E, Kp, fp, cp, split)::Tuple{typeof(E), KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
    end

    if _val(a6) < 2 # Type II
      Kp = KodairaSymbol("II")
      fp = ZZ(vD)
      cp = ZZ(1)
      return (E, Kp, fp, cp, true)::Tuple{typeof(E), KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
    end

    if _val(b8) < 3 # Type III
      Kp = KodairaSymbol("III")
      fp = ZZ(vD - 1)
      cp = ZZ(2)
      return (E, Kp, fp, cp, true)::Tuple{typeof(E), KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
    end

    if _val(b6) < 3 # Type IV
      cp = _hasroot(one(K), a3//pi, -a6//pi^2) ? ZZ(3) : ZZ(1)
      Kp = KodairaSymbol("IV")
      fp = ZZ(vD - 2)
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
      fp = ZZ(vD - 4)
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
      return (E, Kp, ZZ(fp), ZZ(cp), true)::Tuple{typeof(E), KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
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
        fp = ZZ(vD - 6)
        return (E, Kp, fp, ZZ(cp), true)::Tuple{typeof(E), KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
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
        fp = ZZ(vD - 7)
        cp = ZZ(2)
        return (E, Kp, fp, ZZ(cp), true)::Tuple{typeof(E), KodairaSymbol, ZZRingElem, ZZRingElem, Bool}
      end

      if _val(a6) < 6 # Type II*
        Kp = KodairaSymbol("II*")
        fp = ZZ(vD - 8)
        cp = ZZ(1)
        return (E, Kp, fp, ZZ(cp), true)::Tuple{typeof(E), KodairaSymbol,  ZZRingElem, ZZRingElem, Bool}
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

Return the reduction type of E at a prime p. It can either be good, additive,
split multiplicative or nonsplit multiplicative.
"""
function reduction_type(E::EllipticCurve{QQFieldElem}, p)
  return _reduction_type_impl(E, p)
end

@doc raw"""
    reduction_type(E::EllipticCurve{AbsSimpleNumFieldElem}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> String

Return the reduction type of E at a prime ideal p.
It can either be good, additive, split multiplicative or nonsplit multiplicative.
"""
function reduction_type(E::EllipticCurve{AbsSimpleNumFieldElem}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  return _reduction_type_impl(E, p)
end

function _reduction_type_impl(E, p)
  _, Ks, _, _, split = tates_algorithm_local(E, p)

  has_good_reduction(Ks) && return "Good"
  has_multiplicative_reduction(Ks) && return (split ? "Split multiplicative" : "Nonsplit multiplicative")

  @assert has_additive_reduction(Ks)
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

  result = one(ZZ)
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

  result = 1 * order(badp[1])
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
#  Kodaira Symbol
#
################################################################################

@doc raw"""
    KodairaSymbol

Represents the Kodaira symbol of a fiber of a Neron model of an elliptic
curve. The symbol encodes the reduction type at a prime.

The internal encoding uses a single integer (PARI/GP convention):
- `I0` = 1, `II` = 2, `III` = 3, `IV` = 4, `In` (n >= 1) = 4 + n
- `I0*` = -1, `II*` = -2, `III*` = -3, `IV*` = -4, `In*` (n >= 1) = -(4 + n)

Kodaira symbols can be constructed from strings:

```jldoctest
julia> KodairaSymbol("I5")
I5

julia> KodairaSymbol("IV*")
IV*
```
"""
struct KodairaSymbol
  ksymbol::Int

  function KodairaSymbol(n::Int)
    @req n != 0 "0 does not correspond to any Kodaira symbol."
    return new(n)
  end

  function KodairaSymbol(s::String)
    return new(_kodaira_symbol_from_string(s))
  end
end

function _kodaira_symbol_from_string(s::String)
  s == "I0"   && return  1
  s == "I0*"  && return -1
  s == "II"   && return  2
  s == "II*"  && return -2
  s == "III"  && return  3
  s == "III*" && return -3
  s == "IV"   && return  4
  s == "IV*"  && return -4

  (length(s) >= 2 && s[1] == 'I') || error("\"$s\" is not a valid Kodaira symbol.")

  if s[end] == '*'
    m = parse(Int, SubString(s, 2, lastindex(s) - 1))
    return - (4 + m)
  else
    m = parse(Int, SubString(s, 2))
    return 4 + m
  end
end

function _kodaira_symbol_to_string(n::Int)
  @req n != 0 "0 does not correspond to any Kodaira symbol."

  n ==  1 && return "I0"
  n == -1 && return "I0*"
  n ==  2 && return "II"
  n == -2 && return "II*"
  n ==  3 && return "III"
  n == -3 && return "III*"
  n ==  4 && return "IV"
  n == -4 && return "IV*"

  if n > 4
    return "I$(n - 4)"
  else # n < -4
    return "I$(-(n + 4))*"
  end
end

function ==(K1::KodairaSymbol, K2::KodairaSymbol)
  return K1.ksymbol == K2.ksymbol
end

function Base.hash(K::KodairaSymbol, h::UInt)
  return hash(K.ksymbol, h)
end

@doc raw"""
    ==(K::KodairaSymbol, s::String) -> Bool

Return `true` if `K` corresponds to the Kodaira symbol given by the string.
In addition to specific symbols like `"I5"` or `"IV*"`, the generic types
`"In"` and `"In*"` can be used to test if `K` is of that family.
"""
function ==(K::KodairaSymbol, s::String)
  if s == "In"
    return K.ksymbol > 4
  elseif s == "In*"
    return K.ksymbol < -4
  else
    return K.ksymbol == _kodaira_symbol_from_string(s)
  end
end

function ==(s::String, K::KodairaSymbol)
  return K == s
end

function show(io::IO, K::KodairaSymbol)
  print(io, _kodaira_symbol_to_string(K.ksymbol))
end

function has_good_reduction(K::KodairaSymbol)
  return K.ksymbol == 1
end

function has_multiplicative_reduction(K::KodairaSymbol)
  return K.ksymbol > 4
end

function has_additive_reduction(K::KodairaSymbol)
  return !(has_good_reduction(K) || has_multiplicative_reduction(K))
end

