################################################################################
#
#             EllipticCurve/LocalData.jl : Computing local data for elliptic curves
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

@doc raw"""
    EllipticCurveReduction

Submodule holding the [`ReductionType`](@ref) enumeration used by
[`EllipticCurveLocalData`](@ref). Short names are scoped here to avoid
polluting the top-level namespace.
"""
module EllipticCurveReduction
  export ReductionType, good, split_multiplicative, nonsplit_multiplicative, additive

  @doc raw"""
    EllipticCurveReduction.ReductionType

Enumeration of the reduction types of an elliptic curve at a place of
its base field, as produced by Tate's algorithm.

The values are scoped in the `EllipticCurveReduction` submodule; reference
them with the module prefix:

- `EllipticCurveReduction.good`
- `EllipticCurveReduction.split_multiplicative`
- `EllipticCurveReduction.nonsplit_multiplicative`
- `EllipticCurveReduction.additive`

# Examples
```jldoctest
julia> E = elliptic_curve([1, 1, 0, 40050, 7557750]);

julia> ld = tates_algorithm_local(E, 5, EllipticCurveLocalData);

julia> ld.reduction_type == EllipticCurveReduction.additive
true
```
See also [`EllipticCurveLocalData`](@ref).
  """
  @enum ReductionType begin
    good
    split_multiplicative
    nonsplit_multiplicative
    additive
  end
end

################################################################################
#
#  Local Data
#
################################################################################

@doc raw"""
    EllipticCurveLocalData

Local data of an elliptic curve at a prime, as computed by Tate's algorithm.

# Fields
- `minimal_model::EllipticCurve{T}`: local minimal model
- `kodaira_symbol::KodairaSymbol`: Kodaira symbol of the fiber
- `conductor_valuation::ZZRingElem`: conductor valuation
- `tamagawa_number::ZZRingElem`: local Tamagawa number
- `reduction_type::EllipticCurveReduction.ReductionType`: the type of reduction
"""
struct EllipticCurveLocalData{T}
  minimal_model::EllipticCurve{T}
  kodaira_symbol::KodairaSymbol
  conductor_valuation::ZZRingElem
  tamagawa_number::ZZRingElem
  reduction_type::EllipticCurveReduction.ReductionType
end

function EllipticCurveLocalData(E::EllipticCurve{T}, ks::KodairaSymbol, cv::IntegerUnion, tn::IntegerUnion, split::Bool) where T
  return EllipticCurveLocalData{T}(E, ks, ZZ(cv), ZZ(tn), _reduction_type(ks, split))
end

################################################################################
#
#  Tate's Algorithm
#
################################################################################

# Tate's algorithm over number fields, see Cremona, p. 66, Silverman p. 366
@doc raw"""
    tates_algorithm_local(E::EllipticCurve{QQFieldElem}, p::IntegerUnion)
    tates_algorithm_local(E::EllipticCurve{AbsSimpleNumFieldElem}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
    tates_algorithm_local(E::EllipticCurve{<:AbstractAlgebra.Generic.RationalFunctionFieldElem}, f::PolyRingElem)
    tates_algorithm_local(E::EllipticCurve{<:AbstractAlgebra.Generic.RationalFunctionFieldElem}, ::typeof(degree))
    tates_algorithm_local(E::EllipticCurve{T}, x::T) where {T <: AbstractAlgebra.Generic.RationalFunctionFieldElem}

Run Tate's algorithm for the elliptic curve $E$ at the prime/place given by the second argument.
See Cremona p. 66 or Silverman AEC II, IV.9.

The second argument denotes a prime/place of the base field of $E$:
- a rational prime for $E$ over $\mathbf{Q}$,
- a prime ideal of the ring of integers for $E$ over a number field,
- an irreducible polynomial in $k[t]$, the symbol `degree` (for the place
  at infinity), or a rational function equal to such a polynomial or to
  $1/t$, for $E$ over a rational function field $k(t)$.

Returns a tuple $(\tilde E, K, f, c, s)$, where $\tilde E$ is a local
minimal model at the given prime, $K$ is the Kodaira symbol, $f$ is the
conductor valuation, $c$ is the local Tamagawa number, and $s$ is `false`
if and only if $E$ has non-split multiplicative reduction.

See also [`tates_algorithm_local(E, p, ::Type{EllipticCurveLocalData})`](@ref)
for a variant returning the full local data struct.
"""
function tates_algorithm_local(E, P)
  ld = _tates_algorithm(E, P)
  split = (ld.reduction_type != EllipticCurveReduction.nonsplit_multiplicative)
  return (ld.minimal_model, ld.kodaira_symbol, ld.conductor_valuation, ld.tamagawa_number, split)
end

@doc raw"""
    tates_algorithm_local(E::EllipticCurve{QQFieldElem}, p::IntegerUnion, ::Type{EllipticCurveLocalData})
    tates_algorithm_local(E::EllipticCurve{AbsSimpleNumFieldElem}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::Type{EllipticCurveLocalData})
    tates_algorithm_local(E::EllipticCurve{<:AbstractAlgebra.Generic.RationalFunctionFieldElem}, f::PolyRingElem, ::Type{EllipticCurveLocalData})
    tates_algorithm_local(E::EllipticCurve{<:AbstractAlgebra.Generic.RationalFunctionFieldElem}, ::typeof(degree), ::Type{EllipticCurveLocalData})
    tates_algorithm_local(E::EllipticCurve{T}, x::T, ::Type{EllipticCurveLocalData}) where {T <: AbstractAlgebra.Generic.RationalFunctionFieldElem}

Variant of [`tates_algorithm_local`](@ref) returning an
[`EllipticCurveLocalData`](@ref) struct instead of a tuple.
"""
function tates_algorithm_local(E, P, ::Type{EllipticCurveLocalData})
  return _tates_algorithm(E, P)
end

function _tates_algorithm(E::EllipticCurve{QQFieldElem}, p::IntegerUnion)
  return _tates_algorithm(E, QQValuation(p))
end

function _tates_algorithm(E::EllipticCurve{AbsSimpleNumFieldElem}, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  return _tates_algorithm(E, AbsSimpleNumFieldValuation(P))
end

function _tates_algorithm(E::EllipticCurve{<:AbstractAlgebra.Generic.RationalFunctionFieldElem}, ::typeof(degree))
  return _tates_algorithm(E, RationalFunctionFieldDegreeValuation(base_field(E)))
end

function _tates_algorithm(E::EllipticCurve{<:AbstractAlgebra.Generic.RationalFunctionFieldElem}, f::PolyRingElem)
  return _tates_algorithm(E, RationalFunctionFieldValuation(base_field(E), f))
end

function _tates_algorithm(E::EllipticCurve{T}, x::T) where {T <: AbstractAlgebra.Generic.RationalFunctionFieldElem}
  K = base_field(E)
  @assert parent(x) === K

  if is_one(denominator(x))
    return _tates_algorithm(E, numerator(x))
  else
    @assert x == 1 // gen(K)
    return _tates_algorithm(E, degree)
  end
end

function _tates_algorithm(E::EllipticCurve{T}, v::DiscreteValuation{T}) where T
  K = base_field(E)
  F = residue_field(v)
  p = characteristic(F)
  pi = uniformizer(v)

  # 1//2 modulo p
  inv_2_modp = p == 0 ? QQ(1//2) : (p == 2 ? ZZ(0) : invmod(ZZ(2), ZZ(p)))
  # n-th root modulo p (lifted back to K)
  function nth_root_mod(x::T, e::Integer)
    fl, y = is_power(reduce(v, x), e)
    return fl ? lift(v, y) : zero(x)
  end

  Fx = polynomial_ring(F, cached = false)[1]
  # check if ax^2 + bx + c has roots in residue field F
  function quadratic_has_root(a::T, b::T, c::T)
    f = Fx(reduce.(Ref(v), [c, b, a]))
    return !isempty(roots(f))
  end

  a1, a2, a3, a4, a6 = a_invariants(E)

  # make elliptic curve integral at prime: enough to consider uniform scaling by u
  int_e = 0
  for (ai, w) in [(a1, 1), (a2, 2), (a3, 3), (a4, 4), (a6, 6)]
    ai_val = valuation(v, ai)
    if ai_val < 0
      int_e = max(int_e, div(-ai_val + w - 1, w))
    end
  end

  if int_e > 0
    u = pi^int_e
    a1, a2, a3, a4, a6 = a1*u, a2*u^2, a3*u^3, a4*u^4, a6*u^6
  end

  # Now the model is P-integral
  while true
    E = elliptic_curve(K, [a1, a2, a3, a4, a6])
    b2, b4, b6, b8 = b_invariants(E)
    c4, c6 = c_invariants(E)

    vD = valuation(v, discriminant(E))

    # Step 1 in Silverman description
    # Line 4 in Cremona description
    if vD == 0  # Good Reduction
      return EllipticCurveLocalData(E, KodairaSymbol("I0"), 0, 1, true)
    end

    # Step 2 in Silverman description
    # Lines 5-17 in Cremona description

    # move singular point to (0,0): change coords so that p | a3, a4, a6
    if p == 2
      if valuation(v, b2) > 0
        r = nth_root_mod(a4, 2)
        t = nth_root_mod(((r + a2)*r + a4)*r + a6, 2)
      else
        a1inv = inv_mod(v, a1)
        r = a1inv * a3
        t = a1inv * (a4 + r^2)
      end
    elseif p == 3
      r = valuation(v, b2) > 0 ? nth_root_mod(-b6, 3) : -inv_mod(v, b2) * b4
      t = a1 * r + a3
    else
      r = valuation(v, c4) > 0 ? -inv_mod(v, K(12)) * b2 : -inv_mod(v, 12*c4) * (c6 + b2*c4)
      t = -inv_2_modp * (a1 * r + a3)
    end
    r = reduce_mod(v, r)
    t = reduce_mod(v, t)

    # transform and update invariants
    E, = transform_rstu(E, [r, 0, t, 1])
    a1, a2, a3, a4, a6 = a_invariants(E)
    b2, b4, b6, b8 = b_invariants(E)
    # note that c-invariants are unchanged (the transform has u = 1)

    # ensure the model stays P-integral
    @assert minimum(valuation(v, x) for x in [a1, a2, a3, a4, a6]) >= 0
    # ensure a3, a4, a6 are divisible by P
    @assert minimum(valuation(v, x) for x in [a3, a4, a6]) > 0

    # Test for In, II, III, IV

    # part of Step 2 in Silverman description
    # Lines 19-21 in Cremona description
    if valuation(v, c4) == 0  # Type In
      split = quadratic_has_root(one(K), a1, -a2)
      if split
        cp = vD
      else
        cp = mod(vD, 2) == 0 ? 2 : 1
      end
      return EllipticCurveLocalData(E, KodairaSymbol("I$(vD)"), 1, cp, split)
    end

    # Step 3 in Silverman description
    # Line 23 in Cremona description
    if valuation(v, a6) < 2   # Type II
      return EllipticCurveLocalData(E, KodairaSymbol("II"), vD, 1, true)
    end

    # Step 4 in Silverman description
    # Line 24 in Cremona description
    if valuation(v, b8) < 3   # Type III
      return EllipticCurveLocalData(E, KodairaSymbol("III"), vD - 1, 2, true)
    end

    # Step 5 in Silverman description
    # Lines 25-28 in Cremona description
    if valuation(v, b6) < 3   # Type IV
      cp = quadratic_has_root(one(K), a3//pi, -a6//pi^2) ? 3 : 1
      return EllipticCurveLocalData(E, KodairaSymbol("IV"), vD - 2, cp, true)
    end

    # Step 6 in Silverman description
    # Lines 29-33 in Cremona description
    # Change coords so that p|a1,a2, p^2|a3,a4, p^3|a6

    if p == 2
      s = nth_root_mod(a2, 2)
      t = pi * nth_root_mod(a6//pi^2, 2)
    elseif p == 3
      s = a1
      t = a3
    else
      s = -a1 * inv_2_modp
      t = -a3 * inv_2_modp
    end

    # transform and update invariants
    E, = transform_rstu(E, [0, s, t, 1])
    a1, a2, a3, a4, a6 = a_invariants(E)
    b2, b4, b6, b8 = b_invariants(E)
    c4, c6 = c_invariants(E)

    # ensure divisibility conditions
    @assert valuation(v, a1) >= 1 && valuation(v, a2) >= 1
    @assert valuation(v, a3) >= 2 && valuation(v, a4) >= 2
    @assert valuation(v, a6) >= 3

    # part of Step 6 in Silverman description
    # Lines 34-36 in Cremona description
    # Analyse roots of the cubic T^3  + bT^2  + cT^2 + d = 0, where
    #   b = a2/p, c = a4/p^2, d = a6/p^3
    b = a2 // pi
    c = a4 // pi^2
    d = a6 // pi^3
    w = 27*d^2 - b^2*c^2 + 4*b^3*d - 18*b*c*d + 4*c^3
    x = 3*c - b^2

    # part of Step 6 in Silverman description
    # Line 37 in Cremona description
    if valuation(v, w) == 0     # Three distinct roots: I0*
      # we need the number of roots of x^3 + bx^2 + cx + d
      f = Fx(reduce.(Ref(v), [d, c, b, one(K)]))
      return EllipticCurveLocalData(E, KodairaSymbol("I0*"), vD - 4, 1 + length(roots(f)), true)
    elseif valuation(v, x) == 0 # One double root: Im*
      # part of Step 7 in Silverman description
      # Lines 39-41 in Cremona description
      # Change coords so that the double root is T = 0 mod p
      if p == 2
        r = nth_root_mod(c, 2)
      elseif p == 3
        r = c * inv_mod(v, b)
      else
        r = (b*c - 9 * d) * inv_mod(v, 2*x)
      end
      r = pi * reduce_mod(v, r)

      E, = transform_rstu(E, [r, 0, 0, 1])
      a1, a2, a3, a4, a6 = a_invariants(E)
      b2, b4, b6, b8 = b_invariants(E)
      c4, c6 = c_invariants(E)

      # Lines 42-64 in Cremona description
      # See step 7 in Silverman description for details
      # We proceed in "pairs" of quadratic equations,
      #   unless we find one with distinct roots (in the algebraic closure)
      # The first equation increases the valuation of a3, a6
      # The second increases the valuation of a4, a6
      # Since the discriminant is unchanged by these transforms,
      #   the process terminates (the valuations of the a_i are bounded)
      m  = 1
      mx = pi^2
      my = pi^2
      cp = 0
      while cp == 0
        a2t = a2 // pi
        a3t = a3 // my
        a4t = a4 // (pi * mx)
        a6t = a6 // (mx * my)

        if valuation(v, a3t^2 + 4*a6t) == 0 # discriminant is non-zero: either 2 or 0 roots
          cp = quadratic_has_root(one(K), a3t, -a6t) ? 4 : 2
        else
          if p == 2
            t = my * nth_root_mod(a6t, 2)
          else
            t = my * reduce_mod(v, -a3t * inv_2_modp)
          end
          E, = transform_rstu(E, [0, 0, t, 1])
          a1, a2, a3, a4, a6 = a_invariants(E)
          b2, b4, b6, b8 = b_invariants(E)

          my = my * pi
          m  = m + 1

          a2t = a2 // pi
          a3t = a3 // my
          a4t = a4 // (pi * mx)
          a6t = a6 // (mx * my)

          if valuation(v, a4t^2 - 4*a6t*a2t) == 0 # discriminant is non-zero: either 2 or 0 roots
            cp = quadratic_has_root(a2t, a4t, a6t) ? 4 : 2
          else
            if p == 2
              r = mx * nth_root_mod(a6t * inv_mod(v, a2t), 2)
            else
              r = mx * reduce_mod(v, -a4t * inv_mod(v, 2*a2t))
            end
            E, = transform_rstu(E, [r, 0, 0, 1])

            a1, a2, a3, a4, a6 = a_invariants(E)
            b2, b4, b6, b8 = b_invariants(E)

            mx = mx * pi
            m  = m + 1
          end
        end
      end
      return EllipticCurveLocalData(E, KodairaSymbol("I$(m)*"), vD - m - 4, cp, true)
    else  # Triple root
      # Step 8 in Silverman description
      # Lines 66-73 in Cremona description

      # Change coordinates so that the triple root is T = 0 mod p
      if p == 2
        r = b
      elseif p == 3
        r = nth_root_mod(-d, 3)
      else
        r = -b * inv_mod(v, K(3))
      end
      r = pi * reduce_mod(v, r)

      E, = transform_rstu(E, [r, 0, 0, 1])
      a1, a2, a3, a4, a6 = a_invariants(E)
      b2, b4, b6, b8 = b_invariants(E)

      # Cubic after transform must have triple root at 0
      #
      # note that we had transform involving only r (divisible by p)
      # thus the valuation of a1 is unchanged and
      # the valuation of a3 is guaranteed to be at least 2:
      #   before transform v(a1) >= 1, v(a3) >= 2 and a3 = a3 + r*a1 (recall, t = 0)
      @assert valuation(v, a2) >= 2 && valuation(v, a4) >= 3 && valuation(v, a6) >= 4

      a3t = a3 // pi^2
      a6t = a6 // pi^4

      # Test for Type IV*
      # we want x^2 + a3/pi^2*x - a6/pi^4 to have distinct roots: check discriminant valuation
      if valuation(v, a3t^2 + 4*a6t) == 0
        cp = quadratic_has_root(one(K), a3t, -a6t) ? 3 : 1
        return EllipticCurveLocalData(E, KodairaSymbol("IV*"), vD - 6, cp, true)
      end

      # Steps 9,10 in Silverman description
      # Lines 74-79 in Cremona description
      # Change coordinates so that p^3|a3, p^5|a6
      if p == 2
        t = -pi^2 * nth_root_mod(a6t, 2)
      else
        t = pi^2 * reduce_mod(v, -a3t * inv_2_modp)
      end
      E, = transform_rstu(E, [0, 0, t, 1])
      a1, a2, a3, a4, a6 = a_invariants(E)
      b2, b4, b6, b8 = b_invariants(E)

      if valuation(v, a4) < 4 # Type III*
        return EllipticCurveLocalData(E, KodairaSymbol("III*"), vD - 7, 2, true)
      end

      if valuation(v, a6) < 6 # Type II*
        return EllipticCurveLocalData(E, KodairaSymbol("II*"), vD - 8, 1, true)
      end
    end

    # Step 11 in Silverman description
    # Line 80 in Cremona description
    # at this point we have p^6|a6, and the original Weierstrass equation was not minimal
    a1 = a1 // pi
    a2 = a2 // pi^2
    a3 = a3 // pi^3
    a4 = a4 // pi^4
    a6 = a6 // pi^6
  end
end

@doc raw"""
    tates_algorithm_global(E::EllipticCurve{QQFieldElem}) -> EllipticCurve{QQFieldElem}

Return a global reduced minimal model for $E$ using Tate's algorithm.
"""
function tates_algorithm_global(E::EllipticCurve{QQFieldElem})
  delta = abs(numerator(discriminant(E)))

  # apply tates algorithm successively for all primes dividing the discriminant
  for p in sort([p for (p, e) in factor(delta)])
    E = _tates_algorithm(E, p).minimal_model
  end

  # reduce coefficients (see tidy_model)
  return tidy_model(E)
end

@doc raw"""
    tates_algorithm_global(E::EllipticCurve{T}) where T <: AbstractAlgebra.Generic.RationalFunctionFieldElem{<:FieldElem,<:PolyRingElem} -> EllipticCurve{T}

Return a model for $E$ that is minimal at all finite places using Tate's algorithm.
"""
function tates_algorithm_global(E::EllipticCurve{T}) where T <: AbstractAlgebra.Generic.RationalFunctionFieldElem{<:FieldElem,<:PolyRingElem}
  R = base_ring(base_field(E).fraction_field)

  for (p, _) in factor(R, discriminant(E))
    E = _tates_algorithm(E, p).minimal_model
  end

  return E
end

@doc raw"""
    tamagawa_number(E::EllipticCurve{QQFieldElem}, p::IntegerUnion) -> ZZRingElem
    tamagawa_number(E::EllipticCurve{AbsSimpleNumFieldElem}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> ZZRingElem

Return the local Tamagawa number for E at p.
"""
function tamagawa_number(E::EllipticCurve{QQFieldElem}, p::IntegerUnion)
  return _tates_algorithm(E, p).tamagawa_number
end

function tamagawa_number(E::EllipticCurve{AbsSimpleNumFieldElem}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  return _tates_algorithm(E, p).tamagawa_number
end

@doc raw"""
    kodaira_symbol(E::EllipticCurve{QQFieldElem}, p::IntegerUnion) -> KodairaSymbol
    kodaira_symbol(E::EllipticCurve{AbsSimpleNumFieldElem}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> KodairaSymbol

Return the reduction type of E at p using a Kodaira symbol.
"""
function kodaira_symbol(E::EllipticCurve{QQFieldElem}, p::IntegerUnion)
  return _tates_algorithm(E, p).kodaira_symbol
end

function kodaira_symbol(E::EllipticCurve{AbsSimpleNumFieldElem}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  return _tates_algorithm(E, p).kodaira_symbol
end

@doc raw"""
    tamagawa_numbers(E::EllipticCurve{QQFieldElem}) -> Vector{ZZRingElem}

Return the sequence of Tamagawa numbers for $E$ at all the
bad primes $p$ of $E$.
"""
function tamagawa_numbers(E::EllipticCurve{QQFieldElem})
  badp = bad_primes(E)
  return [tamagawa_number(E,p) for p in badp]
end

@doc raw"""
    kodaira_symbols(E::EllipticCurve{QQFieldElem}) -> Vector{KodairaSymbol}

Return the reduction types of E at all bad primes as a sequence of
Kodaira symbols
"""
function kodaira_symbols(E::EllipticCurve{QQFieldElem})
  badp = bad_primes(E)
  return [kodaira_symbol(E,p) for p in badp]
end

@doc raw"""
    tamagawa_numbers(E::EllipticCurve{QQFieldElem}) -> Vector{(AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, ZZRingElem)}

Return the sequence of Tamagawa numbers for $E$ at all the bad
prime ideals $p$ of $E$.
"""
function tamagawa_numbers(E::EllipticCurve{AbsSimpleNumFieldElem})
  badp = bad_primes(E)
  return [tamagawa_number(E,p) for p in badp]
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
    reduction_type(E::EllipticCurve{QQFieldElem}, p::IntegerUnion) -> String
    reduction_type(E::EllipticCurve{AbsSimpleNumFieldElem}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> String

Return the reduction type of E at p. It can either be good, additive,
split multiplicative or nonsplit multiplicative.
"""
function reduction_type(E::EllipticCurve{QQFieldElem}, p::IntegerUnion)
  ld = _tates_algorithm(E, p)
  return "$(ld.reduction_type)"
end

function reduction_type(E::EllipticCurve{AbsSimpleNumFieldElem}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  ld = _tates_algorithm(E, p)
  return "$(ld.reduction_type)"
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
  result = one(ZZ)
  for p in bad_primes(E)
    result = result * p^_tates_algorithm(E, p).conductor_valuation
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
    result = result * p^_tates_algorithm(E, p).conductor_valuation
  end
  return result
end

@doc raw"""
    conductor(E::EllipticCurve{T}) where {T <: AbstractAlgebra.Generic.RationalFunctionFieldElem{<:FieldElem, <:PolyRingElem}} -> Vector{Tuple{T, ZZRingElem}}

Return the conductor of $E$ as a list of pairs $(p, e)$, where $p$
is a generator of a place of bad reduction and $e$ is the conductor
valuation at that place. Finite places are represented by irreducible
polynomials (lifted to the base field of $E$) and the place at infinity by $1/t$.
"""
function conductor(E::EllipticCurve{T}) where {T <: AbstractAlgebra.Generic.RationalFunctionFieldElem{<:FieldElem, <:PolyRingElem}}
  K = base_field(E)
  R = base_ring(K.fraction_field)

  result = Tuple{T, ZZRingElem}[]
  for (p, _) in factor(R, discriminant(E))
    e = _tates_algorithm(E, p).conductor_valuation
    e > 0 && push!(result, (K(p), e))
  end
  e_inf = _tates_algorithm(E, degree).conductor_valuation
  e_inf > 0 && push!(result, (1//gen(K), e_inf))

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

function Base.show(io::IO, K::KodairaSymbol)
  print(io, _kodaira_symbol_to_string(K.ksymbol))
end

################################################################################
#
#  Reduction Type
#
################################################################################

function Base.show(io::IO, rt::EllipticCurveReduction.ReductionType)
  if rt == EllipticCurveReduction.good
    print(io, "Good")
  elseif rt == EllipticCurveReduction.split_multiplicative
    print(io, "Split multiplicative")
  elseif rt == EllipticCurveReduction.nonsplit_multiplicative
    print(io, "Nonsplit multiplicative")
  else
    print(io, "Additive")
  end
end

Base.print(io::IO, rt::EllipticCurveReduction.ReductionType) = show(io, rt)

function _reduction_type(ks::KodairaSymbol, split::Bool)
  ks.ksymbol == 1 && return EllipticCurveReduction.good
  ks.ksymbol > 4 && return (split ? EllipticCurveReduction.split_multiplicative : EllipticCurveReduction.nonsplit_multiplicative)
  return EllipticCurveReduction.additive
end

function is_multiplicative_reduction(rt::EllipticCurveReduction.ReductionType)
  return rt == EllipticCurveReduction.split_multiplicative || rt == EllipticCurveReduction.nonsplit_multiplicative
end
