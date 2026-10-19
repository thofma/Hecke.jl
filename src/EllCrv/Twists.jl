###############################################################################
#
#  Twists
#
#
#  (C) 2022 Jeroen Hanselman
#
###############################################################################

@doc raw"""
    quadratic_twist(E::EllipticCurve{T}, d::T) -> EllipticCurve{T}

Compute the quadratic twist of $E$ by $d$.
"""

# Note that d is untyped for the case of EllipticCurve over Q, where we want to
#   allow d to be Integer, or ZZRingElem, etc
# Specializing to EllipticCurve{QQFieldElem} causes method ambiguity, so d is left untyped
function quadratic_twist(E::EllipticCurve{T}, d) where T<: FieldElem
  K = base_field(E)
  a1, a2, a3, a4, a6 = a_invariants(E)

  if characteristic(K) != 2 # multiplicative twist, have degree 2 when d is non-square
    a2_ = a2*d   + a1^2 *  (d   - 1) // 4
    a4_ = a4*d^2 + a1*a3 * (d^2 - 1) // 2
    a6_ = a6*d^3 + a3^2 *  (d^3 - 1) // 4
    return elliptic_curve(K, [a1, a2_, a3, a4_, a6_])
  else                      # additive twist, have degree 2 when Tr(d) = 1
    a2_ = a2 + a1^2*d
    a6_ = a6 + a3^2*d
    return elliptic_curve(K, [a1, a2_, a3, a4, a6_])
  end
end

# An element of K^* whose class generates K^*/(K^*)^n, for n dividing |K| - 1:
# K^* being cyclic, one that is an l-th power for no prime l dividing n. The
# twists of a curve with j = 0 or 1728 correspond to K^*/(K^*)^n, so the powers
# 1, a, ..., a^(n - 1) of such an element give one twist each. gen(K) need not
# be one: it is a power when the defining polynomial of K is not primitive, and
# for a prime field it is 0, 1 or not defined. The search is deterministic, so
# the twists are the same models on every call; it tries gen(K) + k first,
# which in even degree avoids the prime field, all of whose elements are
# squares, and over a prime field it tries 1, 2, ...
function _twisting_element(K::FinField, n::Int)
  es = [divexact(order(K) - 1, l) for l in prime_divisors(n)]
  is_generator(a) = !iszero(a) && all(e -> !isone(a^e), es)
  g = absolute_degree(K) == 1 ? zero(K) : gen(K)
  k = 0
  while k < characteristic(K)
    is_generator(g + k) && return g + k
    k += 1
  end
  for a in K
    is_generator(a) && return a
  end
  error("K^* has no generator modulo n-th powers; n does not divide |K| - 1")
end

# The first element of K, in its iteration order, of non-zero absolute trace.
function _nonzero_trace_element(K::FinField)
  return first(a for a in K if !iszero(absolute_tr(a)))
end

@doc raw"""
    quadratic_twist(E::EllipticCurve{FinFieldElem}) -> EllipticCurve{FinFieldElem}

Compute the unique quadratic twist of $E$, the same model on every call.
"""
function quadratic_twist(E::EllipticCurve{T}) where T<: FinFieldElem
  K = base_field(E)

  if characteristic(K) != 2 # twist-by-d has degree 2 when d is non-square
    return quadratic_twist(E, _twisting_element(K, 2))
  end

  # in characteristic 2 twist-by-d has degree 2 when absolute trace of d is 1
  return quadratic_twist(E, _nonzero_trace_element(K))
end

#Test if we can't sometimes get two isomorphic curves
@doc raw"""
    quadratic_twists(E::EllipticCurve{FinFieldElem}}) -> Vector{EllipticCurve{FinFieldElem}}

Compute all quadratic twists of $E$.
"""
function quadratic_twists(E::EllipticCurve{T}) where T<: FinFieldElem

  return [E, quadratic_twist(E)]

end

function supersingular_twists2(E::EllipticCurve{T}) where T<: FinFieldElem
#Adapted from Magma code
  K = base_field(E)
  # the absolute degree: over a relative extension, degree(K) is relative
  if isodd(absolute_degree(K))
    return EllipticCurve{T}[elliptic_curve(K, [0, 0, 1, 0, 0]), elliptic_curve(K, [0, 0, 1, 1, 0]), elliptic_curve(K, [0, 0, 1, 1, 1]) ]
  end

  # u generates K^*/(K^*)^3, which has order 3 in even degree
  u = _twisting_element(K, 3)
  c = _nonzero_trace_element(K)
  #First three curves
  part_1 = EllipticCurve{T}[elliptic_curve(K, [0, 0, 1, 0, 0]), elliptic_curve(K, [0, 0, 1, c, 0]), elliptic_curve(K, [0, 0, 1, 0, c]) ]
  #The other four
  part_2 = EllipticCurve{T}[elliptic_curve(K, [0, 0, a, 0, a^2*b]) for (a, b) in [[u, 0], [inv(u), 0], [u, c], [inv(u), c]]]
  return vcat(part_1, part_2)
end


function supersingular_twists3(E::EllipticCurve{T}) where T<: FinFieldElem
#Adapted from Magma code
    K = base_field(E)
    # the absolute degree: over a relative extension, degree(K) is relative
    d = absolute_degree(K)

    if mod(d, 3) != 0
        c = one(K)
    else
      c = _nonzero_trace_element(K)
    end

    if isodd(d)
      return EllipticCurve{T}[elliptic_curve(K, [1,0]), elliptic_curve(K, [-1, 0]), elliptic_curve(K, [-1, c]), elliptic_curve(K, [-1, -c]) ];
    end
    # u generates K^*/(K^*)^4, which has order 4 in even degree
    u = _twisting_element(K, 4)
    #First four curves
    part_1 = EllipticCurve{T}[elliptic_curve(K, [-u^i,0]) for i in (0:3)]
    part_2 = EllipticCurve{T}[elliptic_curve(K, [-1,c]), elliptic_curve(K, [-u^2,(u^3)*c])]
    return vcat(part_1, part_2)

end

@doc raw"""
    twists(E::EllipticCurve{FinFieldElem}}) -> Vector{EllipticCurve{FinFieldElem}}

Return the twists of $E$: one curve in each isomorphism class over the base
field of the curves with the $j$-invariant of $E$, the same models on every
call.
"""
function twists(E::EllipticCurve{T}) where T<: FinFieldElem
#Adapted from Magma code
   K = base_field(E);
   p = characteristic(K)
   j = j_invariant(E)
   if j != 0 && j != 1728
      return EllipticCurve{T}[E, quadratic_twist(E)]
   elseif p == 2
      return supersingular_twists2(E)
   elseif p == 3
      return supersingular_twists3(E)
   elseif j == 0
      n = gcd(6, order(K)-1)
      a = _twisting_element(K, Int(n))
      c4, c6 = c_invariants(E)
      c = -c6//864
      return EllipticCurve{T}[ elliptic_curve(K, [0,c*a^i]) for i in (0:n-1) ]
   elseif j == 1728
      n = gcd(4, order(K)-1)
      a = _twisting_element(K, Int(n))
      c4, c6 = c_invariants(E)
      c = -c4//48;
      return EllipticCurve{T}[ elliptic_curve(K, [c*a^i,0]) for i in (0:n-1)]
   end
   #This can never happen:
   error("There is a bug in twists.")
end

@doc raw"""
    is_twist(EEllCrv, EllipticCurve) -> Bool

Return true if $F$ is a twist of $E$
"""
function is_twist(E::EllipticCurve, F::EllipticCurve)

  return j_invariant(E) == j_invariant(F)
end



