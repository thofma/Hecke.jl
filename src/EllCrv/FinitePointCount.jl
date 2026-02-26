################################################################################
#
#         EllipticCurve/FinitePointCount.jl : Counting points on elliptic curves
#                                             over finite fields
#
################################################################################

################################################################################
#
# Order via exhaustive search
#
################################################################################

@doc raw"""
    order_via_exhaustive_search(E::EllipticCurve{FinFieldElem) -> ZZRingElem

Calculate the number of points on an elliptic curve $E$ over a finite field
$\mathbf Z/p\mathbf Z$ using exhaustive search.
"""
function order_via_exhaustive_search(E::EllipticCurve{T}) where T<:FinFieldElem
  R = base_field(E)
  order = ZZ(1)
  a1, a2, a3, a4, a6 = a_invariants(E)
  Ry, y = polynomial_ring(R,"y")
  for x = R
    f = y^2 +a1*x*y + a3*y - x^3 - a2*x^2 - a4*x - a6
    ys = roots(f)
    order += length(ys)
  end

  return order
end

################################################################################
#
# Order via Legendre symbol
#
################################################################################

# Th. 4.14
@doc raw"""
    order_via_legendre(E::EllipticCurve{EuclideanRingResidueRingElem{ZZRingElem}) -> ZZRingElem

Calculate the number of points on an elliptic curve $E$ over a finite field
$\mathbf Z/p\mathbf Z$ using the Legendre symbol. It is assumed that $p$ is
prime.
"""
function order_via_legendre(E::EllipticCurve{T}) where T<:FinFieldElem
  R = base_field(E)
  p = characteristic(R)
  q = order(R)
  @req p != 0 "Base field must be finite"
  @req p == q "Finite field must have degree 1"

  if !E.short
    E = short_weierstrass_model(E)[1]
  end
  _, _, _, a4, a6 = a_invariants(E)

  s = ZZ(0)
  x = ZZ(0)
  while x < p
    C = x^3 + a4*x + a6
    s = s + jacobi_symbol(lift(ZZ, C), p)
    x = x + 1
  end

  return p + 1 + s
end

################################################################################
#
#  Hasse interval
#
################################################################################

@doc raw"""
    hasse_interval(E::EllipticCurve) -> (ZZRingElem, ZZRingElem)

Given an elliptic curve $E$ over a finite field $\mathbf F$, return an array
`[l, b]` of integers, such that $l \leq \#E(\mathbf F) \leq b$ using
Hasse's theorem.

# Examples

```jldoctest
julia> E = elliptic_curve(GF(3), [1, 2]);

julia> hasse_interval(E)
(0, 8)
```
"""
function hasse_interval(E::EllipticCurve{<: FinFieldElem})
  R = base_field(E)
  characteristic(R) == 0 && error("Base field must be finite")
  q = order(R)
  s = isqrtrem(q)[1] # sqrt(q) rounded down

  l = q + 1 - 2*(s + 1)
  b = q + 1 + 2*(s + 1)

  return l, b
end

################################################################################
#
#  Order via BSGS
#
################################################################################

@doc raw"""
    order_via_bsgs(E::EllipticCurve) -> Vector{ZZRingElem}

Returns a vector of candidates for the number of points on an elliptic curve $E$ given
over a finite field $\mathbf{F}_q$, using the Baby-step Giant-step method. If
$q$ is prime, and if $q > 229$, then the order is determined uniquely by this algorithm.
It is assumed that the characteristic is not 2.
"""
function order_via_bsgs(E::EllipticCurve{T}) where T<:FinFieldElem
  R = base_field(E)
  p = characteristic(R)
  p == 0 && error("Base field must be finite")

  q = order(R)

  if (p == 2)
    error("Characteristic must not be 2")
  end
  #char also not 3 right?
  if E.short == false
    E = short_weierstrass_model(E)[1]
  end

  Nposs = ZZ(1)
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
    candidates = ZZRingElem[]
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
    N = (divrem(l, Nposs)[1] + 1) * Nposs
    output = [N]
  end

  if (p == q) && (p > 229) && (length(output) != 1)
  # group order is uniquely determined, but by quadratic twist

    d = R(0)
    boolie = true
    while boolie # get a quadratic non-residue mod p
      d = rand(R)
      if is_square(d)[1] == false
        boolie = false
      end
    end
    _, _, _, a4, a6 = a_invariants(E)
    Eprime = elliptic_curve([a4*d^2, a6*d^3]) # quadratic twist
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

# prepare division polynomials: n = -1 .. l+1
# WARNING: this is essentially a copy of divpol_g_short, but uses different convention
#   for even n: f_n = Psi_n / y (like in Schoof paper)
# to compute [k]P we need f[k-2], ..., f[k+2]
# thus for k in [1,l-1] we need to precompute f[-1], ..., f[l+2]
# WARNING: since we start f_n from n = -1, we always add 2 for indexing
function _generate_division_polynomials_for_schoof(x::PolyRingElem{T}, a4::T, a6::T, l::Integer) where T<:FinFieldElem
  @assert l >= 3

  Rx = parent(x)
  R  = base_ring(Rx)
  @assert R == parent(a4) && R == parent(a6)

  inv_2 = inv(R(2))
  f_sqr = (x^3 + a4*x + a6)^2

  fn = Array{elem_type(Rx)}(undef, l+3)
  fn[-1 + 2] = -one(Rx)
  fn[ 0 + 2] = zero(Rx)
  fn[ 1 + 2] = one(Rx)
  fn[ 2 + 2] = 2*one(Rx)
  fn[ 3 + 2] = 3*x^4 + 6*a4*x^2 + 12*a6*x - a4^2
  fn[ 4 + 2] = 4*(x^6 + 5*a4*x^4 + 20*a6*x^3 - 5*a4^2*x^2 - 4*a4*a6*x - 8*a6^2 - a4^3)
  for n = 5:l+1
    if mod(n, 2) == 0
      m = divexact(n, 2)
      fn[n + 2] = ( fn[m + 2] * (fn[m+2 + 2]*fn[m-1 + 2]^2 - fn[m-2 + 2]*fn[m+1 + 2]^2) ) * inv_2
    else
      m = divexact(n-1, 2)
      part1 = fn[m+2 + 2] * fn[m + 2]^3
      part2 = fn[m-1 + 2] * fn[m+1 + 2]^3
      if mod(m, 2) == 0
        fn[n + 2] = f_sqr * part1 - part2
      else
        fn[n + 2] = part1 - f_sqr * part2
      end
    end
  end

  return fn
end

@doc raw"""
    order_via_schoof(E::EllipticCurve) -> ZZRingElem

Given an elliptic curve $E$ over a finite field $\mathbf{F}$,
this function computes the order of $E(\mathbf{F})$ using Schoof's algorithm
The characteristic must be $5$ or greater.
"""
function order_via_schoof(E::EllipticCurve{T}) where T<:FinFieldElem
  R = base_field(E)
  q = order(R)
  p = characteristic(R)

  @req p != 0 "Base field must be finite"
  @req p >= 5 "Characteristic must be 5 or greater"

  if !E.short
    E = short_weierstrass_model(E)[1]
  end

  # generates set of primes S such that
  # 1. characteristic p is not in S
  # 2. product of elements of S is larger than the Hasse interval length
  hasse_length = 4*(isqrtrem(q)[1] + 1)

  # note that we need to know the largest prime in S, to know the limit on division polynomials
  l = 1

  S = ZZRingElem[]
  S_product = 1
  while S_product < hasse_length
    l = next_prime(l)
    if l != p
      push!(S, l)
      S_product = S_product * l
    end
  end

  # prepare data
  Rx, x = polynomial_ring(R, :x, cached = false)
  _, _, _, a4, a6 = a_invariants(E)
  div_poly = _generate_division_polynomials_for_schoof(x, a4, a6, l)

  t_mod_l = ZZRingElem[_trace_of_frobenius_mod_l_schoof(E, div_poly, x, a4, a6, Int(l)) for l in S]
  t = crt_signed(t_mod_l, crt_env(S))

  return q + 1 - t
end

# Schoof algorithm is best formulated in terms of Jacobian coordinates
# these compute coordinate functions [n]P = (X : y*Y : Z)
# writing y^2 = F(x), we have
# even n: X = 4*F * (x*F*f[n]^2 - f[n-1]*f[n+1])
#         Y = y * 2*F * (f[n+2]*f[n-1]^2 - f[n-2]*f[n+1]^2)
#         Z = 2 * F*f[n]
# odd  n: X = 4 * (x*f[n]^2 - F*f[n-1]*f[n+1])
#         Y = y * 2 * (f[n+2]*f[n-1]^2 - f[n-2]*f[n+1]^2)
#         Z = 2 * f[n]
# NOTE: usually the formulae are written with Z = f[n] or Z = F*f[n]
#       resulting in 4 in the denominator in Y (and without 4 in numerator in X)
#       we keep it this way to avoid extra divisions
# NOTE: we pass division polynomials individually, because we need
#   to compute both [n]P and [n]phi(P), and the latter needs q-th powers of division polynomials
function _kP_jacobian_x(k::Integer, x::T, F::T, f_km1::T, f_k::T, f_kp1::T) where T <: EuclideanRingResidueRingElem{FqPolyRingElem}
  if iseven(k)
    return 4 * F * (x * F * f_k^2 - f_km1 * f_kp1)
  else
    return 4 * (x * f_k^2 - F * f_km1 * f_kp1)
  end
end
function _kP_jacobian_y(k::Integer, F::T, f_km2::T, f_km1::T, f_kp1::T, f_kp2::T) where T <: EuclideanRingResidueRingElem{FqPolyRingElem}
  if iseven(k)
    return 2 * F * (f_kp2 * f_km1^2 - f_km2 * f_kp1^2)
  else
    return 2 * (f_kp2 * f_km1^2 - f_km2 * f_kp1^2)
  end
end
function _kP_jacobian_z(k::Integer, F::T, f_k::T) where T <: EuclideanRingResidueRingElem{FqPolyRingElem}
  if iseven(k)
    return 2 * F * f_k
  else
    return 2 * f_k
  end
end

function _trace_of_frobenius_mod_l_schoof(E::EllipticCurve{T}, div_poly::AbstractVector{<:PolyRingElem{T}}, x::PolyRingElem{T}, a4::T, a6::T, l::Integer) where T <: FinFieldElem
  Rx = parent(x)
  R  = base_ring(Rx)
  @assert R == parent(a4) && R == parent(a6)
  @assert R == base_field(E)

  q = order(R)
  f = x^3 + a4*x + a6

  # |E| = t mod 2, so t = 0 mod 2 iff E has non-trivial 2-torsion point
  # this is equivalent to f having a root that is (x^q - x, f) != 1
  if l == 2
    return isone(gcd(f, powermod(x, q, f) - x)) ? ZZ(1) : ZZ(0)
  end

  fl = div_poly[l + 2]
  Rx_fl = residue_ring(Rx, fl)[1]

  # from here on we do ALL calculation modulo f_l
  x = Rx_fl(x)
  f = Rx_fl(f)

  Z = Native.GF(l, cached = false)
  k = Int(mod(q, l))

  # tiny helper to simplify indexing division polynomials, and bringing to residue ring
  function _div_poly(n::Integer)
    return Rx_fl(div_poly[n + 2])
  end

  f_km2, f_km1  = _div_poly(k-2), _div_poly(k-1)
  f_k           = _div_poly(k)
  f_kp1, f_kp2  = _div_poly(k+1), _div_poly(k+2)

  # first check if phi^2(P) == +-kP for *some* point P
  # for this we need to compare only x-coordinates
  Frob_X  = x^q
  Frob2_X = Frob_X^q
  # for q = 2n+1, y^q = y * y^{2n} = y * f^n
  # y(phi(x)) = y * Frob_Y
  Frob_Y = f^divexact(q-1, 2)

  # compute Jacobian coordinates of [k]P
  kP_X = _kP_jacobian_x(k, x, f, f_km1, f_k, f_kp1)
  kP_Y = _kP_jacobian_y(k,    f, f_km2, f_km1, f_kp1, f_kp2)
  kP_Z = _kP_jacobian_z(k,    f, f_k)

  h_x = (Frob2_X * kP_Z^2 - kP_X).data
  if !isone(gcd(h_x, fl))  # case 1 in schoof original paper
    is_square, w_mod = is_square_with_sqrt(Z(k))
    if !is_square # t = 0 mod l is the only possibility
      return ZZ(0)
    end
    w = w_mod.data >= 0 ? Int(w_mod.data) : l + Int(w_mod.data)

    # check if +-w is eigenvalue of frobenius
    f_wm1, f_w, f_wp1 = _div_poly(w-1), _div_poly(w), _div_poly(w+1)
    wP_X = _kP_jacobian_x(w, x, f, f_wm1, f_w, f_wp1)
    wP_Z = _kP_jacobian_z(w,    f, f_w)

    h_x = (Frob_X * wP_Z^2 - wP_X).data
    if isone(gcd(h_x, fl)) # +-w not an eigenvalue, so t = 0 mod l
      return ZZ(0)
    end

    # check y coordinate to determine sign
    f_wm2, f_wp2 = _div_poly(w-2), _div_poly(w+2)

    wP_Y = _kP_jacobian_y(w, f, f_wm2, f_wm1, f_wp1, f_wp2)
    h_y = (Frob_Y * wP_Z^3 - wP_Y).data
    return isone(gcd(h_y, fl)) ? -2*ZZ(w) : 2*ZZ(w)

  else # case 2
    # y^(q^2) = (y^q)^q = (y*Frob_Y)^q = y*Frob_Y * Frob_Y^q
    Frob2_Y = Frob_Y^(q+1)

    # LHS is phi^2(P) + [k]P
    # (x_1, y*y_1) + (x_2, y*y_2) = (x_3, y*y_3)
    #   point 1 is frobenius (z_1 = 1), and point 2 is [k]P (z_2 = kP_Z)
    # setting lambda = y * (y_2 - y_1)/(x_2 - x_1) we have
    # x_3 = lambda^2 - (x_1 + x_2), y_3 = (x_1 - x_3)*lambda - y_1
    #
    # we write lambda = y * LN / (LD * z_2), lambda^2 = (f * LN^2) / (LD^2 * z_2^2)
    # x_3 = [f * LN^2 - LD^2 * (x_1 + x_2)] / (z_2^2 * LD^2)
    # y_3 = (x_1 - x_3) * LN / (LD * z_2) - y_1
    LN = kP_Y - Frob2_Y * kP_Z^3
    LD = kP_X - Frob2_X * kP_Z^2
    LHS_X_numer = LN^2 * f - LD^2 * (kP_X + Frob2_X*kP_Z^2)
    LHS_X_denom = kP_Z^2 * LD^2
    LHS_Y_denom = LHS_X_denom * kP_Z * LD
    LHS_Y_numer = (Frob2_X * LHS_X_denom - LHS_X_numer)*LN - Frob2_Y * LHS_Y_denom

    # on RHS we have [tau]phi(P)
    # this involves q-th powers of division polynomials
    #   we will do a rolling update to avoid recomputing them
    f_tm2 = zero(Rx_fl)
    f_tm1, f_t, f_tp1, f_tp2 = _div_poly(-1)^q, _div_poly(0)^q, _div_poly(1)^q, _div_poly(2)^q
    f_to_q = f^q

    for tau in 1:divexact(l-1,2)
      f_tm2, f_tm1, f_t, f_tp1 = f_tm1, f_t, f_tp1, f_tp2
      f_tp2 = _div_poly(tau+2)^q

      # compute Jacobian coordinates of [tau]P
      tauP_X = _kP_jacobian_x(tau, Frob_X, f_to_q, f_tm1, f_t, f_tp1)
      tauP_Z = _kP_jacobian_z(tau,         f_to_q, f_t)

      if iszero(LHS_X_numer*tauP_Z^2 - LHS_X_denom*tauP_X)
        # we know that +- tau gives a solution. to determine sign, compare y coordinates
        tauP_Y = _kP_jacobian_y(tau, f_to_q, f_tm2, f_tm1, f_tp1, f_tp2) * Frob_Y
        return iszero(LHS_Y_numer*tauP_Z^3 - LHS_Y_denom*tauP_Y) ? ZZ(tau) : ZZ(l - tau)
      end
    end
  end
end

################################################################################
#
#  Point counting
#
################################################################################

@doc raw"""
    order(E::EllipticCurve{<: FinFieldElem}) -> ZZRingElem

Given an elliptic curve $E$ over a finite field $\mathbf{F}$, compute
$\#E(\mathbf{F})$.

# Examples

```jldoctest
julia> E = elliptic_curve(GF(101), [1, 2]);

julia> order(E)
100
```
"""
@attr ZZRingElem function order(E::EllipticCurve{T}) where T<:FinFieldElem
  R = base_field(E)
  p = characteristic(R)
  q = order(R)

  p == 0 && error("Characteristic must be nonzero")

  j_invariant(E) == 0 && return _order_j_0(E)
  p == 2 && return _order_ordinary_char2(E)
  p == 3 && return _order_ordinary_char3(E)
  j_invariant(E) == R(1728) && return _order_j_1728(E)

  A = order_via_bsgs(E)
  if length(A) == 1
    return ZZ(A[1])
  end
  return ZZ(order_via_schoof(E)) # bsgs may only return candidate list
end

# don't use @attr, because I need that the attribute has this
# name
function _order_factored(E::EllipticCurve{<:FinFieldElem})
  return get_attribute!(E, :order_factored) do
    return factor(order(E))
  end::Fac{ZZRingElem}
end

@doc raw"""
    trace_of_frobenius(E::EllipticCurve{FinFieldElem}) -> Int

Return the trace of the Frobenius endomorphism on the elliptic curve $E$
over $\mathbf{F}_q$. This is equal to $q + 1 - n$ where n is the
number of points on $E$ over $\mathbf{F}_q$.

# Examples

```jldoctest
julia> E = elliptic_curve(GF(101), [1, 2]);

julia> trace_of_frobenius(E) == 101 + 1 - order(E)
true
```
"""
function trace_of_frobenius(E::EllipticCurve{T}) where T<:FinFieldElem
  return order(base_field(E))+1 - order(E)
end

@doc raw"""
    trace_of_frobenius(E::EllipticCurve{<: FinFieldElem}, r::Int) -> ZZRingElem

Return the trace of the $r$-th power of the Frobenius endomorphism on
the elliptic curve $E$.

```jldoctest
julia> E = elliptic_curve(GF(101, 2), [1, 2]);

julia> trace_of_frobenius(E, 2)
18802
```
"""
function trace_of_frobenius(E::EllipticCurve{T}, n::Int) where T<:FinFieldElem
  K = base_field(E)
  q = order(K)
  a = q +1 - order(E)
  R, x = polynomial_ring(QQ)
  f = x^2 - a*x + q
  if is_irreducible(f)
    L, alpha = number_field(f)
    return ZZ(trace(alpha^n))
  else
    _alpha = roots(f)[1]
    return 2 * ZZ(_alpha^n)
  end
end

################################################################################
#
#  Helpers for p-adic point counting
#
################################################################################

# NOTE: residue_field(R) creates a non-cached finite field and a map using it.
#   In our context, the finite field element comes from outside, and although we
#   create a qadic_field with the same residue field, the field objects differ,
#   causing preimage(f::MapFromFunc, y) to fail its assertions.
#   Thus we lift from the residue field to the qadic field manually.
function _qadic_from_residue_element(R::QadicField, x::T; precision::Int=precision(R)) where T <: FinFieldElem
  z = R(precision=precision)
  for i in 0:degree(R)-1
    setcoeff!(z, i, lift(ZZ, coeff(x, i)))
  end
  return z
end

# Let q=p^d, and E be the elliptic curve over F_{p^m}
# If E is defined over F_q, we can compute the trace of Frobenius of E/F_{p^m} from the trace of Frobenius of E/F_{p^d}
# The recurrence is: t_k = t_1 * t_{k-1} - q * t_{k-2} with t_0 = 2,
#   where t_k is the trace of Frobenius of E/F_{q^k}
# We compute t_n with n = m/d
# see "Handbook of Elliptic and Hyperelliptic Curve Cryptography", section 17.1.2
function _trace_of_frobenius_subfield_curve(q, t_1, n::Int)
  @assert n >= 1
  t_prev = ZZ(2); t_cur = t_1
  for _ in 2:n
    t_cur, t_prev = t_1*t_cur - q*t_prev, t_cur
  end
  return t_cur
end

################################################################################
#
#  Point counting in characteristic 2
#
################################################################################

# common knowledge
# j = 0: supersingular curve
#   Canonical form is y^2 + a_3*y = x^3 + a_4*x + a_6
#   Isomorphism classes and point counts are known
# j != 0: ordinary curve
#   Canonical form is y^2 + xy = x^3 + a_2*x^2 + a_6
#   If Tr(a2) == 0, it is isomorphic to y^2 + xy = x^3 + a_6
#   Otherwise, it is isomorphic to quadratic twist of y^2 + xy = x^3 + a_6

# finds order of a supersingular elliptic curve defined over finite field of characteristic 2
# This implements sections 3.4 and 3.5 of Menezes' "Elliptic Curve Public Key Cryptosystems"
function _order_supersingular_char2(E::EllipticCurve{T}) where T <: FinFieldElem
  R = base_field(E)
  q = order(R)
  d = degree(R)

  @req characteristic(R) == 2 "Characteristic must be 2"
  @req iszero(j_invariant(E)) "Curve must be supersingular"

  # transform to canonical form: (x,y) -> (x+a_2,y)
  a3 = E.a_invariants[3]
  a4 = E.a_invariants[2]^2 + E.a_invariants[4]
  a6 = E.a_invariants[2]*E.a_invariants[4] + E.a_invariants[5]

  # this is common for both odd/even d: for a3 cube we transform to a form with a3=1
  function _update_coeffs_when_a3_cube(r::T, a4::T, a6::T)
    r_inv = divexact(one(R), r)
    return (a4*r_inv^4, a6*r_inv^6)
  end

  # see Menezes "Elliptic Curve Public Key Cryptosystems" sections 3.4 and 3.5
  _, X = polynomial_ring(R, "X", cached=false)
  if isodd(d)
    # bring to the form y^2 + y = x^3 + a_4*x + a_6
    if a3 != one(R)
      # r = cube root of a_3, (x,y) -> (r^2*x, r^3*y)
      # to find r: let q = 3k+2 [d is odd!]
      # a_3^( (q+1)/3 ) = a_3^(k+1) = r^(3k+3) = r^(q+1) = r^2
      r = sqrt(a3^(divexact(q+1,3)))
      (a4, a6) = _update_coeffs_when_a3_cube(r, a4, a6)
    end

    # 1) y^2 + y = x^3 : q+1 points
    # for s root of X^4 + X + a_4, we need t^2 + t + (s^6 + a_6) to be solvable
    # which is equivalent to Tr(s^6 + a_6) == 0
    # for a root s, s+1 is also a root and Tr((s+1)^6 + a_6) = Tr(s^6 + a_6) + 1
    # thus we only need to check for root existence
    if !isempty(roots(X^4 + X + a4))
      return q + 1
    end

    # 2) y^2 + y = x^3 + x     : q + 1 +- sqrt(2q) points with + for d = 1,7 mod 8
    # 3) y^2 + y = x^3 + x + 1 : q + 1 +- sqrt(2q) points with + for d = 3,5 mod 8
    # there should be a root s of X^4 + X + a_4 + 1
    # to distinguish curves we check if Tr(s^6 + s^2 + a_6) == 0 (then curve 2)
    ss = roots(X^4 + X + a4 + one(R))
    @assert !isempty(ss)

    sqrt_2q = ZZ(2)^divexact(d + 1, 2)
    t = iszero(tr(ss[1]^6 + ss[1]^2 + a6)) ? sqrt_2q : -sqrt_2q
    return mod(d, 8) in (1, 7) ? q + 1 + t : q + 1 - t
  else
    # check if a3 is a cube (type II and III)
    a3_cbrt = roots(X^3 - a3)
    if !isempty(a3_cbrt)
      (a4, a6) = _update_coeffs_when_a3_cube(a3_cbrt[1], a4, a6)

      function _trace_4(x)  # x + x^(2^2) + ... + x^(2^[d-2])
        ret = x; term = x
        for e in 2:2:d-2
          term = term^4
          ret = ret + term
        end
        return ret
      end

      if iszero(_trace_4(a4))
        # type III: we can assume u = 1, find root s of X^4 + X + a_4 (we have 4)
        # and check the trace of s^6 + a_6 to select a correct class
        ss = roots(X^4 + X + a4)
        @assert length(ss) == 4

        sqrt_q_times2 = ZZ(2)^(divexact(d,2)+1)
        t = iszero(tr(ss[1]^6 + a6)) ? sqrt_q_times2 : -sqrt_q_times2
        return mod(d, 4) == 2 ? q + 1 + t : q + 1 - t
      else
        # type II
        return q + 1
      end
    else
      # type I: we can assume u = 1, find root s of X^4 + a_3 X + a_4,
      # and check the Trace of [s^6 + a_6] / a_3^2 to select a correct class
      s = only(roots(X^4 + a3*X + a4))

      sqrt_q = ZZ(2)^divexact(d,2)
      t = iszero(tr(divexact(s^6+a6, a3^2))) ? sqrt_q : -sqrt_q
      return mod(d, 4) == 0 ? q + 1 + t : q + 1 - t
    end
  end
end

# Univariate AGM method of finding trace of Frobenius (in characteristic 2)
# assumes the curve is in the form E: y^2 + xy = x^3 + a_6
# assumes that j-invariant (j = a_6^{-1}) does not lie in F_4
# see "Handbook of Elliptic and Hyperelliptic Curve Cryptography", section 17.3.2.b
function _trace_of_frobenius_char2_agm(a6::T) where T <: FinFieldElem
  R = parent(a6)
  q = order(R)
  d = degree(R)

  @req characteristic(R) == 2 "Characteristic must be 2"
  @req a6^4 != a6 "j-invariant must not lie in F_4"

  # for d = 3 the Hecke bound greatly overshoots the possible values of trace
  # it is easy to precompute trace for all a_6 in F_8 \ F_2
  # 1  for t, t^2, t^2 + t
  # -3 for t+1, t^2 + 1, t^2 + t + 1
  if d == 3
    return iszero(coeff(a6, 0)) ? ZZ(1) : ZZ(-3)
  end

  N = div(d+1,2) + 3

  # WARNING: currently FLINT does not expose creating qadic context with custom modulus
  # WARNING: so for a large exponent (where Conway polynomial is not available)
  # WARNING:   the random polynomial will be used to create a context
  # WARNING: clearly it is certain to be different from the modulus used
  # WARNING:   to create the finite field over which curve is defined
  # WARNING: FLINT pr: https://github.com/flintlib/flint/pull/2550
  # WARNING: for now we err for the exponent bigger than 91 (flint limit)
  d >= 92 && error("Currently exponents above 91 are not supported")
  Qq,_ = qadic_field(2, d, precision=N, cached=false)

  # TODO: we should implement a lift from F_q to Q_q (in Nemo) directly
  # TODO: instead of going through full padic coefficients

  # z = 1 + 8*a_6 [4 digits precision]
  z = 1 + 8*_qadic_from_residue_element(Qq, a6, precision=4)

  for k in 5:N  # get k correct digits
    # iteration: z <- [1 + z] / [2 * sqrt(z)] = [(1+z)/2] / sqrt(z)
    setprecision!(z, k+1) # we divide by 2 below so we need extra digit
    z = divexact(shift_right(Qq(1, precision=k+1) + z, 1), sqrt(z))
    setprecision!(z, k) # we have z modulo 2^k
  end

  # we need Norm(2z / [1+z]) = Norm(z / ([1+z]/2) )
  setprecision!(z, N+1) # we divide by 2 below so we need extra digit
  zz = shift_right(Qq(1, precision=N+1) + z, 1)

  norm_z = norm(divexact(z, zz))
  setprecision!(norm_z, N-1) # we have norm modulo 2^(N-1)
  t = lift(ZZ, norm_z)

  if t^2 > 4*q # bring inside Hasse interval
    t = t - 2^(N-1)
  end

  return t
end

# implements Subfield Curve approach for the case of j being in F_4
# assumes E/F_{2^d}: y^2 + xy = x^3 + a_6 (j = 1/a_6)
function _trace_of_frobenius_j_nonzero_in_f4(a6::T, d::Int) where T <: FinFieldElem
  R = parent(a6)

  @req characteristic(R) == 2 "Characteristic must be 2"
  @req a6 == a6^4 "j invariant must lie in F_4"

  # j = 1: y^2 + xy = x^3 + 1
  # - for even d, we can "define" it over F_4: trace = -3
  # - for odd d, we define over F_2: trace = -1
  # j in F_4\F_2. Writing c for a generator of F_4
  # both E: y^2 + xy = x^3 + c and E': y^2 + xy = x^3 + 1/c have trace = 1 over F_4
  @assert isone(a6) || iseven(d)
  q = isone(a6) && isodd(d) ? ZZ(2) : ZZ(4)
  n = isone(a6) && isodd(d) ? d : divexact(d, 2)

  local t_1
  if isone(a6)
    t_1 = iseven(d) ? ZZ(-3) : ZZ(-1)
  else
    t_1 = ZZ(1)
  end

  return _trace_of_frobenius_subfield_curve(q, t_1, n)
end

# finds order of an ordinary elliptic curve defined over finite field of characteristic 2
# it uses the univariate AGM in general case
# if the j-invariant lies in F_4 it uses "Subfield Curve" approach
function _order_ordinary_char2(E::EllipticCurve{T}) where T <: FinFieldElem
  R = base_field(E)
  j = j_invariant(E)
  q = order(R)
  d = degree(R)

  @req characteristic(R) == 2 "Characteristic must be 2"
  @req !iszero(j) "Curve must be ordinary"

  # transform to canonical form:
  # (x,y) -> ( a_1^2 * x + a_3/a_1, a_1^3 * y + [a_1^2 * a_4 + a_3^2]/a_1^3 )
  a2 = divexact(E.a_invariants[1]^4*E.a_invariants[2] + E.a_invariants[1]^3*E.a_invariants[3], E.a_invariants[1]^6)
  a6 = inv(j)

  # compute trace of frobenius for E'
  if j^4 == j
    trace_frob = _trace_of_frobenius_j_nonzero_in_f4(a6, d)
  else
    trace_frob = _trace_of_frobenius_char2_agm(a6)
  end

  return iszero(tr(a2)) ? q + 1 - trace_frob : q + 1 + trace_frob
end

################################################################################
#
#  Point counting in characteristic 3
#
################################################################################

# common knowledge
# j = 0: supersingular curve
#   Canonical form is y^2 = x^3 + a_4*x + a_6
#   Isomorphism classes and point counts are known
# j != 0: ordinary curve
#   Canonical form is y^2 = x^3 + a_2*x^2 + a_6
#   If a_2 is a square, it is isomorphic to y^2 = x^3 + x^2 + a_6/a_2^3
#   Otherwise, it is isomorphic to quadratic twist of y^2 = x^3 + x^2 + a_6/a_2^3

# finds order of a supersingular elliptic curve defined over finite field of characteristic 3
# since no definitive source was found, a short report was created
# arxiv: http://arxiv.org/abs/2601.21756
# after the first version, we found a paper by Francois Morain
# http://www.lix.polytechnique.fr/Labo/Francois.Morain/Articles/sseclassif.ps.gz
# both classifications agree; ours is more suitable for implementation
function _order_supersingular_char3(E::EllipticCurve{T}) where T <: FinFieldElem
  R = base_field(E)
  q = order(R)
  d = degree(R)

  @req characteristic(R) == 3 "Characteristic must be 3"
  @req iszero(j_invariant(E)) "Curve must be supersingular"

  # transform to canonical form
  # change of variables (x,y) -> (x,[y-a_1x-a_3]/2)
  # transforms into y^2 = x^3 + b_2*x^2 - b_4*x + b_6 (b_i the usual values, b_2 = 0)
  a4 = -(2*E.a_invariants[4] + E.a_invariants[1]*E.a_invariants[3])
  a6 = E.a_invariants[3]^2 + E.a_invariants[5]

  # here is the short description of the process. E: y^2 = x^3 + a_4*x + a_6 (q = 3^d)
  # * d odd and -a_4 = v^4
  #   - Tr(a_6*v^(-6)) =  0: #E = q + 1
  #   - Tr(a_6*v^(-6)) =  1: #E = q + 1 +- sqrt(3*q) [+ when d = 1 mod 4]
  #   - Tr(a_6*v^(-6)) = -1: #E = q + 1 -+ sqrt(3*q) [- when d = 1 mod 4]
  # * d odd and -a_4 is not a fourth power: #E = q + 1
  # * d even and -a_4 = v^2, with v square
  #   - Tr(a_6*v^(-3))  = 0: #E = q + 1 -+ 2*sqrt(q) [- when d = 0 mod 4]
  #   - Tr(a_6*v^(-3)) != 0: #E = q + 1 +- sqrt(q)   [+ when d = 0 mod 4]
  # * d even and -a_4 = v^2, with v not a square
  #   - Tr(a_6*v^(-3))  = 0: #E = q + 1 +- 2*sqrt(q) [+ when d = 0 mod 4]
  #   - Tr(a_6*v^(-3)) != 0: #E = q + 1 -+ sqrt(q)   [- when d = 0 mod 4]
  # * d even and -a_4 is not a square: #E = q + 1

  # for d odd, being a square and a being fourth power are equivalent
  # considering gamma (sqrt of -a_4) for odd d allows us to unify the implementation
  a4_square, gamma = Nemo.is_square_with_sqrt(-a4)
  if !a4_square
    return q + 1
  end

  # trace of b in representative y^2 = x^3 - x + b (if gamma is a square)
  # or trace of b in twist y^2 = x^3 - x + b (if gamma is not a square)
  trace_b = tr(a6*inv(gamma^3))

  if isodd(d)
    # of course there is a catch to the above:
    # only one of {gamma, -gamma} is a square (giving rise to a fourth root of -a_4)
    # if gamma is not a square, gamma^3 has opposite sign to v^6, where v^4 = -a_4
    if !Nemo.is_square(gamma)
      trace_b = -trace_b
    end

    sqrt_3q = ZZ(3)^divexact(d + 1, 2)
    if iszero(trace_b)
      return q + 1
    else
      return mod(d, 4) == (isone(trace_b) ? 1 : 3) ? q + 1 + sqrt_3q : q + 1 - sqrt_3q
    end
  else
    sqrt_q = ZZ(3)^divexact(d, 2)
    typeI = Nemo.is_square(gamma)
    if iszero(trace_b)
      return mod(d, 4) == (typeI ? 2 : 0) ? q + 1 + ZZ(2)*sqrt_q : q + 1 - ZZ(2)*sqrt_q
    else
      return mod(d, 4) == (typeI ? 0 : 2) ? q + 1 + sqrt_q : q + 1 - sqrt_q
    end
  end
end

# AGM method of finding trace of Frobenius (in characteristic 3)
# assumes the curve is in the form E: y^2 = x^3 + x^2 + a_6
# assumes that j-invariant (j = -a_6^{-1}) does not lie in F_9
# see "An AGM-Type Elliptic Curve Point Counting Algorithm in Characteristic Three" by Gustavsen, Ranestad
function _trace_of_frobenius_char3_agm(j::T) where T <: FinFieldElem
  R = parent(j)
  q = order(R)
  d = degree(R)
  N = div(d, 2) + 2

  @req characteristic(R) == 3 "Characteristic must be 3"
  @req j^9 != j "j-invariant must not lie in F_9"

  # Hesse form x^3 + y^3 + 1 = dxy, d^3 = j
  D = pth_root(j)

  # WARNING: currently FLINT does not expose creating qadic context with custom modulus
  # WARNING: so for a large exponent (where Conway polynomial is not available)
  # WARNING:   the random polynomial will be used to create a context
  # WARNING: clearly it is certain to be different from the modulus used
  # WARNING:   to create the finite field over which curve is defined
  # WARNING: FLINT pr: https://github.com/flintlib/flint/pull/2550
  # WARNING: for now we err for the exponent bigger than 57 (flint limit)
  d >= 58 && error("Currently exponents above 57 are not supported")
  Q = qadic_field(3, d, precision=N, cached=false)[1]
  z = polynomial_ring(Q, "z", cached=false)[2]

  # we are solving (z + 6)^3 − (z^2 + 3*z + 9)*D_k^3 = 0
  # j(E_{D_k}) = j(\mathcal{E}^k) mod 3^{k+1}
  # the starting value of Newton iteration is the lift of d^{3^k}

  d_base = D
  D_lift = _qadic_from_residue_element(Q, d_base; precision=2)
  for k in 2:N
    d_base = d_base^3
    a = _qadic_from_residue_element(Q, d_base; precision=k)
    setprecision!(D_lift, k) # important to have proper precision of the polynomial
    D_lift = newton_lift((z + 6)^3 - (z^2 + 3*z + 9)*D_lift^3, a, k)
  end

  norm_d = norm(1 + 6*inv(D_lift))
  setprecision!(norm_d, N)

  t = lift(ZZ, norm_d)
  if t^2 > 4*q
    t = t - 3^N
  end

  return t
end

# implements Subfield Curve approach for the case of j being in F_9
# assumes E/F_{3^d}: y^2 = x^3 + x^2 + a_6 (j = -a_6^{-1})
function _trace_of_frobenius_j_nonzero_in_f9(a6::T, d) where T <: FinFieldElem
  R = parent(a6)

  @req characteristic(R) == 3 "Characteristic must be 3"
  @req a6 == a6^9 "j invariant must lie in F_9"

  # j = -1: y^2 = x^3 + x^2 + 1
  # - for even d, we can "define" it over F_9: trace = -2
  # - for odd d, we define over F_3: trace = -2
  # j = 1: y^2 = x^3 + x^2 - 1
  # - for even d, we can "define" it over F_9: trace = -5
  # - for odd d, we define over F_3: trace = 1
  # j in F_9 \ F_3: the only option is to do an embedding and compute the trace (via exhaustive search)
  j_in_F3 = isone(a6) || isone(-a6)
  @assert j_in_F3 || iseven(d)
  q = j_in_F3 && isodd(d) ? ZZ(3) : ZZ(9)
  n = j_in_F3 && isodd(d) ? d : divexact(d, 2)

  local t_1
  if isone(a6)
    t_1 = ZZ(-2)
  elseif isone(-a6)
    t_1 = iseven(d) ? ZZ(-5) : ZZ(1)
  else
    R_base,_ = finite_field(3, 2)
    a6_base = preimage(embed(R_base, R), a6)
    E = elliptic_curve(R_base, [0,1,0,0,a6])
    t_1 = q + 1 - Hecke.order_via_exhaustive_search(E)
  end

  return _trace_of_frobenius_subfield_curve(q, t_1, n)
end

# finds order of an ordinary elliptic curve defined over finite field of characteristic 3
# it uses the AGM in general case
# if the j-invariant lies in F_9 it uses "Subfield Curve" approach
function _order_ordinary_char3(E::EllipticCurve{T}) where T <: FinFieldElem
  R = base_field(E)
  j = j_invariant(E)
  q = order(R)
  d = degree(R)

  @req characteristic(R) == 3 "Characteristic must be 3"
  @req !iszero(j) "Curve must be ordinary"

  # transform to canonical form
  # change of variables (x,y) -> (x,[y-a_1x-a_3]/2)
  # transforms into y^2 = x^3 + b_2*x^2 - b_4*x + b_6 (b_i the usual values)
  # setting v = b_4/b_2, change of variables (x,y) -> (x - v, y)
  # transforms into y^2 = x^3 + a_2*x^2 + a_6 [with a_2 = b_2]
  # we consider E: y^2 = x^3 + x^2 + a_6/a_2^3, with j = -(a_6/a_2^3)^{-1}
  # NOTE: we need the value of a_2 = b_2 to determine
  # NOTE: if original curve is isomorphic to E or to its quadratic twist
  b2 = E.a_invariants[1]^2 + E.a_invariants[2]

  if j^9 == j
    trace_frob = _trace_of_frobenius_j_nonzero_in_f9(-inv(j), d)
  else
    trace_frob = _trace_of_frobenius_char3_agm(j)
  end

  return Nemo.is_square(b2) ? q + 1 - trace_frob : q + 1 + trace_frob
end

################################################################################
#
#  Point counting for j = 0
#
################################################################################

function _order_j_0(E::EllipticCurve{T}) where T <: FinFieldElem
  @req iszero(j_invariant(E)) "j-invariant must be zero"
  R = base_field(E)
  p = characteristic(R)
  q = order(R)
  d = degree(R)

  # p = 2, 3: we have a supersingular curve, dispatch to specialized procedures
  p == 2 && return _order_supersingular_char2(E)
  p == 3 && return _order_supersingular_char3(E)

  if mod(p, 3) == 2
    # supersingular: p divides trace of frobenius

    # t^2 in {0, q, 2q, 3q, 4q}, for odd d the only possibility is 0
    mod(d, 2) == 1 && return q + 1

    # p is inert in Q(sqrt(-3))
    # Frob^2 acts on y^2 = x^3 + 1 over F_{p^2} as [-p]
    # the "base" trace over F_q is then 2 (-p)^{d/2}
    base_t = (-p)^divexact(d,2)

    # from short form to y^2 = x^3 + b, with b = -c_6/864
    b = divexact(c_invariants(E)[2], -864)

    # find the twist
    w = b^divexact(q-1, 6)
    isone(w)    && return q + 1 - 2*base_t  # isomorphic
    isone(-w)   && return q + 1 + 2*base_t  # non-square - quadratic twist
    isone(w^3)  && return q + 1 +   base_t  # non-cube - cubic twist
    return                q + 1 -   base_t  # not square nor cube - sextic twist
  else
    X = polynomial_ring(ZZ, "X", cached=false)[2]
    K, t = number_field(X^2 - X + 1, :t, cached=false)
    OK = maximal_order(K)

    # p is split in Q(sqrt(-3)), p = pi*pi'
    # find pi: it is a generator of a prime above p
    principal_check, pp = is_principal_with_data(prime_decomposition(OK, p)[1][1])
    @assert principal_check "Q(sqrt(-3)) should have class order 1"

    # find associate so that pi = 1 mod 3, pi = 1 mod 2 [Norm(2) = 4]
    # this way we pick unique one out of six associates
    ot = OK(t)
    while mod(norm(pp-1), 12) != 0
      pp *= ot
    end

    # pi = a + b \zeta_6, N(pi-1) = 0 mod 12
    # we need conjugate (inverse) of primitive 6-th root of unity
    # recall that in the formula we have Tr(chi'(b) pi)
    pp_a, pp_b = coordinates(pp)
    z = divexact(R(-pp_b), R(pp_a))

    # lift to F_q
    if d > 1
      pp = pp^d
      pp_a, pp_b = coordinates(pp)
    end

    # from short form to y^2 = x^3 + b, with b = -c_6/864
    b = divexact(c_invariants(E)[2], -864)

    # find the (sextic) twist
    w = b^divexact(q-1, 6)
    isone(w)    && return q + 1 - (2*pp_a + pp_b) # Tr(pi)
    isone(-w)   && return q + 1 + (2*pp_a + pp_b) # Tr(-pi)
    w == z      && return q + 1 - (pp_a - pp_b)   # Tr(pi * \zeta_6)
    w == z^2    && return q + 1 + (pp_a + 2*pp_b) # Tr(pi * \zeta_6^2)
    w == z^4    && return q + 1 + (pp_a - pp_b)   # Tr(pi * \zeta_6^4)
    return                q + 1 - (pp_a + 2*pp_b) # Tr(pi * \zeta_6^5)
  end
end

################################################################################
#
#  Point counting for j = 1728
#
################################################################################

function _order_j_1728(E::EllipticCurve{T}) where T <: FinFieldElem
  R = base_field(E)
  @req j_invariant(E) == R(1728) "j-invariant must be 1728"

  p = characteristic(R)
  q = order(R)
  d = degree(R)

  # p = 2, 3: we have a supersingular curve, dispatch to specialized procedures
  p == 2 && return _order_supersingular_char2(E)
  p == 3 && return _order_supersingular_char3(E)

  if mod(p, 4) == 3
    # supersingular: p divides trace of frobenius

    # t^2 in {0, q, 2q, 3q, 4q}, for odd d the only possibility is 0
    mod(d, 2) == 1 && return q + 1

    # p is inert in Q(sqrt(-1))
    # Frob^2 acts on y^2 = x^3 + x over F_{p^2} as [-p]
    # the "base" trace over F_q is then 2 (-p)^{d/2}
    base_t = ZZ(2) * (-p)^divexact(d,2)

    # from short form to y^2 = x^3 - ax, with a = c_4/48
    a = divexact(c_invariants(E)[1], 48)

    # find the twist
    w = a^divexact(q-1, 4)
    isone(w)    && return q + 1 - base_t  # isomorphic
    isone(-w)   && return q + 1 + base_t  # not 4th power - quadratic twist
    return                q + 1           # not square - quartic twist
  else
    X = polynomial_ring(ZZ, "X", cached=false)[2]
    K, t = number_field(X^2 + 1, :t, cached=false)
    OK = maximal_order(K)

    # p is split in Q(sqrt(-1)), p = pi*pi'
    # find pi: it is a generator of a prime above p
    principal_check, pp = is_principal_with_data(prime_decomposition(OK, p)[1][1])
    @assert principal_check "Q(sqrt(-1)) should have class order 1"

    # find associate so that pi = 1 mod (1+i)^3 [= 2i-2]
    # this becomes for a + b*i: (a,b) = (1,0) or (3,2) mod 4
    pp_a, pp_b = coordinates(pp)
    if iseven(pp_a)
      pp_a, pp_b = -pp_b, pp_a  # mul by i
    end
    if mod(pp_a + pp_b, 4) != 1
      pp_a, pp_b = -pp_a, -pp_b # mul by i^2
    end
    pp = pp_a + pp_b*OK(t)

    # pi = a + b*i
    # we need conjugate (inverse) of primitive 4-th root of unity
    # recall that in the formula we have Tr(chi'(a) pi)
    z = divexact(R(-pp_b), R(pp_a))

    # lift to F_q
    if d > 1
      pp = pp^d
      pp_a, pp_b = coordinates(pp)
    end

    # from short form to y^2 = x^3 - ax, with a = c_4/48
    a = divexact(c_invariants(E)[1], 48)

    # find the (quartic) twist
    w = a^divexact(q-1, 4)
    isone(w)    && return q + 1 - (2*pp_a) # Tr(pi)
    isone(-w)   && return q + 1 + (2*pp_a) # Tr(-pi)
    w == z      && return q + 1 + (2*pp_b) # Tr(pi * i)
    return                q + 1 - (2*pp_b) # Tr(pi * (-i))
  end
end
