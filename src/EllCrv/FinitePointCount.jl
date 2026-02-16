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
  grouporder = ZZ(0)
  p == 0 && error("Base field must be finite")

  if p != q
    error("Finite field must have degree 1")
  end

  if E.short == false
    E = short_weierstrass_model(E)[1]
  end
  _, _, _, a4, a6 = a_invariants(E)
  x = ZZ(0)

  while x < p
    C = x^3 + a4*x + a6
    Cnew = lift(ZZ, C) # convert to ZZRingElem
    a = jacobi_symbol(Cnew, p) # can be used to compute (C/F_p) since p prime
    grouporder = grouporder + a
    x = x + 1
  end

  grouporder = grouporder + p + 1

#  return grouporder
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

@doc raw"""
    order_via_schoof(E::EllipticCurve) -> ZZRingElem

Given an elliptic curve $E$ over a finite field $\mathbf{F}$,
this function computes the order of $E(\mathbf{F})$ using Schoof's algorithm
The characteristic must not be $2$ or $3$.
"""
function order_via_schoof(E::EllipticCurve{T}) where T<:FinFieldElem
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
    B = residue_ring(ZZ, S[i], cached = false)[1]
    M_i = inv(B(n_i))
    M_i = M_i.data
    t = t + (M_i * n_i * t_mod_l[i])
  end

  t = mod(t, product)
  if t > product//2
    t = t - product
  end

  return (q + 1 - t)::ZZRingElem
end


function fn_from_schoof(E::EllipticCurve, n::Int, x)

  poly = division_polynomial_univariate(E, n, x)[2]
    if iseven(n)
      poly = 2*poly
    end

  return(poly)

end


function fn_from_schoof2(E::EllipticCurve, n::Int, x)

  R = base_field(E)
  S, y = polynomial_ring(parent(x),"y")

  f = psi_poly_field(E, n, x, y)

 # println("f: $f, $(degree(f))")
    A = E.a_invariants[4]
    B = E.a_invariants[5]

  g = x^3 + A*x + B

  if isodd(n)
    return replace_all_squares(f, g)
  else
    return replace_all_squares(divexact(f, y), g)
  end


end

#prime_set(M::Nemo.ZZRingElem, char::Nemo.ZZRingElem) -> Array{Nemo.ZZRingElem}
#  returns a set S of primes with:
# 1) char not contained in S
# 2) product of elements in S is greater than M
function prime_set(M, char)
  S = Nemo.ZZRingElem[]

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

# t_mod_prime(l::Nemo.ZZRingElem, E::EllipticCurve) -> Nemo.ZZRingElem
# determines the value of t modulo some prime l (used in Schoof's algorithm)
function t_mod_prime(l, E)
  R = base_field(E)
  q = order(R)
  q_int = Int(q)
  l = Int(l)

  S, x = polynomial_ring(R, "x")
  T, y = polynomial_ring(S, "y")
  Z = Native.GF(l, cached = false)

  _, _, _, a4, a6 = a_invariants(E)
  f = x^3 + a4*x + a6
  fl = division_polynomial_univariate(E, l, x)[2]
  if iseven(l)
    fl = 2*fl
  end
  U = residue_ring(S, fl)[1]

  PsiPoly = [] # list of psi-polynomials
  for i = -1:(l + 1)
    push!(PsiPoly, psi_poly_field(E, i, x, y)) # Psi[n] is now found in PsiPoly[n+2]
  end

  #Fnschoof = [] # list of the fn- functions # Psi[n] is now found in PsiPoly[n+2]
  #for i = -1:(l + 1)
  #  push!(Fnschoof, fn_from_schoof(E,i,x))
  #end

  #push!(PsiPoly, -one(T))
  #push!(PsiPoly, zero(T))
  #for i = 1:(l + 1)
  #  push!(PsiPoly, division_polynomial(E, i, x, y)) # Psi[n] is now found in PsiPoly[n+2]
  #end


  Fnschoof = [] # list of the fn- functions # Psi[n] is now found in PsiPoly[n+2]
  push!(Fnschoof, -one(S))
  push!(Fnschoof, zero(S))
  for i = 1:(l + 1)
    poly = division_polynomial_univariate(E, i, x)[2]
    if iseven(i)
      poly = 2*poly
    end
    push!(Fnschoof,poly)
  end

  # case where l == 2. value of t mod l determined by some gcd, see p. 124
  if l == 2
    x_q = powermod(x, q_int, f)
    ggt = gcd(f, x_q - x)
    if ggt == 1
      t = ZZ(1)
    else
      t = ZZ(0)
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
    g = U( (powermod(x, q_int^2, fl) - x) * fk^2 * f + fkme * fkpe).data
    ggT = gcd(g, fl)
  else
    g = U( (powermod(x, q_int^2, fl) - x) * fk^2 + fkme * fkpe * f).data
    ggT = gcd(g, fl)
  end

  if ggT != 1 # case 1
    if jacobi_symbol(ZZ(k), ZZ(l)) == -1
      return ZZ(0)
    else
      # need square root of q (mod l)
      w = is_square_with_sqrt(k_mod)[2]
      if w.data < 0
        w = w + l
      end
      w_int = Int(w.data)

      fw = Fnschoof[w_int+2]
      fwme = Fnschoof[w_int+1]
      fwpe = Fnschoof[w_int+3]

      if mod(w_int, 2) == 0
        g = U((powermod(x,q_int,fl) - x) * fw^2*f + fwme*fwpe).data # reduce mod fl
        ggT = gcd(g, fl)
      else
        g = U((powermod(x,q_int,fl) - x) * fw^2 + fwme*fwpe*f).data
        ggT = gcd(g, fl)
      end

      if ggT == 1
        return ZZ(0)
      else
        fwmz = Fnschoof[w_int]
        fwpz = Fnschoof[w_int+4]

        if mod(w_int, 2) == 0
          g = U(4 * powermod(f,div(q_int + 3, 2),fl)*fw^3 - (fwpz * fwme^2) + (fwmz*fwpe^2)).data
          ggT2 = gcd(g, fl)
        else
          g = U(4 * powermod(f,div(q_int - 1, 2),fl)*fw^3 - (fwpz * fwme^2) + (fwmz*fwpe^2)).data
          ggT2 = gcd(g, fl)
        end

        if ggT2 == 1
          return -2*ZZRingElem(w.data)
        else
          return 2*ZZRingElem(w.data)
        end
      end
    end
  else # case 2
    Fkmz = PsiPoly[k]
    Fkme = PsiPoly[k+1]
    Fk = PsiPoly[k+2]
    Fkpe = PsiPoly[k+3]
    Fkpz = PsiPoly[k+4]

    alpha = Fkpz*psi_power_mod_poly(k-1, E, x, y, 2, fl) - Fkmz*psi_power_mod_poly(k+1, E, x, y, 2, fl) - 4*powermod(f, div(q_int^2+1, 2), fl)*psi_power_mod_poly(k, E, x, y, 3, fl)
    beta = ((x - powermod(x, (q_int^2), fl))*psi_power_mod_poly(k, E, x, y, 2, fl)- Fkme*Fkpe)*4*y*Fk

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

      gammahelp = powermod(fntaupz*fntaume^2- fntaumz * fntaupe^2,q_int,fl)

      if mod(tau, 2) == 0
        gamma = y * powermod(f,div(q_int-1,2),fl) * gammahelp
      else
        gamma = powermod(f,q_int,fl) * gammahelp
      end

      monster1 = ((Fkme*Fkpe - psi_power_mod_poly(k, E, x, y, 2, fl)*(powermod(x, q_int^2, fl) + powermod(x, q_int, fl) + x)) * beta^2 + psi_power_mod_poly(k, E, x, y, 2, fl)*alpha^2) * psi_power_mod_poly(tau, E, x, y, 2*q_int, fl) + psi_power_mod_poly(tau-1, E, x,y,q_int,fl)*psi_power_mod_poly(tau+1, E, x,y,q_int, fl)*beta^2*psi_power_mod_poly(k, E, x, y, 2, fl)

      if divrem(degree(monster1), 2)[2] == 1
        monster1 = divexact(monster1, y)
      end

      monster1_1 = replace_all_squares_modulo(monster1, f, fl)
      monster1_2 = U(monster1_1).data # monster1_1 reduced

      if monster1_2 != 0
        tau = tau + 1
      else
        monster2 = 4*y*powermod(f,div(q_int-1,2),fl)*psi_power_mod_poly(tau,E,x,y,3*q_int,fl) * (alpha * (((2*powermod(x, q_int^2, fl) + x) * psi_power_mod_poly(k,E,x,y,2,fl) - Fkme*Fkpe )*beta^2 - alpha^2*psi_power_mod_poly(k,E,x,y,2,fl)) - y*powermod(f,div(q_int^2-1,2),fl)*beta^3 * Fk^2) - beta^3*psi_power_mod_poly(k,E,x,y,2,fl)*gamma

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


# Division polynomials in general for an elliptic curve over an arbitrary field

# standard division polynomial Psi (as needed in Schoof's algorithm)
function psi_poly_field(E::EllipticCurve, n::Int, x, y)

    R = base_field(E)
    A = E.a_invariants[4]
    B = E.a_invariants[5]

    if n == -1
        return -y^0
    elseif n == 0
        return zero(parent(y))
    elseif n == 1
        return y^0
    elseif n == 2
        return 2*y
    elseif n == 3
        return (3*x^4 + 6*(A)*x^2 + 12*(B)*x - (A)^2)*y^0
    elseif n == 4
        return 4*y*(x^6 + 5*(A)*x^4 + 20*(B)*x^3 - 5*(A)^2*x^2 - 4*(A)*(B)*x - 8*(B)^2 - (A)^3)
    elseif mod(n,2) == 0
        m = div(n,2)
        return divexact( (psi_poly_field(E,m,x,y))*(psi_poly_field(E,m+2,x,y)*psi_poly_field(E,m-1,x,y)^2 - psi_poly_field(E,m-2,x,y)*psi_poly_field(E,m+1,x,y)^2), 2*y)
    else m = div(n-1,2)
        return psi_poly_field(E,m+2,x,y)*psi_poly_field(E,m,x,y)^3 - psi_poly_field(E,m-1,x,y)*psi_poly_field(E,m+1,x,y)^3
    end
end

# computes psi_n^power mod g
function psi_power_mod_poly(n, E, x, y, power, g)

    A = E.a_invariants[4]
    B = E.a_invariants[5]

    fn = fn_from_schoof2(E, n, x)
    f = x^3 + A*x + B
    p = powermod(fn,power,g)

    if mod(n, 2) == 0
        if mod(power, 2) == 0
            p1 = powermod(f, div(power, 2), g)
        else
            p1 = powermod(f, div(power - 1, 2), g) * y
        end
    else p1 = 1
    end

    return p * p1
end


function replace_all_squares(f, g)
    # assumes that f is in Z[x,y^2] and g in Z[x]. Replaces y^2 with g.
    # the result will be in Z[x]
    z = zero(parent(g)) # this is the zero in Z[x]
    d = div(degree(f), 2) # degree of f in y^2 should be even
    for i in 0:d
        z = z + coeff(f, 2*i)*g^i
    end
    return z
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

  if p == 2
    if j_invariant(E) == 0
      return ZZ(_order_supersingular_char2(E))
    else
      return ZZ(_order_ordinary_char2(E))
    end
  end

  if p == 3
    if j_invariant(E) == 0
      return ZZ(_order_supersingular_char3(E))
    else
      return ZZ(_order_ordinary_char3(E))
    end
  end

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
  _, X = polynomial_ring(R, "X")
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
    # p is split in Q(sqrt(-3)), p = pi*pi'
    # find pi: do the prime decomposition
    X = polynomial_ring(ZZ, "X", cached=false)[2]
    K, t = number_field(X^2 - X + 1, :t, cached=false)

    OK = maximal_order(K)
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
