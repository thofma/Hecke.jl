###############################################################################
#
#  Isogenies
#
#
#  (C) 2022 Jeroen Hanselman
#
###############################################################################

mutable struct Isogeny{T} <: Map{EllipticCurve, EllipticCurve, HeckeMap, Isogeny} where T<: RingElem
  header::MapHeader{EllipticCurve{T}, EllipticCurve{T}}
  domain::EllipticCurve{T}
  codomain::EllipticCurve{T}
  coordx::RingElem
  coordy::RingElem
  phi::RingElem
  omega::RingElem
  psi::RingElem
  degree::Int

  function Isogeny(E::EllipticCurve{T}) where T<:RingElem
    r = new{T}()
    r.domain = E
    return r
  end
end

function Isogeny(E::EllipticCurve{T}, psi::RingElem) where T<:RingElem
  r = Isogeny(E)

  #Normalize and set kernel polynomial
  R = parent(psi)
  psi = numerator(psi//R(leading_coefficient(psi)))
  r.psi = psi

  #Compute codomain and maps
  r.codomain, phi, omega, r.degree = isogeny_kernel_polynomial(E, psi)
  Ry = parent(omega)
  r.coordx = phi//psi^2
  r.coordy = Ry(omega)//Ry(psi^3)

  #Set header
  r.header = MapHeader(E, r.codomain)
  return r
end


#Maybe this can be done more efficiently
function is_kernel_polynomial(E::EllipticCurve{T}, f::PolyRingElem{T}, check::Bool = false) where T
  @req base_ring(f) === base_field(E) "Polynomial and elliptic curve must be defined over same field"

  #Assume f to be square-free


  tor_2 = division_polynomial_univariate(E, 2)[1]
  ker_G = gcd(f, tor_2)

  #2-torsion can only be of degree 0, 1 or 3
  if degree(ker_G) == 2
    return false
  end

  #Kernel can't be cyclic if we have full 2-torsion
  if degree(ker_G)==3 && check
    return false
  end

  #First we kill all the 2-torsion
  while (0 != degree(ker_G))
    phi = Isogeny(E, ker_G)
    f = push_through_isogeny(phi, f)
    E = codomain(phi)

    tor_2 = division_polynomial_univariate(E, 2)[1]
    ker_G = gcd(f, tor_2)
  end

  #Now we check if the corresponding isogeny factors through some
  #multiplication by m map.
  d = ZZRingElem(2*degree(f) + 1)
  n = Hecke.squarefree_part(d)
  m = sqrt(div(d, n))

  M = divisors(m)
  c = length(M)
  psi_m = division_polynomial_univariate(E, M[c])[1]
  #Kill the non-cyclic part
  for i in (c-1:-1:1)
    if degree(gcd(psi_m, f)) == degree(psi_m)
      break
    end
    psi_m = division_polynomial_univariate(E, M[i])[1]
  end
  #If we have a non_cyclic part return false
  if degree(psi_m) != 0 && check
    return false
  end

  phi_m = Isogeny(E, psi_m)
  f = push_through_isogeny(phi_m, f)
  E = codomain(phi_m)

  #Now the remainder should give us a cyclic isogeny
  #Check if the remaining cyclic part actually defines an isogeny
  d = 2*degree(f)+1
  L = sort(prime_divisors(d))
  while (!isempty(L))
    p = L[1]
    tor_p = division_polynomial_univariate(E, p)[1]
    ker_G = gcd(f, tor_p)
    if !is_prime_cyclic_kernel_polynomial(E, p, f)
      return false
    end

    phi = Isogeny(E, ker_G)
    f = push_through_isogeny(phi, f)
    E = codomain(phi)
    d = 2*degree(f)+1
    L = sort(prime_divisors(d))
  end

  return true

end




@doc raw"""
    is_prime_cyclic_kernel_polynomial(E::EllipticCurve, p::IntegerUnion, f::PolyRingElem)

Return whether `E` has a cyclic isogeny of with kernel polynomial
`f`.
"""
function is_cyclic_kernel_polynomial(E::EllipticCurve, f::PolyRingElem)
  return is_kernel_polynomial(E, f, true)
end

function is_prime_cyclic_kernel_polynomial(E::EllipticCurve, p::IntegerUnion, f::PolyRingElem)
  @req base_ring(f) === base_field(E) "Polynomial and elliptic curve must be defined over the same field"
  @req is_prime(p) || p ==1 "p needs to be prime"
  m2 = div(p, 2)

  # The polynomial f must have degree (m-1)/2 (m odd) or degree `m/2` (m even)
  # Moreover, for every root x of f, mu(x) is a root of f, where mu is the
  # multiplication by a map, and a runs over generators of (ZZ/m)^*/{1, -1}

  if degree(f) != m2
    return false
  end

  if p == 1
    return true
  end

  # Quotient ring R[x]/(f)
  S = residue_ring(parent(f), f)[1]
  xbar = S(gen(parent(f)))

  # Test if the p-division polynomial is a multiple of f by computing it in the quotient:
  g, _ = division_polynomial_univariate(E, p, xbar)

  if !iszero(g)
    return false
  end

  if p == 2 || p == 3
    return true
  end

  # For each a in a set of generators of (Z/pZ)^*/{1, -1}  we check that the
  # multiplication-by-a map permutes the roots of f.
  Zp = residue_ring(ZZ, p)[1]
  U, mU = unit_group(Zp)
  Q, UtoQ = quo(U, [mU\(Zp(-1))])
  for g in gens(Q)
    a = lift(mU(UtoQ\(g)))
    mu = multiplication_by_m_numerator(E, a, xbar) *
      inv(multiplication_by_m_denominator(E, a, xbar))
    if !iszero(evaluate(f, mu))
      return false
    end
  end
  return true
end

#Currently only works for kernels do not contain 4-torsion. Kernels need to be checked for correctness. Input polynomial needs to be separable.
@doc raw"""
    isogeny_from_kernel(E::EllipticCurve, psi::RingElem) -> Isogeny

Compute the isogeny $\phi$: $E$ -> $E'$ where the kernel of $\phi$ contains
the points whose $x$-coordinates are roots of the input polynomial $\psi$.
"""
function isogeny_from_kernel(E::EllipticCurve, psi::RingElem)
  return Isogeny(E, psi)
end

#Input polynomial needs to be separable. (2^r-torsion is allowed however)
@doc raw"""
    isogeny_from_kernel_factored(E::EllipticCurve, psi::RingElem) -> Isogeny

Compute the isogeny $\phi$: $E$ -> $E'$ where the kernel of $\phi$ contains
the points whose $x$-coordinates are roots of the input polynomial $\psi$.
Return an array of isogenies whose composition equals the isogeny with the given
kernel. The factorisation is determined in the following way: The first maps
will purely contain 2-torsion points in the kernel. When there is no 2-torsion left
the remaining maps will consist of an isogeny with kernel contained in the p-torsion
for every prime divisor p of the degree of the isogeny.
"""
function isogeny_from_kernel_factored(E::EllipticCurve, psi::RingElem)
  isogeny_list = Isogeny[]

  kernel = psi
  domain = E

  #First compute all isogenies containing 2-torsion
  tor_2 = division_polynomial_univariate(domain, 2)[1]
  ker_G = gcd(kernel, tor_2)

  while (0 != degree(ker_G))

    phi = Isogeny(domain, ker_G)
    push!(isogeny_list, phi)
    kernel = push_through_isogeny(phi, kernel)
    domain = codomain(phi)

    tor_2 = division_polynomial_univariate(domain, 2)[1]
    ker_G = gcd(kernel, tor_2)
  end

  #Then the other isogenies
  d = 2*degree(kernel)+1
  L = sort(prime_divisors(d))

  while (!isempty(L))
    n = L[1]
    tor_n = division_polynomial_univariate(domain, n)[1]
    ker_G = gcd(kernel, tor_n)
    phi = Isogeny(domain, ker_G)
    push!(isogeny_list, phi)
    kernel = push_through_isogeny(phi, kernel)
    domain = codomain(phi)
    d = 2*degree(kernel)+1
    L = sort(prime_divisors(d))
  end
  return isogeny_list
end


@doc raw"""
    degree(f::Isogeny) -> Int

Return the degree of the isogeny $f$.
"""
function degree(f::Isogeny)
  return f.degree
end

@doc raw"""
    isogeny_map_psi(f::Isogeny) -> Poly

Return the kernel polynomial defining the isogeny $f$.
"""
function isogeny_map_psi(f::Isogeny)
  return f.psi
end

@doc raw"""
    isogeny_map_psi_squared(f::Isogeny) -> Poly

Return the denominator of the first coordinate of $f$,
which will usually be the square of the kernel polynomial
(unless the kernel contains 2-torsion, in which case it will almost be a square)
"""
function isogeny_map_psi_squared(f::Isogeny)
  return denominator(f.coordx)
end

@doc raw"""
    isogeny_map_phi(f::Isogeny) -> Poly

Return the polynomial phi defining the isogeny $f$.
"""
function isogeny_map_phi(f::Isogeny)
  return numerator(f.coordx)
end

@doc raw"""
    isogeny_map_omega(f::Isogeny) -> Poly

Return the polynomial omega defining the isogeny $f$.
"""
function isogeny_map_omega(f::Isogeny)
  return numerator(f.coordy)
end

@doc raw"""
    image(phi::Isogeny, P::EllipticCurvePoint) -> EllipticCurvePoint

Return $\phi(P)$.
"""
function image(f::Isogeny, P::EllipticCurvePoint)
  @assert domain(f) == parent(P)
  x = P.coordx
  y = P.coordy

  if evaluate(isogeny_map_psi(f),x) == 0
    return infinity(codomain(f))
  end

  coordx = f.coordx
  coordy = f.coordy

  phix = evaluate(coordx, x)
  phiy = evaluate(evaluate(coordy,y), x)

  return codomain(f)([phix, phiy])
end

@doc raw"""
    image(fs::Vector{Isogeny}, P::EllipticCurvePoint) -> EllipticCurvePoint

Return phi_n \circ phi_(n-1) \circ phi_1(P) where fs is a list of compatible
isogenies [phi_1, ..., phi_n].
"""
function image(fs::Vector{Isogeny}, P::EllipticCurvePoint)

  for f in fs
    @assert domain(f) == parent(P)
    P = image(f, P)
  end
  return P
end

@doc raw"""
    push_through_isogeny(f::Isogeny, v::RingElem) -> RingElem

Let $f:E \to E'$ be an isogeny and let S be the set of points on E
whose x-coordinate is a root of v. Assume that the kernel polynomial of f
divides v. Return the polynomial psi whose roots are exactly the x-coordinates
of the points $Q$ in $f(S)$.
"""
function push_through_isogeny(f::Isogeny, v::RingElem)

  #The kernel polynomial of f needs to divide v
  R = parent(isogeny_map_psi(f))
  v = divexact(v(gen(R)), isogeny_map_psi(f))

  phi = isogeny_map_phi(f)
  psi_sq = isogeny_map_psi_squared(f)
  Rxy, (x,y) = polynomial_ring(base_ring(phi), 2)
  pol1 = phi(x) - psi_sq(x)*y
  pol2 = v(x)
  L = factor(resultant(pol1, pol2, 1))
  return prod([f for (f,e) in L], init = one(Rxy))(0,gen(parent(phi)))
end

#TODO Need check that we don't need to compose with an automorphism to get the actual dual. Currently we will get the dual up
#to automorphism. Also need to carefully see what happens when the curve is supersingular and we compute the dual of frobenius
@doc raw"""
    dual_isogeny(psi::Isogeny) -> Isogeny

Return the dual isogeny of psi. Currently only works for separable isogenies.
"""
function dual_isogeny(psi::Isogeny)

  E = domain(psi)
  d = degree(psi)
  K = base_field(E)

  if K(d) == 0
    error("Cannot compute duals of separable isogenies yet.")
  end

  psi_d = division_polynomial_univariate(E, d)[1]
  psinew = push_through_isogeny(psi, psi_d)
  psihat = isogeny_from_kernel(codomain(psi), psinew)

  trans = isomorphism(codomain(psihat), E)

  psihat_up_to_auto = psihat * trans

  #Compute the first coefficients of psi and psihat
  scalar_psi = coeff(formal_isogeny(psi, 5), 1)
  scalar_psihat = coeff(formal_isogeny(psihat_up_to_auto, 5), 1)

  #Their product needs to be equal to the degree of phi (i.e. the first coefficient of the multiplication by m map)
  scalar = scalar_psi*scalar_psihat//d
  if scalar != one(base_field(E))
    aut_E = automorphism_list(E)

    for s in aut_E
      u = isomorphism_data(s)[4]
      if u == scalar
        return psihat_up_to_auto *s
      end
    end
    error("There is a bug in dual isogeny")
  end
  return psihat_up_to_auto
end

#Might need some tweaks in characteristic 2. Also might be inefficient inefficient, but it works.
@doc raw"""
    dual_of_frobenius(psi::Isogeny) -> Isogeny

Return the dual of frobenius.
"""
function dual_of_frobenius(E)

  supsing = is_supersingular(E)

  a1, a2, a3, a4, a6 = a_invariants(E)
  f = Isogeny(E)
  K = base_field(E)
  p = characteristic(K)

  f.codomain = E
  f.degree = p

  p = characteristic(base_field(E))
  phim = multiplication_by_m_map(E, p)
  psi = isogeny_map_psi(phim)
  phi = isogeny_map_phi(phim)
  omega = isogeny_map_omega(phim)
  Kxy = parent(omega)
  y = gen(Kxy)
  x = gen(base_ring(Kxy))

  #The omega part is written as omega0(x^p) + y^p*(omega1(x^p))
  #We find omega1 by dividing the y-part by the y-part of y^p mod f(x, y)
  #Then we use this to compute omega0.

  #If the curve is supersingular the dual of Frobenius will be an automorphism composed with Frobenius,
  #so we write y^(p^2) = f(x) +y*g(x) to find the automorphism
  #Otherwise it will be a separable isogeny and it suffices to find f and g such that
  #y^p = = f(x) +y*g(x)
  if supsing
    yp = lift(residue_ring(Kxy, y^2 +a1*x*y + a3*y - x^3 - a2*x^2 - a4*x -a6)[1](y^(p^2)))
  else
    yp = lift(residue_ring(Kxy, y^2 +a1*x*y + a3*y - x^3 - a2*x^2 - a4*x -a6)[1](y^p))
  end

  omega1 = divexact(coefficients(omega)[1], coefficients(yp)[1])
  omega0 = coefficients(omega)[0] - coefficients(yp)[0] * omega1

  dual_psi = defrobenify(psi, p)
  dual_phi = defrobenify(phi, p)

  dual_omega0= defrobenify(omega0, p)
  dual_omega1= defrobenify(omega1, p)


  f.coordx = dual_phi//(dual_psi)^2
  f.coordy = (dual_omega0 + dual_omega1*y)//(Kxy(dual_psi))^3

  f.psi = dual_psi
  f.header = MapHeader(E, f.codomain)
  if supsing
    return f*frobenius_map(E)
  else
    return f
  end
end


@doc raw"""
    identity_isogeny((E::EllipticCurve) -> Isogeny

Return the isogeny corresponding to the identity map on $E$
"""
function identity_isogeny(E::EllipticCurve)
  return isomorphism_to_isogeny(identity_map(E))
end

@doc raw"""
    multiplication_by_m_map((E::EllipticCurve, m::Int) -> Isogeny

Return the isogeny corresponding to the multiplication by m map on $E$
"""
function multiplication_by_m_map(E::EllipticCurve, m::S) where S<:Union{Integer, ZZRingElem}

  if m==1
    return isomorphism_to_isogeny(identity_map(E))
  end

  p = characteristic(base_field(E))

  if !is_simplified_model(E)
    F, pre_iso, post_iso = simplified_model(E)
    return pre_iso * multiplication_by_m_map(F, m) * post_iso
  end

  Kx, x = polynomial_ring(base_field(E), "x")
  Kxy, y = polynomial_ring(Kx, "y")

  mult_mx = multiplication_by_m_numerator(E, m, x)//multiplication_by_m_denominator(E, m, x)
  mult_my = multiplication_by_m_y_coord(E, m)

  mul_m = Isogeny(E)
  mul_m.coordx = mult_mx
  mul_m.coordy = mult_my
  mul_m.degree = m^2

  #This feels superfluous. Maybe division polynomials need to be cached somehow
  psi_temp = division_polynomial_univariate(E, m)[1]
  mul_m.psi = divexact(psi_temp, leading_coefficient(psi_temp))
  mul_m.codomain = E
  mul_m.header = MapHeader(E, E)

  return mul_m
end

#If the input is a polynomial of the form f(x^p) this returns f(x).
#Warning: The function will not give an error if f is not of the form f(x^p)
function defrobenify(f::RingElem, p, rmax::Int = -1)

  if is_zero(f)
    return f
  end

  p = Int(p)
  nonzerocoeffs = [coefficients(f)[i]!=0 ? i : 0 for i in (0:p:degree(f))]
  pr = gcd(nonzerocoeffs)

  if is_zero(pr)
    return f
  end

  r = valuation(pr, p)
  if rmax >= 0 && rmax < r
    r = rmax
    pr = p^r
  end

  R = parent(f)
  x = gen(R)

  return sum([coefficients(f)[pr*i]*x^i for i in (0:div(degree(f), pr))])

end


@doc raw"""
    frobenius_map(E::EllipticCurve{FinFieldElem}) -> Isogeny

Return the Frobenius map on E.
"""
function frobenius_map(E::EllipticCurve{T}) where T<:FinFieldElem
  return frobenius_map(E, 1)
end

@doc raw"""
    frobenius_map(E::EllipticCurve{FinFieldElem}, n::Int) -> Isogeny

Return the $n$-th power of the Frobenius map on E.
"""
function frobenius_map(E::EllipticCurve{T}, n) where T<:FinFieldElem
  f = Isogeny(E)
  K = base_field(E)
  p = characteristic(K)
  pn = p^n
  Rx, x = polynomial_ring(K, "x")
  Rxy, y = polynomial_ring(Rx, "y")
  f.codomain = E
  f.degree = pn
  f.coordx = x^pn//1
  f.coordy = y^pn//1
  f.psi = one(Rx)
  f.header = MapHeader(E, f.codomain)
  return f
end


@doc raw"""
    rational_maps(I::Isogeny) -> [Poly, Poly]

Return the rational maps defining the isogeny.
"""
function rational_maps(I::Isogeny)
  fnum = to_bivariate(numerator(I.coordx))
  fdenom = to_bivariate(denominator(I.coordx))
  gnum = to_bivariate(numerator(I.coordy))
  gdenom = to_bivariate(denominator(I.coordy))

  Ix = fnum//fdenom
  Iy = gnum//gdenom

  return [Ix, Iy, one(parent(Ix))]
end

function Base.getindex(f::Isogeny, i::Int)
  @req 1 <= i <= 3 "Index must be 1, 2 or 3"

  return rational_maps(f)[i]
end

################################################################################
#
#  Show
#
################################################################################


function show(io::IO, f::Isogeny)
  E1 = domain(f)
  E2 = codomain(f)
  fx, fy = rational_maps(f)
  print(io, "Isogeny from
  $(E1) to \n
  $(E2) given by \n
  (x : y : 1) -> ($(fx) : $(fy) : 1 )")
end

@doc raw"""
    compose(I1::Isogeny, I2::Isogeny) -> Isogeny

Return composition $I2 \circ I1$.
"""
function compose(I1::Isogeny, I2::Isogeny)
#Maybe this can be done better. Currently I just evaluate and recalculate phi, omega and psi based on numerator and
#denominator

  @assert codomain(I1) == domain(I2)

  E = domain(I1)
  F = codomain(I2)

  newx = I1.coordx
  newy = I1.coordy
  Rxy = parent(newy)

  tempx = evaluate(I2.coordx, newx)


  newx_overy = Rxy(numerator(newx))//Rxy(denominator(newx))


  tempomega_num = numerator(I2.coordy)
  tempomega_denom = denominator(I2.coordy)

  omega_num = sum( [evaluate(tempomega_num.coeffs[i + 1], newx_overy)*newy^i for i in (0:length(tempomega_num.coeffs) - 1)])

  omega_denom = evaluate(tempomega_denom.coeffs[1], newx_overy)

  #To compute the kernel polynomial psi, we need to factor out the 2-torsion part first before we can take the square of the denominator

  psi_2 = division_polynomial_univariate(E, 2)[1]

  R = parent(psi_2)
  psitemp = denominator(tempx)(gen(R))
  psi_2 = numerator(psi_2//R(leading_coefficient(psi_2)))
  psi_G = gcd(psi_2, psitemp)
  if (0 != degree(psi_G))
    newpsi = psi_G*sqrt(divexact(psitemp, psi_G))
  else
    newpsi = sqrt(psitemp)
  end


  E = domain(I1)
  F = codomain(I2)

  f = Isogeny(E)
  f.coordx = evaluate(I2.coordx, newx)
  f.coordy = omega_num//omega_denom
  f.psi = newpsi

  f.codomain = F
  f.degree = I1.degree*I2.degree
  f.header = MapHeader(E, F)
  return f
end

@doc raw"""
    compose(fs::Vector{Isogeny}) -> Isogeny

Return the composition phi_n \circ phi_(n-1) \circ phi_1 where fs is a list of compatible
isogenies [phi_1, ..., phi_n].
"""
function compose(fs::Vector{Isogeny})
  g = fs[1]
  n = length(fs)
  for i in (2:n)
    g = g*fs[i]
  end
  return g
end

function ^(phi::Isogeny, n::Int)

  res = identity_isogeny(E)

  for i in (1:n)
    res = phi*res
  end
  return res
end

@doc raw"""
    is_isogenous(E::EllipticCurve, F::EllipticCurve) -> Bool

Return true when $E$ and $F$ are isogenous. Currently only implemented for
curves over finite fields.
"""
function is_isogenous(E::EllipticCurve{T}, F::EllipticCurve{T}) where T<:FinFieldElem
  return order(E) == order(F)
end


#Algorithm uses Kohel's formulas for isogenies. Based on implementation in Sage described
#in Daniel Shumow's thesis: Isogenies of Elliptic Curves: A Computational Approach
function isogeny_kernel_polynomial(E::EllipticCurve, psi)

#TODO: Test if polynomial defines a possible kernel, i.e. it needs to be monic, separable, defined over the base field and its roots (in the alg. closure)
#need to be x-coordinates of torsion points on the curve

  R = parent(psi)

  psi_G = gcd(division_polynomial_univariate(E, 2, gen(R))[1], psi)
  # force this polynomial to be monic
  psi_G = numerator(psi_G//R(leading_coefficient(psi_G)))

  if (0 != degree(psi_G))
    psi_quo = numerator((psi//psi_G))
      if (degree(psi_quo)!=0)
          throw(DomainError(psi, "In order to use Kohel's algorithm, a kernel of even degree needs to be contained in the two torsion."))
      end
    phi, omega, v, w, n, d = even_kernel_polynomial(E,psi)
  else
    phi, omega, v, w, n, d = odd_kernel_polynomial(E,psi)
  end
  phi = phi
  psi = psi
  return compute_codomain(E,v,w), phi, omega, d
end

function even_kernel_polynomial(E::EllipticCurve, psi_G)
  R = parent(psi_G)
  x = gen(R)
  psi_2tor = division_polynomial_univariate(E,2, x)[1]
  if  mod(psi_2tor,psi_G) != 0
    throw(DomainError(psi_G,"Does not define a finite subgroup of the elliptic curve."))
  end
  n = degree(psi_G)
  d = n+1
  K = base_field(E)
  char = characteristic(K)


  Kxy,y = polynomial_ring(R,"y")


  a1, a2, a3, a4, a6 = a_invariants(E)
  b2, b4, b6 = b_invariants(E)

  if n == 1
    x0 = constant_coefficient(-psi_G)

    # determine y0
    if (2 == characteristic(base_field(E)))
      y0 = sqrt(x0^3 + a2*x0^2 + a4*x0 + a6)
    else
      y0 = -(a1*x0 + a3)//2
      v = (3*x0^2 + 2*a2*x0 + a4 - a1*y0)
      w = x0*v

      phi = (x*psi_G + v)*psi_G
      omega = (y*psi_G^2 - v*(a1*psi_G + (y - y0)))*psi_G
    end
  elseif (3 == n)
    s = coefficients(psi_G)
    s1 = -s[n-1]
    s2 = s[n-2]
    s3 = -s[n-3]

    dpsi_G = derivative(psi_G)
    ddpsi_G = derivative(dpsi_G)

    phi = (dpsi_G^2) + (-2*ddpsi_G + (4*x - s1))*psi_G
    dphi = derivative(phi)

    psi_2 = 2*y + a1*x + a3

    omega = (psi_2*(dphi*psi_G - phi*dpsi_G) - (a1*phi + a3*psi_G)*psi_G)//2

    phi = phi*psi_G
    omega = omega*psi_G

    v = 3*(s1^2 - 2*s2) + b2*s1//2 + 3*b4//2
    w = 3*(s1^3 - 3*s1*s2 + 3*s3) + b2*(s1^2 - 2*s2)//2 + b4*s1//2
  else
     throw(DomainError(psi_G, "Input polynomial must be of degree 1 or 3."))
  end
return phi, omega, v, w, n, d
end


function odd_kernel_polynomial(E, psi)
  n = degree(psi)
  d = 2*n+1

  #@req is_kernel_polynomial(E, d, psi) "Kernel polynomial does not seem to define a cyclic isogeny"

  char = characteristic(base_field(E))

  a1, a2, a3, a4, a6 = a_invariants(E)
  b2, b4, b6 = b_invariants(E)

  R = parent(psi)
  x = gen(R)

  Rxy,y = polynomial_ring(R,"y")
  psi_2 = 2*y + a1*x + a3

  psicoeffs = coefficients(psi)


  s1 = s2 = s3 = 0

  if (1 <= n)
    s1 = -psicoeffs[n-1]
  end
  if (2 <= n)
    s2 = psicoeffs[n-2]
  end
  if (3 <= n)
    s3 = -psicoeffs[n-3]
  end

  #Variables for computing the codomain
  v = 6*(s1^2 - 2*s2) + b2*s1 + n*b4
  w = 10*(s1^3 - 3*s1*s2 + 3*s3) + 2*b2*(s1^2 - 2*s2) + 3*b4*s1 + n*b6

  dpsi = derivative(psi)
  ddpsi = derivative(dpsi)

  phi = (4*x^3 + b2*x^2 + 2*b4*x + b6)*(dpsi^2 - ddpsi*psi) - (6*x^2 + b2*x + b4)*dpsi*psi + (d*x - 2*s1)*psi^2
  dphi = derivative(phi)

  if (char!=2)
    omega = numerator(dphi*psi*psi_2//2) - phi*dpsi*psi_2 -numerator((a1*phi + a3*psi^2)*psi//2)
  else
  #Characteristic 2 case:
    if (0 < n)
      s1 = -psicoeffs[n-1]
    else
      s1 = 0
    end
    ddpsi = 0
    temp = 1
    for j in (0:n-1)
      ddpsi = ddpsi + binomial(j+2,2)*psicoeffs[j+2]*temp
      temp = x*temp
    end

    dddpsi = 0
    temp = 1
    for j in (0:n-2)
      dddpsi = dddpsi + (3*binomial(j+3,3))*psicoeffs[(j+3)]*temp
      temp = x*temp
    end

    omega = dphi*psi*y - phi*dpsi*psi_2 + ((a1*x + a3)*(psi_2^2)*(ddpsi*dpsi-dddpsi*psi) + (a1*psi_2^2 - 3*(a1*x + a3)*(6*x^2 + b2*x + b4))*dpsi*psi +(a1*x^3 + 3*a3*x^2 + (2*a2*a3 - a1*a4)*x + (a3*a4 - 2*a1*a6))*dpsi^2 +(-(3*a1*x^2 + 6*a3*x + (-a1*a4 + 2*a2*a3)) + (a1*x + a3)*(d*x - 2*s1) )*dpsi*psi + (a1*s1 + a3*n)*psi^2)*psi
  end
  return phi, omega, v, w, n, d
end

function compute_codomain(E::EllipticCurve, v, w)
  a1, a2, a3, a4, a6 = a_invariants(E)
  newa4 = a4 - 5*v
  newa6 = a6 - (a1^2 + 4*a2)*v - 7*w
  return elliptic_curve([a1, a2, a3, newa4, newa6])
end

function to_bivariate(f::AbstractAlgebra.Generic.Poly{S}) where S<:PolyRingElem{T} where T<:FieldElem
  Rxy = parent(f)
  Rx = base_ring(Rxy)
  R = base_ring(Rx)

  Kxy, (x, y) = polynomial_ring(R, ["x","y"])
  cx = coefficients(f)

  newf = zero(Kxy)
  for i in (0:length(cx))
    newf += cx[i](x)*y^i
  end

  return newf
end

function to_bivariate(f::PolyRingElem{T}) where T<:FieldElem

  K = base_ring(f)

  Kxy, (x, y) = polynomial_ring(K, ["x","y"])

  return f(x)
end

