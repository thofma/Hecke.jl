###############################################################################
#
#  Isogenies
#
#
#  (C) 2022 Jeroen Hanselman
#
###############################################################################

export Isogeny

export isogeny_from_kernel, isogeny_from_kernel_factored, degree, image,
rational_maps, frobenius_map, isogeny_map_psi, isogeny_map_psi_squared, isogeny_map_phi, 
isogeny_map_omega, push_through_isogeny, dual_isogeny, identity_isogeny, multiplication_by_m_map


mutable struct Isogeny{T} <: Map{EllCrv, EllCrv, HeckeMap, Isogeny} where T<: RingElem
  header::MapHeader{EllCrv{T}, EllCrv{T}}
  domain::EllCrv{T}
  codomain::EllCrv{T}
  coordx::RingElem
  coordy::RingElem
  phi::RingElem
  omega::RingElem
  psi::RingElem
  degree::Int
  
  function Isogeny(E::EllCrv{T}) where T<:RingElem
    r = new{T}()
    r.domain = E
    return r
  end
end

function Isogeny(E::EllCrv{T}, psi::RingElem) where T<:RingElem
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

#Currently only works for kernels do not contain 4-torsion. Kernels need to be checked for correctness. Input polynomial needs to be separable.
@doc Markdown.doc"""
    isogeny_from_kernel(E::EllCrv, psi::RingElem) -> Isogeny

Compute the isogeny $\phi$: $E$ -> $E'$ where the kernel of $\phi$ contains 
the points whose $x$-coordinates are roots of the input polynomial $\psi$.
"""
function isogeny_from_kernel(E::EllCrv, psi::RingElem)
  return Isogeny(E, psi)
end

#Input polynomial needs to be separable. (2^r-torsion is allowed however)
@doc Markdown.doc"""
    isogeny_from_kernel_factored(E::EllCrv, psi::RingElem) -> Isogeny

Compute the isogeny $\phi$: $E$ -> $E'$ where the kernel of $\phi$ contains 
the points whose $x$-coordinates are roots of the input polynomial $\psi$.
Return an array of isogenies whose composition equals the isogeny with the given 
kernel. The factorisation is determined in the following way: The first maps
will purely contain 2-torsion points in the kernel. When there is no 2-torsion left
the remaining maps will consist of an isogeny with kernel contained in the p-torsion
for every prime divisor p of the degree of the isogeny.
"""
function isogeny_from_kernel_factored(E::EllCrv, psi::RingElem)
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


@doc Markdown.doc"""
    degree(f::Isogeny) -> Int

Return the degree of the isogeny $f$.
"""
function degree(f::Isogeny)
  return f.degree
end

@doc Markdown.doc"""
    isogeny_map_psi(f::Isogeny) -> Poly

Return the kernel polynomial defining the isogeny $f$.
"""
function isogeny_map_psi(f::Isogeny)
  return f.psi
end

@doc Markdown.doc"""
    isogeny_map_psi_squared(f::Isogeny) -> Poly

Return the denominator of the first coordinate of $f$, 
which will usually be the square of the kernel polynomial 
(unless the kernel contains 2-torsion, in which case it will almost be a square)
"""
function isogeny_map_psi_squared(f::Isogeny)
  return denominator(f.coordx)
end

@doc Markdown.doc"""
    isogeny_map_phi(f::Isogeny) -> Poly

Return the polynomial phi defining the isogeny $f$.
"""
function isogeny_map_phi(f::Isogeny)
  return numerator(f.coordx)
end

@doc Markdown.doc"""
    isogeny_map_omega(f::Isogeny) -> Poly

Return the polynomial omega defining the isogeny $f$.
"""
function isogeny_map_omega(f::Isogeny)
  return numerator(f.coordy)
end

@doc Markdown.doc"""
    image(phi::Isogeny, P::EllCrvPt) -> EllCrvPt

Return $\phi(P)$.
"""
function image(f::Isogeny, P::EllCrvPt)
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

@doc Markdown.doc"""
    image(fs::Vector{Isogeny}, P::EllCrvPt) -> EllCrvPt

Return phi_n \circ phi_(n-1) \circ phi_1(P) where fs is a list of compatible
isogenies [phi_1, ..., phi_n].
"""
function image(fs::Vector{Isogeny}, P::EllCrvPt)
  
  for f in fs
    @assert domain(f) == parent(P)
    P = image(f, P)
  end
  return P
end

@doc Markdown.doc"""
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
  Rxy, (x,y) = PolynomialRing(base_ring(phi), 2)
  pol1 = phi(x) - psi_sq(x)*y
  pol2 = v(x)
  L = factor(resultant(pol1, pol2, 1))
  return prod([f for (f,e) in L], init = one(Rxy))(0,gen(parent(phi)))
end

#TODO Need check that we don't need to compose with an automorphism to get the actual dual. Currently we will get the dual up 
#to automorphism. Also need to carefully see what happens when the curve is supersingular and we compute the dual of frobenius
@doc Markdown.doc"""
    dual_isogeny(f::Isogeny) -> Isogeny

Return the dual isogeny of f. Currently only returns the dual up to automorphism.
"""
function dual_isogeny(f::Isogeny)

  d = degree(f)
  psi_d = division_polynomial_univariate(f.domain, d)[1]
  psinew = push_through_isogeny(f, psi_d)
  psihat = isogeny_from_kernel(codomain(f), psinew)
  
  trans = isomorphism(codomain(psihat), domain(f))
  
  return psihat * trans
end

@doc Markdown.doc"""
    identiy_isogeny((E::EllCrv) -> Isogeny

Return the isogeny corresponding to the identity map on $E$
"""
function identity_isogeny(E::EllCrv)
  return isomorphism_to_isogeny(identity_map(E))
end

@doc Markdown.doc"""
    multiplication_by_m_map((E::EllCrv, m::Int) -> Isogeny

Return the isogeny corresponding to the multiplication by m map on $E$
"""
function multiplication_by_m_map(E::EllCrv, m::S) where S<:Union{Integer, fmpz}

  if m==1
    return isomorphism_to_isogeny(identity_map(E))
  end
  
  a1, a2, a3 = a_invars(E)

  Kx, x = PolynomialRing(base_field(E), "x")
  Kxy, y = PolynomialRing(Kx, "y")
  
  mult_mx = multiplication_by_m_numerator(E, m, x)//multiplication_by_m_denominator(E, m, x)
  mult_mx_deriv = derivative(mult_mx)

  x = Kxy(x)
  mult_mxy = multiplication_by_m_numerator(E, m, x)//multiplication_by_m_denominator(E, m, x)
  mult_mx_derivy = numerator(mult_mx_deriv)(x)//denominator(mult_mx_deriv)(x)
  
  mult_my = ((2*y+a1*x+a3)*mult_mx_derivy//m - a1*mult_mxy-a3)//2

  mul_m = Isogeny(E)
  mul_m.coordx = mult_mx
  mul_m.coordy = mult_my
  mul_m.degree = m^2
  
  #This feels superfluous. Maybe division polynomials need to be cached somehow
  mul_m.psi = division_polynomial_univariate(E, m)[1]
  mul_m.codomain = E
  mul_m.header = MapHeader(E, E)

  return mul_m
end

@doc Markdown.doc"""
    frobenius_map(E::EllCrv{FinFieldElem}) -> Isogeny

Return the Frobenius map on E.
"""
function frobenius_map(E::EllCrv{T}) where T<:FinFieldElem
  return frobenius_map(E, 1)
end

@doc Markdown.doc"""
    frobenius_map(E::EllCrv{FinFieldElem}, n::Int) -> Isogeny

Return the $n$-th power of the Frobenius map on E.
"""
function frobenius_map(E::EllCrv{T}, n) where T<:FinFieldElem
  f = Isogeny(E)
  K = base_field(E)
  p = characteristic(K)
  pn = p^n
  Rx, x = PolynomialRing(K, "x")
  Rxy, y = PolynomialRing(Rx, "y")
  f.codomain = E
  f.degree = pn
  f.coordx = x^pn//1
  f.coordy = y^pn//1
  f.psi = one(Rx)
  f.header = MapHeader(E, f.codomain)
  return f
end


@doc Markdown.doc"""
    rational_maps(I::Isogeny) -> [Poly, Poly]

Return the rational maps defining the isogeny.
"""
function rational_maps(I::Isogeny)
  return [I.coordx, I.coordy]
end

@doc Markdown.doc"""
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
  
  omega_num = evaluate(tempomega_num.coeffs[1], newx_overy) + evaluate(tempomega_num.coeffs[2], newx_overy)*newy
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

@doc Markdown.doc"""
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

@doc Markdown.doc"""
    is_isogenous(E::EllCrv, F::EllCrv) -> Bool

Return true when $E$ and $F$ are isogenous. Currently only implemented for 
curves over finite fields.
"""
function is_isogenous(E::EllCrv{T}, F::EllCrv{T}) where T<:FinFieldElem
  return order(E) == order(F)
end


#Algorithm uses Kohel's formulas for isogenies. Based on implementation in Sage described
#in Daniel Shumow's thesis: Isogenies of Elliptic Curves: A Computational Approach
function isogeny_kernel_polynomial(E::EllCrv, psi)

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

function even_kernel_polynomial(E::EllCrv, psi_G)
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
  

  Kxy,y = PolynomialRing(R,"y")
  

  a1, a2, a3, a4, a6 = a_invars(E)
  b2, b4, b6 = E.b_invars

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

  char = characteristic(base_field(E))

  a1, a2, a3, a4, a6 = a_invars(E)
  b2, b4, b6 = b_invars(E)
  
  R = parent(psi)
  x = gen(R)
  
  Rxy,y = PolynomialRing(R,"y")
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

function compute_codomain(E::EllCrv, v, w)
  a1, a2, a3, a4, a6 = a_invars(E)
  newa4 = a4 - 5*v
  newa6 = a6 - (a1^2 + 4*a2)*v - 7*w
  return EllipticCurve([a1, a2, a3, newa4, newa6])  
end


