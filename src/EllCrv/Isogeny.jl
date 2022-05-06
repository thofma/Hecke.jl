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
rational_map, frobenius_map, isogeny_map_psi, isogeny_map_psi_squared, isogeny_map_phi, 
isogeny_map_omega, push_through_isogeny, dual_isogeny, isomorphism, isomorphism_data,
isomorphism_to_isogeny, negation_map, identity_isogeny, multiplication_by_m_map, 
automorphism_group_generators

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

function image(fs::Vector{Isogeny}, P::EllCrvPt)
  
  for f in fs
    @assert domain(f) == parent(P)
    P = image(f, P)
  end
  return P
end

function push_through_isogeny(f::Isogeny, v::RingElem)
  
  #The kernel polynomial of f needs to divide v
  v = divexact(v, isogeny_map_psi(f))
  
  phi = isogeny_map_phi(f)
  psi_sq = isogeny_map_psi_squared(f)
  Rxy, (x,y) = PolynomialRing(base_ring(phi), 2)
  pol1 = phi(x) - psi_sq(x)*y
  pol2 = v(x)
  L = factor(resultant(pol1, pol2, 1))
  return prod([f for (f,e) in L], init = one(Rxy))(0,gen(parent(phi)))
end

#TODO Need check that we don't need to compose with an automorphism to get the actual dual. Currently we will get the dual up 
#to automorphism. 
function dual_isogeny(f::Isogeny)

  d = degree(f)
  psi_d = division_polynomial_univariate(f.domain, d)[1]
  psinew = push_through_isogeny(f, psi_d)
  psihat = isogeny_from_kernel(codomain(f), psinew)
  
  trans = isomorphism(codomain(psihat), domain(f))
  
  return psihat * trans
end

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

function rational_map(I::Isogeny)
  return [I.coordx, I.coordy]
end

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
  psitemp = denominator(tempx)
  psi_2 = division_polynomial_univariate(E, 2)[1]
  
  R = parent(psi_2)
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

function compose(fs::Vector{Isogeny})
  g = fs[1]
  n = length(fs)
  for i in (2:n)
    g = g*fs[i]
  end
  return g
end

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
  

  a1,a2,a3,a4,a6 = a_invars(E)
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

function is_isogenous(E::EllCrv{T}, F::EllCrv{T}) where T<:FinFieldElem
  return order(E) == order(F)
end

function frobenius_map(E::EllCrv{T}) where T<:FinFieldElem
  return frobenius_map(E, 1)
end


function frobenius_map(E::EllCrv{T}, n) where T<:FinFieldElem
  f = Isogeny(E)
  K = base_field(E)
  p = characteristic(K)
  pn = p^n
  Rx, x = PolynomialRing(K, "x")
  Rxy, y = PolynomialRing(Rx, "y")
  f.codomain = E
  f.degree = pn
  f.coordx = x^pn
  f.coordy = y^pn
  f.psi = one(Rx)
  r.header = MapHeader(E, r.codomain)
  return f
end


###############################################################################
#
#  Isomorphisms
#
###############################################################################


mutable struct EllCrvIso{T} <:Map{EllCrv, EllCrv, HeckeMap, EllCrvIso} where T<:RingElem
  header::MapHeader{EllCrv{T}, EllCrv{T}}
  domain::EllCrv{T}
  codomain::EllCrv{T}
  data::Tuple{T, T, T, T}
  
  function EllCrvIso(E::EllCrv{T}, data::Vector{T}) where T <:RingElem
    f = new{T}()
    f.domain = E
    
    if length(data)!= 4 
      throw(DomainError(T, "Array needs to have length 4"))
    end
    r, s, t, u = data[1], data[2], data[3], data[4]
    f.data = (r, s, t, u)
    a1, a2, a3, a4, a6 = a_invars(E)

    a1new = divexact(a1 + 2*s, u)
    a2new = divexact(a2 - s*a1 + 3*r - s^2, u^2)
    a3new = divexact(a3 + r*a1 + 2*t, u^3)
    a4new = divexact(a4 - s*a3 + 2*r*a2 - (t + r*s)*a1 + 3*r^2 - 2*s*t, u^4)
    a6new = divexact(a6 + r*a4 + r^2*a2 + r^3 - t*a3 - t^2 - r*t*a1, u^6)

    F = EllipticCurve([a1new, a2new, a3new, a4new, a6new])
    f.codomain = F
    f.header = MapHeader(E, F)
    return f
  end
  
end

function identity_map(E::EllCrv)
  return isomorphism(E, [0, 0, 0, 1])
end

function identity_isogeny(E::EllCrv)
  return isomorphism_to_isogeny(identity_map(E))
end

function negation_map(E::EllCrv)
  a1, a2, a3, a4, a6 = a_invars(E)
  return isomorphism(E, [0, -a1, -a3, -1])
end

function isomorphism_data(f::EllCrvIso)

  return f.data
end

function inv(f::EllCrvIso{T}) where T<:RingElem
  
  r, s, t, u = isomorphism_data(f)
  newr = -r//u^2
  news = -s//u
  newt = (r*s-t)//u^3
  newu = 1//u
  
  g = EllCrvIso(codomain(f),[newr, news, newt, newu])
  return g
end

function isomorphism_to_isogeny(f::EllCrvIso)
  r, s, t, u = f.data
  E = f.domain
  phi = Isogeny(E)
  phi.codomain = f.codomain
  phi.degree = 1

  R = base_field(E)
  phi.psi = one(R)
  
  Rx, x = PolynomialRing(R, "x")
  phi.coordx = (x - r)//Rx(u^2)
  Rxy, y = PolynomialRing(Rx, "y")
  phi.coordy = (y - s*(x-r) - t)//Rxy(u^3)
  phi.header = f.header
  return phi
end


function compose(f::Isogeny, g::EllCrvIso)
  return compose(f, isomorphism_to_isogeny(g))
end 

function compose(g::EllCrvIso, f::Isogeny)
  return compose(isomorphism_to_isogeny(g), f)
end 


function isomorphism(E::EllCrv{T}, data::Vector{T}) where T

 if length(data)!= 4 
      throw(DomainError(T, "Array needs to have length 4"))
 end
 return EllCrvIso(E, data)
end

function isomorphism(E::EllCrv, data::Vector)

 if length(data)!= 4 
      throw(DomainError(T, "Array needs to have length 4"))
 end
 
 K = base_field(E)
 data = map(K, data)
 
 return EllCrvIso(E, data)
end

function degree(f::EllCrvIso)
  return 1
end

function image(f::EllCrvIso, P::EllCrvPt)
  @assert domain(f) == parent(P)
  F = codomain(f)
  if !isfinite(P)
    return infinity(F)
  end
  r, s, t, u = isomorphism_data(f)
  xnew = divexact(1, u^2)*(P.coordx - r)
  ynew = divexact(1, u^3)*(P.coordy - s*u^2*xnew - t)
  Q = F([xnew, ynew])
  return Q
end

function preimage(f::EllCrvIso, P::EllCrvPt)
  @assert codomain(f) == parent(P)
  E = domain(f)
  if !isfinite(P)
    return infinity(E)
  end
  r, s, t, u = isomorphism_data(f)
  xnew = u^2*P.coordx + r
  ynew = u^3*P.coordy + s*u^2*P.coordx + t
  Q = E([xnew, ynew])
  return Q
end

function compose(f::EllCrvIso, g::EllCrvIso)
  r1, s1, t1, u1 = f.data
  r2, s2, t2, u2 = g.data
  
  r3 = r1 + u1^2*r2
  s3 = s1 + u1*s2 
  t3 = t1 + u1^2*s1*r2 + u1^3*t2
  u3 = u1*u2
  
  return isomorphism(domain(f), [r3, s3, t3, u3]) 

end

function automorphism_group_generators(E::EllCrv)
  K = base_field(E)
  char = characteristic(K)
  j = j_invariant(E)
  
  #Group is Z/2Z
  if j!= 0 && j!= 1728
    aut = abelian_group(2)
    return [negation_map(E)] 
  end
  
  Kx, x = PolynomialRing(K)
  
  Es, pre_iso, post_iso = simplified_model(E)
  a1, a2, a3, a4, a6 = a_invars(Es)
  if char!=2 && char!=3
    if j == 1728
      f = x^2+1
      a = roots(f)
      if !isempty(roots(f)) 
        #Group is Z/4Z
        i = a[1]
        return [pre_iso * isomorphism(Es, [0, 0, 0, i]) * post_iso]
      end
    elseif j == 0
      f = x^2+x+1
      
      a = roots(f)
      if !isempty(roots(f)) 
        #Group is Z/6Z
        zeta3 = a[1]
        return [pre_iso * isomorphism(Es, [0, 0, 0, -zeta3]) * post_iso]
      end
    end
    #Group is Z/2Z
    return [negation_map]
  end
  
  if char == 3 #And j-invariant is 0.
    us = roots(x^2 + 1)  #See if x^4 + 1 = (x^2 +1)*(x^2 -1) has a root that induces an element of order 4
    if !isempty(us)
      rs = roots(x^3 + a4*x + 2*a6) 
      i = us[1]
        if !isempty(rs) 
          # Group is dicyclic group of order 12. <a, b | a^6 = b^4 = id, a^3 = b^2, bab^(-1) = a^(-1)>
          r = rs[1]
          return [pre_iso * isomorphism(Es, [r, 0, 0, -1]) * post_iso, pre_iso * isomorphism(Es, [r, 0, 0, i]) * post_iso]
        else
          #Group is Z/4Z
          return [pre_iso * isomorphism(Es, [0, 0, 0, i]) * post_iso]
        end
    else
      rs = roots(x^2 + a4) #Now u^2 = 1, so x^3 + a4*x + a6 - u^6*a6 = x*(x^2+a4)
      if !isempty(rs)
      #Group is Z/6Z 
        r = rs[1]
        return [pre_iso * isomorphism(Es, [0, 0, 0, -r]) * post_iso]
      end
    end
    #Group is Z/2Z
    return [negation_map(E)]
  end
  
  if char == 2 #And j-invariant is 0
    auts = EllCrvIso[]
    us = roots(x^2 + x +1) #Check if there are us other than u = 1.
    if !isempty(us)
      u = us[1]
      g = x^4 + a3*x + (1+u)*a4
      ss = roots(g)
      for s in ss
        h = x^2 + a3*x + s^6 + a4*s^2
        ts = roots(h)
        for t in ts
          push!(auts, pre_iso * isomorphism(Es, [s^2, s, t, u]) * post_iso)
        end
      end
    end
    size = length(auts)
    if size == 8 #Group is SL(2,3)
      #Search for generators. One element of order 3 and one element of order 4 should suffice.
      #Element of order 3
      for phi in auts
        phi3 = phi * phi * phi
        if phi3 == identity_map(Es)
          g1 = phi
        end
      end
      #Element of order 4. Need to take u = 1.
      g = x^3 + a3*x 
      s = roots(g)[1]
      h = x^2 + a3*x + s^6 + a4*s^2
      t = roots(h)[1]
      
      g2 = pre_iso * isomorphism(Es, [s^2, s, t, 1]) * post_iso
      
      return [g1, g2] 
    elseif size == 2 #Group is Z/6Z
      g1 = auts[1]
      g2 = auts[2]
      if (g1 * g1 * g1) != identity_element(Es)
        return g1
      else
        return g2
      end
    end
  else
      #u = 1
    auts = EllCrvIso[]
    g = x^3 + a_3 
    ss = roots(g)
    for s in ss
      h = x^2 + a3*x + s^6 + a4*s^2
      ts = roots(h)
      for t in ts
        push!(auts, pre_iso * isomorphism(Es, [s^2, s, t, 1]) * post_iso)
      end
    end
    size = length(auts)
    if size == 6 #Group isomorphic to Quaternions
      if auts[1] == inv(auts[2])
        return [auts[1], auts[3]]
      else
        return [auts[1], auts[2]]
      end
    elseif size == 2 # Group isomorphic to Z/4Z
      return [auts[1]]
    end
  #Group is Z/2Z
  return [negation_map(E)]
  end
end

function rational_map(f::EllCrvIso)
  K = base_field(domain(f))
  Kx, x = PolynomialRing(K, "x")
  Kxy, y = PolynomialRing(Kx, "y")
  r, s, t, u = f.data
  xnew = divexact(1, u^2)*(x - r)
  ynew = divexact(1, u^3)*(y - s*u^2*xnew - t)
  return [xnew, ynew]
end


@doc Markdown.doc"""
    ==(f::EllCrvIso, g::EllCrvIso) -> Bool

Return true if $f$ and $g$ define the same map over the same field.
"""
function ==(f::EllCrvIso, g::EllCrvIso) where T
  Ef = domain(f)
  Eg = domain(g)
  return f.data == g.data && Ef == Eg && base_field(Ef) == base_field(Eg)
end


