###############################################################################
#
#  Isogenies
#
#
#  (C) 2022 Jeroen Hanselman
#
###############################################################################

export Isogeny

export isogeny_from_kernel, domain, codomain, degree, image

mutable struct Isogeny
  domain::EllCrv
  codomain::EllCrv
  coordx::RingElem
  coordy::RingElem
  kernel::Vector{EllCrvPt}
  kernel_polynomial::RingElem
  degree::Int
  
  function Isogeny(E,psi)
    r = new()
    r.domain = E
    r.kernel_polynomial = psi
    r.codomain, r.coordx, r.coordy, r.degree = isogeny_kernel_polynomial(E,psi)
    return r
  end

end

function isogeny_from_kernel(E::EllCrv,psi::RingElem)
  return Isogeny(E,psi)
end


function domain(f::Isogeny)
  return f.domain
end

function codomain(f::Isogeny)
  return f.codomain
end


function degree(f::Isogeny)
  return f.degree
end


function image(phi::Isogeny, P::EllCrvPt)
  @assert domain(phi) === parent(P)
  x = P.coordx
  y = P.coordy
  
  phix = evaluate(evaluate(phi.coordx,y),x)
  phiy = evaluate(evaluate(phi.coordy,y),x)
  
  return codomain(phi)([phix,phiy])
end

function isogeny_kernel_polynomial(E,psi)

#TODO: Test if polynomial defines a possible kernel, i.e. it needs to be separable, defined over the base field and its roots (in the alg. closure)
#need to be x-coordinates of torsion points on the curve 

  R = parent(psi)
  psi = numerator(psi//R(leading_coefficient(psi)))

  psi_G = gcd(division_polynomial(E,2,2),psi)
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
 Ry = parent(omega)
 phi = Ry(phi)
 psi = Ry(psi)
 return compute_codomain(E,v,w), phi//psi^2, omega//psi^3, d
end

function even_kernel_polynomial(E, psi_G)

  psi_2tor = division_polynomial(E,2,2)
  if  mod(psi_2tor,psi_G) != 0
    throw(DomainError(psi_G,"Does not define a finite subgroup of the elliptic curve."))
  end
  n = degree(psi_G)
  d = n+1
  K = base_field(E)
  char = characteristic(K)
  
  Kx,x = PolynomialRing(K,"x")
  Kxy,y = PolynomialRing(Kx,"y")

  a1,a2,a3,a4,a6 = a_invars(E)
  b2, b4, b6 = E.b_invars

  if (n == 1)
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
      s1 = -psi_coeffs[n-1]
    else
      s1 = 0
    end
    ddpsi = 0
    temp = 1
    for j in (0:n-1)
      ddpsi = ddpsi + binomial(j+2,2)*psi_coeffs[j+2]*temp
      temp = x*temp
    end

    for j in (0:n-2)
      dddpsi = dddpsi + (3*binomial(j+3,3))*psi_coeffs[(j+3)]*temp
      temp = x*temp
    end

    omega = dphi*psi*y - phi*dpsi*psi_2 + ((a1*x + a3)*(psi_2^2)*(ddpsi*dpsi-dddpsi*psi) + (a1*psi_2^2 - 3*(a1*x + a3)*(6*x^2 + b2*x + b4))*dpsi*psi +(a1*x^3 + 3*a3*x^2 + (2*a2*a3 - a1*a4)*x + (a3*a4 - 2*a1*a6))*dpsi^2 +(-(3*a1*x^2 + 6*a3*x + (-a1*a4 + 2*a2*a3)) + (a1*x + a3)*(d*x - 2*s1) )*dpsi*psi + (a1*s1 + a3*n)*psi^2)*psi
  end
  return phi, omega, v, w, n, d
end


function compute_codomain(E::EllCrv, v, w)

a1,a2,a3,a4,a6 = a_invars(E)

newa4 = a4 - 5*v
newa6 = a6 - (a1^2 + 4*a2)*v - 7*w

return EllipticCurve([a1, a2, a3, newa4, newa6])
end


