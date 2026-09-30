# [Ohn07] T. Ohno.
# The graded ring of invariants of ternary quartics I, 2007.

# Return all the coefficients of a quartic in the same order as in [Ohn07].
function _get_quartic_coefficients(quartic::MPolyRingElem{T}) where T
  R = parent(quartic)
  @req number_of_generators(R) == 3 && total_degree(quartic) == 4 "Input needs to be a ternary quartic."
  x, y, z = gens(R)

  a = coeff(quartic, x^4)
  b = coeff(quartic, x^3*y)
  c = coeff(quartic, x^2*y^2)
  d = coeff(quartic, x*y^3)
  e = coeff(quartic, y^4)
  f = coeff(quartic, x^3*z)
  g = coeff(quartic, x^2*y*z)
  h = coeff(quartic, x*y^2*z)
  i = coeff(quartic, y^3*z)
  j = coeff(quartic, x^2*z^2)
  k = coeff(quartic, x*y*z^2)
  l = coeff(quartic, y^2*z^2)
  m = coeff(quartic, x*z^3)
  n = coeff(quartic, y*z^3)
  p = coeff(quartic, z^4)

  return a, b, c, d, e, f, g, h, i, j, k, l, m, n, p
end 

#J_{1,1} operator from [Ohn07]. First argument is a covariant, second argument a contravariant
function J11(P::MPolyRingElem{T}, Q::MPolyRingElem{T}) where T
  R = parent(P)
  x, y, z = gens(R)
  A, C, F, B, E, D = (coeff(P, x^2), coeff(P, y^2), coeff(P, z^2), coeff(P, x*y)/2, coeff(P, y*z)/2, coeff(P, x*z)/2)
  A_, C_, F_, B_, E_, D_ = (coeff(Q, x^2), coeff(Q, y^2), coeff(Q, z^2), coeff(Q, x*y)/2, coeff(Q, y*z)/2, coeff(Q, x*z)/2)
  
  return A*A_ + 2*B*B_ + C*C_ + 2*D*D_ +2*E*E_ +F*F_
end

#J_{2,2} operator from [Ohn07]. First argument is a covariant, second argument a contravariant
function J22(P::MPolyRingElem{T}, Q::MPolyRingElem{T}) where T
  return J11(_dual_variant(Q), _dual_variant(P))
end

#Compute the dual (contra/co)variant of P
function _dual_variant(P::MPolyRingElem{T}) where T
  R = parent(P)
  x, y, z = gens(R)
  A, C, F, B, E, D = (coeff(P, x^2), coeff(P, y^2), coeff(P, z^2), coeff(P, x*y)/2, coeff(P, y*z)/2, coeff(P, x*z)/2)
  return (E^2-C*F)*x^2 + 2*(B*F - D*E)*x*y + (D^2 - A*F)*y^2 + 
          2*(C*D - B*E)*x*z + 2*(A*E - B*D)*y*z + (B^2 - A*C)*z^2
end


#J_{3,0} operator from [Ohn07].  (Input is a covariant, output a covariant.) 
#Discriminant of a ternary quadric. 
function J30(P::MPolyRingElem{T}) where T
  R = parent(P)
  x, y, z = gens(R)
  L = [coeff(P, x^2), coeff(P, y^2), coeff(P, z^2), coeff(P, x*y), coeff(P, y*z), coeff(P, x*z) ]
  a11, a22, a33, a12, a23, a13 = L
  M = matrix([a11 a12/2 a13/2 ; a12/2 a22 a23/2; a13/2 a23/2 a33])
  return det(M)
  return d
end

#J_{0,3} operator from [Ohn07]. (Input is a contravariant, output a covariant. Implementation is identical)
function J03(P::MPolyRingElem{T}) where T
  return J30(P)
end

@doc raw"""
    dixmier_ohno_invariants(quartic::MPolyRingElem{T}) -> Vector{T}, Vector{Int}

Compute the Dixmier-Ohno invariants of a ternary quartic.
The second argument gives the weights of the invariants in weighted 
projective space.
"""
function dixmier_ohno_invariants(quartic::MPolyRingElem{T}) where T
  R = parent(quartic)
  K = base_ring(R)
  @req number_of_generators(R) == 3 && total_degree(quartic) == 4 "Input needs to be a ternary quartic."
  @req characteristic(K) > 7 || characteristic(K) == 0 "Dixmier-Ohno invariants not implemented yet for characteristic 2, 3, 5 or 7."

  a, b, c, d, e, f, g, h, i, j, k, l, m, n, p = _get_quartic_coefficients(quartic)

  #Rescale as in [Ohn07]
  b/=4; c/=6; d/=4; f/=4; g/=12; h/=12
  i/=4; j/=6; k/=12; l/=6; m/=4; n/=4

  I3 = a*e*p - 4*a*i*n + 3*a*l^2 - 4*b*d*p + 12*b*h*n + 4*b*i*m - 12*b*k*l + 
  3*c^2*p - 12*c*g*n - 12*c*h*m + 6*c*j*l + 12*c*k^2 + 4*d*f*n + 12*d*g*m - 
  12*d*j*k - 4*e*f*m + 3*e*j^2 - 12*f*h*l + 12*f*i*k + 12*g^2*l - 12*g*h*k - 
  12*g*i*j + 12*h^2*j

  I6 = det(matrix([a b c f g j;
                   b c d g h k;
                   c d e h i l;
                   f g h j k m;
                   g h i k l n;
                   j k l m n p]))


  rho, tau, ksi, pi, eta, zeta, chi, nu = _compute_covariants_and_contravariants(quartic)
  I9a = J11(tau, rho)
  I9b = J11(ksi, rho)
  I12a = J03(rho)
  I12b = J11(tau, eta)
  I15a = J30(tau)
  I15b = J30(ksi)
  I18a = J22(tau, rho)
  I18b = J22(ksi, rho)
  I21a = J03(eta)
  I21b = J11(nu, eta)
  I27 = discriminant_of_ternary_quartic(quartic)

  weights = [3, 6, 9, 9, 12, 12, 15, 15, 18, 18, 21, 21, 27]
  
  return [I3, I6, I9a, I9b, I12a, I12b, I15a, I15b, I18a, I18b, I21a, I21b, I27], weights
end

@doc raw"""
    discriminant_of_ternary_quartic(quartic::MPolyRingElem{T}) -> T

Compute the discriminant of a ternary quartic.
"""
function discriminant_of_ternary_quartic(quartic::MPolyRingElem{T}) where T
  R = parent(quartic)
  K = base_ring(R)
  x, y, z = gens(R)
  @req number_of_generators(R) == 3 && total_degree(quartic) == 4 "Input needs to be a ternary quartic."
  @req characteristic(K) > 7 || characteristic(K) == 0 "Discriminant not implemented yet for characteristic 2, 3, 5 or 7."

  dfx = derivative(quartic, 1)/4
  dfy = derivative(quartic, 2)/4
  dfz = derivative(quartic, 3)/4

  Hessian = _hessian(quartic)
  dHx = derivative(Hessian, 1)
  dHy = derivative(Hessian, 2)
  dHz = derivative(Hessian, 3)

  matrix_entries = [dHx/2, dHy/2, dHz/2]
  mons = _mons_of_degree_n(R, 2)
  for mon in mons
    for df in [dfx, dfy, dfz]
      push!(matrix_entries, mon*df)
    end
  end

  M5 = _mons_of_degree_n(R, 5)
  
  M = zero_matrix(R, 21, 21)
  for i in (1:21)
    for j in (1:21)
      M[i,j] = coeff(matrix_entries[i], M5[j])
    end
  end
  #Just converting it back to QQ
  return det(M)(K(0), K(0), K(0))
end

#Just a helper functions that (inefficiently) spits out all homogeneous monomials of
#a fixed degree.
function _mons_of_degree_n(R, n)
  X = gens(R)
  if n == 1
    return X
  end
  old_mons = _mons_of_degree_n(R, n-1)
  result = Set{MPolyRingElem}()
  for x in X
    for mon in old_mons
      push!(result, x*mon)
    end
  end
  return collect(result)
end

#Given multivariate polynomials A and f
#Computes a differential operator D_A as defined in [Ohn07] and applies it to f.
#For polynomials with 3 variables it would look like
#D_A = A_{q,0,0}d/dx^q + A_{q−1,1,0}d/dx^{q-1}dy + ... + A_{0,0,q}d/dz^q
function _differential_operator(A::MPolyRingElem{T}, f::MPolyRingElem{T}) where T
  R = parent(f)
  result = zero(f)
  mons = monomials(A)
  for mon in mons
    result += coeff(A, mon) * derivative(f, exponent_vector(mon, 1))
  end
  return result
end

#Computes the Hessian of the input quartic. Afterwards divides it by 1728
#for the computation of invariants.
function _hessian(quartic::MPolyRingElem{T}) where T
  R = parent(quartic)
  result = zero_matrix(R, 3, 3)
  for i in (1:3)
    for j in (i:3)
      exp = [0,0,0]
      exp[i]+=1
      exp[j]+=1
      result[i,j] = derivative(quartic, exp)
      if i != j
        result[j,i] = result[i,j]
      end
    end
  end
  return det(result)/1728
end

#Computes the covariants and contrariants as defined in [Ohn07].
function _compute_covariants_and_contravariants(phi::MPolyRingElem{T}) where T
  sigma = sigma_contravariant(phi)
  psi = psi_contravariant(phi)
  He = _hessian(phi)
  rho = _differential_operator(phi, psi)/144
  tau =  _differential_operator(rho, phi)/12
  ksi = _differential_operator(sigma, He)/72
  pi = _differential_operator(rho, He)/2
  eta = _differential_operator(ksi, sigma)/12
  zeta = _differential_operator(tau, psi)/2
  chi = _differential_operator(tau, zeta)/4
  nu = _differential_operator(eta, pi)/4
  return rho, tau, ksi, pi, eta, zeta, chi, nu
end

#Computes the sigma contrariant as defined in [Ohn07].
function sigma_contravariant(quartic::MPolyRingElem{T}) where T
  R = parent(quartic)
  x, y, z = gens(R)
  a, b, c, d, e, f, g, h, i, j, k, l, m, n, p = _get_quartic_coefficients(quartic)

  sigma = a*e*z^4 - a*i*y*z^3 + a*l*y^2*z^2 - a*n*y^3*z +
  a*p*y^4 - b*d*z^4/4 + b*h*y*z^3/4 + b*i*x*z^3/4 -
  b*k*y^2*z^2/4 - b*l*x*y*z^2/2 + b*m*y^3*z/4 +
  3*b*n*x*y^2*z/4 - b*p*x*y^3 + c^2*z^4/12 - c*g*y*z^3/6 -
  c*h*x*z^3/6 + c*j*y^2*z^2/6 + c*k*x*y*z^2/3 + 
  c*l*x^2*z^2/6 - c*m*x*y^2*z/2 - c*n*x^2*y*z/2 + 
  c*p*x^2*y^2 + d*f*y*z^3/4 + d*g*x*z^3/4 - d*j*x*y*z^2/2 - 
  d*k*x^2*z^2/4 + 3*d*m*x^2*y*z/4 + d*n*x^3*z/4 - d*p*x^3*y - 
  e*f*x*z^3 + e*j*x^2*z^2 - e*m*x^3*z + e*p*x^4 - f*h*y^2*z^2/4 + 
  3*f*i*x*y*z^2/4 + f*k*y^3*z/4 - f*l*x*y^2*z/2 - 
  f*m*y^4/4 + f*n*x*y^3/4 + g^2*y^2*z^2/12 - 
  g*h*x*y*z^2/12 - g*i*x^2*z^2/4 - g*j*y^3*z/6 - 
  g*k*x*y^2*z/12 + g*l*x^2*y*z/3 + g*m*x*y^3/4 - 
  g*n*x^2*y^2/4 + h^2*x^2*z^2/12 + h*j*x*y^2*z/3 - 
  h*k*x^2*y*z/12 - h*l*x^3*z/6 - h*m*x^2*y^2/4 + 
  h*n*x^3*y/4 - i*j*x^2*y*z/2 + i*k*x^3*z/4 + i*m*x^3*y/4 - 
  i*n*x^4/4 + j^2*y^4/12 - j*k*x*y^3/6 + j*l*x^2*y^2/6 + 
  k^2*x^2*y^2/12 - k*l*x^3*y/6 + l^2*x^4/12

  return sigma
end


#Computes the psi contrariant as defined in [Ohn07].
function psi_contravariant(quartic::MPolyRingElem{T}) where T
  R = parent(quartic)
  x, y, z = gens(R)
  a, b, c, d, e, f, g, h, i, j, k, l, m, n, p = _get_quartic_coefficients(quartic)


psi = a*c*e*z^6/6 - a*c*i*y*z^5/6 + a*c*l*y^2*z^4/6 - 
  a*c*n*y^3*z^3/6 + a*c*p*y^4*z^2/6 - a*d^2*z^6/16 + 
  a*d*h*y*z^5/8 + a*d*i*x*z^5/8 - a*d*k*y^2*z^4/8 - 
  a*d*l*x*y*z^4/4 + a*d*m*y^3*z^3/8 + 3*a*d*n*x*y^2*z^3/8 - 
  a*d*p*x*y^3*z^2/2 - a*e*g*y*z^5/6 - a*e*h*x*z^5/6 + 
  a*e*j*y^2*z^4/6 + a*e*k*x*y*z^4/3 + a*e*l*x^2*z^4/6 - 
  a*e*m*x*y^2*z^3/2 - a*e*n*x^2*y*z^3/2 + a*e*p*x^2*y^2*z^2 + 
  a*g*i*y^2*z^4/6 - a*g*l*y^3*z^3/6 + a*g*n*y^4*z^2/6 - 
  a*g*p*y^5*z/6 - a*h^2*y^2*z^4/16 + a*h*i*x*y*z^4/24 + 
  a*h*k*y^3*z^3/8 + a*h*l*x*y^2*z^3/12 - a*h*m*y^4*z^2/8 - 
  5*a*h*n*x*y^3*z^2/24 + a*h*p*x*y^4*z/3 - a*i^2*x^2*z^4/16 - 
  a*i*j*y^3*z^3/6 - 5*a*i*k*x*y^2*z^3/24 + a*i*l*x^2*y*z^3/12 + 
  3*a*i*m*x*y^3*z^2/8 + a*i*n*x^2*y^2*z^2/8 - a*i*p*x^2*y^3*z/2 + 
  a*j*l*y^4*z^2/6 - a*j*n*y^5*z/6 + a*j*p*y^6/6 - a*k^2*y^4*z^2/16 + 
  a*k*l*x*y^3*z^2/12 + a*k*m*y^5*z/8 + a*k*n*x*y^4*z/24 - 
  a*k*p*x*y^5/6 - a*l^2*x^2*y^2*z^2/12 - a*l*m*x*y^4*z/4 + 
  a*l*n*x^2*y^3*z/12 + a*l*p*x^2*y^4/6 - a*m^2*y^6/16 + 
  a*m*n*x*y^5/8 - a*n^2*x^2*y^4/16 - b^2*e*z^6/16 + b^2*i*y*z^5/16 -
  b^2*l*y^2*z^4/16 + b^2*n*y^3*z^3/16 - b^2*p*y^4*z^2/16 +
  b*c*d*z^6/48 - b*c*h*y*z^5/48 - b*c*i*x*z^5/48 + 
  b*c*k*y^2*z^4/48 + b*c*l*x*y*z^4/24 - b*c*m*y^3*z^3/48 - 
  b*c*n*x*y^2*z^3/16 + b*c*p*x*y^3*z^2/12 - b*d*g*y*z^5/48 - 
  b*d*h*x*z^5/48 + b*d*j*y^2*z^4/48 + b*d*k*x*y*z^4/24 + 
  b*d*l*x^2*z^4/48 - b*d*m*x*y^2*z^3/16 - b*d*n*x^2*y*z^3/16 + 
  b*d*p*x^2*y^2*z^2/8 + b*e*f*y*z^5/8 + b*e*g*x*z^5/8 - 
  b*e*j*x*y*z^4/4 - b*e*k*x^2*z^4/8 + 3*b*e*m*x^2*y*z^3/8 + 
  b*e*n*x^3*z^3/8 - b*e*p*x^3*y*z^2/2 - b*f*i*y^2*z^4/8 + 
  b*f*l*y^3*z^3/8 - b*f*n*y^4*z^2/8 + b*f*p*y^5*z/8 + 
  b*g*h*y^2*z^4/48 - 5*b*g*i*x*y*z^4/48 - b*g*k*y^3*z^3/48 + 
  b*g*l*x*y^2*z^3/12 + b*g*m*y^4*z^2/48 - b*g*n*x*y^3*z^2/16 + 
  b*g*p*x*y^4*z/24 + b*h^2*x*y*z^4/48 + b*h*i*x^2*z^4/48 - 
  b*h*j*y^3*z^3/48 - b*h*k*x*y^2*z^3/16 - b*h*l*x^2*y*z^3/16 + 
  b*h*m*x*y^3*z^2/12 + b*h*n*x^2*y^2*z^2/8 - 5*b*h*p*x^2*y^3*z/24 + 
  11*b*i*j*x*y^2*z^3/48 + b*i*k*x^2*y*z^3/12 - b*i*l*x^3*z^3/48 - 
  5*b*i*m*x^2*y^2*z^2/16 - b*i*n*x^3*y*z^2/16 + 3*b*i*p*x^3*y^2*z/8 + 
  b*j*k*y^4*z^2/48 - 5*b*j*l*x*y^3*z^2/24 - b*j*m*y^5*z/48 + 
  3*b*j*n*x*y^4*z/16 - b*j*p*x*y^5/6 + b*k^2*x*y^3*z^2/24 - 
  b*k*l*x^2*y^2*z^2/48 - 5*b*k*m*x*y^4*z/48 - b*k*n*x^2*y^3*z/16 + 
  b*k*p*x^2*y^4/6 + b*l^2*x^3*y*z^2/24 + 11*b*l*m*x^2*y^3*z/48 - 
  b*l*n*x^3*y^2*z/16 - b*l*p*x^3*y^3/6 + b*m^2*x*y^5/16 - 
  b*m*n*x^2*y^4/8 + b*n^2*x^3*y^3/16 - c^3*z^6/216 + 
  c^2*g*y*z^5/72 + c^2*h*x*z^5/72 - c^2*j*y^2*z^4/72 - 
  c^2*k*x*y*z^4/36 - c^2*l*x^2*z^4/72 + c^2*m*x*y^2*z^3/24 + 
  c^2*n*x^2*y*z^3/24 - c^2*p*x^2*y^2*z^2/12 - c*d*f*y*z^5/48 - 
  c*d*g*x*z^5/48 + c*d*j*x*y*z^4/24 + c*d*k*x^2*z^4/48 - 
  c*d*m*x^2*y*z^3/16 - c*d*n*x^3*z^3/48 + c*d*p*x^3*y*z^2/12 - 
  c*e*f*x*z^5/6 + c*e*j*x^2*z^4/6 - c*e*m*x^3*z^3/6 + 
  c*e*p*x^4*z^2/6 + c*f*h*y^2*z^4/48 + 3*c*f*i*x*y*z^4/16 - 
  c*f*k*y^3*z^3/48 - 5*c*f*l*x*y^2*z^3/24 + c*f*m*y^4*z^2/48 + 
  11*c*f*n*x*y^3*z^2/48 - c*f*p*x*y^4*z/4 - c*g^2*y^2*z^4/72 - 
  c*g*h*x*y*z^4/144 + c*g*i*x^2*z^4/48 + c*g*j*y^3*z^3/36 + 
  5*c*g*k*x*y^2*z^3/144 - c*g*l*x^2*y*z^3/72 - c*g*m*x*y^3*z^2/16 - 
  c*g*n*x^2*y^2*z^2/48 + c*g*p*x^2*y^3*z/12 - c*h^2*x^2*z^4/72 - 
  c*h*j*x*y^2*z^3/72 + 5*c*h*k*x^2*y*z^3/144 + c*h*l*x^3*z^3/36 - 
  c*h*m*x^2*y^2*z^2/48 - c*h*n*x^3*y*z^2/16 + c*h*p*x^3*y^2*z/12 - 
  5*c*i*j*x^2*y*z^3/24 - c*i*k*x^3*z^3/48 + 11*c*i*m*x^3*y*z^2/48 + 
  c*i*n*x^4*z^2/48 - c*i*p*x^4*y*z/4 - c*j^2*y^4*z^2/72 - 
  c*j*k*x*y^3*z^2/72 + 2*c*j*l*x^2*y^2*z^2/9 + c*j*m*x*y^4*z/24 - 
  5*c*j*n*x^2*y^3*z/24 + c*j*p*x^2*y^4/6 - 5*c*k^2*x^2*y^2*z^2/144 - 
  c*k*l*x^3*y*z^2/72 + c*k*m*x^2*y^3*z/12 + c*k*n*x^3*y^2*z/12 - 
  c*k*p*x^3*y^3/6 - c*l^2*x^4*z^2/72 - 5*c*l*m*x^3*y^2*z/24 + 
  c*l*n*x^4*y*z/24 + c*l*p*x^4*y^2/6 - c*m^2*x^2*y^4/16 + 
  c*m*n*x^3*y^3/8 - c*n^2*x^4*y^2/16 + d^2*f*x*z^5/16 - 
  d^2*j*x^2*z^4/16 + d^2*m*x^3*z^3/16 - d^2*p*x^4*z^2/16 + 
  d*f*g*y^2*z^4/48 - 5*d*f*h*x*y*z^4/48 - d*f*i*x^2*z^4/8 - 
  d*f*j*y^3*z^3/48 + d*f*k*x*y^2*z^3/12 + 11*d*f*l*x^2*y*z^3/48 - 
  d*f*m*x*y^3*z^2/16 - 5*d*f*n*x^2*y^2*z^2/16 + 3*d*f*p*x^2*y^3*z/8 + 
  d*g^2*x*y*z^4/48 + d*g*h*x^2*z^4/48 - d*g*j*x*y^2*z^3/16 - 
  d*g*k*x^2*y*z^3/16 - d*g*l*x^3*z^3/48 + d*g*m*x^2*y^2*z^2/8 + 
  d*g*n*x^3*y*z^2/12 - 5*d*g*p*x^3*y^2*z/24 + d*h*j*x^2*y*z^3/12 - 
  d*h*k*x^3*z^3/48 - d*h*m*x^3*y*z^2/16 + d*h*n*x^4*z^2/48 + 
  d*h*p*x^4*y*z/24 + d*i*j*x^3*z^3/8 - d*i*m*x^4*z^2/8 + 
  d*i*p*x^5*z/8 + d*j^2*x*y^3*z^2/24 - d*j*k*x^2*y^2*z^2/48 - 
  5*d*j*l*x^3*y*z^2/24 - d*j*m*x^2*y^3*z/16 + 11*d*j*n*x^3*y^2*z/48 - 
  d*j*p*x^3*y^3/6 + d*k^2*x^3*y*z^2/24 + d*k*l*x^4*z^2/48 - 
  d*k*m*x^3*y^2*z/16 - 5*d*k*n*x^4*y*z/48 + d*k*p*x^4*y^2/6 + 
  3*d*l*m*x^4*y*z/16 - d*l*n*x^5*z/48 - d*l*p*x^5*y/6 + 
  d*m^2*x^3*y^3/16 - d*m*n*x^4*y^2/8 + d*n^2*x^5*y/16 - 
  e*f^2*y^2*z^4/16 + e*f*g*x*y*z^4/24 + e*f*h*x^2*z^4/6 + 
  e*f*j*x*y^2*z^3/12 - 5*e*f*k*x^2*y*z^3/24 - e*f*l*x^3*z^3/6 + 
  e*f*m*x^2*y^2*z^2/8 + 3*e*f*n*x^3*y*z^2/8 - e*f*p*x^3*y^2*z/2 - 
  e*g^2*x^2*z^4/16 + e*g*j*x^2*y*z^3/12 + e*g*k*x^3*z^3/8 - 
  5*e*g*m*x^3*y*z^2/24 - e*g*n*x^4*z^2/8 + e*g*p*x^4*y*z/3 - 
  e*h*j*x^3*z^3/6 + e*h*m*x^4*z^2/6 - e*h*p*x^5*z/6 - 
  e*j^2*x^2*y^2*z^2/12 + e*j*k*x^3*y*z^2/12 + e*j*l*x^4*z^2/6 + 
  e*j*m*x^3*y^2*z/12 - e*j*n*x^4*y*z/4 + e*j*p*x^4*y^2/6 - 
  e*k^2*x^4*z^2/16 + e*k*m*x^4*y*z/24 + e*k*n*x^5*z/8 - 
  e*k*p*x^5*y/6 - e*l*m*x^5*z/6 + e*l*p*x^6/6 - e*m^2*x^4*y^2/16 + 
  e*m*n*x^5*y/8 - e*n^2*x^6/16 + f^2*i*y^3*z^3/16 - 
  f^2*l*y^4*z^2/16 + f^2*n*y^5*z/16 - f^2*p*y^6/16 - 
  f*g*h*y^3*z^3/48 - f*g*i*x*y^2*z^3/16 + f*g*k*y^4*z^2/48 + 
  f*g*l*x*y^3*z^2/12 - f*g*m*y^5*z/48 - 5*f*g*n*x*y^4*z/48 + 
  f*g*p*x*y^5/8 + f*h^2*x*y^2*z^3/24 - f*h*i*x^2*y*z^3/16 + 
  f*h*j*y^4*z^2/48 - f*h*k*x*y^3*z^2/16 - f*h*l*x^2*y^2*z^2/48 + 
  f*h*m*x*y^4*z/24 + f*h*n*x^2*y^3*z/12 - f*h*p*x^2*y^4/8 +
  f*i^2*x^3*z^3/16 - f*i*j*x*y^3*z^2/16 + f*i*k*x^2*y^2*z^2/8 - 
  f*i*l*x^3*y*z^2/16 - f*i*m*x^2*y^3*z/16 - f*i*n*x^3*y^2*z/16 + 
  f*i*p*x^3*y^3/8 - f*j*k*y^5*z/48 + f*j*l*x*y^4*z/24 + 
  f*j*m*y^6/48 - f*j*n*x*y^5/48 + f*k^2*x*y^4*z/48 - 
  f*k*l*x^2*y^3*z/16 - f*k*m*x*y^5/48 + f*k*n*x^2*y^4/48 + 
  f*l^2*x^3*y^2*z/24 + f*l*m*x^2*y^4/48 - f*l*n*x^3*y^3/48 + 
  g^3*y^3*z^3/216 - g^2*h*x*y^2*z^3/144 + g^2*i*x^2*y*z^3/24 - 
  g^2*j*y^4*z^2/72 - g^2*k*x*y^3*z^2/144 - 5*g^2*l*x^2*y^2*z^2/144 + 
  g^2*m*x*y^4*z/48 + g^2*n*x^2*y^3*z/24 - g^2*p*x^2*y^4/16 - 
  g*h^2*x^2*y*z^3/144 - g*h*i*x^3*z^3/48 + 5*g*h*j*x*y^3*z^2/144 + 
  g*h*k*x^2*y^2*z^2/36 + 5*g*h*l*x^3*y*z^2/144 - g*h*m*x^2*y^3*z/16 - 
  g*h*n*x^3*y^2*z/16 + g*h*p*x^3*y^3/8 - g*i*j*x^2*y^2*z^2/48 - 
  g*i*k*x^3*y*z^2/16 + g*i*l*x^4*z^2/48 + g*i*m*x^3*y^2*z/12 + 
  g*i*n*x^4*y*z/24 - g*i*p*x^4*y^2/8 + g*j^2*y^5*z/72 - 
  g*j*k*x*y^4*z/144 - g*j*l*x^2*y^3*z/72 - g*j*m*x*y^5/48 + 
  g*j*n*x^2*y^4/48 - g*k^2*x^2*y^3*z/144 + 5*g*k*l*x^3*y^2*z/144 + 
  g*k*m*x^2*y^4/48 - g*k*n*x^3*y^3/48 - g*l^2*x^4*y*z/36 - 
  g*l*m*x^3*y^3/48 + g*l*n*x^4*y^2/48 + h^3*x^3*z^3/216 - 
  5*h^2*j*x^2*y^2*z^2/144 - h^2*k*x^3*y*z^2/144 - h^2*l*x^4*z^2/72 + 
  h^2*m*x^3*y^2*z/24 + h^2*n*x^4*y*z/48 - h^2*p*x^4*y^2/16 + 
  h*i*j*x^3*y*z^2/12 + h*i*k*x^4*z^2/48 - 5*h*i*m*x^4*y*z/48 - 
  h*i*n*x^5*z/48 + h*i*p*x^5*y/8 - h*j^2*x*y^4*z/36 + 
  5*h*j*k*x^2*y^3*z/144 - h*j*l*x^3*y^2*z/72 + h*j*m*x^2*y^4/48 - 
  h*j*n*x^3*y^3/48 - h*k^2*x^3*y^2*z/144 - h*k*l*x^4*y*z/144 - 
  h*k*m*x^3*y^3/48 + h*k*n*x^4*y^2/48 + h*l^2*x^5*z/72 + 
  h*l*m*x^4*y^2/48 - h*l*n*x^5*y/48 - i^2*j*x^4*z^2/16 + 
  i^2*m*x^5*z/16 - i^2*p*x^6/16 + i*j^2*x^2*y^3*z/24 - 
  i*j*k*x^3*y^2*z/16 + i*j*l*x^4*y*z/24 - i*j*m*x^3*y^3/48 + 
  i*j*n*x^4*y^2/48 + i*k^2*x^4*y*z/48 - i*k*l*x^5*z/48 + 
  i*k*m*x^4*y^2/48 - i*k*n*x^5*y/48 - i*l*m*x^5*y/48 + 
  i*l*n*x^6/48 - j^3*y^6/216 + j^2*k*x*y^5/72 - j^2*l*x^2*y^4/72 - 
  j*k^2*x^2*y^4/72 + j*k*l*x^3*y^3/36 - j*l^2*x^4*y^2/72 + 
  k^3*x^3*y^3/216 - k^2*l*x^4*y^2/72 + k*l^2*x^5*y/72 - l^3*x^6/216
  return psi
end
