function a_invariants(D::G1Model{T}) where T
  if degree(D) == 2 
    return a_invariants_d2(equations(D)...)
  elseif degree(D) == 3
    return a_invariants_d3(equations(D)[1])
  elseif degree(D) == 4
    return a_invariants_d4(equations(D)...)
  end
  error("Degree of genus one model has to be either 2, 3 or 4.")
end

function b_invariants(D::G1Model{T}) where T
  a1, a2, a3, a4, a6 = a_invariants(D)
  return Hecke._ellcrv_b_invariants(a1, a2, a3, a4, a6)
end

function c_invariants(D::G1Model{T}) where T
  b2, b4, b6, b8 = b_invariants(D)
  return Hecke._ellcrv_c_invariants(b2, b4, b6, b8)
end 

function discriminant(D::G1Model{T}) where T
  c4, c6 = c_invariants(D)
  return (c4^3 - c6^2)/1728
end 


function a_invariants(F::MPolyRingElem)
  if total_degree(F) == 3
    return a_invariants_d3(F)
  end
end

function b_invariants(F::MPolyRingElem)
  a1, a2, a3, a4, a6 = a_invariants(F)
  return Hecke._ellcrv_b_invariants(a1, a2, a3, a4, a6)
end

function c_invariants(F::MPolyRingElem)
  b2, b4, b6, b8 = b_invariants(F)
  return Hecke._ellcrv_c_invariants(b2, b4, b6, b8)
end 

function a_invariants_d2(Q::MPolyRingElem, P::MPolyRingElem)
  R = parent(Q)
  x, z = gens(R)

  a = coeff(Q, x^4)
  b = coeff(Q, x^3*z)
  c = coeff(Q, x^2*z^2)
  d = coeff(Q, x*z^3)
  e = coeff(Q, z^4)
  l = coeff(P, x^2)
  m = coeff(P, x*z)
  n = coeff(P, z^2)

  a1 = m
  a2 = c - l*n
  a3 = l*d + n*b
  a4 = - 4*a*e + b*d - (l^2*e + l*n*c + n^2*a)
  a6 = - 4*a*c*e + a*d^2 + b^2*e - (l^2*c*e + m^2*a*e + n^2*a*c + l*n*b*d) + l*m*b*e + m*n*a*d

  return a1, a2, a3, a4, a6
end

function a_invariants_d3(F::MPolyRingElem)
  R = parent(F)
  x, y, z = gens(R)
 
  a = coeff(F, x^3)
  b = coeff(F, y^3)
  c = coeff(F, z^3)
  d = coeff(F, x^2*y)
  e = coeff(F, x^2*z)
  f = coeff(F, x*y^2)
  g = coeff(F, y^2*z)
  h = coeff(F, x*z^2)
  i = coeff(F, y*z^2)
  m = coeff(F, x*y*z)

  a1 = m
  a2 = -(d*i + e*g + f*h);
  a3 = 9*a*b*c - (a*g*i + b*e*h + c*d*f) - (d*g*h + e*f*i)
  a4 = -3*(a*b*h*i + a*c*f*g  + b*c*d*e) + a*(f*i^2 + g^2*h) +
      b*(d*h^2 + e^2*i) + c*(d^2*g + e*f^2) + d*i*e*g + f*h*d*i + e*g*f*h
  a6 = a*b*c*(-27*a*b*c + 9*(a*g*i + c*d*f + b*e*h) + m^3) +
   3*a*b*c*((d*g*h + e*f*i) - (d*i + e*g + f*h)*m) - a^2*(b*i^3 + c*g^3) - 
   b^2*(c*e^3 + a*h^3) - c^2*(a*f^3 + b*d^3) + 
   (a*b*h*i + b*c*d*e + a*c*f*g)*(2*(d*i + e*g + f*h) - m^2) - 
   3*(a*b*e*g*h*i + b*c*d*e*f*h + a*c*d*f*g*i) - a*((f*h + d*i)*g^2*h +
   (h*f + e*g)*f*i^2) - b*((i*d + e*g)*h^2*d + (d*i + f*h)*i*e^2) - 
   c*((e*g + f*h)*d^2*g + (g*e + d*i)*e*f^2) - d*e*f*g*h*i +
   a*b*(e*i^2 + g*h^2)*m + b*c*(d^2*h + e^2*f)*m + a*c*(d*g^2 + f^2*i)*m +
  (a*f*g*h*i + b*d*e*h*i + c*d*e*f*g)*m

  return a1, a2, a3, a4, a6
end

function a_invariants_d4(Q1::MPolyRingElem, Q2::MPolyRingElem)
  R = parent(Q1)
  x, y, z, w = gens(R)
  K = base_ring(R)

  a11 = coeff(Q1, x^2); a12 = coeff(Q1, x*y); a13 = coeff(Q1, x*z); a14 = coeff(Q1, x*w)
  a22 = coeff(Q1, y^2); a23 = coeff(Q1, y*z); a24 = coeff(Q1, y*w); a33 = coeff(Q1, z^2)
  a34 = coeff(Q1, z*w); a44 = coeff(Q1, w^2)

  b11 = coeff(Q2, x^2); b12 = coeff(Q2, x*y); b13 = coeff(Q2, x*z); b14 = coeff(Q2, x*w)
  b22 = coeff(Q2, y^2); b23 = coeff(Q2, y*z); b24 = coeff(Q2, y*w); b33 = coeff(Q2, z^2)
  b34 = coeff(Q2, z*w); b44 = coeff(Q2, w^2)


  a = 4*b11*b22*b33*b44 - b11*b22*b34^2 - b11*b23^2*b44 + b11*b23*b24*b34 - b11*b24^2*b33 - b12^2*b33*b44 + 
    b12*b13*b23*b44 - b12*b13*b24*b34 - b12*b14*b23*b34 + b12*b14*b24*b33 - b13^2*b22*b44 + 
    b13*b14*b22*b34 - b13*b14*b23*b24 - b14^2*b22*b33

  b = 4*a11*b22*b33*b44 - a11*b22*b34^2 - 
    a11*b23^2*b44 + a11*b23*b24*b34 - a11*b24^2*b33 - 2*a12*b12*b33*b44 + a12*b13*b23*b44 - 
    a12*b13*b24*b34 - a12*b14*b23*b34 + a12*b14*b24*b33 + a13*b12*b23*b44 - a13*b12*b24*b34 - 
    2*a13*b13*b22*b44 + a13*b14*b22*b34 - a13*b14*b23*b24 - a14*b12*b23*b34 + a14*b12*b24*b33 + 
    a14*b13*b22*b34 - a14*b13*b23*b24 - 2*a14*b14*b22*b33 + 4*a22*b11*b33*b44 - a22*b11*b34^2 - 
    a22*b13^2*b44 + a22*b13*b14*b34 - a22*b14^2*b33 - 2*a23*b11*b23*b44 + a23*b11*b24*b34 + 
    a23*b12*b13*b44 - a23*b12*b14*b34 - a23*b13*b14*b24 + a24*b11*b23*b34 - 2*a24*b11*b24*b33 - 
    a24*b12*b13*b34 + a24*b12*b14*b33 - a24*b13*b14*b23 + 4*a33*b11*b22*b44 - a33*b11*b24^2 - 
    a33*b12^2*b44 + a33*b12*b14*b24 - a33*b14^2*b22 - 2*a34*b11*b22*b34 + a34*b11*b23*b24 - 
    a34*b12*b13*b24 - a34*b12*b14*b23 + a34*b13*b14*b22 + 4*a44*b11*b22*b33 - a44*b11*b23^2 - 
    a44*b12^2*b33 + a44*b12*b13*b23 - a44*b13^2*b22

  c = 4*a11*a22*b33*b44 - a11*a22*b34^2 - 
    2*a11*a23*b23*b44 + a11*a23*b24*b34 + a11*a24*b23*b34 - 2*a11*a24*b24*b33 + 4*a11*a33*b22*b44 - 
    a11*a33*b24^2 - 2*a11*a34*b22*b34 + a11*a34*b23*b24 + 4*a11*a44*b22*b33 - a11*a44*b23^2 - 
    a12^2*b33*b44 + a12*a13*b23*b44 - a12*a13*b24*b34 - a12*a14*b23*b34 + a12*a14*b24*b33 + 
    a12*a23*b13*b44 - a12*a23*b14*b34 - a12*a24*b13*b34 + a12*a24*b14*b33 - 2*a12*a33*b12*b44 + 
    a12*a33*b14*b24 - a12*a34*b13*b24 - a12*a34*b14*b23 - 2*a12*a44*b12*b33 + a12*a44*b13*b23 - 
    a13^2*b22*b44 + a13*a14*b22*b34 - a13*a14*b23*b24 - 2*a13*a22*b13*b44 + a13*a22*b14*b34 + 
    a13*a23*b12*b44 - a13*a23*b14*b24 - a13*a24*b12*b34 - a13*a24*b14*b23 - a13*a34*b12*b24 + 
    a13*a34*b14*b22 + a13*a44*b12*b23 - 2*a13*a44*b13*b22 - a14^2*b22*b33 + a14*a22*b13*b34 - 
    2*a14*a22*b14*b33 - a14*a23*b12*b34 - a14*a23*b13*b24 + a14*a24*b12*b33 - a14*a24*b13*b23 + 
    a14*a33*b12*b24 - 2*a14*a33*b14*b22 - a14*a34*b12*b23 + a14*a34*b13*b22 + 4*a22*a33*b11*b44 - 
    a22*a33*b14^2 - 2*a22*a34*b11*b34 + a22*a34*b13*b14 + 4*a22*a44*b11*b33 - a22*a44*b13^2 - 
    a23^2*b11*b44 + a23*a24*b11*b34 - a23*a24*b13*b14 + a23*a34*b11*b24 - a23*a34*b12*b14 - 
    2*a23*a44*b11*b23 + a23*a44*b12*b13 - a24^2*b11*b33 - 2*a24*a33*b11*b24 + a24*a33*b12*b14 + 
    a24*a34*b11*b23 - a24*a34*b12*b13 + 4*a33*a44*b11*b22 - a33*a44*b12^2 - a34^2*b11*b22

  d = 4*a11*a22*a33*b44 - 2*a11*a22*a34*b34 + 4*a11*a22*a44*b33 - a11*a23^2*b44 + a11*a23*a24*b34 + 
    a11*a23*a34*b24 - 2*a11*a23*a44*b23 - a11*a24^2*b33 - 2*a11*a24*a33*b24 + a11*a24*a34*b23 + 
    4*a11*a33*a44*b22 - a11*a34^2*b22 - a12^2*a33*b44 - a12^2*a44*b33 + a12*a13*a23*b44 - 
    a12*a13*a24*b34 - a12*a13*a34*b24 + a12*a13*a44*b23 - a12*a14*a23*b34 + a12*a14*a24*b33 + 
    a12*a14*a33*b24 - a12*a14*a34*b23 - a12*a23*a34*b14 + a12*a23*a44*b13 + a12*a24*a33*b14 - 
    a12*a24*a34*b13 - 2*a12*a33*a44*b12 - a13^2*a22*b44 - a13^2*a44*b22 + a13*a14*a22*b34 - 
    a13*a14*a23*b24 - a13*a14*a24*b23 + a13*a14*a34*b22 + a13*a22*a34*b14 - 2*a13*a22*a44*b13 - 
    a13*a23*a24*b14 + a13*a23*a44*b12 - a13*a24*a34*b12 - a14^2*a22*b33 - a14^2*a33*b22 - 
    2*a14*a22*a33*b14 + a14*a22*a34*b13 - a14*a23*a24*b13 - a14*a23*a34*b12 + a14*a24*a33*b12 + 
    4*a22*a33*a44*b11 - a22*a34^2*b11 - a23^2*a44*b11 + a23*a24*a34*b11 - a24^2*a33*b11

  e = 4*a11*a22*a33*a44 - a11*a22*a34^2 - a11*a23^2*a44 + a11*a23*a24*a34 - a11*a24^2*a33 - a12^2*a33*a44
    + a12*a13*a23*a44 - a12*a13*a24*a34 - a12*a14*a23*a34 + a12*a14*a24*a33 - a13^2*a22*a44 + 
    a13*a14*a22*a34 - a13*a14*a23*a24 - a14^2*a22*a33

  l = a12*a34 + a13*a24 + a14*a23
  m = a12*b34 + a13*b24 + a14*b23 + a23*b14 + a24*b13 + a34*b12
  n = b12*b34 + b13*b24 + b14*b23

  R, (x,z) = polynomial_ring(K, [:x,:z])
  D = g1_model_d2(a*x^4 + b*x^3*z + c*x^2*z^2 +d*x*z^3 + e*z^4, l*x^2 + m*x*z + n*z^2)
  return a_invariants(D)
end

