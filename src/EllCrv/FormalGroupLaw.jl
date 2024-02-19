###############################################################################
#
#  Formal Group Law
#
#
#  (C) 2022 Jeroen Hanselman
#
###############################################################################

#Can probably be made more efficient using Newton iteration like Sage does.
@doc raw"""
    formal_w(E::EllipticCurve, prec::Int) -> LaurentSeriesElem

Return the formal expansion of w = -1/y at infinity in terms of parameter z= -x/y up to O(z^prec).
"""
function formal_w(E::EllipticCurve, prec::Int = 20)
  k = base_field(E)
  kz, z = laurent_series_ring(k, prec, "z")
  kzw, w = polynomial_ring(kz, "w")

  a1, a2, a3, a4, a6 = a_invariants(E)

  f = z^3 + a1*z*w + a2*z^2*w + a3*w^2 + a4*z*w^2 + a6*w^3
  result = z^3 + a1*z*w + a2*z^2*w + a3*w^2 + a4*z*w^2 + a6*w^3

  for i in (1:prec)
    result = truncate(f(result), div(10,3))
  end
  return result(0)

end

@doc raw"""
    formal_y(E::EllipticCurve, prec::Int) -> LaurentSeriesElem

Return the formal expansion of y at infinity in terms of parameter z= -x/y up to O(z^prec).
"""
function formal_y(E::EllipticCurve, prec::Int = 20)

  #I took this prec + 6 from Sage
  w = formal_w(E, prec + 6)
  return truncate(-inv(w), prec)

end

@doc raw"""
    formal_x(E::EllipticCurve, prec::Int) -> LaurentSeriesElem

Return the formal expansion of x at infinity in terms of parameter z= -x/y up to O(z^prec).
"""
function formal_x(E::EllipticCurve, prec::Int = 20)

  y = formal_y(E, prec)
  z = gen(parent(y))
  return truncate(-z*y, prec)

end

@doc raw"""
    formal_differential_form(E::EllipticCurve, prec::Int) -> LaurentSeriesElem

Return the formal expansion of f(z) where f(z)dz is the invariant differential dx/(2y + a_1 x + a_3)
at infinity in terms of parameter z= -x/y up to O(z^prec).
"""
function formal_differential_form(E::EllipticCurve, prec::Int = 20)
  a1, a2, a3, a4, a6 = a_invariants(E)
  x = formal_x(E, prec + 1)
  y = formal_y(E, prec + 1)
  dx = derivative(x)

  return truncate(dx//(2*y + a1*x + a3), prec)
end

@doc raw"""
    formal_log(E::EllipticCurve, prec::Int) -> LaurentSeriesElem

Return the formal logarithm of E as a power series at infinity in terms of the parameter z= -x/y up to O(z^prec).
"""
function formal_log(E::EllipticCurve, prec::Int = 20)
  return integral(formal_differential_form(E, prec - 1))
end

#Taking powers is inefficient here everywhere
#=function formal_group_law(E::EllipticCurve, prec::Int = 20)
  k = base_field(E)
  a1, a2, a3, a4, a6 = a_invariants(E)
  ktt, (z1, z2) = power_series_ring(k, prec + 1, ["z1", "z2"])

  #We now compute the slope lambda of the addition in the formal group law
  #Following Silverman
  #A_n-3 = w[n] for n in 3 to infinity
  #(z1^n - z2^n)//(z1 - z2) = z1^(n-1) + z1^(n-2)*z2 +.... +z2^(n-2)
  #lambda = sum A_n-3*(z1^n - z2^n)//(z1 - z2)

  w = formal_w(E, prec + 1)

  lambda = sum([coeff(w, n)*sum([z1^m * z2^(n-m-1) for m in (0:n-1)]) for n in (3:prec +1)])

  #Needs to simply be evaluating
  wz1 = sum([coeff(w, i)*z1^i for i in (0:prec +1)])

  nu = wz1 - lambda*z1

  z3 = -z1 - z2 - divexact(a1*lambda + a3*lambda^2 + a2*nu + 2*a4*lambda*nu + 3*a6*lambda^2*nu, 1 + a2*lambda + a4*lambda^2 + a6*lambda^3)

  inv = formal_inverse(E, prec)

  #Needs to simply be evaluating
  result = sum([coeff(inv, i)*z3^i for i in (0:prec +1)])

  #Sage and Magma truncate to O(z1, z2)^20 instead of O(z1)^20 + O(z2)^20 like we do
  return result
end
=#

@doc raw"""
    formal_inverse(E::EllipticCurve, prec::Int) -> LaurentSeriesElem

Return the formal power series i with the property that F(z, i(z)) = 0 where F is the formal group law of E
in terms of the parameter z= -x/y up to O(z^prec).
"""
function formal_inverse(E::EllipticCurve, prec::Int = 20)
   x = formal_x(E, prec+1)
   y = formal_y(E, prec+1)
   a1, a2, a3 = a_invariants(E)
   return truncate(x //(y + a1*x + a3), prec)
end

@doc raw"""
    formal_isogeny(phi::Isogeny, prec::Int) -> LaurentSeriesElem

Return the formal power series associated to the formal group homomorphism
associated tot the isogeny phi in terms of the parameter z= -x/y up to O(z^prec).
"""
function formal_isogeny(phi::Isogeny, prec::Int = 20)
  E = domain(phi)
  x = formal_x(E, prec)
  y = formal_y(E, prec)

  Rz = parent(x)

  maps = rational_maps(phi)

  fnum = change_base_ring(Rz, numerator(maps[1]))
  fdenom = change_base_ring(Rz, denominator(maps[1]))
  gnum = change_base_ring(Rz, numerator(maps[2]))
  gdenom = change_base_ring(Rz, denominator(maps[2]))
  return - fnum(x, y)*gdenom(x, y)//(fdenom(x, y)*gnum(x, y))
end

