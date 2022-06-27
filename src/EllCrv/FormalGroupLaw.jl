###############################################################################
#
#  Formal Group Law
#
#
#  (C) 2022 Jeroen Hanselman
#
###############################################################################

export formal_w, formal_y, formal_x, formal_differential_form, formal_log, formal_isogeny, formal_group_law, formal_inverse

#Can probably be made more efficient using Newton iteration like Sage does.
function formal_w(E::EllCrv, prec::Int = 20)
  k = base_field(E)
  kz, z = LaurentSeriesRing(k, prec, "z")
  kzw, w = PolynomialRing(kz, "w")
  
  a1, a2, a3, a4, a6 = a_invars(E)
  
  f = z^3 + a1*z*w + a2*z^2*w + a3*w^2 + a4*z*w^2 + a6*w^3
  result = z^3 + a1*z*w + a2*z^2*w + a3*w^2 + a4*z*w^2 + a6*w^3
  
  for i in (1:prec)
    result = truncate(f(result), div(10,3))
  end
  return result(0)
  
end

function formal_y(E::EllCrv, prec::Int = 20)

  #I took this prec + 6 from Sage
  w = formal_w(E, prec + 6)
  return truncate(-inv(w), prec)

end

function formal_x(E::EllCrv, prec::Int = 20)

  y = formal_y(E, prec)
  z = gen(parent(y))
  return truncate(-z*y, prec)

end

function formal_differential_form(E::EllCrv, prec::Int = 20)
  
  a1, a2, a3, a4, a6 = a_invars(E)
  x = formal_x(E, prec + 1)
  y = formal_y(E, prec + 1)
  dx = derivative(x)
  
  return truncate(dx//(2*y + a1*x + a3), prec)

end

function formal_log(E::EllCrv, prec::Int = 20)
  return integral(formal_differential_form(E, prec - 1))
end

function formal_group_law(E::EllCrv, prec::Int = 20)
  k = base_field(E)
  a1, a2, a3, a4, a6 = a_invars(E)
  ktt, (z1, z2) = PowerSeriesRing(k, prec, ["z1", "z2"])
  
  #We now compute the slope lambda of the addition in the formal group law
  #Following Silverman
  #A_n-3 = w[n] for n in 3 to infinity
  #(z1^n - z2^n)//(z1 - z2) = z1^(n-1) + z1^(n-2)*z2 +.... +z2^(n-2) 
  #lambda = sum A_n-3*(z1^n - z2^n)//(z1 - z2) 
  
  w = formal_w(E, prec + 1)
  
  lambda = sum([coeff(w, n - 3)*sum([z1^m * z2^(n-m) for m in (1:n)]) for n in (3:prec +1)])
  
  nu = w(z1) - lambda*z1
  
  z3_num = -z1 - z2 - (a1*lambda + a3*lambda^2 + a2*nu + 2*a4*lambda*nu + 3*a6*lambda^2*nu)
  z3_denom = (1 + a2*lambda + a4*lambda^2 + a6*lambda^3)
  
  z3 = z3_num//z3_denom
  
  return truncate(formal_inverse(E, prec)(z3), prec)
  
end

function formal_inverse(E::EllCrv, prec::Int = 20)
   x = formal_x(prec)
   y = formal_y(prec)
   a1, a2, a3 = a_invars(E)
   return truncate(x //(y + a1*x + a3), prec)
end

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

