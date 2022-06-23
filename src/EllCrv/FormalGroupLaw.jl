###############################################################################
#
#  Formal Group Law
#
#
#  (C) 2022 Jeroen Hanselman
#
###############################################################################

export formal_w, formal_y, formal_x, formal_differential_form, formal_log, formal_isogeny

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


function formal_isogeny(phi::Isogeny, prec::Int = 20)
  E = domain(phi)
  x = formal_x(E, prec)
  y = formal_y(E, prec)
  
  Rz = parent(x)
  
  maps =rational_maps(phi)
  
  fnum = change_base_ring(Rz, numerator(maps[1]))
  fdenom = change_base_ring(Rz, denominator(maps[1]))
  gnum = change_base_ring(Rz, numerator(maps[2]))
  gdenom = change_base_ring(Rz, denominator(maps[2]))
  
  
  return fnum(x, y)*gdenom(x, y)//(fdenom(x, y)*gnum(x, y))
end

