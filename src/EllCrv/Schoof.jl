
function fn_from_schoof(E::EllCrv, n::Int, x)
    
    R = base_field(E)
    S, y = PolynomialRing(parent(x),"y")
    
    f = psi_poly_field(E, n, x, y)
    
   # println("f: $f, $(degree(f))")
    
    g = x^3 + E.coeff[1]*x + E.coeff[2]

    if isodd(n)
        return replace_all_squares(f, g)
        
    else
        return replace_all_squares(divexact(f, y), g)
    end
end

function mult_with_n_y_component(E::EllCrv, n::Int, x)
    # the second component is y*r(x). This function returns the r(x)
    # y*r(x) = omega_n(x, y)/psi_n^3(x, y) = omega_n(x, y)/psi_n^2(x, y) * 1/psi_n(x, y)
    # the first factor is a polynomial in x (after replacing y^2 with x^3 + .. )
    # 1/psi_n(x, y) = 1/(y * p(x)) = y/(y^2 * p(x)) = y * 1/(pp(x))
    # also r(x) = omega_n(x, y)/psi_n^2(x, y) * 1/pp(x) (replace y^2 with x^3)
end
