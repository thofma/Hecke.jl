export acb_poly

type acb_poly
  coeffs::Ptr{Void}
  length::Clong
  alloc::Clong

  function acb_poly(x::fmpz_poly, p::Clong)
    z = new() 
    ccall((:acb_poly_init, :libarb), Void, (Ptr{acb_poly}, ), &z)
    ccall((:acb_poly_set_fmpz_poly, :libarb), Void, (Ptr{acb_poly}, Ptr{fmpz_poly}, Clong), &z, &x, p)
    finalizer(z, _acb_poly_clear_fn)
    return z
  end

  function acb_poly()
    z = new()
    ccall((:acb_poly_init, :libarb), Void, (Ptr{acb_poly}, ), &z)
    finalizer(z, _acb_poly_clear_fn)
    return z
  end
end

function _acb_poly_clear_fn(x::acb_poly)
  ccall((:acb_poly_clear, :libarb), Void, (Ptr{acb_poly}, ), &x)
end

function show(io::IO, f::acb_poly)
  if length(f) == 0
    print(io, "0")
  else
    print(io, "[ ")
    for i in 0:degree(f)-1
      show(io, coeff(f,i))
      print(io, ", ")
    end
    show(coeff(f,degree(f)))
    print(io, " ]")
  end
end

function coeff(a::acb_poly, n::Clong)
  n < 0 && n > degree(a) && throw(DomainError())
  t = acb()
  ccall((:acb_poly_get_coeff_acb, :libarb), Void, (Ptr{acb}, Ptr{acb_poly}, Clong), &t, &a, n)
  return t
end

degree(f::acb_poly) = f.length - 1

length(f::acb_poly) = f.length
