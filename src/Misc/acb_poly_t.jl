################################################################################
#
#  acb_poly_t.jl: Wrapper for acb_poly_t C-struct
#
################################################################################

export acb_poly_t, AcbPolyRing

export complex_roots, degree, length, one, zero

################################################################################
#
#  Types and memory management
#
################################################################################

AcbPolyRingID = ObjectIdDict()

type AcbPolyRing <: Ring
  base_ring::Ring
  S::Symbol

  function AcbPolyRing(R::Ring, S::Symbol)
    try
      return AcbPolyRingID[R, S]
    catch
      AcbPolyRingID[R, S] = new(R,S)
    end
  end
end
    
type acb_poly_t
  data::Ptr{Void}
  length::Clong
  degree::Clong
  parent::AcbPolyRing

  function acb_poly_t()
    z = new()
    z.data = ccall((:_acb_poly_init, :libarb), Ptr{Void}, ())
    ccall((:acb_poly_init, :libarb), Ptr{Void}, (Ptr{Void}, ), z.data)
    finalizer(z, _acb_poly_clear_fn)
    return z
  end

  function acb_poly_t(x::fmpz_poly, p::Clong)
    z = new() 
    z.data = ccall((:_acb_poly_init, :libarb), Ptr{Void}, ())
    ccall((:acb_poly_init, :libarb), Ptr{Void}, (Ptr{Void}, ), z.data)
    ccall((:acb_poly_set_fmpz_poly, :libarb), Void, (Ptr{Void}, Ptr{fmpz_poly}, Clong), z.data, &x, p)
    finalizer(z, _acb_poly_clear_fn)
    z.length = length(x)
    z.degree = degree(x)
    return z
  end

  function acb_poly_t(x::fmpq_poly, p::Clong)
    z = new() 
    z.data = ccall((:_acb_poly_init, :libarb), Ptr{Void}, ())
    ccall((:acb_poly_init, :libarb), Ptr{Void}, (Ptr{Void}, ), z.data)
    ccall((:acb_poly_set_fmpq_poly, :libarb), Void, (Ptr{Void}, Ptr{fmpq_poly}, Clong), z.data, &x, p)
    finalizer(z, _acb_poly_clear_fn)
    z.length = length(x)
    z.degree = degree(x)
    return z
  end
end

function _acb_poly_clear_fn(a::acb_poly_t)
  ccall((:acb_poly_clear, :libarb), Void, (Ptr{Void}, ), a.data)
end

parent(x::acb_poly_t) = x.parent

var(r::AcbPolyRing) = r.S

function coeff(a::acb_poly_t, n::Clong)
  n < 0 && n > degree(a) && throw(DomainError())
  temp = acb_t()
  temp.parent = parent(a).base_ring
  ccall((:acb_poly_get_coeff_acb, :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong), temp.data, a.data, n)
  return temp
end

function set_coeff!(x::acb_poly_t, n::Clong, y::acb_t)
  n < 0 && n > degree(a) && throw(DomainError())
  x.base_ring != parent(y) && error("base ring is not parent of element")
  ccall((:acb_poly_set_coeff_acb, :libarb), Void, (Ptr{Void}, Clong, Ptr{Void}), x.data, n, y.data)
end

function one(r::AcbPolyRing)
  z = r()
  ccall((:acb_poly_one, :libarb), Void, (Ptr{Void}, ), z.data)
  return z
end

function zero(r::AcbPolyRing)
  z = r()
  ccall((:acb_poly_zero, :libarb), Void, (Ptr{Void}, ), z.data)
  return z
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, f::acb_poly_t)
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

################################################################################
#
#  Primitive functions
#
################################################################################

function length(f::acb_poly_t)
  l = ccall((:_acb_poly_length, :libarb), Clong, (Ptr{Void}, ), f.data)
  f.length = l
  return f.length
end

function degree(f::acb_poly_t)
  l = ccall((:_acb_poly_degree, :libarb), Clong, (Ptr{Void}, ), f.data)
  f.degree = l
  return f.degree
end

################################################################################
#
#  Root isolation for fmpz_poly
#
################################################################################

function complex_roots(f::fmpz_poly; target_prec::Clong = 2, initial_prec::Clong = 32)
  result_ptr = ccall((:poly_roots, :libarb), Ptr{Void}, (Ptr{fmpz_poly}, Clong, Clong, Clong), &f, initial_prec, target_prec, 0)
  return _get_from_acb_arr(result_ptr, degree(f), target_prec)
end

function _get_from_acb_arr(vec::Ptr{Void}, length::Clong, p::Clong)
  a = acb_t[]
  for i=0:length-1
    z = acb_t()
    ccall((:_acb_poly_arr_get, :libarb), Void, (Ptr{Void}, Ptr{Void}, Clong), z.data, vec, i)
    z.parent = AcbField(p)
    push!(a,z)
  end
  return a
end

################################################################################
#
#  Parent object overloads
#
################################################################################

function Base.call(r::AcbPolyRing)
  z = acb_poly_t()
  z.parent = r
  return z
end

function Base.call(r::AcbPolyRing, x::fmpz_poly)
  z = acb_poly_t(x, r.base_ring.prec)
  z.parent = r
  return z
end

function Base.call(r::AcbPolyRing, x::fmpq_poly)
  z = acb_poly_t(x, r.base_ring.prec)
  z.parent = r
  return z
end
  
################################################################################
#
#  Polynomial ring constructor
#
################################################################################

function PolynomialRing(R::AcbField, s::ASCIIString)
  obj = AcbPolyRing(R, symbol(s))
  return obj, symbol(s)
end
