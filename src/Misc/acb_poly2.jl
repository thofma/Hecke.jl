###############################################################################
#
#   acb_poly.jl : Polynomials over arb
#
###############################################################################

# Copyright 2015 - Fredrik Johansson

export AcbPolyRing, acb_poly, isreal, strongequal, derivative, integral, evaluate,
       evaluate2, compose, from_roots, evaluate_iter, evaluate_fast, evaluate,
       interpolate_newton, interpolate_barycentric, interpolate_fast, interpolate,
       roots

const AcbPolyRingID = ObjectIdDict()

type AcbPolyRing <: Ring
  base_ring::AcbField
  S::Symbol

  function AcbPolyRing(R::AcbField, S::Symbol)
    try
      return AcbPolyRingID[R, S]::AcbPolyRing
    catch
      AcbPolyRingID[R, S] = new(R,S)
      return AcbPolyRingID[R, S]::AcbPolyRing
    end
  end
end

type acb_struct
  real_mid_exp::Int # fmpz
  real_mid_size::UInt # mp_size_t
  real_mid_d1::Int # mantissa_struct
  real_mid_d2::Int
  real_rad_exp::Int # fmpz
  real_rad_man::UInt
  imag_mid_exp::Int # fmpz
  imag_mid_size::UInt # mp_size_t
  imag_mid_d1::Int # mantissa_struct
  imag_mid_d2::Int
  imag_rad_exp::Int # fmpz
  imag_rad_man::UInt
end

type acb_poly <: PolyElem{acb}
  coeffs::Ptr{Void}
  length::Int
  alloc::Int
  parent::AcbPolyRing

  function acb_poly()
    z = new()
    ccall((:acb_poly_init, :libarb), Void, (Ptr{acb_poly}, ), &z)
    finalizer(z, _acb_poly_clear_fn)
    return z
  end

  function acb_poly(x::acb, p::Int)
    z = new() 
    ccall((:acb_poly_init, :libarb), Void, (Ptr{acb_poly}, ), &z)
    ccall((:acb_poly_set_coeff_acb, :libarb), Void,
                (Ptr{acb_poly}, Int, Ptr{acb}), &z, 0, &x)
    finalizer(z, _acb_poly_clear_fn)
    return z
  end

  function acb_poly(x::Array{acb, 1}, p::Int)
    z = new() 
    ccall((:acb_poly_init, :libarb), Void, (Ptr{acb_poly}, ), &z)
    for i = 1:length(x)
        ccall((:acb_poly_set_coeff_acb, :libarb), Void,
                (Ptr{acb_poly}, Int, Ptr{acb}), &z, i - 1, &x[i])
    end
    finalizer(z, _acb_poly_clear_fn)
    return z
  end

  function acb_poly(x::acb_poly)
    z = new() 
    ccall((:acb_poly_init, :libarb), Void, (Ptr{acb_poly}, ), &z)
    ccall((:acb_poly_set, :libarb), Void, (Ptr{acb_poly}, Ptr{acb_poly}), &z, &x)
    finalizer(z, _acb_poly_clear_fn)
    return z
  end

#  function acb_poly(x::arb_poly, p::Int)
#    z = new() 
#    ccall((:acb_poly_init, :libarb), Void, (Ptr{acb_poly}, ), &z)
#    ccall((:acb_poly_set_arb_poly, :libarb), Void,
#                (Ptr{acb_poly}, Ptr{arb_poly}, Int), &z, &x, p)
#    ccall((:acb_poly_set_round, :libarb), Void,
#                (Ptr{acb_poly}, Ptr{acb_poly}, Int), &z, &z, p)
#    finalizer(z, _acb_poly_clear_fn)
#    return z
#  end

  function acb_poly(x::acb_poly, p::Int)
    z = new() 
    ccall((:acb_poly_init, :libarb), Void, (Ptr{acb_poly}, ), &z)
    ccall((:acb_poly_set_round, :libarb), Void,
                (Ptr{acb_poly}, Ptr{acb_poly}, Int), &z, &x, p)
    finalizer(z, _acb_poly_clear_fn)
    return z
  end

  function acb_poly(x::fmpz_poly, p::Int)
    z = new() 
    ccall((:acb_poly_init, :libarb), Void, (Ptr{acb_poly}, ), &z)
    ccall((:acb_poly_set_fmpz_poly, :libarb), Void,
                (Ptr{acb_poly}, Ptr{fmpz_poly}, Int), &z, &x, p)
    finalizer(z, _acb_poly_clear_fn)
    return z
  end

  function acb_poly(x::fmpq_poly, p::Int)
    z = new() 
    ccall((:acb_poly_init, :libarb), Void, (Ptr{acb_poly}, ), &z)
    ccall((:acb_poly_set_fmpq_poly, :libarb), Void,
                (Ptr{acb_poly}, Ptr{fmpq_poly}, Int), &z, &x, p)
    finalizer(z, _acb_poly_clear_fn)
    return z
  end
end

function _acb_poly_clear_fn(x::acb_poly)
  ccall((:acb_poly_clear, :libarb), Void, (Ptr{acb_poly}, ), &x)
end

parent(x::acb_poly) = x.parent

elem_type(x::AcbPolyRing) = acb_poly

var(x::AcbPolyRing) = x.S

prec(x::AcbPolyRing) = prec(x.base_ring)

base_ring(a::AcbPolyRing) = a.base_ring

###############################################################################
#
#   Basic manipulation
#
###############################################################################    
  
length(x::acb_poly) = ccall((:acb_poly_length, :libarb), Int, 
                                   (Ptr{acb_poly},), &x)

set_length!(x::acb_poly, n::Int) = ccall((:_acb_poly_set_length, :libarb), Void,
                                   (Ptr{acb_poly}, Int), &x, n)

degree(x::acb_poly) = length(x) - 1

function coeff(a::acb_poly, n::Int)
  n < 0 && throw(DomainError())
  t = parent(a).base_ring()
  ccall((:acb_poly_get_coeff_acb, :libarb), Void,
              (Ptr{acb}, Ptr{acb_poly}, Int), &t, &a, n)
  return t
end

zero(a::AcbPolyRing) = a(0)

one(a::AcbPolyRing) = a(1)

function gen(a::AcbPolyRing)
   z = acb_poly()
   ccall((:acb_poly_set_coeff_si, :libarb), Void,
        (Ptr{acb_poly}, Int, Int), &z, 1, 1)
   z.parent = a
   return z
end

# todo: write a C function for this
function isgen(a::acb_poly)
   return strongequal(a, gen(parent(a)))
end

#function iszero(a::acb_poly)
#   return length(a) == 0
#end

#function isone(a::acb_poly)
#   return strongequal(a, one(parent(a)))
#end

function deepcopy(a::acb_poly)
   z = acb_poly(a)
   z.parent = parent(a)
   return z
end

###############################################################################
#
#   AbstractString{} I/O
#
###############################################################################

function show(io::IO, x::AcbPolyRing)
  print(io, "Univariate Polynomial Ring in ")
  print(io, string(var(x)))
  print(io, " over ")
  show(io, x.base_ring)
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

###############################################################################
#
#   Comparisons
#
###############################################################################

function strongequal(x::acb_poly, y::acb_poly)
   return ccall((:acb_poly_equal, :libarb), Bool, 
                                      (Ptr{acb_poly}, Ptr{acb_poly}), &x, &y)
end

function overlaps(x::acb_poly, y::acb_poly)
   return ccall((:acb_poly_overlaps, :libarb), Bool, 
                                      (Ptr{acb_poly}, Ptr{acb_poly}), &x, &y)
end

function contains(x::acb_poly, y::acb_poly)
   return ccall((:acb_poly_contains, :libarb), Bool, 
                                      (Ptr{acb_poly}, Ptr{acb_poly}), &x, &y)
end

function contains(x::acb_poly, y::fmpz_poly)
   return ccall((:acb_poly_contains_fmpz_poly, :libarb), Bool, 
                                      (Ptr{acb_poly}, Ptr{fmpz_poly}), &x, &y)
end

function contains(x::acb_poly, y::fmpq_poly)
   return ccall((:acb_poly_contains_fmpq_poly, :libarb), Bool, 
                                      (Ptr{acb_poly}, Ptr{fmpq_poly}), &x, &y)
end

function ==(x::acb_poly, y::acb_poly)
    if length(x) != length(y)
        return false
    end
    for i = 0:degree(x)
        if !(coeff(x, i) == coeff(y, i))
            return false
        end
    end
    return true
end

function !=(x::acb_poly, y::acb_poly)
    for i = 0:max(degree(x), degree(y))
        if coeff(x, i) != coeff(y, i)
            return true
        end
    end
    return false
end

function unique_integer(x::acb_poly)
  z = FmpzPolyRing(var(parent(x)))()
  unique = ccall((:acb_poly_get_unique_fmpz_poly, :libarb), Int,
    (Ptr{fmpz_poly}, Ptr{acb_poly}), &z, &x)
  return (unique != 0, z)
end

function isreal(x::acb_poly)
  return ccall((:acb_poly_is_real, :libarb), Cint, (Ptr{acb_poly}, ), &x) != 0
end

###############################################################################
#
#   Shifting
#
###############################################################################

function shift_left(x::acb_poly, len::Int)
   len < 0 && throw(DomainError())
   z = parent(x)()
   ccall((:acb_poly_shift_left, :libarb), Void,
      (Ptr{acb_poly}, Ptr{acb_poly}, Int), &z, &x, len)
   return z
end

function shift_right(x::acb_poly, len::Int)
   len < 0 && throw(DomainError())
   z = parent(x)()
   ccall((:acb_poly_shift_right, :libarb), Void,
       (Ptr{acb_poly}, Ptr{acb_poly}, Int), &z, &x, len)
   return z
end

################################################################################
#
#  Unary operations
#
################################################################################

function -(x::acb_poly)
  z = parent(x)()
  ccall((:acb_poly_neg, :libarb), Void, (Ptr{acb_poly}, Ptr{acb_poly}), &z, &x)
  return z
end

################################################################################
#
#  Binary operations
#
################################################################################

function +(x::acb_poly, y::acb_poly)
  z = parent(x)()
  ccall((:acb_poly_add, :libarb), Void,
              (Ptr{acb_poly}, Ptr{acb_poly}, Ptr{acb_poly}, Int),
              &z, &x, &y, prec(parent(x)))
  return z
end

function *(x::acb_poly, y::acb_poly)
  z = parent(x)()
  ccall((:acb_poly_mul, :libarb), Void,
              (Ptr{acb_poly}, Ptr{acb_poly}, Ptr{acb_poly}, Int),
              &z, &x, &y, prec(parent(x)))
  return z
end

function -(x::acb_poly, y::acb_poly)
  z = parent(x)()
  ccall((:acb_poly_sub, :libarb), Void,
              (Ptr{acb_poly}, Ptr{acb_poly}, Ptr{acb_poly}, Int),
              &z, &x, &y, prec(parent(x)))
  return z
end

function ^(x::acb_poly, y::Int)
  y < 0 && throw(DomainError())
  z = parent(x)()
  ccall((:acb_poly_pow_ui, :libarb), Void,
              (Ptr{acb_poly}, Ptr{acb_poly}, UInt, Int),
              &z, &x, y, prec(parent(x)))
  return z
end

###############################################################################
#
#   Ad hoc binary operators
#
###############################################################################

#function +(x::acb_poly, y::Union{Int,fmpz,fmpq,Float64,arb,fmpz_poly,fmpq_poly})
#    return x + parent(x)(y)
#end

#function -(x::acb_poly, y::Union{Int,fmpz,fmpq,Float64,arb,fmpz_poly,fmpq_poly})
#    return x - parent(x)(y)
#end

#function *(x::acb_poly, y::Union{Int,fmpz,fmpq,Float64,arb,fmpz_poly,fmpq_poly})
#    return x * parent(x)(y)
#end

#function +(x::Union{Int,fmpz,fmpq,Float64,arb,fmpz_poly,fmpq_poly}, y::acb_poly)
#    return parent(y)(x) + y
#end

#function -(x::Union{Int,fmpz,fmpq,Float64,arb,fmpz_poly,fmpq_poly}, y::acb_poly)
#    return parent(y)(x) - y
#end

#function *(x::Union{Int,fmpz,fmpq,Float64,arb,fmpz_poly,fmpq_poly}, y::acb_poly)
#    return parent(y)(x) * y
#end

###############################################################################
#
#   Scalar division
#
###############################################################################

function divexact(x::acb_poly, y::Union{Int,fmpz,fmpq,Float64,arb,acb})
    return x * inv(base_ring(parent(x))(y))
end

//(x::acb_poly, y::Union{Int,fmpz,fmpq,Float64,arb,acb}) = divexact(x, y)

###############################################################################
#
#   Euclidean division
#
###############################################################################

function divrem(x::acb_poly, y::acb_poly)
   iszero(y) && throw(DivideError())
   q = parent(x)()
   r = parent(x)()
   if (ccall((:acb_poly_divrem, :libarb), Int, 
         (Ptr{acb_poly}, Ptr{acb_poly}, Ptr{acb_poly}, Ptr{acb_poly}, Int), 
               &q, &r, &x, &y, prec(parent(x))) == 1)
      return (q, r)
   else
      throw(DivideError())
   end
end

function mod(x::acb_poly, y::acb_poly)
   return divrem(x, y)[2]
end

function divexact(x::acb_poly, y::acb_poly)
   return divrem(x, y)[1]
end

###############################################################################
#
#   Truncation
#
###############################################################################

function truncate(a::acb_poly, n::Int)
   n < 0 && throw(DomainError())
   if length(a) <= n
      return a
   end
   # todo: implement set_trunc in arb
   z = deepcopy(a)
   ccall((:acb_poly_truncate, :libarb), Void,
                (Ptr{acb_poly}, Int), &z, n)
   return z
end

function mullow(x::acb_poly, y::acb_poly, n::Int)
   n < 0 && throw(DomainError())
   z = parent(x)()
   ccall((:acb_poly_mullow, :libarb), Void,
         (Ptr{acb_poly}, Ptr{acb_poly}, Ptr{acb_poly}, Int, Int),
            &z, &x, &y, n, prec(parent(x)))
   return z
end

###############################################################################
#
#   Reversal
#
###############################################################################

#function reverse(x::acb_poly, len::Int)
#   len < 0 && throw(DomainError())
#   z = parent(x)()
#   ccall((:acb_poly_reverse, :libarb), Void,
#                (Ptr{acb_poly}, Ptr{acb_poly}, Int), &z, &x, len)
#   return z
#end

###############################################################################
#
#   Evaluation
#
###############################################################################

function evaluate(x::acb_poly, y::acb)
   z = parent(y)()
   ccall((:acb_poly_evaluate, :libarb), Void, 
                (Ptr{acb}, Ptr{acb_poly}, Ptr{acb}, Int),
                &z, &x, &y, prec(parent(y)))
   return z
end

function evaluate2(x::acb_poly, y::acb)
   z = parent(y)()
   w = parent(y)()
   ccall((:acb_poly_evaluate2, :libarb), Void, 
                (Ptr{acb}, Ptr{acb}, Ptr{acb_poly}, Ptr{acb}, Int),
                &z, &w, &x, &y, prec(parent(y)))
   return z, w
end

function evaluate(x::acb_poly, y::Union{Int,Float64,fmpq,arb})
    return evaluate(x, base_ring(parent(x))(y))
end

function evaluate(x::acb_poly, y::fmpz)
    return evaluate(x, base_ring(parent(x))(y))
end

function evaluate2(x::acb_poly, y::Union{Int,Float64,fmpz,fmpq,arb})
    return evaluate2(x, base_ring(parent(x))(y))
end

###############################################################################
#
#   Composition
#
###############################################################################

function compose(x::acb_poly, y::acb_poly)
   z = parent(x)()
   ccall((:acb_poly_compose, :libarb), Void, 
                (Ptr{acb_poly}, Ptr{acb_poly}, Ptr{acb_poly}, Int),
                &z, &x, &y, prec(parent(x)))
   return z
end

###############################################################################
#
#   Derivative and integral
#
###############################################################################

function derivative(x::acb_poly)
   z = parent(x)()
   ccall((:acb_poly_derivative, :libarb), Void, 
                (Ptr{acb_poly}, Ptr{acb_poly}, Int), &z, &x, prec(parent(x)))
   return z
end

function integral(x::acb_poly)
   z = parent(x)()
   ccall((:acb_poly_integral, :libarb), Void, 
                (Ptr{acb_poly}, Ptr{acb_poly}, Int), &z, &x, prec(parent(x)))
   return z
end

###############################################################################
#
#   Multipoint evaluation and interpolation
#
###############################################################################

function acb_vec(n::Int)
   return ccall((:_acb_vec_init, :libarb), Ptr{acb_struct}, (Int,), n)
end

function acb_vec(b::Array{acb, 1})
   v = ccall((:_acb_vec_init, :libarb), Ptr{acb_struct}, (Int,), length(b))
   for i=1:length(b)
       ccall((:acb_set, :libarb), Void, (Ptr{acb_struct}, Ptr{acb}),
           v + (i-1)*sizeof(acb_struct), &b[i])
   end
   return v
end

function array(R::AcbField, v::Ptr{acb_struct}, n::Int)
   r = Array(acb, n)
   for i=1:n
       r[i] = R()
       ccall((:acb_set, :libarb), Void, (Ptr{acb}, Ptr{acb_struct}),
           &r[i], v + (i-1)*sizeof(acb_struct))
   end
   return r
end

function acb_vec_clear(v::Ptr{acb_struct}, n::Int)
   ccall((:_acb_vec_clear, :libarb), Void, (Ptr{acb_struct}, Int), v, n)
end

function from_roots(R::AcbPolyRing, b::Array{acb, 1})
   z = R()
   tmp = acb_vec(b)
   ccall((:acb_poly_product_roots, :libarb), Void, 
                (Ptr{acb_poly}, Ptr{acb_struct}, Int, Int), &z, tmp, length(b), prec(R))
   acb_vec_clear(tmp, length(b))
   return z
end

function evaluate_iter(x::acb_poly, b::Array{acb, 1})
   return acb[evaluate(x, b[i]) for i=1:length(b)]
end

function evaluate_fast(x::acb_poly, b::Array{acb, 1})
   tmp = acb_vec(b)
   ccall((:acb_poly_evaluate_vec_fast, :libarb), Void, 
                (Ptr{acb_struct}, Ptr{acb_poly}, Ptr{acb_struct}, Int, Int),
            tmp, &x, tmp, length(b), prec(parent(x)))
   res = array(base_ring(parent(x)), tmp, length(b))
   acb_vec_clear(tmp, length(b))
   return res
end

function interpolate_newton(R::AcbPolyRing, xs::Array{acb, 1}, ys::Array{acb, 1})
   length(xs) != length(ys) && error()
   z = R()
   xsv = acb_vec(xs)
   ysv = acb_vec(ys)
   ccall((:acb_poly_interpolate_newton, :libarb), Void, 
                (Ptr{acb_poly}, Ptr{acb_struct}, Ptr{acb_struct}, Int, Int),
            &z, xsv, ysv, length(xs), prec(R))
   acb_vec_clear(xsv, length(xs))
   acb_vec_clear(ysv, length(ys))
   return z
end

function interpolate_barycentric(R::AcbPolyRing, xs::Array{acb, 1}, ys::Array{acb, 1})
   length(xs) != length(ys) && error()
   z = R()
   xsv = acb_vec(xs)
   ysv = acb_vec(ys)
   ccall((:acb_poly_interpolate_barycentric, :libarb), Void, 
                (Ptr{acb_poly}, Ptr{acb_struct}, Ptr{acb_struct}, Int, Int),
            &z, xsv, ysv, length(xs), prec(R))
   acb_vec_clear(xsv, length(xs))
   acb_vec_clear(ysv, length(ys))
   return z
end

function interpolate_fast(R::AcbPolyRing, xs::Array{acb, 1}, ys::Array{acb, 1})
   length(xs) != length(ys) && error()
   z = R()
   xsv = acb_vec(xs)
   ysv = acb_vec(ys)
   ccall((:acb_poly_interpolate_fast, :libarb), Void, 
                (Ptr{acb_poly}, Ptr{acb_struct}, Ptr{acb_struct}, Int, Int),
            &z, xsv, ysv, length(xs), prec(R))
   acb_vec_clear(xsv, length(xs))
   acb_vec_clear(ysv, length(ys))
   return z
end

# todo: cutoffs for fast algorithm
function interpolate(R::AcbPolyRing, xs::Array{acb, 1}, ys::Array{acb, 1})
   return interpolate_newton(R, xs, ys)
end

# todo: cutoffs for fast algorithm
function evaluate(x::acb_poly, b::Array{acb, 1})
   return evaluate_iter(x, b)
end

function _roots(x::Union{fmpq_poly, fmpz_poly}, abs_tol = 32, initial_prec = 0, max_iter = 0)
  roots = acb_vec(degree(x))
  deg = degree(x)

  initial_prec = (initial_prec >= 2) ? initial_prec : 32

  wp = initial_prec

  while true
    in_roots = (wp == initial_prec) ? C_NULL : roots
    step_max_iter = (max_iter >= 1) ? max_iter : min(max(deg, 32), wp)
    y = acb_poly(x, wp) 
    isolated = ccall((:acb_poly_find_roots, :libarb), Int,
            (Ptr{acb_struct}, Ptr{acb_poly}, Ptr{acb_struct}, Int, Int),
            roots, &y, in_roots, step_max_iter, wp)


    if isolated == deg
      ok = true
      if abs_tol > 0
        for i = 0 : deg-1
          re = ccall((:acb_real_ptr, :libarb), Ptr{Nemo.arb_struct},
                (Ptr{acb}, ), roots + i * sizeof(acb_struct))
          im = ccall((:acb_imag_ptr, :libarb), Ptr{Nemo.arb_struct},
                (Ptr{acb}, ), roots + i * sizeof(acb_struct))
          t = ccall((:arb_rad_ptr, :libarb), Ptr{Nemo.mag_struct}, (Ptr{arb}, ), re)
          u = ccall((:arb_rad_ptr, :libarb), Ptr{Nemo.mag_struct}, (Ptr{arb}, ), im)
          ok = ok && (ccall((:mag_cmp_2exp_si, :libarb), Cint,
              (Ptr{Nemo.mag_struct}, Int), t, -abs_tol) <= 0)
          ok = ok && (ccall((:mag_cmp_2exp_si, :libarb), Cint,
              (Ptr{Nemo.mag_struct}, Int), u, -abs_tol) <= 0)
        end
      end
      real_ok = ccall((:acb_poly_validate_real_roots, :libarb),
          Bool, (Ptr{acb_struct}, Ptr{acb_poly}, Int), roots, &y, wp)

      if !real_ok
          ok = false
      end

      if real_ok
          for i = 0 : deg - 1
              im = ccall((:acb_imag_ptr, :libarb), Ptr{Nemo.arb_struct},
                  (Ptr{acb}, ), roots + i * sizeof(acb_struct))
              if ccall((:arb_contains_zero, :libarb), Bool, (Ptr{Nemo.arb_struct}, ), im)
                  ccall((:arb_zero, :libarb), Void, (Ptr{Nemo.arb_struct}, ), im)
              end
          end
      end

      if ok
        break
      end
    end

  wp = wp * 2
    if wp > 2^16
      error("Something wrong")
    end
  end
         ccall((:_acb_vec_sort_pretty, :libarb), Void,
            (Ptr{acb_struct}, Int), roots, deg)
        res = array(AcbField(wp), roots, deg)
  acb_vec_clear(roots, deg)
  return res
end

function _roots(x::Union{fmpq_poly, fmpz_poly}, roots::Ptr{acb_struct}, abs_tol = 32, initial_prec = 0, max_iter = 0)
  deg = degree(x)

  initial_prec = (initial_prec >= 2) ? initial_prec : 32

  wp = initial_prec

  while true
    in_roots = roots
    step_max_iter = (max_iter >= 1) ? max_iter : min(max(deg, 32), wp)
    y = acb_poly(x, wp) 
    isolated = ccall((:acb_poly_find_roots, :libarb), Int,
            (Ptr{acb_struct}, Ptr{acb_poly}, Ptr{acb_struct}, Int, Int),
            roots, &y, in_roots, step_max_iter, wp)


    if isolated == deg
      ok = true
      if abs_tol > 0
        for i = 0 : deg-1
          re = ccall((:acb_real_ptr, :libarb), Ptr{Nemo.arb_struct},
                (Ptr{acb}, ), roots + i * sizeof(acb_struct))
          im = ccall((:acb_imag_ptr, :libarb), Ptr{Nemo.arb_struct},
                (Ptr{acb}, ), roots + i * sizeof(acb_struct))
          t = ccall((:arb_rad_ptr, :libarb), Ptr{Nemo.mag_struct}, (Ptr{arb}, ), re)
          u = ccall((:arb_rad_ptr, :libarb), Ptr{Nemo.mag_struct}, (Ptr{arb}, ), im)
          ok = ok && (ccall((:mag_cmp_2exp_si, :libarb), Cint,
              (Ptr{Nemo.mag_struct}, Int), t, -abs_tol) <= 0)
          ok = ok && (ccall((:mag_cmp_2exp_si, :libarb), Cint,
              (Ptr{Nemo.mag_struct}, Int), u, -abs_tol) <= 0)
        end
      end
      real_ok = ccall((:acb_poly_validate_real_roots, :libarb),
          Bool, (Ptr{acb_struct}, Ptr{acb_poly}, Int), roots, &y, wp)

      if !real_ok
          ok = false
      end

      if real_ok
          for i = 0 : deg - 1
              im = ccall((:acb_imag_ptr, :libarb), Ptr{Nemo.arb_struct},
                  (Ptr{acb}, ), roots + i * sizeof(acb_struct))
              if ccall((:arb_contains_zero, :libarb), Bool, (Ptr{Nemo.arb_struct}, ), im)
                  ccall((:arb_zero, :libarb), Void, (Ptr{Nemo.arb_struct}, ), im)
              end
          end
      end

      if ok
        break
      end
    end

  wp = wp * 2
    if wp > 2^16
      error("Something wrong")
    end
  end
         ccall((:_acb_vec_sort_pretty, :libarb), Void,
            (Ptr{acb_struct}, Int), roots, deg)
        res = array(AcbField(wp), roots, deg)
  return res
end


function roots(x::acb_poly; target=0, isolate_real=false, initial_prec=0, max_prec=0, max_iter=0)
    deg = degree(x)
    if deg <= 0
        return Array(acb, 0)
    end

    initial_prec = (initial_prec >= 2) ? initial_prec : 32
    max_prec = (max_prec >= 2) ? max_prec : 3 * prec(parent(x))

    isolated = 0
    wp = initial_prec
    roots = acb_vec(deg)

    while true
        in_roots = (wp == initial_prec) ? C_NULL : roots
        step_max_iter = (max_iter >= 1) ? max_iter : min(max(deg, 32), wp)
        isolated = ccall((:acb_poly_find_roots, :libarb), Int,
            (Ptr{acb_struct}, Ptr{acb_poly}, Ptr{acb_struct}, Int, Int),
                roots, &x, in_roots, step_max_iter, wp)

        wp = wp * 2

        if isolated == deg
            ok = true
            if target > 0
                for i = 0 : deg-1
                    re = ccall((:acb_real_ptr, :libarb), Ptr{Nemo.arb_struct},
                        (Ptr{acb}, ), roots + i * sizeof(acb_struct))
                    im = ccall((:acb_imag_ptr, :libarb), Ptr{Nemo.arb_struct},
                        (Ptr{acb}, ), roots + i * sizeof(acb_struct))
                    t = ccall((:arb_rad_ptr, :libarb), Ptr{Nemo.mag_struct}, (Ptr{arb}, ), re)
                    u = ccall((:arb_rad_ptr, :libarb), Ptr{Nemo.mag_struct}, (Ptr{arb}, ), im)
                    ok = ok && (ccall((:mag_cmp_2exp_si, :libarb), Cint,
                        (Ptr{Nemo.mag_struct}, Int), t, -target) <= 0)
                    ok = ok && (ccall((:mag_cmp_2exp_si, :libarb), Cint,
                        (Ptr{Nemo.mag_struct}, Int), u, -target) <= 0)
                end
            end

            if isreal(x)
                real_ok = ccall((:acb_poly_validate_real_roots, :libarb),
                    Bool, (Ptr{acb_struct}, Ptr{acb_poly}, Int), roots, &x, wp)

                if isolate_real && !real_ok
                    ok = false
                end

                if real_ok
                    for i = 0 : deg - 1
                        im = ccall((:acb_imag_ptr, :libarb), Ptr{Nemo.arb_struct},
                            (Ptr{acb}, ), roots + i * sizeof(acb_struct))
                        if ccall((:arb_contains_zero, :libarb), Bool, (Ptr{Nemo.arb_struct}, ), im)
                            ccall((:arb_zero, :libarb), Void, (Ptr{Nemo.arb_struct}, ), im)
                        end
                    end
                end
            end

            if ok
                break
            end
        end

        if wp > max_prec
            break
        end
    end

    if isolated == deg
        ccall((:_acb_vec_sort_pretty, :libarb), Void,
            (Ptr{acb_struct}, Int), roots, deg)
        res = array(base_ring(parent(x)), roots, deg)
    end

    acb_vec_clear(roots, deg)

    if isolated == deg
        return res
    else
        error("unable to isolate all roots (insufficient precision, or there is a multiple root)")
    end
end

###############################################################################
#
#   Unsafe functions
#
###############################################################################

function fit!(z::acb_poly, n::Int)
   ccall((:acb_poly_fit_length, :libarb), Void, 
                    (Ptr{acb_poly}, Int), &z, n)
end

function setcoeff!(z::acb_poly, n::Int, x::fmpz)
   ccall((:acb_poly_set_coeff_fmpz, :libarb), Void, 
                    (Ptr{acb_poly}, Int, Ptr{fmpz}), &z, n, &x)
end

function setcoeff!(z::acb_poly, n::Int, x::acb)
   ccall((:acb_poly_set_coeff_acb, :libarb), Void, 
                    (Ptr{acb_poly}, Int, Ptr{acb}), &z, n, &x)
end

function mul!(z::acb_poly, x::acb_poly, y::acb_poly)
   ccall((:acb_poly_mul, :libarb), Void, 
                (Ptr{acb_poly}, Ptr{acb_poly}, Ptr{acb_poly}, Int),
                    &z, &x, &y, prec(parent(z)))
end

function addeq!(z::acb_poly, x::acb_poly)
   ccall((:acb_poly_add, :libarb), Void, 
                (Ptr{acb_poly}, Ptr{acb_poly}, Ptr{acb_poly}, Int),
                    &z, &z, &x, prec(parent(z)))
end

###############################################################################
#
#   Promotions
#
###############################################################################

Base.promote_rule(::Type{acb_poly}, ::Type{Float64}) = acb_poly

Base.promote_rule(::Type{acb_poly}, ::Type{Complex{Float64}}) = acb_poly

Base.promote_rule(::Type{acb_poly}, ::Type{Int}) = acb_poly

Base.promote_rule(::Type{acb_poly}, ::Type{Complex{Int}}) = acb_poly

Base.promote_rule(::Type{acb_poly}, ::Type{fmpz}) = acb_poly

Base.promote_rule(::Type{acb_poly}, ::Type{fmpq}) = acb_poly

Base.promote_rule(::Type{acb_poly}, ::Type{arb}) = acb_poly

Base.promote_rule(::Type{acb_poly}, ::Type{acb}) = acb_poly

Base.promote_rule(::Type{acb_poly}, ::Type{fmpz_poly}) = acb_poly

Base.promote_rule(::Type{acb_poly}, ::Type{fmpq_poly}) = acb_poly

#Base.promote_rule(::Type{acb_poly}, ::Type{arb_poly}) = acb_poly

################################################################################
#
#  Parent object call overloads
#
################################################################################

function Base.call(a::AcbPolyRing)
   z = acb_poly()
   z.parent = a
   return z
end

function Base.call(a::AcbPolyRing, b::Union{Int,fmpz,fmpq,Float64,Complex{Float64},Complex{Int},arb,acb})
   z = acb_poly(base_ring(a)(b), a.base_ring.prec)
   z.parent = a
   return z
end

function Base.call(a::AcbPolyRing, b::Array{acb, 1})
   z = acb_poly(b, a.base_ring.prec)
   z.parent = a
   return z
end

function Base.call(a::AcbPolyRing, b::fmpz_poly)
   z = acb_poly(b, a.base_ring.prec)
   z.parent = a
   return z
end

function Base.call(a::AcbPolyRing, b::fmpq_poly)
   z = acb_poly(b, a.base_ring.prec)
   z.parent = a
   return z
end

#function Base.call(a::AcbPolyRing, b::arb_poly)
#   z = acb_poly(b, a.base_ring.prec)
#   z.parent = a
#   return z
#end

function Base.call(a::AcbPolyRing, b::acb_poly)
   z = acb_poly(b, a.base_ring.prec)
   z.parent = a
   return z
end

################################################################################
#
#  PolynomialRing constructor
#
################################################################################

function PolynomialRing(R::AcbField, s::AbstractString)
  S = Symbol(s)
  parent_obj = AcbPolyRing(R, S)
  return parent_obj, parent_obj(fmpz_poly([fmpz(0), fmpz(1)]))
end

