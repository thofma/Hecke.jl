################################################################################
#
#  Types and memory management for ArbMatSpace
#
################################################################################

import Base: exp

const ArbMatSpaceID = ObjectIdDict()

type ArbMatSpace <: Ring{Nemo.Arb}
  rows::Int
  cols::Int
  base_ring::ArbField

  function ArbMatSpace(R::ArbField, r::Int, c::Int)
    if haskey(ArbMatSpaceID, (R, r, c))
      return ArbMatSpaceID[(R, r, c)]::ArbMatSpace
    else
      z = new(r, c, R)
      ArbMatSpaceID[(R, r, c)] = z
      return z
    end
  end
end

type arb_mat <: MatElem{arb}
  entries::Ptr{Void}
  r::Int
  c::Int
  rows::Ptr{Void}
  parent::ArbMatSpace

  function arb_mat(r::Int, c::Int)
    z = new()
    ccall((:arb_mat_init, :libarb), Void, (Ptr{arb_mat}, Int, Int), &z, r, c)
    finalizer(z, _arb_mat_clear_fn)
    return z
  end

  function arb_mat(a::fmpz_mat)
    z = new()
    ccall((:arb_mat_init, :libarb), Void,
                (Ptr{arb_mat}, Int, Int), &z, a.r, a.c)
    ccall((:arb_mat_set_fmpz_mat, :libarb), Void,
                (Ptr{arb_mat}, Ptr{fmpz_mat}), &z, &a)
    finalizer(z, _arb_mat_clear_fn)
    return z
  end
  
  function arb_mat(a::fmpz_mat, prec::Int)
    z = new()
    ccall((:arb_mat_init, :libarb), Void,
                (Ptr{arb_mat}, Int, Int), &z, a.r, a.c)
    ccall((:arb_mat_set_round_fmpz_mat, :libarb), Void,
                (Ptr{arb_mat}, Ptr{fmpz_mat}, Int), &z, &a, prec)
    finalizer(z, _arb_mat_clear_fn)
    return z
  end

  function arb_mat{T <: Union{Int, UInt, fmpz, Float64, BigFloat,
                              arb}}(r::Int, c::Int, arr::Array{T, 2})
    z = new()
    ccall((:arb_mat_init, :libarb), Void, 
                (Ptr{arb_mat}, Int, Int), &z, r, c)
    finalizer(z, _arb_mat_clear_fn)
    for i = 1:r
      for j = 1:c
        el = ccall((:arb_mat_entry_ptr, :libarb), Ptr{arb},
                    (Ptr{arb_mat}, Int, Int), &z, i - 1, j - 1)
        Nemo._arb_set(el, arr[i, j])
      end
    end
    return z
  end

  function arb_mat{T <: Union{Int, UInt, fmpz, fmpq, Float64, BigFloat, arb,
                              AbstractString}}(r::Int, c::Int, arr::Array{T, 2},
                                               prec::Int)
    z = new()
    ccall((:arb_mat_init, :libarb), Void, 
                (Ptr{arb_mat}, Int, Int), &z, r, c)
    finalizer(z, _arb_mat_clear_fn)
    for i = 1:r
      for j = 1:c
        el = ccall((:arb_mat_entry_ptr, :libarb), Ptr{arb},
                    (Ptr{arb_mat}, Int, Int), &z, i - 1, j - 1)
        Nemo._arb_set(el, arr[i, j], prec)
      end
    end
    return z
  end
     
#  function arb_mat(a::fmpq_mat, prec::Int)
#    z = new()
#    ccall((:arb_mat_init, :libarb), Void,
#                (Ptr{arb_mat}, Int, Int), &z, a.r, a.c)
#    ccall((:arb_mat_set_fmpq_mat, :libarb), Void,
#                (Ptr{arb_mat}, Ptr{fmpq_mat}, Int), &z, &a, prec)
#    finalizer(z, _arb_mat_clear_fn)
#    return z
#  end
end

function _arb_mat_clear_fn(x::arb_mat)
  ccall((:arb_mat_clear, :libarb), Void, (Ptr{arb_mat}, ), &x)
end

################################################################################
#
#  Types and memory management for AcbMatSpace
#
################################################################################

const AcbMatSpaceID = ObjectIdDict()

type AcbMatSpace <: Ring{Nemo.Arb}
  rows::Int
  cols::Int
  base_ring::AcbField

  function AcbMatSpace(R::AcbField, r::Int, c::Int)
    if haskey(AcbMatSpaceID, (R, r, c))
      return AcbMatSpaceID[(R, r, c)]::AcbMatSpace
    else
      z = new(r, c, R)
      AcbMatSpaceID[(R, r, c)] = z
      return z
    end
  end
end

type acb_mat <: MatElem{acb}
  entries::Ptr{Void}
  r::Int
  c::Int
  rows::Ptr{Void}
  parent::AcbMatSpace

  function acb_mat(r::Int, c::Int)
    z = new()
    ccall((:acb_mat_init, :libarb), Void, (Ptr{acb_mat}, Int, Int), &z, r, c)
    finalizer(z, _acb_mat_clear_fn)
    return z
  end

  function acb_mat(a::fmpz_mat)
    z = new()
    ccall((:acb_mat_init, :libarb), Void,
                (Ptr{acb_mat}, Int, Int), &z, a.r, a.c)
    ccall((:acb_mat_set_fmpz_mat, :libarb), Void,
                (Ptr{acb_mat}, Ptr{fmpz_mat}), &z, &a)
    finalizer(z, _acb_mat_clear_fn)
    return z
  end
  
  function acb_mat(a::fmpz_mat, prec::Int)
    z = new()
    ccall((:acb_mat_init, :libarb), Void,
                (Ptr{acb_mat}, Int, Int), &z, a.r, a.c)
    ccall((:acb_mat_set_round_fmpz_mat, :libarb), Void,
                (Ptr{acb_mat}, Ptr{fmpz_mat}, Int), &z, &a, prec)
    finalizer(z, _acb_mat_clear_fn)
    return z
  end

  function acb_mat(a::arb_mat)
    z = new()
    ccall((:acb_mat_init, :libarb), Void,
                (Ptr{acb_mat}, Int, Int), &z, a.r, a.c)
    ccall((:acb_mat_set_arb_mat, :libarb), Void,
                (Ptr{acb_mat}, Ptr{arb_mat}), &z, &a)
    finalizer(z, _acb_mat_clear_fn)
    return z
  end

  function acb_mat(a::arb_mat, prec::Int)
    z = new()
    ccall((:acb_mat_init, :libarb), Void,
                (Ptr{acb_mat}, Int, Int), &z, a.r, a.c)
    ccall((:acb_mat_set_round_arb_mat, :libarb), Void,
                (Ptr{acb_mat}, Ptr{arb_mat}, Int), &z, &a, prec)
    finalizer(z, _acb_mat_clear_fn)
    return z
  end
   
  function acb_mat{T <: Union{Int, UInt, Float64, fmpz, BigFloat, acb,
                              arb}}(r::Int, c::Int, arr::Array{T, 2})
    z = new()
    ccall((:acb_mat_init, :libarb), Void, 
                (Ptr{acb_mat}, Int, Int), &z, r, c)
    finalizer(z, _acb_mat_clear_fn)
    for i = 1:r
      for j = 1:c
        el = ccall((:acb_mat_entry_ptr, :libarb), Ptr{acb},
                    (Ptr{acb_mat}, Int, Int), &z, i - 1, j - 1)
        _acb_set(el, arr[i, j])
      end
    end
    return z
  end

  function acb_mat{T <: Union{Int, UInt, fmpz, fmpq, Float64, BigFloat, arb,
                              AbstractString, acb}}(r::Int, c::Int,
                                                    arr::Array{T, 2}, prec::Int)
    z = new()
    ccall((:acb_mat_init, :libarb), Void, 
                (Ptr{acb_mat}, Int, Int), &z, r, c)
    finalizer(z, _acb_mat_clear_fn)
    for i = 1:r
      for j = 1:c
        el = ccall((:acb_mat_entry_ptr, :libarb), Ptr{acb},
                    (Ptr{acb_mat}, Int, Int), &z, i - 1, j - 1)
        _acb_set(el, arr[i, j], prec)
      end
    end
    return z
  end

  function acb_mat{T <: Union{Int, UInt, Float64, fmpz, fmpq, BigFloat, arb,
                              AbstractString}}(r::Int, c::Int,
                                               arr::Array{Tuple{T, T}, 2},
                                               prec::Int)

    z = new()
    ccall((:acb_mat_init, :libarb), Void, 
                (Ptr{acb_mat}, Int, Int), &z, r, c)
    finalizer(z, _acb_mat_clear_fn)
    for i = 1:r
      for j = 1:c
        el = ccall((:acb_mat_entry_ptr, :libarb), Ptr{acb},
                    (Ptr{acb_mat}, Int, Int), &z, i - 1, j - 1)
        _acb_set(el, arr[i, j][1], arr[i,j][2], prec)
      end
    end
    return z
  end

    
#  function arb_mat(a::fmpq_mat, prec::Int)
#    z = new()
#    ccall((:arb_mat_init, :libarb), Void,
#                (Ptr{arb_mat}, Int, Int), &z, a.r, a.c)
#    ccall((:arb_mat_set_fmpq_mat, :libarb), Void,
#                (Ptr{arb_mat}, Ptr{fmpq_mat}, Int), &z, &a, prec)
#    finalizer(z, _arb_mat_clear_fn)
#    return z
#  end
end

function _acb_mat_clear_fn(x::acb_mat)
  ccall((:acb_mat_clear, :libarb), Void, (Ptr{acb_mat}, ), &x)
end

###############################################################################
#
#   arb_mat.jl : arb_mat matrices
#
#   Copyright (C) 2015 Tommy Hofmann
#
###############################################################################

export parent, elem_type, prec, base_ring, cols, rows, deepcopy, getindex!,
       setindex!, one, zero, show, strongequal, overlaps, contains, issquare,
       transpose, bound_inf_norm, -, +, *, //,  swap_rows!, lufact!, lufact,
       solve, solve!, solve_lu_precomp, solve_lu_precomp!, inv, det, charpoly, 
       exp, add!, mul!, sub!, call

###############################################################################
#
#   Basic manipulation
#
###############################################################################

parent(a::arb_mat) = a.parent

elem_type(a::ArbMatSpace) = arb_mat

prec(a::ArbMatSpace) = prec(a.base_ring)

base_ring(a::ArbMatSpace) = a.base_ring

base_ring(a::arb_mat) = base_ring(parent(a))

cols(x::arb_mat) = x.c

rows(x::arb_mat) = x.r

function deepcopy(x::arb_mat)
  z = parent(x)()
  ccall((:arb_mat_set, :libarb), Void, (Ptr{arb_mat}, Ptr{arb_mat}), &z, &x)
  return z
end

function getindex!(z::arb, x::arb_mat, r::Int, c::Int)
  v = ccall((:arb_mat_entry_ptr, :libarb), Ptr{arb},
              (Ptr{arb_mat}, Int, Int), &x, r - 1, c - 1)
  ccall((:arb_set, :libarb), Void, (Ptr{arb}, Ptr{arb}), &z, v)
  return z
end

function getindex(x::arb_mat, r::Int, c::Int)
  Nemo._checkbounds(rows(x), r) || throw(BoundsError())
  Nemo._checkbounds(cols(x), c) || throw(BoundsError())

  z = base_ring(x)()
  v = ccall((:arb_mat_entry_ptr, :libarb), Ptr{arb},
              (Ptr{arb_mat}, Int, Int), &x, r - 1, c - 1)
  ccall((:arb_set, :libarb), Void, (Ptr{arb}, Ptr{arb}), &z, v)
  return z
end

function setindex!(x::arb_mat, y::Union{Int, UInt, fmpz, fmpq, Float64,
                                        BigFloat, arb, AbstractString},
                                        r::Int, c::Int)
  Nemo._checkbounds(rows(x), r) || throw(BoundsError())
  Nemo._checkbounds(cols(x), c) || throw(BoundsError())

  z = ccall((:arb_mat_entry_ptr, :libarb), Ptr{arb},
              (Ptr{arb_mat}, Int, Int), &x, r - 1, c - 1)
  Nemo._arb_set(z, y, prec(base_ring(x)))
end

function one(x::ArbMatSpace)
  z = x()
  ccall((:arb_mat_one, :libarb), Void, (Ptr{arb_mat}, ), &z)
  return z
end

function zero(x::ArbMatSpace)
  z = x()
  ccall((:arb_mat_zero, :libarb), Void, (Ptr{arb_mat}, ), &z)
  return z
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::ArbMatSpace)
   print(io, "Matrix Space of ")
   print(io, a.rows, " rows and ", a.cols, " columns over ")
   print(io, base_ring(a))
end

function show(io::IO, a::arb_mat)
   rows = a.parent.rows
   cols = a.parent.cols
   for i = 1:rows
      print(io, "[")
      for j = 1:cols
         print(io, a[i, j])
         if j != cols
            print(io, " ")
         end
      end
      print(io, "]")
      if i != rows
         println(io, "")
      end
   end
end

################################################################################
#
#  Comparison
#
################################################################################

function ==(x::arb_mat, y::arb_mat)
  check_parent(x, y)
  r = ccall((:arb_mat_eq, :libarb), Cint, (Ptr{arb_mat}, Ptr{arb_mat}), &x, &y)
  return Bool(r)
end

function !=(x::arb_mat, y::arb_mat)
  r = ccall((:arb_mat_ne, :libarb), Cint, (Ptr{arb_mat}, Ptr{arb_mat}), &x, &y)
  return Bool(r)
end

function strongequal(x::arb_mat, y::arb_mat)
  r = ccall((:arb_mat_equal, :libarb), Cint,
              (Ptr{arb_mat}, Ptr{arb_mat}), &x, &y)
  return Bool(r)
end

function overlaps(x::arb_mat, y::arb_mat)
  r = ccall((:arb_mat_overlaps, :libarb), Cint,
              (Ptr{arb_mat}, Ptr{arb_mat}), &x, &y)
  return Bool(r)
end

function contains(x::arb_mat, y::arb_mat)
  r = ccall((:arb_mat_contains, :libarb), Cint,
              (Ptr{arb_mat}, Ptr{arb_mat}), &x, &y)
  return Bool(r)
end

function contains(x::arb_mat, y::fmpz_mat)
  r = ccall((:arb_mat_contains_fmpz_mat, :libarb), Cint,
              (Ptr{arb_mat}, Ptr{fmpz_mat}), &x, &y)
  return Bool(r)
end

#function contains(x::arb_mat, y::fmpq_mat)
#  r = ccall((:arb_mat_contains_fmpq_mat, :libarb), Cint,
#              (Ptr{arb_mat}, Ptr{arb_mat}))
#  return Bool(r)
#end

################################################################################
#
#  Predicates
#
################################################################################

issquare(x::arb_mat) = cols(x) == rows(x)

################################################################################
#
#  Transpose
#
################################################################################

function transpose(x::arb_mat)
  z = MatrixSpace(base_ring(x), cols(x), rows(x))()
  ccall((:arb_mat_transpose, :libarb), Void,
              (Ptr{arb_mat}, Ptr{arb_mat}), &z, &x)
  return z
end

################################################################################
#
#  Norm
#
################################################################################

function bound_inf_norm(x::arb_mat)
  z = arb()
  t = ccall((:arb_rad_ptr, :libarb), Ptr{mag_struct}, (Ptr{arb}, ), &z)
  ccall((:arb_mat_bound_inf_norm, :libarb), Void,
              (Ptr{mag_struct}, Ptr{arb_mat}), t, &x)
  s = ccall((:arb_mid_ptr, :libarb), Ptr{arf_struct}, (Ptr{arb}, ), &z)
  ccall((:arf_set_mag, :libarb), Void,
              (Ptr{arf_struct}, Ptr{mag_struct}), s, t)
  ccall((:mag_zero, :libarb), Void,
              (Ptr{mag_struct},), t)
  return base_ring(x)(z)
end

################################################################################
#
#  Unary operations
#
################################################################################

function -(x::arb_mat)
  z = parent(x)()
  ccall((:arb_mat_neg, :libarb), Void, (Ptr{arb_mat}, Ptr{arb_mat}), &z, &x)
  return z
end

################################################################################
#
#  Binary operations
#
################################################################################

function +(x::arb_mat, y::arb_mat)
  check_parent(x, y)
  z = parent(x)()
  ccall((:arb_mat_add, :libarb), Void,
              (Ptr{arb_mat}, Ptr{arb_mat}, Ptr{arb_mat}, Int),
              &z, &x, &y, prec(parent(x)))
  return z
end

function -(x::arb_mat, y::arb_mat)
  check_parent(x, y)
  z = parent(x)()
  ccall((:arb_mat_sub, :libarb), Void,
              (Ptr{arb_mat}, Ptr{arb_mat}, Ptr{arb_mat}, Int),
              &z, &x, &y, prec(parent(x)))
  return z
end

function *(x::arb_mat, y::arb_mat)
  check_parent(x, y)
  cols(x) != rows(y) && error("Matrices have wrong  dimensions")
  z = MatrixSpace(base_ring(x), rows(x), cols(y))()
  ccall((:arb_mat_mul, :libarb), Void,
              (Ptr{arb_mat}, Ptr{arb_mat}, Ptr{arb_mat}, Int),
              &z, &x, &y, prec(parent(x)))
  return z
end

function ^(x::arb_mat, y::UInt)
  rows(x) != cols(x) && error("Matrix must be square")
  z = parent(x)()
  ccall((:arb_mat_pow_ui, :libarb), Void,
              (Ptr{arb_mat}, Ptr{arb_mat}, UInt, Int),
              &z, &x, y, prec(parent(x)))
  return z
end

function *(x::arb_mat, y::Int)
  z = parent(x)()
  ccall((:arb_mat_scalar_mul_si, :libarb), Void,
              (Ptr{arb_mat}, Ptr{arb_mat}, Int, Int),
              &z, &x, y, prec(parent(x)))
  return z
end

*(x::Int, y::arb_mat) = y*x

function *(x::arb_mat, y::fmpz)
  z = parent(x)()
  ccall((:arb_mat_scalar_mul_fmpz, :libarb), Void,
              (Ptr{arb_mat}, Ptr{arb_mat}, Ptr{fmpz}, Int),
              &z, &x, &y, prec(parent(x)))
  return z
end

*(x::fmpz, y::arb_mat) = y*x

function *(x::arb_mat, y::arb)
  z = parent(x)()
  ccall((:arb_mat_scalar_mul_arb, :libarb), Void,
              (Ptr{arb_mat}, Ptr{arb_mat}, Ptr{arb}, Int),
              &z, &x, &y, prec(parent(x)))
  return z
end

*(x::arb, y::arb_mat) = y*x

function //(x::arb_mat, y::Int)
  y == 0 && throw(DivideError())
  z = parent(x)()
  ccall((:arb_mat_scalar_div_si, :libarb), Void,
              (Ptr{arb_mat}, Ptr{arb_mat}, Int, Int),
              &z, &x, y, prec(parent(x)))
  return z
end

function //(x::arb_mat, y::fmpz)
  z = parent(x)()
  ccall((:arb_mat_scalar_div_fmpz, :libarb), Void,
              (Ptr{arb_mat}, Ptr{arb_mat}, Ptr{fmpz}, Int),
              &z, &x, &y, prec(parent(x)))
  return z
end

function //(x::arb_mat, y::arb)
  z = parent(x)()
  ccall((:arb_mat_scalar_div_arb, :libarb), Void,
              (Ptr{arb_mat}, Ptr{arb_mat}, Ptr{arb}, Int),
              &z, &x, &y, prec(parent(x)))
  return z
end

################################################################################
#
#  Permutation
#
################################################################################

# this can be done faster
function *(P::perm, x::arb_mat)
   z = parent(x)()
   m = rows(x)
   n = cols(x)
   for i = 1:m
      for j = 1:n
         z[P[i], j] = x[i, j]
      end
   end
   return z
end

################################################################################
#
#  Solving
#
################################################################################

function swap_rows!(x::arb_mat, i::Int, j::Int)
  Nemo._checkbounds(rows(x), i) || throw(BoundsError())
  Nemo._checkbounds(rows(x), j) || throw(BoundsError())
  ccall((:arb_mat_swap_rows, :libarb), Void,
              (Ptr{arb_mat}, Ptr{Void}, Int, Int),
              &x, C_NULL, i - 1, j - 1)
end

function lufact!(P::perm, x::arb_mat)
  cols(x) != rows(x) && error("Matrix must be square")
  parent(P).n != rows(x) && error("Permutation does not match matrix")
  r = ccall((:arb_mat_lu, :libarb), Cint,
              (Ptr{Int}, Ptr{arb_mat}, Ptr{arb_mat}, Int),
              P.d, &x, &x, prec(parent(x)))
  r == 0 && error("Could not find $(rows(x)) invertible pivot elements")
  inv!(P)
  return rows(x)
end

function lufact(x::arb_mat, P = FlintPermGroup(rows(x)))
  p = P()
  R = base_ring(x)
  L = parent(x)()
  U = deepcopy(x)
  n = cols(x)
  r = lufact!(p, U)
  for i = 1:n
    for j = 1:n
      if i > j
        L[i, j] = U[i, j]
        U[i, j] = R()
      elseif i == j
        L[i, j] = one(R)
      else
        L[i, j] = R()
      end
    end
  end
  return r, p, L, U
end

function solve!(z::arb_mat, x::arb_mat, y::arb_mat)
  r = ccall((:arb_mat_solve, :libarb), Cint,
              (Ptr{arb_mat}, Ptr{arb_mat}, Ptr{arb_mat}, Int),
              &z, &x, &y, prec(parent(x)))
  r == 0 && error("Matrix cannot be inverted numerically")
  nothing
end

function solve(x::arb_mat, y::arb_mat)
  cols(x) != rows(x) && error("First argument must be square")
  cols(x) != rows(y) && error("Matrix dimensions are wrong")
  z = parent(y)()
  solve!(z, x, y)
  return z
end

function solve_lu_precomp!(z::arb_mat, P::perm, LU::arb_mat, y::arb_mat)
  Q = inv(P)
  ccall((:arb_mat_solve_lu_precomp, :libarb), Void,
              (Ptr{arb_mat}, Ptr{Int}, Ptr{arb_mat}, Ptr{arb_mat}, Int),
              &z, Q.d, &LU, &y, prec(parent(LU)))
  nothing
end

function solve_lu_precomp(P::perm, LU::arb_mat, y::arb_mat)
  cols(LU) != rows(y) && error("Matrix dimensions are wrong")
  z = parent(y)()
  solve_lu_precomp!(z, P, LU, y)
  return z
end

function inv(x::arb_mat)
  cols(x) != rows(x) && error("Matrix must be square")
  z = parent(x)()
  r = ccall((:arb_mat_inv, :libarb), Cint,
              (Ptr{arb_mat}, Ptr{arb_mat}, Int), &z, &x, prec(parent(x)))
  Bool(r) ? (return z) : error("Matrix cannot be inverted numerically")
end

################################################################################
#
#  Determinant
#
################################################################################

function det(x::arb_mat)
  cols(x) != rows(x) && error("Matrix must be square")
  z = base_ring(x)()
  ccall((:arb_mat_det, :libarb), Void,
              (Ptr{arb}, Ptr{arb_mat}, Int), &z, &x, prec(parent(x)))
  return z
end

################################################################################
#
#  Characteristic polynomial
#
################################################################################

#function charpoly(x::ArbPolyRing, y::arb_mat)
#  base_ring(y) != base_ring(x) && error("Base rings must coincide")
#  z = x()
#  ccall((:arb_mat_charpoly, :libarb), Void,
#              (Ptr{arb_poly}, Ptr{arb_mat}, Int), &z, &y, prec(parent(y)))
#  return z
#end

################################################################################
#
#  Special functions
#
################################################################################

function exp(x::arb_mat)
  cols(x) != rows(x) && error("Matrix must be square")
  z = parent(x)()
  ccall((:arb_mat_exp, :libarb), Void,
              (Ptr{arb_mat}, Ptr{arb_mat}, Int), &z, &x, prec(parent(x)))
  return z
end

################################################################################
#
#  Unsafe operations
#
################################################################################

for (s,f) in (("add!","arb_mat_add"), ("mul!","arb_mat_mul"),
              ("sub!","arb_mat_sub"))
  @eval begin
    function ($(symbol(s)))(z::arb_mat, x::arb_mat, y::arb_mat)
      ccall(($f, :libarb), Void,
                  (Ptr{arb_mat}, Ptr{arb_mat}, Ptr{arb_mat}, Int),
                  &z, &x, &y, prec(parent(x)))
    end
  end
end

################################################################################
#
#  Parent object overloading
#
################################################################################

function call(x::ArbMatSpace)
  z = arb_mat(x.rows, x.cols)
  z.parent = x
  return z
end

function call(x::ArbMatSpace, y::fmpz_mat)
  (x.cols != cols(y) || x.rows != rows(y)) &&
      error("Dimensions are wrong")
  z = arb_mat(y, prec(x))
  z.parent = x
  return z
end

function call{T <: Union{Int, UInt, fmpz, fmpq, Float64, BigFloat, arb,
                         AbstractString}}(x::ArbMatSpace, y::Array{T, 2})
  (x.rows, x.cols) != size(y) && error("Dimensions are wrong")
  z = arb_mat(x.rows, x.cols, y, prec(x))
  z.parent = x
  return z
end

call{T <: Union{Int, UInt, fmpz, fmpq, Float64, BigFloat, arb,
                AbstractString}}(x::ArbMatSpace, y::Array{T, 1}) = x(y'')

################################################################################
#
#  Matrix space constructor
#
################################################################################

function MatrixSpace(R::ArbField, r::Int, c::Int)
  return ArbMatSpace(R, r, c)
end

###############################################################################
#
#   acb_mat.jl : acb_mat matrices
#
#   Copyright (C) 2015 Tommy Hofmann
#
###############################################################################

export parent, elem_type, prec, base_ring, cols, rows, deepcopy, getindex!,
       setindex!, one, zero, show, strongequal, overlaps, contains, issquare,
       transpose, bound_inf_norm, -, +, *, //,  ldexp, swap_rows!, lufact!, lufact,
       solve, solve!, solve_lu_precomp, solve_lu_precomp!, inv, det, charpoly, 
       exp, add!, mul!, sub!, call

###############################################################################
#
#   Basic manipulation
#
###############################################################################

parent(a::acb_mat) = a.parent

elem_type(a::AcbMatSpace) = acb_mat

prec(a::AcbMatSpace) = prec(a.base_ring)

base_ring(a::AcbMatSpace) = a.base_ring

base_ring(a::acb_mat) = base_ring(parent(a))

cols(x::acb_mat) = x.c

rows(x::acb_mat) = x.r

function deepcopy(x::acb_mat)
  z = parent(x)()
  ccall((:acb_mat_set, :libarb), Void, (Ptr{acb_mat}, Ptr{acb_mat}), &z, &x)
  return z
end

function getindex!(z::acb, x::acb_mat, r::Int, c::Int)
  v = ccall((:acb_mat_entry_ptr, :libarb), Ptr{acb},
              (Ptr{acb_mat}, Int, Int), &x, r - 1, c - 1)
  ccall((:acb_set, :libarb), Void, (Ptr{acb}, Ptr{acb}), &z, v)
  return z
end

function getindex(x::acb_mat, r::Int, c::Int)
  Nemo._checkbounds(rows(x), r) || throw(BoundsError())
  Nemo._checkbounds(cols(x), c) || throw(BoundsError())

  z = base_ring(x)()
  v = ccall((:acb_mat_entry_ptr, :libarb), Ptr{acb},
              (Ptr{acb_mat}, Int, Int), &x, r - 1, c - 1)
  ccall((:acb_set, :libarb), Void, (Ptr{acb}, Ptr{acb}), &z, v)
  return z
end

function setindex!(x::acb_mat,
                   y::Union{Int, UInt, Float64, fmpz, fmpq, arb, BigFloat,
                            acb, AbstractString},
                   r::Int, c::Int)
  Nemo._checkbounds(rows(x), r) || throw(BoundsError())
  Nemo._checkbounds(cols(x), c) || throw(BoundsError())

  z = ccall((:acb_mat_entry_ptr, :libarb), Ptr{acb},
              (Ptr{acb_mat}, Int, Int), &x, r - 1, c - 1)
  _acb_set(z, y, prec(base_ring(x)))
end

function setindex!{T <: Union{Int, UInt, Float64, fmpz, fmpq, arb, BigFloat,
                              AbstractString}}(x::acb_mat, y::Tuple{T, T},
                              r::Int, c::Int)
  Nemo._checkbounds(rows(x), r) || throw(BoundsError())
  Nemo._checkbounds(cols(x), c) || throw(BoundsError())

  z = ccall((:acb_mat_entry_ptr, :libarb), Ptr{acb},
              (Ptr{acb_mat}, Int, Int), &x, r - 1, c - 1)
  _acb_set(z, y[1], y[2], prec(base_ring(x)))
end

function one(x::AcbMatSpace)
  z = x()
  ccall((:acb_mat_one, :libarb), Void, (Ptr{acb_mat}, ), &z)
  return z
end

function zero(x::AcbMatSpace)
  z = x()
  ccall((:acb_mat_zero, :libarb), Void, (Ptr{acb_mat}, ), &z)
  return z
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::AcbMatSpace)
   print(io, "Matrix Space of ")
   print(io, a.rows, " rows and ", a.cols, " columns over ")
   print(io, base_ring(a))
end

function show(io::IO, a::acb_mat)
   rows = a.parent.rows
   cols = a.parent.cols
   for i = 1:rows
      print(io, "[")
      for j = 1:cols
         print(io, a[i, j])
         if j != cols
            print(io, " ")
         end
      end
      print(io, "]")
      if i != rows
         println(io, "")
      end
   end
end

################################################################################
#
#  Comparison
#
################################################################################

function ==(x::acb_mat, y::acb_mat)
  check_parent(x, y)
  r = ccall((:acb_mat_eq, :libarb), Cint, (Ptr{acb_mat}, Ptr{acb_mat}), &x, &y)
  return Bool(r)
end

function !=(x::acb_mat, y::acb_mat)
  r = ccall((:acb_mat_ne, :libarb), Cint, (Ptr{acb_mat}, Ptr{acb_mat}), &x, &y)
  return Bool(r)
end

function strongequal(x::acb_mat, y::acb_mat)
  r = ccall((:acb_mat_equal, :libarb), Cint,
              (Ptr{acb_mat}, Ptr{acb_mat}), &x, &y)
  return Bool(r)
end

function overlaps(x::acb_mat, y::acb_mat)
  r = ccall((:acb_mat_overlaps, :libarb), Cint,
              (Ptr{acb_mat}, Ptr{acb_mat}), &x, &y)
  return Bool(r)
end

function contains(x::acb_mat, y::acb_mat)
  r = ccall((:acb_mat_contains, :libarb), Cint,
              (Ptr{acb_mat}, Ptr{acb_mat}), &x, &y)
  return Bool(r)
end

function contains(x::acb_mat, y::fmpz_mat)
  r = ccall((:acb_mat_contains_fmpz_mat, :libarb), Cint,
              (Ptr{acb_mat}, Ptr{fmpz_mat}), &x, &y)
  return Bool(r)
end

#function contains(x::acb_mat, y::fmpq_mat)
#  r = ccall((:acb_mat_contains_fmpq_mat, :libarb), Cint,
#              (Ptr{acb_mat}, Ptr{acb_mat}))
#  return Bool(r)
#end

==(x::acb_mat, y::fmpz_mat) = x == parent(x)(y)

==(x::fmpz_mat, y::acb_mat) = y == x

==(x::acb_mat, y::arb_mat) = x == parent(x)(y)

==(x::arb_mat, y::acb_mat) = y == x

################################################################################
#
#  Predicates
#
################################################################################

issquare(x::acb_mat) = cols(x) == rows(x)

isreal(x::acb_mat) =
            Bool(ccall((:acb_mat_is_real, :libarb), Cint, (Ptr{acb_mat}, ), &x))

################################################################################
#
#  Transpose
#
################################################################################

function transpose(x::acb_mat)
  z = MatrixSpace(base_ring(x), cols(x), rows(x))()
  ccall((:acb_mat_transpose, :libarb), Void,
              (Ptr{acb_mat}, Ptr{acb_mat}), &z, &x)
  return z
end

################################################################################
#
#  Norm
#
################################################################################

function bound_inf_norm(x::acb_mat)
  z = arb()
  t = ccall((:arb_rad_ptr, :libarb), Ptr{mag_struct}, (Ptr{arb}, ), &z)
  ccall((:acb_mat_bound_inf_norm, :libarb), Void,
              (Ptr{mag_struct}, Ptr{acb_mat}), t, &x)
  s = ccall((:arb_mid_ptr, :libarb), Ptr{arf_struct}, (Ptr{arb}, ), &z)
  ccall((:arf_set_mag, :libarb), Void,
              (Ptr{arf_struct}, Ptr{mag_struct}), s, t)
  ccall((:mag_zero, :libarb), Void,
              (Ptr{mag_struct},), t)
  return ArbField(prec(parent(x)))(z)
end

################################################################################
#
#  Unary operations
#
################################################################################

function -(x::acb_mat)
  z = parent(x)()
  ccall((:acb_mat_neg, :libarb), Void, (Ptr{acb_mat}, Ptr{acb_mat}), &z, &x)
  return z
end

################################################################################
#
#  Binary operations
#
################################################################################

function +(x::acb_mat, y::acb_mat)
  check_parent(x, y)
  z = parent(x)()
  ccall((:acb_mat_add, :libarb), Void,
              (Ptr{acb_mat}, Ptr{acb_mat}, Ptr{acb_mat}, Int),
              &z, &x, &y, prec(parent(x)))
  return z
end

function -(x::acb_mat, y::acb_mat)
  check_parent(x, y)
  z = parent(x)()
  ccall((:acb_mat_sub, :libarb), Void,
              (Ptr{acb_mat}, Ptr{acb_mat}, Ptr{acb_mat}, Int),
              &z, &x, &y, prec(parent(x)))
  return z
end

function *(x::acb_mat, y::acb_mat)
  check_parent(x, y)
  cols(x) != rows(y) && error("Matrices have wrong  dimensions")
  z = MatrixSpace(base_ring(x), rows(x), cols(y))()
  ccall((:acb_mat_mul, :libarb), Void,
              (Ptr{acb_mat}, Ptr{acb_mat}, Ptr{acb_mat}, Int),
              &z, &x, &y, prec(parent(x)))
  return z
end

function ^(x::acb_mat, y::UInt)
  rows(x) != cols(x) && error("Matrix must be square")
  z = parent(x)()
  ccall((:acb_mat_pow_ui, :libarb), Void,
              (Ptr{acb_mat}, Ptr{acb_mat}, UInt, Int),
              &z, &x, y, prec(parent(x)))
  return z
end

function *(x::acb_mat, y::Int)
  z = parent(x)()
  ccall((:acb_mat_scalar_mul_si, :libarb), Void,
              (Ptr{acb_mat}, Ptr{acb_mat}, Int, Int),
              &z, &x, y, prec(parent(x)))
  return z
end

*(x::Int, y::acb_mat) = y*x

function *(x::acb_mat, y::fmpz)
  z = parent(x)()
  ccall((:acb_mat_scalar_mul_fmpz, :libarb), Void,
              (Ptr{acb_mat}, Ptr{acb_mat}, Ptr{fmpz}, Int),
              &z, &x, &y, prec(parent(x)))
  return z
end

*(x::fmpz, y::acb_mat) = y*x

function *(x::acb_mat, y::arb)
  z = parent(x)()
  ccall((:acb_mat_scalar_mul_arb, :libarb), Void,
              (Ptr{acb_mat}, Ptr{acb_mat}, Ptr{arb}, Int),
              &z, &x, &y, prec(parent(x)))
  return z
end

*(x::arb, y::acb_mat) = y*x

function *(x::acb_mat, y::acb)
  z = parent(x)()
  ccall((:acb_mat_scalar_mul_acb, :libarb), Void,
              (Ptr{acb_mat}, Ptr{acb_mat}, Ptr{acb}, Int),
              &z, &x, &y, prec(parent(x)))
  return z
end

*(x::acb, y::acb_mat) = y*x

function //(x::acb_mat, y::Int)
  y == 0 && throw(DivideError())
  z = parent(x)()
  ccall((:acb_mat_scalar_div_si, :libarb), Void,
              (Ptr{acb_mat}, Ptr{acb_mat}, Int, Int),
              &z, &x, y, prec(parent(x)))
  return z
end

function //(x::acb_mat, y::fmpz)
  z = parent(x)()
  ccall((:acb_mat_scalar_div_fmpz, :libarb), Void,
              (Ptr{acb_mat}, Ptr{acb_mat}, Ptr{fmpz}, Int),
              &z, &x, &y, prec(parent(x)))
  return z
end

function //(x::acb_mat, y::arb)
  z = parent(x)()
  ccall((:acb_mat_scalar_div_arb, :libarb), Void,
              (Ptr{acb_mat}, Ptr{acb_mat}, Ptr{arb}, Int),
              &z, &x, &y, prec(parent(x)))
  return z
end

function //(x::acb_mat, y::acb)
  z = parent(x)()
  ccall((:acb_mat_scalar_div_acb, :libarb), Void,
              (Ptr{acb_mat}, Ptr{acb_mat}, Ptr{acb}, Int),
              &z, &x, &y, prec(parent(x)))
  return z
end

################################################################################
#
#  Precision, shifting and other operations
#
################################################################################

function ldexp(x::acb_mat, y::Int)
  z = parent(x)()
  ccall((:acb_mat_scalar_mul_2exp_si, :libarb), Void,
              (Ptr{acb_mat}, Ptr{acb_mat}, Int), &z, &x, y)
  return z
end

################################################################################
#
#  Permutation
#
################################################################################

# this can be done faster
function *(P::perm, x::acb_mat)
   z = parent(x)()
   m = rows(x)
   n = cols(x)
   for i = 1:m
      for j = 1:n
         z[P[i], j] = x[i, j]
      end
   end
   return z
end

################################################################################
#
#  Solving
#
################################################################################

function swap_rows!(x::acb_mat, i::Int, j::Int)
  Nemo._checkbounds(rows(x), i) || throw(BoundsError())
  Nemo._checkbounds(rows(x), j) || throw(BoundsError())
  ccall((:acb_mat_swap_rows, :libarb), Void,
              (Ptr{acb_mat}, Ptr{Void}, Int, Int),
              &x, C_NULL, i - 1, j - 1)
end

function lufact!(P::perm, x::acb_mat)
  r = ccall((:acb_mat_lu, :libarb), Cint,
              (Ptr{Int}, Ptr{acb_mat}, Ptr{acb_mat}, Int),
              P.d, &x, &x, prec(parent(x)))
  r == 0 && error("Could not find $(rows(x)) invertible pivot elements")
  inv!(P)
  return rows(x)
end

function lufact(P::perm, x::acb_mat)
  cols(x) != rows(x) && error("Matrix must be square")
  parent(P).n != rows(x) && error("Permutation does not match matrix")
  R = base_ring(x)
  L = parent(x)()
  U = deepcopy(x)
  n = cols(x)
  lufact!(P, U)
  for i = 1:n
    for j = 1:n
      if i > j
        L[i, j] = U[i, j]
        U[i, j] = R()
      elseif i == j
        L[i, j] = one(R)
      else
        L[i, j] = R()
      end
    end
  end
  return L, U
end

function solve!(z::acb_mat, x::acb_mat, y::acb_mat)
  r = ccall((:acb_mat_solve, :libarb), Cint,
              (Ptr{acb_mat}, Ptr{acb_mat}, Ptr{acb_mat}, Int),
              &z, &x, &y, prec(parent(x)))
  r == 0 && error("Matrix cannot be inverted numerically")
  nothing
end

function solve(x::acb_mat, y::acb_mat)
  cols(x) != rows(x) && error("First argument must be square")
  cols(x) != rows(y) && error("Matrix dimensions are wrong")
  z = parent(y)()
  solve!(z, x, y)
  return z
end

function solve_lu_precomp!(z::acb_mat, P::perm, LU::acb_mat, y::acb_mat)
  Q = inv(P)
  ccall((:acb_mat_solve_lu_precomp, :libarb), Void,
              (Ptr{acb_mat}, Ptr{Int}, Ptr{acb_mat}, Ptr{acb_mat}, Int),
              &z, Q.d, &LU, &y, prec(parent(LU)))
  nothing
end

function solve_lu_precomp(P::perm, LU::acb_mat, y::acb_mat)
  cols(LU) != rows(y) && error("Matrix dimensions are wrong")
  z = parent(y)()
  solve_lu_precomp!(z, P, LU, y)
  return z
end

function inv(x::acb_mat)
  cols(x) != rows(x) && error("Matrix must be square")
  z = parent(x)()
  r = ccall((:acb_mat_inv, :libarb), Cint,
              (Ptr{acb_mat}, Ptr{acb_mat}, Int), &z, &x, prec(parent(x)))
  Bool(r) ? (return z) : error("Matrix cannot be inverted numerically")
end

################################################################################
#
#  Determinant
#
################################################################################

function det(x::acb_mat)
  cols(x) != rows(x) && error("Matrix must be square")
  z = base_ring(x)()
  ccall((:acb_mat_det, :libarb), Void,
              (Ptr{acb}, Ptr{acb_mat}, Int), &z, &x, prec(parent(x)))
  return z
end

################################################################################
#
#  Characteristic polynomial
#
################################################################################

function charpoly(x::AcbPolyRing, y::acb_mat)
  base_ring(x) != base_ring(y) && error("Base rings must coincide")
  z = x()
  ccall((:acb_mat_charpoly, :libarb), Void,
              (Ptr{acb_poly}, Ptr{acb_mat}, Int), &z, &y, prec(parent(y)))
  return z
end

################################################################################
#
#  Special functions
#
################################################################################

function exp(x::acb_mat)
  cols(x) != rows(x) && error("Matrix must be square")
  z = parent(x)()
  ccall((:acb_mat_exp, :libarb), Void,
              (Ptr{acb_mat}, Ptr{acb_mat}, Int), &z, &x, prec(parent(x)))
  return z
end

################################################################################
#
#  Unsafe operations
#
################################################################################

for (s,f) in (("add!","acb_mat_add"), ("mul!","acb_mat_mul"),
              ("sub!","acb_mat_sub"))
  @eval begin
    function ($(symbol(s)))(z::acb_mat, x::acb_mat, y::acb_mat)
      ccall(($f, :libarb), Void,
                  (Ptr{acb_mat}, Ptr{acb_mat}, Ptr{acb_mat}, Int),
                  &z, &x, &y, prec(parent(x)))
    end
  end
end

################################################################################
#
#  Parent object overloading
#
################################################################################

function call(x::AcbMatSpace)
  z = acb_mat(x.rows, x.cols)
  z.parent = x
  return z
end

function call(x::AcbMatSpace, y::fmpz_mat)
  (x.cols != cols(y) || x.rows != rows(y)) &&
      error("Dimensions are wrong")
  z = acb_mat(y, prec(x))
  z.parent = x
  return z
end

function call(x::AcbMatSpace, y::arb_mat)
  (x.cols != cols(y) || x.rows != rows(y)) &&
      error("Dimensions are wrong")
  z = acb_mat(y, prec(x))
  z.parent = x
  return z
end


function call{T <: Union{Int, UInt, Float64, fmpz, fmpq, BigFloat, arb, acb,
                         AbstractString}}(x::AcbMatSpace, y::Array{T, 2})
  (x.rows, x.cols) != size(y) && error("Dimensions are wrong")
  z = acb_mat(x.rows, x.cols, y, prec(x))
  z.parent = x
  return z
end

call{T <: Union{Int, UInt, Float64, fmpz, fmpq, BigFloat, arb, acb,
                AbstractString}}(x::AcbMatSpace, y::Array{T, 1}) = x(y'')


function call{T <: Union{Int, UInt, Float64, fmpz, fmpq, BigFloat, arb,
                         AbstractString}}(x::AcbMatSpace,
                                          y::Array{Tuple{T, T}, 2})
  (x.rows, x.cols) != size(y) && error("Dimensions are wrong")
  z = acb_mat(x.rows, x.cols, y, prec(x))
  z.parent = x
  return z
end

call{T <: Union{Int, UInt, Float64, fmpz, fmpq, BigFloat, AbstractString,
                arb}}(x::AcbMatSpace, y::Array{Tuple{T, T}, 1}) = x(y'')

################################################################################
#
#  Matrix space constructor
#
################################################################################

function MatrixSpace(R::AcbField, r::Int, c::Int)
  (r <= 0 || c <= 0) && error("Dimensions must be positive")
  return AcbMatSpace(R, r, c)
end
