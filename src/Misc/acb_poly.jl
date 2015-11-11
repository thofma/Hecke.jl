################################################################################
#
#                     acb_poly.jl: wrapper for acb_poly
#
# This file is part of hecke.
#
# Copyright (c) 2015: Claus Fieker, Tommy Hofmann
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
# * Redistributions of source code must retain the above copyright notice, this
#   list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright notice,
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
#
#  Copyright (C) 2015 Tommy Hofmann
#
################################################################################
#
#  TODO
#   - wrap the other functions
#   - pretty print for polynomials? 
#
################################################################################

export AcbPolyRing, acb_poly

################################################################################
#
#  Types and memory management
#
################################################################################

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

type acb_poly
  coeffs::Ptr{Void}
  length::Clong
  alloc::Clong
  parent::AcbPolyRing

  function acb_poly()
    z = new()
    ccall((:acb_poly_init, :libarb), Void, (Ptr{acb_poly}, ), &z)
    finalizer(z, _acb_poly_clear_fn)
    return z
  end

  function acb_poly(x::fmpz_poly, p::Clong)
    z = new() 
    ccall((:acb_poly_init, :libarb), Void, (Ptr{acb_poly}, ), &z)
    ccall((:acb_poly_set_fmpz_poly, :libarb), Void,
                (Ptr{acb_poly}, Ptr{fmpz_poly}, Clong), &z, &x, p)
    finalizer(z, _acb_poly_clear_fn)
    return z
  end

  function acb_poly(x::fmpq_poly, p::Clong)
    z = new() 
    ccall((:acb_poly_init, :libarb), Void, (Ptr{acb_poly}, ), &z)
    ccall((:acb_poly_set_fmpq_poly, :libarb), Void,
                (Ptr{acb_poly}, Ptr{fmpq_poly}, Clong), &z, &x, p)
    finalizer(z, _acb_poly_clear_fn)
    return z
  end
end

function _acb_poly_clear_fn(x::acb_poly)
  ccall((:acb_poly_clear, :libarb), Void, (Ptr{acb_poly}, ), &x)
end

################################################################################
#
#  Field access
#
################################################################################

parent(x::acb_poly) = x.parent

length(x::acb_poly) = ccall((:acb_poly_length, :libarb), Clong,
                                  (Ptr{acb_poly}, ), &x)

degree(x::acb_poly) = length(x) - 1

var(x::AcbPolyRing) = x.S

################################################################################
#
#  Parent object overloading
#
################################################################################

function call(x::AcbPolyRing, y::fmpz_poly)
  z = acb_poly(y, x.base_ring.prec)
  z.parent = x
  return z
end

function call(x::AcbPolyRing, y::fmpq_poly)
  z = acb_poly(y, x.base_ring.prec)
  z.parent = x
  return z
end

function call(x::AcbPolyRing)
  z = acb_poly()
  z.parent = x
  return z
end

################################################################################
#
#  Coefficient access
#
################################################################################

function coeff(a::acb_poly, n::Clong)
  n < 0 && n > degree(a) && throw(DomainError())
  t = parent(a).base_ring()
  ccall((:acb_poly_get_coeff_acb, :libarb), Void,
              (Ptr{acb}, Ptr{acb_poly}, Clong), &t, &a, n)
  return t
end

################################################################################
#
#  String I/O
#
################################################################################

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

################################################################################
#
#  Unary operations
#
################################################################################

function -(x::acb_poly)
  z = parent(x)()
  ccall((:acb_poly_neg, :libarb), Void, (Ptr{acb_poly}, Ptr{acb_poly}), &x, &z)
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
              (Ptr{acb_poly}, Ptr{acb_poly}, Ptr{acb_poly}, Clong),
              &z, &x, &y, parent(x).base_ring.prec)
  return z
end

function *(x::acb_poly, y::acb_poly)
  z = parent(x)()
  ccall((:acb_poly_mul, :libarb), Void,
              (Ptr{acb_poly}, Ptr{acb_poly}, Ptr{acb_poly}, Clong),
              &z, &x, &y, parent(x).base_ring.prec)
  return z
end

function -(x::acb_poly, y::acb_poly)
  z = parent(x)()
  ccall((:acb_poly_sub, :libarb), Void,
              (Ptr{acb_poly}, Ptr{acb_poly}, Ptr{acb_poly}, Clong),
              &z, &x, &y, parent(x).base_ring.prec)
  return z
end

function ^(x::acb_poly, y::Int)
  z = parent(x)()
  ccall((:acb_poly_pow_ui, :libarb), Void,
              (Ptr{acb_poly}, Ptr{acb_poly}, Culong, Clong),
              &z, &x, y, parent(x).base_ring.prec)
  return z
end

################################################################################
#
#  PolynomialRing constructor
#
################################################################################

function PolynomialRing(R::AcbField, s::AbstractString)
  S = symbol(s)
  parent_obj = AcbPolyRing(R, S)
  return parent_obj, parent_obj(fmpz_poly([fmpz(0), fmpz(1)]))
end
