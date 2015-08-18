################################################################################
#
#                       acb.jl: wrapper for acb
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
#  TODO:
#  - Parent checking for (safe) operations
#  - Should == be defined?
#
################################################################################

export acb, AcbField

export imag, real, one, onei, copy

################################################################################
#
#  Types and memory management
#
################################################################################

const AcbFieldID = ObjectIdDict()

type AcbField <: Field
  prec::Clong
  
  function AcbField(p::Clong = 256)
    try
      return AcbFieldID[p]::AcbField
    catch
      AcbFieldID[p] = new(p)::AcbField
    end
  end
end

# _raw_acb is only auxillary type
# do not use

type _raw_acb
  real_mid_exp::Int # fmpz
  real_mid_size::UInt64 # mp_size_t
  real_mid_d1::Int64 # mantissa_struct
  real_mid_d2::Int64
  real_rad_exp::Int # fmpz
  real_rad_man::UInt64
  imag_mid_exp::Int # fmpz
  imag_mid_size::UInt64 # mp_size_t
  imag_mid_d1::Int64 # mantissa_struct
  imag_mid_d2::Int64
  imag_rad_exp::Int # fmpz
  imag_rad_man::UInt64

  function _raw_acb()
    z = new()
    ccall((:acb_init, :libarb), Void, (Ptr{_raw_acb}, ), &z)
    finalizer(z, __acb_clear_fn)
    return z
  end
end

function show(io::IO, y::_raw_acb)
  x = acb()
  x.parent = AcbField(256)
  ccall((:acb_set, :libarb), Void, (Ptr{acb}, Ptr{_raw_acb}), &x, &y)
  show(io, x)
end

function __acb_clear_fn(x::_raw_acb)
  ccall((:acb_clear, :libarb), Void, (Ptr{_raw_acb}, ), &x)
end

type acb
  real_mid_exp::Int     # fmpz
  real_mid_size::UInt64 # mp_size_t
  real_mid_d1::Int64    # mantissa_struct
  real_mid_d2::Int64
  real_rad_exp::Int     # fmpz
  real_rad_man::UInt64
  imag_mid_exp::Int     # fmpz
  imag_mid_size::UInt64 # mp_size_t
  imag_mid_d1::Int64    # mantissa_struct
  imag_mid_d2::Int64
  imag_rad_exp::Int     # fmpz
  imag_rad_man::UInt64
  parent::AcbField

  function acb()
    z = new()
    ccall((:acb_init, :libarb), Void, (Ptr{acb}, ), &z)
    finalizer(z, _acb_clear_fn)
    return z
  end

  function acb(x::Clong)
    z = new()
    ccall((:acb_init, :libarb), Void, (Ptr{acb}, ), &z)
    ccall((:acb_set_si, :libarb), Void, (Ptr{acb}, Clong), &z, x)
    finalizer(z, _acb_clear_fn)
    return z
  end
  
  function acb(i::Culong)
    z = new()
    ccall((:acb_init, :libarb), Void, (Ptr{acb}, ), &z)
    ccall((:acb_set_ui, :libarb), Void, (Ptr{acb}, Culong), &z, i)
    finalizer(z, _acb_clear_fn)
    return z
  end

  function acb(x::fmpz)
    z = new()
    ccall((:acb_init, :libarb), Void, (Ptr{acb}, ), &z)
    ccall((:acb_set_fmpz, :libarb), Void, (Ptr{acb}, Ptr{fmpz}), &z, &x)
    finalizer(z, _acb_clear_fn)
    return z
  end

  function acb(x::arb)
    z = new()
    ccall((:acb_init, :libarb), Void, (Ptr{acb}, ), &z)
    ccall((:acb_set_arb, :libarb), Void, (Ptr{acb}, Ptr{arb}), &z, &x)
    finalizer(z, _acb_clear_fn)
    return z
  end

  function acb(x::acb, p::Clong)
    z = new()
    ccall((:acb_init, :libarb), Void, (Ptr{acb}, ), &z)
    ccall((:acb_set_round, :libarb), Void,
                (Ptr{acb}, Ptr{acb}, Clong), &z, &x, p)
    finalizer(z, _acb_clear_fn)
    return z
  end

  function acb(x::fmpz, p::Clong)
    z = new()
    ccall((:acb_init, :libarb), Void, (Ptr{acb}, ), &z)
    ccall((:acb_set_round_fmpz, :libarb), Void,
                (Ptr{acb}, Ptr{fmpz}, Clong), &z, &x, p)
    finalizer(z, _acb_clear_fn)
    return z
  end

  function acb(x::fmpq, p::Clong)
    z = new()
    ccall((:acb_init, :libarb), Void, (Ptr{acb}, ), &z)
    ccall((:acb_set_fmpq, :libarb), Void,
                (Ptr{acb}, Ptr{fmpq}, Clong), &z, &x, p)
    finalizer(z, _acb_clear_fn)
    return z
  end

  function acb(x::arb, p::Clong)
    z = new()
    ccall((:acb_init, :libarb), Void, (Ptr{acb}, ), &z)
    ccall((:acb_set_round_arb, :libarb), Void,
                (Ptr{acb}, Ptr{arb}, Clong), &z, &x, p)
    finalizer(z, _acb_clear_fn)
    return z
  end
end

function _acb_clear_fn(x::acb)
  ccall((:acb_clear, :libarb), Void, (Ptr{acb}, ), &x)
end

parent(x::acb) = x.parent

function deepcopy(a::acb)
  b = parent(a)()
  ccall((:acb_set, :libarb), Void, (Ptr{acb}, Ptr{acb}), &b, &a)
  return b
end

################################################################################
#
#  Parent object overload
#
################################################################################

function call(r::AcbField)
  z = acb()
  z.parent = r
  return z
end

function call(r::AcbField, x::Clong)
  z = acb(x)
  z = acb(z, r.prec)
  z.parent = r
  return z
end

function call(r::AcbField, x::Culong)
  z = acb(x)
  z = acb(z, r.prec)
  z.parent = r
  return z
end

function call(r::AcbField, x::fmpz)
  z = acb(x, r.prec)
  z.parent = r
  return z
end

function call(r::AcbField, x::fmpq)
  z = acb(x, r.prec)
  z.parent = r
  return z
end

function call(r::AcbField, x::arb)
  z = acb(x, r.prec)
  z.parent = r
  return z
end

################################################################################
#
#  Real and imaginary part
#
################################################################################

function real(x::acb)
  z = arb()
  r = ccall((:acb_get_real, :libarb), Ptr{arb}, (Ptr{acb}, ), &x)
  ccall((:arb_set, :libarb), Void, (Ptr{arb}, Ptr{arb}), &z, r)
  z.parent = ArbField(parent(x).prec)
  return z
end

function imag(x::acb)
  z = arb()
  r = ccall((:acb_get_imag, :libarb), Ptr{arb}, (Ptr{acb}, ), &x)
  ccall((:arb_set, :libarb), Void, (Ptr{arb}, Ptr{arb}), &z, r)
  z.parent = ArbField(parent(x).prec)
  return z
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, x::acb)
  show(io, real(x))
  print(io, " + i*")
  show(io, imag(x))
end

################################################################################
#
#  Special elements
#
################################################################################

function one(r::AcbField)
  z = acb()
  ccall((:acb_one, :libarb), Void, (Ptr{acb}, ), &z)
  z.parent = r
  return z
end

function onei(r::AcbField)
  z = acb()
  ccall((:acb_onei, :libarb), Void, (Ptr{acb}, ), &z)
  z.parent = r
  return z
end

################################################################################
#
#  Comparison
#
################################################################################

function strongequal(x::acb, y::acb)
  check_parent(x,y)
  r = ccall((:acb_equal, :libarb), Cint, (Ptr{acb}, Ptr{acb}), &x, &y)
  return Bool(r)
end

################################################################################
#
#  Unary operations
#
################################################################################

function -(x::acb)
  z = parent(x)()
  ccall((:acb_neg, :libarb), Void, (Ptr{acb}, Ptr{acb}), &z, &x)
  return z
end

################################################################################
#
#  Binary operations
#
################################################################################

function +(x::acb, y::acb)
  z = parent(x)()
  ccall((:acb_add, :libarb), Void,
              (Ptr{acb}, Ptr{acb}, Ptr{acb}, Clong), &z, &x, &y, parent(x).prec)
  return z
end

function -(x::acb, y::acb)
  z = parent(x)()
  ccall((:acb_sub, :libarb), Void,
              (Ptr{acb}, Ptr{acb}, Ptr{acb}, Clong), &z, &x, &y, parent(x).prec)
  return z
end

function *(x::acb, y::acb)
  z = parent(x)()
  ccall((:acb_mul, :libarb), Void,
              (Ptr{acb}, Ptr{acb}, Ptr{acb}, Clong), &z, &x, &y, parent(x).prec)
  return z
end

*(x::acb, y::fmpq) = x*parent(x)(y)

*(x::fmpq, y::acb) = y*x

function /(x::acb, y::acb)
  z = parent(x)()
  ccall((:acb_div, :libarb), Void,
              (Ptr{acb}, Ptr{acb}, Ptr{acb}, Clong), &z, &x, &y, parent(x).prec)
  return z
end

function ^(x::acb, y::Int)
  if y == 1
    return deepcopy(x)
  elseif y == 0
    return one(parent(x))
  end
  y < 0 && error("y must be positive")
  z = parent(x)()
  ccall((:acb_pow_si, :libarb), Void,
              (Ptr{acb}, Ptr{acb}, Cint, Clong), &z, &x, y, parent(x).prec)
  return z
end

################################################################################
#
#  Unsafe arithmetic
#
################################################################################

function add!(z::acb, x::acb, y::acb)
  ccall((:acb_add, :libarb), Void, (Ptr{acb}, Ptr{acb}, Ptr{acb}), &z, &x, &y)
end

function sub!(z::acb, x::acb, y::acb)
  ccall((:acb_sub, :libarb), Void, (Ptr{acb}, Ptr{acb}, Ptr{acb}), &z, &x, &y)
end

function mul!(z::acb, x::acb, y::acb)
  ccall((:acb_mul, :libarb), Void, (Ptr{acb}, Ptr{acb}, Ptr{acb}), &z, &x, &y)
end

function div!(z::acb, x::acb, y::acb)
  ccall((:acb_div, :libarb), Void, (Ptr{acb}, Ptr{acb}, Ptr{acb}), &z, &x, &y)
end
 
################################################################################
#
#  Basic functions
#
###############################################################################

function conj(x::acb)
  z = parent(x)()
  ccall((:acb_conj, :libarb), Void, (Ptr{acb}, Ptr{acb}), &z, &x)
  return z
end

function abs(x::acb)
  z = arb()
  ccall((:acb_abs, :libarb), Void,
                (Ptr{arb}, Ptr{acb}, Clong), &z, &x, parent(x).prec)
  z.parent = ArbField(parent(x).prec)
  return z
end

