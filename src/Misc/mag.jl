################################################################################
#
#                       mag.jl: wrapper for mag 
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

################################################################################
#
#  Types and memory management
#
################################################################################

export mag, MagnSet

type MagnSet
end  

const MagSet = MagnSet()

type mag
  exp::Int    # fmpz
  man::UInt64

  function mag()
    z = new()
    ccall((:mag_init, :libarb), Void, (Ptr{mag}, ), &z)
    finalizer(z, _mag_clear_fn)
    return z
  end
  
  function mag(x::UInt)
    z = new()
    ccall((:mag_init, :libarb), Void, (Ptr{mag}, ), &z)
    ccall((:mag_set_ui, :libarb), Void, (Ptr{mag}, UInt), &z, x)
    finalizer(z, _mag_clear_fn)
    return z
  end
  
  function mag(x::fmpz)
    z = new()
    ccall((:mag_init, :libarb), Void, (Ptr{mag}, ), &z)
    ccall((:mag_set_fmpz, :libarb), Void, (Ptr{mag}, Ptr{fmpz}), &z, &x)
    finalizer(z, _mag_clear_fn)
    return z
  end

  function mag(d::Float64)
    z = new()
    ccall((:mag_init, :libarb), Void, (Ptr{mag}, ), &z)
    ccall((:mag_set_d, :libarb), Void, (Ptr{mag}, Cdouble), &z, Cdouble(d))
    finalizer(z, _mag_clear_fn)
    return z
  end

  function mag(d::Cdouble, x::fmpz)
    z = new()
    ccall((:mag_init, :libarb), Void, (Ptr{mag}, ), &z)
    ccall((:mag_set_d_2exp_fmpz, :libarb), Void,
                (Ptr{mag}, Cdouble, Ptr{fmpz}), &z, &x)
    finalizer(z, _mag_clear_fn)
    return z
  end

  function mag(x::fmpz, y::fmpz)
    z = new()
    ccall((:mag_init, :libarb), Void, (Ptr{mag}, ), &z)
    ccall((:mag_set_fmpz_2_exp_fmpz, :libarb), Void,
                (Ptr{mag}, Ptr{fmpz}, Ptr{fmpz}), &z, &x, &y)
    finalizer(z, _mag_clear_fn)
    return z
  end

  function mag(x::Culong, y::Clong)
    z = new()
    ccall((:mag_init, :libarb), Void, (Ptr{mag}, ), &z)
    ccall((:mag_set_ui_2exp_si, :libarb), Void,
                (Ptr{mag}, Culong, Clong), &z, x, y)
    finalizer(z, _mag_clear_fn)
    return z
  end
end

function _mag_clear_fn(x::mag)
  ccall((:mag_clear, :libarb), Void, (Ptr{mag}, ), &x)
end

parent(::mag) = MagSet

################################################################################
#
#  Parent object overloading
#
################################################################################

function call(::MagnSet)
  return mag()
end

function call(::MagnSet, a::Culong)
  return mag(a)
end

function call(::MagnSet, a::fmpz)
  return mag(a)
end

function call(::MagnSet, a::Int)
  return mag(fmpz(a))
end

function call(::MagnSet, d::Float64)
  return mag(d)
end

function Base.call(::MagnSet, a::Float64, b::fmpz)
  return mag(a,b)
end

function Base.call(::MagnSet, a::fmpz, b::fmpz)
  return mag(a,b)
end

function Base.call(::MagnSet, a::Culong, b::Clong)
  return mag(a,b)
end

################################################################################
#
#  Some functions
#
################################################################################

function mag_lower(x::Culong)
  z = mag()
  ccall((:mag_set_ui_lower, :libarb), Void, (Ptr{mag}, Culong), &z, x)
  return z
end

function mag_lower(x::BigInt)
  z = mag()
  x = fmpz(x)
  ccall((:mag_set_fmpz_lower, :libarb), Void, (Ptr{mag}, Ptr{fmpz}), &z, &x)
  return z
end

function mag_lower(x::BigInt, y::BigInt)
  x = fmpz(x)
  y = fmpz(y)
  z = mag()
  ccall((:mag_set_fmpz_2_exp_fmpz_lower, :libarb), Void,
              (Ptr{mag}, Ptr{fmpz}, Ptr{fmpz}), &z, &x, &y)
  return z
end

################################################################################
#
#  Special values
#
################################################################################

function one(mag)
  z = mag()
  ccall((:mag_one, :libarb), Void, (Ptr{mag}, ), &z)
  return z
end

function zero(mag)
  z = mag()
  ccall((:mag_zero, :libarb), Void, (Ptr{mag}, ), &z)
  return z
end

function inf(mag)
  z = mag()
  ccall((:mag_inf, :libarb), Void, (Ptr{mag}, ), &z)
  return z
end

################################################################################
#
#  String I/O
#
################################################################################

# magic constant 128 :(

function show(io::IO, a::mag)
  show(io,ArfField(128)(a))
end

################################################################################
#
#  Predicates
#
################################################################################

for (s,f) in (("iszero", "mag_is_zero"), ("isone", "mag_is_one"),
              ("isinf", "mag_is_inf"), ("isspecial", "mag_is_special"),
              ("isfinite", "mag_is_finite"))
  @eval begin
    function($(symbol(s)))(x::mag)
      return Bool(ccall(($f, :libarb), Cint, (Ptr{mag},), &x))
    end
  end
end

################################################################################
#
#  Comparisons
#
################################################################################

function ==(x::mag, y::mag)
  r = ccall((:mag_equal, :libarb), Cint, (Ptr{mag}, Ptr{mag}), &x, &y)
  return Bool(r)
end

function compare(x::mag, y::mag)
  r = ccall((:mag_cmp, :libarb), Cint, (Ptr{mag}, Ptr{mag}), &x, &y)
  return r
end

function <(x::mag, y::mag)
  r = compare(x,y)
  r < 0 ? true : false
end

function >(x::mag, y::mag)
  r = compare(x,y)
  r > 0 ? true : false
end

function compare_with_twopower(x::mag, y::Clong)
  r = ccall((:mag_cmp_2exp_si, :libarb), Cint, (Ptr{mag}, Clong), &x, y)
  return r
end

function lttwopower(x::mag, y::Clong)
  r = compare_with_twopower(x, y)
  r < 0 ? true : false
end

function gttwopower(x::mag, y::Clong)
  r = compare_with_twopower(x, y)
  r > 0 ? true : false
end

function eqtwopower(x::mag, y::Clong)
  r = compare_with_twopower(x, y)
  r == 0 ? true : false
end

function min(x::mag, y::mag)
  z = mag()
  ccall((:mag_min, :libarb), Void, (Ptr{mag}, Ptr{mag}, Ptr{mag}), &z, &x, &y)
  return z
end

function max(x::mag, y::mag)
  z = mag()
  ccall((:mag_max, :libarb), Void, (Ptr{mag}, Ptr{mag}, Ptr{mag}), &z, &x, &y)
  return z
end
  
################################################################################
#
#  Conversion
#
################################################################################

function FlintQQ(x::mag)
  y = fmpq()
  ccall((:mag_get_fmpq, :libarb), Void, (Ptr{fmpq}, Ptr{mag}), &y, &x)
  return y
end
  
################################################################################
#
#  Binary operations
#
################################################################################

function +(x::mag, y::mag)
  z = mag()
  ccall((:mag_add, :libarb), Void, (Ptr{mag}, Ptr{mag}, Ptr{mag}), &z, &x, &y)
  return z
end

function *(x::mag, y::mag)
  z = mag()
  ccall((:mag_mul, :libarb), Void, (Ptr{mag}, Ptr{mag}, Ptr{mag}), &z, &x, &y)
  return z
end

function *(x::mag,y::Culong)
  z = mag()
  ccall((:mag_mul_ui, :libarb), Void, (Ptr{mag}, Ptr{mag}, Culong), &z, &x, y)
  return z
end

function *(x::mag, y::fmpz)
  z = mag()
  ccall((:mag_mul_fmpz, :libarb), Void,
              (Ptr{mag}, Ptr{mag}, Ptr{fmpz}), &z, &x, &y)
  return z
end

*(x::BigInt, y::mag) = y*x

function /(x::mag, y::mag)
  z = mag()
  ccall((:mag_div, :libarb), Void, (Ptr{mag}, Ptr{mag}, Ptr{mag}), &z, &x, &y)
  return z
end

function /(x::mag, y::Culong)
  z = mag()
  ccall((:mag_div_ui, :libarb), Void, (Ptr{mag}, Ptr{mag}, Culong), &z, &x, y)
  return z
end

function /(x::mag, y::fmpz)
  z = mag()
  ccall((:mag_div_fmpz, :libarb), Void,
              (Ptr{mag}, Ptr{mag}, Ptr{fmpz}), &z, &x, &y)
  return z
end

