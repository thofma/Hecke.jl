################################################################################
#
#                       arf.jl: wrapper for arf
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
#  - Sensible way to deal with rounding modes (at least documentation)
#
################################################################################

################################################################################
#
#  Types and memory management
#
################################################################################

const ArfFieldID = IdDict()

mutable struct ArfField <: Field
  prec::Int
  rndmode::Cint

  function ArfField(p::Int = 256, r::Cint = Cint(4))
    try
      return ArfFieldID[p,r]::ArfField
    catch
      z = new(p,r)
      ArfFieldID[p,r] = z
      return z
    end
  end
end

mutable struct arf
  exp::Int # ZZRingElem
  size::UInt64 # mp_size_t
  d1::Int64 # mantissa_struct
  d2::Int64
  parent::ArfField

  function arf()
    z = new()
    ccall((:arf_init, libarb), Nothing, (Ref{arf}, ), z)
    finalizer(_arf_clear_fn, z)
    return z
  end

  function arf(i::Int)
    z = new()
    ccall((:arf_init, libarb), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_si, libarb), Nothing, (Ref{arf}, Int), z, i)
    finalizer(_arf_clear_fn, z)
    return z
  end

  function arf(i::UInt)
    z = new()
    ccall((:arf_init, libarb), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_ui, libarb), Nothing, (Ref{arf}, UInt), z, i)
    finalizer(_arf_clear_fn, z)
    return z
  end

  function arf(i::ZZRingElem)
    z = new()
    ccall((:arf_init, libarb), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_fmpz, libarb), Nothing, (Ref{arf}, Ref{ZZRingElem}), z, i)
    finalizer(_arf_clear_fn, z)
    return z
  end

  function arf(x::BigFloat)
    z = new()
    ccall((:arf_init, libarb), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_mpfr, libarb), Nothing, (Ref{arf}, Ref{BigFloat}), z, x)
    finalizer(_arf_clear_fn, z)
    return z
  end

  function arf(x::Cdouble)
    z = new()
    ccall((:arf_init, libarb), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_d, libarb), Nothing, (Ref{arf}, Cdouble), z, x)
    finalizer(_arf_clear_fn, z)
    return z
  end

  function arf(x::mag)
    z = new()
    ccall((:arf_init, libarb), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_mag, libarb), Nothing, (Ref{arf}, Ref{mag}), z, x)
    finalizer(_arf_clear_fn, z)
    return z
  end

  function arf(x::arf, p::Int, r::Cint)
    z = new()
    ccall((:arf_init, libarb), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_round, libarb), Nothing,
                (Ref{arf}, Ref{arf}, Int, Cint), z, x, p, r)
    finalizer(_arf_clear_fn, z)
    return z
  end

  function arf(x::Int, p::Int, r::Cint)
    z = new()
    ccall((:arf_init, libarb), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_round_si, libarb), Nothing,
                  (Ref{arf}, Int, Int, Cint), z, x, p, r)
    finalizer(_arf_clear_fn, z)
    return z
  end

 function arf(x::UInt, p::Int, r::Cint)
    z = new()
    ccall((:arf_init, libarb), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_round_ui, libarb), Nothing,
                  (Ref{arf}, UInt, Int, Cint), z, x, p, r)
    finalizer(_arf_clear_fn, z)
    return z
  end

 function arf(x::ZZRingElem, p::Int, r::Cint)
    z = new()
    ccall((:arf_init, libarb), Nothing, (Ref{arf}, ), z)
    ccall((:arf_set_round_fmpz, libarb), Nothing,
                  (Ref{arf}, Ref{ZZRingElem}, Int, Cint), z, x, p, r)
    finalizer(_arf_clear_fn, z)
    return z
  end
end

function _arf_clear_fn(x::arf)
  ccall((:arf_clear, libarb), Nothing, (Ref{arf}, ), x)
end

parent(x::arf) = x.parent

################################################################################
#
#  Parent object overloads
#
################################################################################

function (r::ArfField)()
  z = arf()
  z.parent = r
  return z
end

function (r::ArfField)(x::Int)
  z = arf(x, r.prec, r.rndmode)
  z.parent = r
  return z
end

function (r::ArfField)(x::UInt)
  z = arf(x, r.prec, r.rndmode)
  z.parent = r
  return z
end

function (r::ArfField)(x::ZZRingElem)
  z = arf(x, r.prec, r.rndmode)
  z.parent = r
  return z
end

function (r::ArfField)(x::Float64)
  z = arf(x)
  z = arf(z, r.prec, r.rndmode)
  z.parent = r
  return z
end

function (r::ArfField)(x::BigFloat)
  z = arf(x)
  z = arf(z, r.prec, r.rndmode)
  z.parent = r
  return z
end

function (r::ArfField)(x::mag)
  z = arf(x)
  z = arf(z, r.prec, r.rndmode)
  z.parent = r
  return z
end

################################################################################
#
#  Special values
#
################################################################################

for (s,f) in (("zero", "arf_zero"), ("one", "arf_one"),
              ("pos_inf", "arf_pos_inf"), ("neg_inf", "arf_neg_inf"),
              ("nan", "arf_nan"))
  @eval begin
    function($(Symbol(s)))(r::ArfField)
      z = r()
      ccall(($f, libarb), Nothing, (Ref{arf}, ), z)
      return z
    end
  end
end

################################################################################
#
#  String I/O
#
################################################################################

# this function is crap
function show(io::IO, a::arf)
  #cstr = ccall((:arf_get_str, libarb), Ref{UInt8}, (Ref{arf}, ), a.data)
  #print(io, bytestring(cstr))
  #ccall((:flint_free, libflint), Nothing, (Ref{UInt8},), cstr)
  return show(io, BigFloat(a))
end

function show(io::IO, a::ArfField)
  print(io, "Field of arf's with precision $(a.prec)")
  print(io, " and rounding mode $(a.rndmode)")
end

################################################################################
#
#  Predicates
#
################################################################################

for (s,f) in (("iszero", "arf_iszero"), ("isone", "arf_is_one"),
              ("isposinf", "arf_is_pos_inf"),
              ("isneginf", "arf_is_neg_inf"),
              ("isinf", "arf_is_inf"),
              ("isnan", "arf_is_nan"),
              ("is_normal", "arf_is_normal"),
              ("isfinite", "arf_isfinite"),
              ("isspecial", "arf_is_special"))
  @eval begin
    function($(Symbol(s)))(x::arf)
      return Bool(ccall(($f, libarb), Cint, (Ref{arf},), x.data))
    end
  end
end

################################################################################
#
#  Comparison
#
################################################################################

function ==(x::arf, y::arf)
  r = ccall((:arf_equal, libarb), Cint, (Ref{arf}, Ref{arf}), x, y)
  return Bool(r)
end

function compare(x::arf, y::arf)
  r = ccall((:arf_cmp, libarb), Cint, (Ref{arf}, Ref{arf}), x, y)
  return r
end

function <(x::arf, y::arf)
  r = compare(x,y)
  r < 0 ? true : false
end

function >(x::arf, y::arf)
  r = compare(x,y)
  r > 0 ? true : false
end

function max(x::arf, y::arf)
  z = parent(x)()
  ccall((:arf_max, libarb), Nothing, (Ref{arf}, Ref{arf}, Ref{arf}), z, x, y)
  return z
end

function min(x::arf, y::arf)
  z = parent(x)()
  ccall((:arf_min, libarb), Nothing, (Ref{arf}, Ref{arf}, Ref{arf}), z, x, y)
  return z
end

################################################################################
#
#  Unary operations
#
################################################################################

function -(x::arf)
  z = parent(x)()
  ccall((:arf_neg, libarb), Nothing, (Ref{arf}, Ref{arf}), z, x)
  return z
end

################################################################################
#
#  Binary operations
#
################################################################################

function +(x::arf, y::arf)
  check_parent(x,y)
  z = parent(x)()
  ccall(("arf_add", libarb), Nothing,
              (Ref{arf}, Ref{arf}, Ref{arf}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

function +(x::arf, y::UInt)
  z = parent(x)()
  ccall(("arf_add_ui", libarb), Nothing,
              (Ref{arf}, Ref{arf}, UInt, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

+(x::UInt, y::arf) = +(y, x)

function +(x::arf, y::Int)
  z = parent(x)()
  ccall(("arf_add_si", libarb), Nothing,
              (Ref{arf}, Ref{arf}, Int, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

+(x::Int, y::arf) = +(y, x)

function +(x::arf, y::ZZRingElem)
  z = parent(x)()
  ccall(("arf_add_fmpz", libarb), Nothing,
              (Ref{arf}, Ref{arf}, Ref{ZZRingElem}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

+(x::ZZRingElem, y::arf) = +(y, x)

function *(x::arf, y::arf)
  z = parent(x)()
  ccall(("_arf_mul", libarb), Nothing,
              (Ref{arf}, Ref{arf}, Ref{arf}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

function *(x::arf, y::UInt)
  z = parent(x)()
  ccall(("arf_mul_ui", libarb), Nothing,
              (Ref{arf}, Ref{arf}, UInt, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

*(x::UInt, y::arf) = *(y, x)

function *(x::arf, y::Int)
  z = parent(x)()
  ccall(("arf_mul_si", libarb), Nothing,
              (Ref{arf}, Ref{arf}, Int, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

*(x::Int, y::arf) = *(y, x)

function *(x::arf, y::ZZRingElem)
  z = parent(x)()
  ccall(("arf_mul_fmpz", libarb), Nothing,
              (Ref{arf}, Ref{arf}, Ref{ZZRingElem}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

*(x::ZZRingElem, y::arf) = *(y, x)

function -(x::arf, y::arf)
  check_parent(x,y)
  z = parent(x)()
  ccall(("arf_sub", libarb), Nothing,
                (Ref{arf}, Ref{arf}, Ref{arf}, Int, Cint),
                z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

function -(x::arf, y::UInt)
  z = parent(x)()
  ccall(("arf_sub_ui", libarb), Nothing,
              (Ref{arf}, Ref{arf}, UInt, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

-(x::UInt, y::arf) = -(y - x)

function -(x::arf, y::Int)
  z = parent(x)()
  ccall(("arf_sub_si", libarb), Nothing,
              (Ref{arf}, Ref{arf}, Int, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

-(x::Int, y::arf) = -(y - x)

function -(x::arf, y::ZZRingElem)
  z = parent(x)()
  ccall(("arf_sub_fmpz", libarb), Nothing,
              (Ref{arf}, Ref{arf}, Ref{ZZRingElem}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

-(x::ZZRingElem, y::arf) = -(y - x)

function /(x::arf, y::arf)
  check_parent(x,y)
  z = parent(x)()
  ccall((:arf_div, libarb), Nothing,
              (Ref{arf}, Ref{arf}, Ref{arf}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
  return z
end

################################################################################
#
#  Unsafe arithmetic
#
################################################################################

function add!(x::arf, y::arf)
  ccall(("arf_add", libarb), Nothing,
              (Ref{arf}, Ref{arf}, Ref{arf}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
end


function div!(z::arf, x::arf, y::arf)
  ccall((:arf_div, libarb), Nothing,
              (Ref{arf}, Ref{arf}, Ref{arf}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
end

function sub!(x::arf, y::arf)
  ccall((:arf_sub, libarb), Nothing,
              (Ref{arf}, Ref{arf}, Ref{arf}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
end

function mul!(x::arf, y::arf)
  ccall((:_arf_mul, libarb), Nothing,
              (Ref{arf}, Ref{arf}, Ref{arf}, Int, Cint),
              z, x, y, parent(x).prec, parent(x).rndmode)
end

################################################################################
#
#  Some functions
#
################################################################################

function sign(x::arf)
  r = ccall((:arf_sgn, libarb), Cint, (Ref{arf}, ), x)
  return r
end

function abs(x::arf)
  z = parent(x)()
  ccall((:arf_abs, libarb), Nothing, (Ref{arf}, Ref{arf}), z, x)
  return z
end

function Base.sqrt(x::arf)
  z = parent(x)()
  ccall((:arf_sqrt, libarb), Nothing,
              (Ref{arf}, Ref{arf}, Int, Cint),
              z, x, parent(x).prec, parent(x).rndmode)
  return z
end


################################################################################
#
#  Conversion
#
################################################################################

function Cdouble(a::arf, rnd::Cint = 4)
  z = ccall((:arf_get_d, libarb), Cdouble, (Ref{arf}, Cint), a.data, rnd)
  return z
end

function BigFloat(x::arf)
  old_prec = get_bigfloat_precision()
  set_bigfloat_precision(parent(x).prec)
  z = BigFloat(0)
  r = ccall((:arf_get_mpfr, libarb), Cint,
                (Ref{BigFloat}, Ref{arf}, Cint), z, x, Cint(0))
  set_bigfloat_precision(old_prec)
  return z
end

