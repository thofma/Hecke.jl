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

export arf, ArfField

export pos_inf, neg_inf, nan, isposinf, isneginf, isnan, isnormal, max, min

################################################################################
#
#  Types and memory management
#
################################################################################

const ArfFieldID = ObjectIdDict()

type ArfField <: Field
  prec::Clong
  rndmode::Cint
  
  function ArfField(p::Clong = 256, r::Cint = Cint(4))
    try
      return ArfFieldID[p,r]::ArfField
    catch
      z = new(p,r)
      ArfFieldID[p,r] = z
      return z
    end
  end
end

type arf
  exp::Int # fmpz
  size::UInt64 # mp_size_t
  d1::Int64 # mantissa_struct
  d2::Int64
  parent::ArfField

  function arf()
    z = new()
    ccall((:arf_init, :libarb), Void, (Ptr{arf}, ), &z)
    finalizer(z, _arf_clear_fn)
    return z
  end
  
  function arf(i::Clong)
    z = new()
    ccall((:arf_init, :libarb), Void, (Ptr{arf}, ), &z)
    ccall((:arf_set_si, :libarb), Void, (Ptr{arf}, Clong), &z, i)
    finalizer(z, _arf_clear_fn)
    return z
  end

  function arf(i::Culong)
    z = new()
    ccall((:arf_init, :libarb), Void, (Ptr{arf}, ), &z)
    ccall((:arf_set_ui, :libarb), Void, (Ptr{arf}, Culong), &z, i)
    finalizer(z, _arf_clear_fn)
    return z
  end

  function arf(i::fmpz)
    z = new()
    ccall((:arf_init, :libarb), Void, (Ptr{arf}, ), &z)
    ccall((:arf_set_fmpz, :libarb), Void, (Ptr{arf}, Ptr{fmpz}), &z, &i)
    finalizer(z, _arf_clear_fn)
    return z
  end

  function arf(x::BigFloat)
    z = new()
    ccall((:arf_init, :libarb), Void, (Ptr{arf}, ), &z)
    ccall((:arf_set_mpfr, :libarb), Ptr{arf}, (Ptr{arf}, Ptr{BigFloat}), &z, &x)
    finalizer(z, _arf_clear_fn)
    return z
  end

  function arf(x::Cdouble)
    z = new()
    ccall((:arf_init, :libarb), Void, (Ptr{arf}, ), &z)
    ccall((:arf_set_d, :libarb), Void, (Ptr{arf}, Cdouble), &z, x)
    finalizer(z, _arf_clear_fn)
    return z
  end

  function arf(x::mag)
    z = new()
    ccall((:arf_init, :libarb), Void, (Ptr{arf}, ), &z)
    ccall((:arf_set_mag, :libarb), Void, (Ptr{arf}, Ptr{mag}), &z, &x)
    finalizer(z, _arf_clear_fn)
    return z
  end

  function arf(x::arf, p::Clong, r::Cint)
    z = new()
    ccall((:arf_init, :libarb), Void, (Ptr{arf}, ), &z)
    ccall((:arf_set_round, :libarb), Void,
                (Ptr{arf}, Ptr{arf}, Clong, Cint), &z, &x, p, r)
    finalizer(z, _arf_clear_fn)
    return z
  end

  function arf(x::Clong, p::Clong, r::Cint)
    z = new()
    ccall((:arf_init, :libarb), Void, (Ptr{arf}, ), &z)
    ccall((:arf_set_round_si, :libarb), Void,
                  (Ptr{arf}, Clong, Clong, Cint), &z, x, p, r)
    finalizer(z, _arf_clear_fn)
    return z
  end

 function arf(x::Culong, p::Clong, r::Cint)
    z = new()
    ccall((:arf_init, :libarb), Void, (Ptr{arf}, ), &z)
    ccall((:arf_set_round_ui, :libarb), Void,
                  (Ptr{arf}, Culong, Clong, Cint), &z, x, p, r)
    finalizer(z, _arf_clear_fn)
    return z
  end

 function arf(x::fmpz, p::Clong, r::Cint)
    z = new()
    ccall((:arf_init, :libarb), Void, (Ptr{arf}, ), &z)
    ccall((:arf_set_round_fmpz, :libarb), Void,
                  (Ptr{arf}, Ptr{fmpz}, Clong, Cint), &z, &x, p, r)
    finalizer(z, _arf_clear_fn)
    return z
  end
end

function _arf_clear_fn(x::arf)
  ccall((:arf_clear, :libarb), Void, (Ptr{arf}, ), &x)
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

function (r::ArfField)(x::Clong)
  z = arf(x, r.prec, r.rndmode)
  z.parent = r
  return z
end

function (r::ArfField)(x::Culong)
  z = arf(x, r.prec, r.rndmode)
  z.parent = r
  return z
end

function (r::ArfField)(x::fmpz)
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
      ccall(($f, :libarb), Void, (Ptr{arf}, ), &z)
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
  #cstr = ccall((:arf_get_str, :libarb), Ptr{UInt8}, (Ptr{arf}, ), a.data)
  #print(io, bytestring(cstr))
  #ccall((:flint_free, :libflint), Void, (Ptr{UInt8},), cstr)
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
              ("isnormal", "arf_is_normal"),
              ("isfinite", "arf_isfinite"),
              ("isspecial", "arf_is_special"))
  @eval begin
    function($(Symbol(s)))(x::arf)
      return Bool(ccall(($f, :libarb), Cint, (Ptr{arf},), x.data))
    end
  end
end

################################################################################
#
#  Comparison
#
################################################################################

function ==(x::arf, y::arf)
  r = ccall((:arf_equal, :libarb), Cint, (Ptr{arf}, Ptr{arf}), &x, &y)
  return Bool(r)
end

function compare(x::arf, y::arf)
  r = ccall((:arf_cmp, :libarb), Cint, (Ptr{arf}, Ptr{arf}), &x, &y)
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
  ccall((:arf_max, :libarb), Void, (Ptr{arf}, Ptr{arf}, Ptr{arf}), &z, &x, &y)
  return z
end

function min(x::arf, y::arf)
  z = parent(x)()
  ccall((:arf_min, :libarb), Void, (Ptr{arf}, Ptr{arf}, Ptr{arf}), &z, &x, &y)
  return z
end

################################################################################
#
#  Unary operations
#
################################################################################

function -(x::arf)
  z = parent(x)()
  ccall((:arf_neg, :libarb), Void, (Ptr{arf}, Ptr{arf}), &z, &x)
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
  ccall(("arf_add", :libarb), Void,
              (Ptr{arf}, Ptr{arf}, Ptr{arf}, Clong, Cint),
              &z, &x, &y, parent(x).prec, parent(x).rndmode)
  return z
end

function +(x::arf, y::Culong)
  z = parent(x)()
  ccall(("arf_add_ui", :libarb), Void,
              (Ptr{arf}, Ptr{arf}, Culong, Clong, Cint),
              &z, &x, y, parent(x).prec, parent(x).rndmode)
  return z
end

+(x::Culong, y::arf) = +(y, x)

function +(x::arf, y::Clong)
  z = parent(x)()
  ccall(("arf_add_si", :libarb), Void,
              (Ptr{arf}, Ptr{arf}, Clong, Clong, Cint),
              &z, &x, y, parent(x).prec, parent(x).rndmode)
  return z
end

+(x::Clong, y::arf) = +(y, x)

function +(x::arf, y::fmpz)
  z = parent(x)()
  ccall(("arf_add_fmpz", :libarb), Void,
              (Ptr{arf}, Ptr{arf}, Ptr{fmpz}, Clong, Cint),
              &z, &x, &y, parent(x).prec, parent(x).rndmode)
  return z
end

+(x::fmpz, y::arf) = +(y, x)

function *(x::arf, y::arf)
  z = parent(x)()
  ccall(("_arf_mul", :libarb), Void,
              (Ptr{arf}, Ptr{arf}, Ptr{arf}, Clong, Cint),
              &z, &x, &y, parent(x).prec, parent(x).rndmode)
  return z
end

function *(x::arf, y::Culong)
  z = parent(x)()
  ccall(("arf_mul_ui", :libarb), Void,
              (Ptr{arf}, Ptr{arf}, Culong, Clong, Cint),
              &z, &x, y, parent(x).prec, parent(x).rndmode)
  return z
end

*(x::Culong, y::arf) = *(y, x)

function *(x::arf, y::Clong)
  z = parent(x)()
  ccall(("arf_mul_si", :libarb), Void,
              (Ptr{arf}, Ptr{arf}, Clong, Clong, Cint),
              &z, &x, y, parent(x).prec, parent(x).rndmode)
  return z
end

*(x::Clong, y::arf) = *(y, x)

function *(x::arf, y::fmpz)
  z = parent(x)()
  ccall(("arf_mul_fmpz", :libarb), Void,
              (Ptr{arf}, Ptr{arf}, Ptr{fmpz}, Clong, Cint),
              &z, &x, &y, parent(x).prec, parent(x).rndmode)
  return z
end

*(x::fmpz, y::arf) = *(y, x)

function -(x::arf, y::arf)
  check_parent(x,y)
  z = parent(x)()
  ccall(("arf_sub", :libarb), Void,
                (Ptr{arf}, Ptr{arf}, Ptr{arf}, Clong, Cint),
                &z, &x, &y, parent(x).prec, parent(x).rndmode)
  return z
end

function -(x::arf, y::Culong)
  z = parent(x)()
  ccall(("arf_sub_ui", :libarb), Void,
              (Ptr{arf}, Ptr{arf}, Culong, Clong, Cint),
              &z, &x, y, parent(x).prec, parent(x).rndmode)
  return z
end

-(x::Culong, y::arf) = -(y - x)

function -(x::arf, y::Clong)
  z = parent(x)()
  ccall(("arf_sub_si", :libarb), Void,
              (Ptr{arf}, Ptr{arf}, Clong, Clong, Cint),
              &z, &x, y, parent(x).prec, parent(x).rndmode)
  return z
end

-(x::Clong, y::arf) = -(y - x)

function -(x::arf, y::fmpz)
  z = parent(x)()
  ccall(("arf_sub_fmpz", :libarb), Void,
              (Ptr{arf}, Ptr{arf}, Ptr{fmpz}, Clong, Cint),
              &z, &x, &y, parent(x).prec, parent(x).rndmode)
  return z
end

-(x::fmpz, y::arf) = -(y - x)
 
function /(x::arf, y::arf)
  check_parent(x,y)
  z = parent(x)()
  ccall((:arf_div, :libarb), Void,
              (Ptr{arf}, Ptr{arf}, Ptr{arf}, Clong, Cint),
              &z, &x, &y, parent(x).prec, parent(x).rndmode)
  return z
end

################################################################################
#
#  Unsafe arithmetic
#
################################################################################

function add!(x::arf, y::arf)
  ccall(("arf_add", :libarb), Void,
              (Ptr{arf}, Ptr{arf}, Ptr{arf}, Clong, Cint),
              &z, &x, &y, parent(x).prec, parent(x).rndmode)
end


function div!(z::arf, x::arf, y::arf)
  ccall((:arf_div, :libarb), Void,
              (Ptr{arf}, Ptr{arf}, Ptr{arf}, Clong, Cint),
              &z, &x, &y, parent(x).prec, parent(x).rndmode)
end

function sub!(x::arf, y::arf)
  ccall((:arf_sub, :libarb), Void,
              (Ptr{arf}, Ptr{arf}, Ptr{arf}, Clong, Cint),
              &z, &x, &y, parent(x).prec, parent(x).rndmode)
end

function mul!(x::arf, y::arf)
  ccall((:_arf_mul, :libarb), Void,
              (Ptr{arf}, Ptr{arf}, Ptr{arf}, Clong, Cint),
              &z, &x, &y, parent(x).prec, parent(x).rndmode)
end

################################################################################
#
#  Some functions
#
################################################################################

function sign(x::arf)
  r = ccall((:arf_sgn, :libarb), Cint, (Ptr{arf}, ), &x)
  return r
end

function abs(x::arf)
  z = parent(x)()
  ccall((:arf_abs, :libarb), Void, (Ptr{arf}, Ptr{arf}), &z, &x)
  return z
end

function sqrt(x::arf)
  z = parent(x)()
  ccall((:arf_sqrt, :libarb), Void,
              (Ptr{arf}, Ptr{arf}, Clong, Cint),
              &z, &x, parent(x).prec, parent(x).rndmode)
  return z
end


################################################################################
#
#  Conversion
#
################################################################################

function Cdouble(a::arf, rnd::Cint = 4)
  z = ccall((:arf_get_d, :libarb), Cdouble, (Ptr{arf}, Cint), a.data, rnd)
  return z
end

function BigFloat(x::arf)
  old_prec = get_bigfloat_precision()
  set_bigfloat_precision(parent(x).prec)
  z = BigFloat(0)
  r = ccall((:arf_get_mpfr, :libarb), Cint,
                (Ptr{BigFloat}, Ptr{arf}, Cint), &z, &x, Cint(0))
  set_bigfloat_precision(old_prec)
  return z
end

