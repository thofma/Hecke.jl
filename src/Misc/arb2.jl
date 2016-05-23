################################################################################
#
#                       arb.jl: wrapper for arb
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
#  Todo:
#    - Think of a meaningful definition for ==
#
################################################################################

export ArbField, arb

export radius, midpoint, zeropminf, indeterminate, contains, contains_zero,
       contains_negative, contains_positive, contains_nonnegative,
       contains_nonpositive, isnonzero, isexact, isint, ispositive,
       isnonnegative, isnegative, isnonpositive, sin, cos, tan, add!, mul!,
       sub!, div!, strongequal, prec

################################################################################
#
#  Types and memory management
#
################################################################################

const ArbFieldID = ObjectIdDict()

type ArbField <: Field
  prec::Clong
  
  function ArbField(p::Clong = 256)
    try
      return ArbFieldID[p]::ArbField
    catch
      ArbFieldID[p] = new(p)
      return ArbFieldID[p]::ArbField
    end
  end
end

prec(x::ArbField) = x.prec

type arb <: FieldElem
  mid_exp::Int # fmpz
  mid_size::UInt64 # mp_size_t
  mid_d1::Int64 # mantissa_struct
  mid_d2::Int64
  rad_exp::Int # fmpz
  rad_man::UInt64
  parent::ArbField

  function arb()
    z = new()
    ccall((:arb_init, :libarb), Void, (Ptr{arb}, ), &z)
    finalizer(z, _arb_clear_fn)
    return z
  end

  function arb(x::arb, p::Clong)
    z = new()
    ccall((:arb_init, :libarb), Void, (Ptr{arb}, ), &z)
    ccall((:arb_set_round, :libarb), Void,
                (Ptr{arb}, Ptr{arb}, Clong), &z, &x, p)
    finalizer(z, _arb_clear_fn)
    return z
  end

  function arb(x::Clong)
    z = new()
    ccall((:arb_init, :libarb), Void, (Ptr{arb}, ), &z)
    ccall((:arb_set_si, :libarb), Void, (Ptr{arb}, Clong), &z, x)
    finalizer(z, _arb_clear_fn)
    return z
  end
 
  function arb(i::Culong)
    z = new()
    ccall((:arb_init, :libarb), Void, (Ptr{arb}, ), &z)
    ccall((:arb_set_ui, :libarb), Void, (Ptr{arb}, Culong), &z, i)
    finalizer(z, _arb_clear_fn)
    return z
  end

  function arb(x::fmpz)
    z = new()
    ccall((:arb_init, :libarb), Void, (Ptr{arb}, ), &z)
    ccall((:arb_set_fmpz, :libarb), Void, (Ptr{arb}, Ptr{fmpz}), &z, &x)
    finalizer(z, _arb_clear_fn)
    return z
  end
 
  function arb(x::fmpz, p::Clong)
    z = new()
    ccall((:arb_init, :libarb), Void, (Ptr{arb}, ), &z)
    ccall((:arb_set_round_fmpz, :libarb), Void,
                (Ptr{arb}, Ptr{fmpz}, Clong), &z, &x, p)
    finalizer(z, _arb_clear_fn)
    return z
  end
 
  function arb(x::fmpq, p::Clong)
    z = new()
    ccall((:arb_init, :libarb), Void, (Ptr{arb}, ), &z)
    ccall((:arb_set_fmpq, :libarb), Void,
                (Ptr{arb}, Ptr{fmpq}, Clong), &z, &x, p)
    finalizer(z, _arb_clear_fn)
    return z
  end
 
  function arb(x::arf)
    z = new()
    ccall((:arb_init, :libarb), Void, (Ptr{arb}, ), &z)
    ccall((:arb_set_arf, :libarb), Void, (Ptr{arb}, Ptr{arf}), &z, &x)
    finalizer(z, _arb_clear_fn)
    return z
  end
end

function _arb_clear_fn(x::arb)
  ccall((:arb_clear, :libarb), Void, (Ptr{arb}, ), &x)
end

elem_type(x::ArbField) = arb

parent(x::arb) = x.parent

################################################################################
#
#  Parent object overloading
#
################################################################################

function call(r::ArbField)
  z = arb()
  z.parent = r
  return z
end

function call(r::ArbField, x::Clong)
  z = arb(fmpz(x), r.prec)
  z.parent = r
  return z
end

function call(r::ArbField, x::Culong)
  z = arb(fmpz(x), r.prec)
  z.parent = r
  return z
end

function call(r::ArbField, x::fmpz)
  z = arb(x, r.prec)
  z.parent = r
  return z
end

function call(r::ArbField, x::fmpq)
  z = arb(x, r.prec)
  z.parent = r
  return z
end
  
function call(r::ArbField, x::arf)
  z = arb(arb(x), r.prec)
  z.parent = r
  return z
end

function call(r::ArbField, x::Float64)
  return r(arf(x))
end

function call(r::ArbField, x::arb)
  z = arb(x, r.prec)
  z.parent = r
  return z
end

function call(r::ArbField, x::MathConst)
  if x == pi
    z = pi_arb(r.prec)
    z.parent = r
    return z
  elseif x == e
    z = e_arb(r.prec)
    z.parent = r 
    return z
  else
    error("constant not supported")
  end
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, x::arb)
  # I print only 40 digits, which is a kind of magic constant
  # Better ideas?
  cstr = ccall((:arb_get_str, :libarb), Ptr{UInt8}, (Ptr{arb}, Clong, Culong),
                                                  &x, Clong(40), Culong(1))
  print(io, bytestring(cstr))
  ccall((:flint_free, :libflint), Void, (Ptr{UInt8},), cstr)
end

################################################################################
#
#  Comparison and containment
#
################################################################################

function strongequal(x::arb, y::arb)
  r = ccall((:arb_equal, :libarb), Cint, (Ptr{arb}, Ptr{arb}), &x, &y)
  return Bool(r)
end

function overlaps(x::arb, y::arb)
  r = ccall((:arb_overlaps, :libarb), Cint, (Ptr{arb}, Ptr{arb}), &x, &y)
  return Bool(r)
end

function contains(x::arb, y::arf)
  r = ccall((:arb_contains_arf, :libarb), Cint, (Ptr{arb}, Ptr{arf}), &x, &y)
  return Bool(r)
end

function contains(x::arb, y::fmpq)
  r = ccall((:arb_contains_fmpq, :libarb), Cint, (Ptr{arb}, Ptr{fmpq}), &x, &y)
  return Bool(r)
end

function contains(x::arb, y::fmpz)
  r = ccall((:arb_contains_fmpz, :libarb), Cint, (Ptr{arb}, Ptr{fmpz}), &x, &y)
  return Bool(r)
end

function contains(x::arb, y::Clong)
  r = ccall((:arb_contains_si, :libarb), Cint, (Ptr{arb}, Ptr{fmpz}), &x, y)
  return Bool(r)
end

function contains(x::arb, y::BigFloat)
  r = ccall((:arb_contains_mpfr, :libarb), Cint,
              (Ptr{arb}, Ptr{BigFloat}), &x, &y)
  return Bool(r)
end

function contains(x::arb, y::arb)
  r = ccall((:arb_contains, :libarb), Cint, (Ptr{arb}, Ptr{arb}), &x, &y)
  return Bool(r)
end

for (s,f) in (("contains_zero", "arb_contains_zero"),
              ("contains_negative", "arb_contains_negative"),
              ("contains_positive", "arb_contains_positive"),
              ("contains_nonpositive", "arb_contains_nonpositive"),
              ("contains_nonnegative", "arb_contains_nonnegative"))
  @eval begin
    function($(Symbol(s)))(x::arb)
      r = ccall(($f, :libarb), Cint, (Ptr{arb}, ), &x)
      return Bool(r)
    end
  end
end

################################################################################
#
#  Predicates
#
################################################################################

for (s,f) in (("iszero", "arb_is_zero"),
              ("isnonzero", "arb_is_nonzero"),
              ("isone", "arb_is_one"),
              ("isfinite", "arb_is_finite"),
              ("isexact", "arb_is_exact"),
              ("isint", "arb_is_int"),
              ("ispositive", "arb_is_positive"),
              ("isnonnegative", "arb_is_nonnegative"),
              ("isnegative", "arb_is_negative"),
              ("isnonpositive", "arb_is_nonpositive"))
  @eval begin
    function($(Symbol(s)))(x::arb)
      i = ccall(($f, :libarb), Cint, (Ptr{arb},), &x)
      return Bool(i)
    end
  end
end

function radius(x::arb)
  r = ccall((:arb_get_rad, :libarb), Ptr{mag}, (Ptr{arb}, ), &x)
  z = mag()
  ccall((:mag_set, :libarb), Void, (Ptr{mag}, Ptr{mag}), &z, r)
  return z
end

function midpoint(x::arb)
  r = ccall((:arb_get_mid, :libarb), Ptr{arf}, (Ptr{arb},), &x)
  z = arf()
  z.parent = ArfField(parent(x).prec)
  ccall((:arf_set, :libarb), Void, (Ptr{arf}, Ptr{arf}), &z, r)
  return z
end

for (s,f) in (("iszero", "arb_is_zero"), ("isnonzero", "arb_is_nonzero"),
              ("isone", "arb_is_one"), ("isfinite", "arb_is_finite"),
              ("isexact", "arb_is_exact"), ("isint", "arb_is_int"),
              ("ispositive", "arb_is_positive"),
              ("isnonnegative", "arb_is_nonnegative"),
              ("isnegative", "arb_is_negative"),
              ("isnonnegative", "arb_is_nonnegative"))
  @eval begin
    function($(Symbol(s)))(x::arb)
      return Bool(ccall(($f, :libarb), Cint, (Ptr{arb}, ), &x))
    end
  end
end

################################################################################
#
#  Unary operations
#
################################################################################

function abs(x::arb)
  z = parent(x)()
  ccall((:arb_abs, :libarb), Void, (Ptr{arb}, Ptr{arb}), &z, &x)
  return z
end

################################################################################
#
#  Binary operations
#
################################################################################

function -(x::arb)
  z = parent(x)()
  ccall((:arb_neg_round, :libarb), Void, (Ptr{arb}, Ptr{arb}), &z, &x)
  return z
end

for (s,f) in ((:+,"arb_add"), (:*,"arb_mul"), (:/, "arb_div"), (:-,"arb_sub"))
  @eval begin
    function ($s)(x::arb, y::arb)
      z = parent(x)()
      ccall(($f, :libarb), Void, (Ptr{arb}, Ptr{arb}, Ptr{arb}, Clong),
                           &z, &x, &y, parent(x).prec)
      return z
    end
  end
end

for (f,s) in ((:+, "add"), (:*, "mul"))
  @eval begin
    function ($f)(x::arb, y::arf)
      z = parent(x)()
      ccall(($("arb_"*s*"_arf"), :libarb), Void,
                  (Ptr{arb}, Ptr{arb}, Ptr{arf}, Clong),
                  &z, &x, &y, parent(x).prec)
      return z
    end

    ($f)(x::arf, y::arb) = ($f)(y, x)

    function ($f)(x::arb, y::Culong)
      z = parent(x)()
      ccall(($("arb_"*s*"_ui"), :libarb), Void,
                  (Ptr{arb}, Ptr{arb}, Culong, Clong),
                  &z, &x, y, parent(x).prec)
      return z
    end

    ($f)(x::Culong, y::arb) = ($f)(y, x)

    function ($f)(x::arb, y::Clong)
      z = parent(x)()
      ccall(($("arb_"*s*"_si"), :libarb), Void,
      (Ptr{arb}, Ptr{arb}, Clong, Clong), &z, &x, y, parent(x).prec)
      return z
    end

    ($f)(x::Clong, y::arb) = ($f)(y,x)

    function ($f)(x::arb, y::fmpz)
      z = parent(x)()
      ccall(($("arb_"*s*"_fmpz"), :libarb), Void,
                  (Ptr{arb}, Ptr{arb}, Ptr{fmpz}, Clong),
                  &z, &x, &y, parent(x).prec)
      return z
    end

    ($f)(x::fmpz, y::arb) = ($f)(y,x)
  end
end

function -(x::arb, y::arf)
  z = parent(x)()
  ccall((:arb_sub_arf, :libarb), Void,
              (Ptr{arb}, Ptr{arb}, Ptr{arf}, Clong), &z, &x, &y, parent(x).prec)
  return z
end

-(x::arf, y::arb) = -(y - x)

function -(x::arb, y::Culong)
  z = parent(x)()
  ccall((:arb_sub_ui, :libarb), Void,
              (Ptr{arb}, Ptr{arb}, Culong, Clong), &z, &x, y, parent(x).prec)
  return z
end

-(x::Culong, y::arb) = -(y - x)

function -(x::arb, y::Clong)
  z = parent(x)()
  ccall((:arb_sub_si, :libarb), Void,
              (Ptr{arb}, Ptr{arb}, Clong, Clong), &z, &x, y, parent(x).prec)
  return z
end

-(x::Clong, y::arb) = -(y - x)

function -(x::arb, y::fmpz)
  z = parent(x)()
  ccall((:arb_sub_fmpz, :libarb), Void,
              (Ptr{arb}, Ptr{arb}, Ptr{fmpz}, Clong),
              &z, &x, &y, parent(x).prec)
  return z
end

-(x::fmpz, y::arb) = -(y-x)

function /(x::arb, y::arf)
  z = parent(x)()
  ccall((:arb_div_arf, :libarb), Void,
              (Ptr{arb}, Ptr{arb}, Ptr{arf}, Clong), &z, &x, &y, parent(x).prec)
  return z
end

function /(x::arb, y::Culong)
  z = parent(x)()
  ccall((:arb_div_ui, :libarb), Void,
              (Ptr{arb}, Ptr{arb}, Culong, Clong), &z, &x, y, parent(x).prec)
  return z
end

function /(x::arb, y::Clong)
  z = parent(x)()
  ccall((:arb_div_si, :libarb), Void,
              (Ptr{arb}, Ptr{arb}, Clong, Clong), &z, &x, y, parent(x).prec)
  return z
end

function /(x::arb, y::fmpz)
  z = parent(x)()
  ccall((:arb_div_fmpz, :libarb), Void,
              (Ptr{arb}, Ptr{arb}, Ptr{fmpz}, Clong),
              &z, &x, &y, parent(x).prec)
  return z
end

function ^(x::arb, y::arb)
  z = parent(x)()
  ccall((:arb_pow, :libarb), Void,
              (Ptr{arb}, Ptr{arb}, Ptr{arb}, Clong), &z, &x, &y, parent(x).prec)
  return z
end

function ^(x::arb, y::fmpz)
  z = parent(x)()
  ccall((:arb_pow_fmpz, :libarb), Void,
              (Ptr{arb}, Ptr{arb}, Ptr{fmpz}, Clong),
              &z, &x, &y, parent(x).prec)
  return z
end

^(x::arb, y::Int) = ^(x, fmpz(y))

function ^(x::arb, y::Culong)
  z = parent(x)()
  ccall((:arb_pow_ui, :libarb), Void,
              (Ptr{arb}, Ptr{arb}, Culong, Clong), &z, &x, y, parent(x).prec)
  return z
end

function inv(x::arb)
  z = parent(x)()
  ccall((:arb_inv, :libarb), Void,
              (Ptr{arb}, Ptr{arb}, Clong), &z, &x, parent(x).prec)
  return parent(x)(z)
end

################################################################################
#
#  Unsafe binary operations
#
################################################################################

for (s,f) in (("add!","arb_add"), ("mul!","arb_mul"), ("div!", "arb_div"),
              ("sub!","arb_sub"))
  @eval begin
    function ($(Symbol(s)))(z::arb, x::arb, y::arb)
      ccall(($f, :libarb), Void, (Ptr{arb}, Ptr{arb}, Ptr{arb}, Clong),
                           &z, &x, &y, parent(x).prec)
    end
  end
end

################################################################################
#
#  Real valued functions
#
################################################################################

function log(x::arb)
  z = parent(x)()
  ccall((:arb_log, :libarb), Void,
              (Ptr{arb}, Ptr{arb}, Clong), &z, &x, parent(x).prec)
  return z
end

function exp(x::arb)
  z = parent(x)()
  ccall((:arb_exp, :libarb), Void,
              (Ptr{arb}, Ptr{arb}, Clong), &z, &x, parent(x).prec)
  return z
end

function sqrt(x::arb)
  z = parent(x)()
  ccall((:arb_sqrt, :libarb), Void,
              (Ptr{arb}, Ptr{arb}, Clong), &z, &x, parent(x).prec)
  return z
end

function sin(x::arb)
  z = parent(x)()
  ccall((:arb_sin, :libarb), Void,
              (Ptr{arb}, Ptr{arb}, Clong), &z, &x, parent(x).prec)
  return z
end

function cos(x::arb)
  z = parent(x)()
  ccall((:arb_cos, :libarb), Void,
              (Ptr{arb}, Ptr{arb}, Clong), &z, &x, parent(x).prec)
  return z
end

function tan(x::arb)
  z = parent(x)()
  ccall((:arban, :libarb), Void,
              (Ptr{arb}, Ptr{arb}, Clong), &z, &x, parent(x).prec)
  return z
end

################################################################################
#
#  Constants
#
################################################################################

function pi_arb(p::Clong)
  z = ArbField(p)()
  ccall((:arb_const_pi, :libarb), Void, (Ptr{arb}, Clong), &z, p)
  return z
end

function e_arb(p::Clong)
  z = ArbField(p)()
  ccall((:arb_const_e, :libarb), Void, (Ptr{arb}, Clong), &z, p)
  return z
end

