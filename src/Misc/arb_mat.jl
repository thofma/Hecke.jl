################################################################################
#
#                 arb_mat.jl: wrapper for arb_mat  
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

export arb_mat, ArbMatSpace

const ArbMatSpaceID = ObjectIdDict()

################################################################################
#
#  Types and memory management
#
################################################################################

type ArbMatSpace
  r::Int
  c::Int
  prec::Int

  function ArbMatSpace(r::Int, c::Int, prec::Int)
    if haskey(ArbMatSpaceID, (r, c, prec))
      return ArbMatSpaceID[(r, c, prec)]::ArbMatSpace
    else
      z = new(r, c, prec)
      ArbMatSpaceID[(r, c, prec)] = z
      return z
    end
  end
end

type arb_mat <: RingElem
  entries::Ptr{Void}
  r::Int
  c::Int
  rows::Ptr{Void}
  parent::ArbMatSpace

  function arb_mat()
    z = new()
    ccall((:arb_mat_init, :libarb), Void, (Ptr{arb_mat}, Int, Int), &z, r, c)
    finalizer(z, _arb_mat_clear_fn)
    return z
  end

  function arb_mat(r::Int, c::Int)
    z = new()
    ccall((:arb_mat_init, :libarb), Void, (Ptr{arb_mat}, Int, Int), &z, r, c)
    finalizer(z, _arb_mat_clear_fn)
    return z
  end

  function arb_mat(r::Int, c::Int, prec::Int)
    z = new()
    ccall((:arb_mat_init, :libarb), Void, (Ptr{arb_mat}, Int, Int), &z, r, c)
    z.parent = ArbMatSpace(r, c, prec)
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
end

function _arb_mat_clear_fn(x::arb_mat)
  ccall((:arb_mat_clear, :libarb), Void, (Ptr{arb_mat}, ), &x)
end

function getindex(x::arb_mat, r::Int, c::Int)
  v = ArbField(parent(x).prec)()
  z = ccall((:arb_mat_entry, :libarb), Ptr{arb},
              (Ptr{arb_mat}, Int, Int), &x, r - 1, c - 1)
  ccall((:arb_set, :libarb), Void, (Ptr{arb}, Ptr{arb}), &v, z)
  return v
end

function setindex!(x::arb_mat, y::arb, r::Int, c::Int)
  z = ccall((:arb_mat_entry, :libarb), Ptr{arb},
              (Ptr{arb_mat}, Int, Int), &x, r - 1, c - 1)
  ccall((:arb_set, :libarb), Void, (Ptr{arb}, Ptr{arb}), z, &y)
end

parent(x::arb_mat) = x.parent

cols(x::arb_mat) = x.c

rows(x::arb_mat) = x.r

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::ArbMatSpace)
  print(io, "Space of $(a.r) x $(a.c) matrices over ArbField ")
  print(io, "with precision $(a.prec)")
end
  
function show(io::IO, a::arb_mat)
   rows = a.r
   cols = a.c
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
#  Parent object overloading
#
################################################################################

function call(x::ArbMatSpace)
  return arb_mat(x.r, x.c, x.prec)
end

function call(x::ArbMatSpace, y::fmpz_mat)
  z = arb_mat(y, x.prec)
  z.parent = x
  return z
end

################################################################################
#
#  Transpose
#
################################################################################

function transpose(x::arb_mat)
  z = ArbMatSpace(parent(x).c, parent(x).r, parent(x).prec)()
  ccall((:arb_mat_transpose, :libarb), Void,
              (Ptr{arb_mat}, Ptr{arb_mat}), &z, &x)
  return z
end

################################################################################
#
#  Inverse
#
################################################################################

function inv(x::arb_mat)
  z = parent(x)()
  i = ccall((:arb_mat_inv, :libarb), Cint,
              (Ptr{arb_mat}, Ptr{arb_mat}, Clong), &z, &x, parent(x).prec)
  i == 0 && error("Could not find invertible pivot element")
  return z
end

################################################################################
#
#  Binary operations
#
################################################################################

function *(x::arb_mat, y::arb_mat)
  x.c != y.r && error("Incompatible dimensions")
  z = ArbMatSpace(x.r, y.c, parent(x).prec)()
  ccall((:arb_mat_mul, :libarb), Void,
              (Ptr{arb_mat}, Ptr{arb_mat}, Ptr{arb_mat}, Clong),
              &z, &x, &y, parent(x).prec)
  return z
end

################################################################################
#
#  Determinant
#
################################################################################

function det(x::arb_mat)
  z = ArbField(parent(x).prec)()
  ccall((:arb_mat_det, :libarb), Void,
              (Ptr{arb}, Ptr{arb_mat}, Clong), &z, &x, parent(x).prec)
  return z
end

