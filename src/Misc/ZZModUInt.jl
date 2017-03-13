################################################################################
#
#               ZZModUInt.jl : Z/nZ modelled with UInts
#
# This file is part of Hecke.
#
# Copyright (c) 2015, 2016: Claus Fieker, Tommy Hofmann
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
#  Copyright (C) 2015, 2016 Tommy Hofmann, Claus Fieker
#
################################################################################

export ZZModUInt, UIntMod

################################################################################
#
#  Basics
#
################################################################################

elem_type(::ZZModUInt) = UIntMod

parent_type(::Type{UIntMod}) = ZZModUInt

zero(R::ZZModUInt) = R(0)

Base.promote_rule(::Type{UIntMod}, ::Type{Int}) = UIntMod

parent(x::UIntMod) = x.parent

@inline function iszero(x::UIntMod)
  return x.m == 0
end

@inline function isone(x::UIntMod)
  return x.m == 1
end
################################################################################
#
#  String I/O
#
################################################################################

Base.show(io::IO, x::UIntMod) = Base.show(io, x.m)

function Base.show(io::IO, R::ZZModUInt)
  print(io, "Residue ring of ZZ of size $(R.mod.n) (UInt)\n")
end

################################################################################
#
#  Binary operations
#
################################################################################

for (fn, fc) in ((:+, "nmod_add"), (:*, "nmod_mul"), (:-, "nmod_sub"),
      (://, "nmod_div"))
  @eval begin
    function ($fn)(x::UIntMod, y::UIntMod)
      z = UIntMod(parent(x), (ccall(($fc, :libflint), UInt,
              (UInt, UInt, nmod_struct),
              x.m, y.m, x.parent.mod)))
      return z
    end
  end
end

divexact(x::UIntMod, y::UIntMod) = //(x, y)

################################################################################
#
#  Unary operations
#
################################################################################

function -(x::UIntMod)
  z = UIntMod(parent(x), ccall((:nmod_neg, :libflint), UInt,
              (UInt, nmod_struct), x.m, x.parent.mod))
  return z
end

################################################################################
#
#  Comparison
#
################################################################################

function ==(x::UIntMod, y::UIntMod)
  x.parent == y.parent && x.m == y.m
end

################################################################################
#
#  Parent object overloading
#
################################################################################

function (R::ZZModUInt)()
  return ZZModUInt(R)
end

function (R::ZZModUInt)(n::UInt)
  return UIntMod(R, mod(n, R.mod.n))
end

function (R::ZZModUInt)(n::fmpz)
  u = ccall((:fmpz_fdiv_ui, :libflint), UInt, (Ptr{fmpz}, UInt), &n, R.mod.n)
  return UIntMod(R, u)
end

(R::ZZModUInt)(n::Int) = R(UInt(mod(n, R.mod.n)))

function (R::ZZModUInt)(x::GenRes{fmpz})
  R.mod.n != parent(x).modulus && error("moduli must be equal")
  return R(UInt(x.data))
end

