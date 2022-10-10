################################################################################
#
#    NfAbs/Hilbert.jl: Hilbert symbols
#
# This file is part of Hecke.
#
# Copyright (c) 2015-2019: Claus Fieker, Tommy Hofmann
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
#  Copyright (C) 2019 Markus Kirschmer
#
################################################################################

export quadratic_defect, hilbert_symbol

function quadratic_defect(a::Union{Rational{<:Integer},IntegerUnion,fmpq}, p::IntegerUnion)
  return quadratic_defect(fmpq(a), fmpz(p))
end

@doc doc"""
    quadratic_defect(a::Union{NumFieldElem,Rational,fmpq}, p) -> Union{Inf, PosInf}

Returns the valuation of the quadratic defect of the element $a$ at $p$, which
can either be prime object or an infinite place of the parent of $a$.
"""
function quadratic_defect(a, p) end

function quadratic_defect(a::fmpq, p::fmpz)
  if iszero(a)
    return inf
  end

  v = valuation(a, p)

  if isodd(v)
    return v
  end

  a = a//QQ(p)^v

  if isodd(p)
    return jacobi_symbol(mod(a, p), p) == 1 ? inf : v
  end

  a = mod(a, 8)

  if a == 1
    return inf
  elseif a == 5
    return v + 2
  end

  return v + 1
end


function _quadratic_defect_unit(a::NumFieldElem, p::Union{NfAbsOrdIdl, NfRelOrdIdl})
  @assert valuation(a, p) == 0 && is_dyadic(p)
  o = order(p)
  f = nf(o)
  parent(a) != f && error("incompatible arguments")
  k, h = ResidueField(o, p)
  hex = extend(h, f)
  ok, s = is_square_with_sqrt(hex(a))

  a = a * (hex\(s))^-2;
  w = isone(a) ? inf : valuation(a-1, p)
  ee = 2*valuation(o(2), p);
  pi = f(uniformizer(p))

  while w < ee && iseven(w)
    ok, s = is_square_with_sqrt(hex((a-1) * pi^-w))
    a =  a * (1+(hex\(s))*pi^(div(w,2)))^-2;
    w = isone(a) ? inf : valuation(a-1, p)
  end

  if w > ee return inf, one(f)
  elseif w == ee
    kx, x = PolynomialRing(k, cached = false)
    d = x^2 + x + hex((a-1)//4)
    if !is_irreducible(d)
      return inf, one(f)
    end
  end
  return w, a
end

function quadratic_defect(a::NumFieldElem, p::Union{NfAbsOrdIdl, NfRelOrdIdl})
  if iszero(a)
    return inf
  end

  v = valuation(a, p)

  if isodd(v)
    return v
  end

  o = order(p)
  f = nf(o)
  pi = f(uniformizer(p))
  a = a//pi^v

  if !is_dyadic(p)
    k, h = ResidueField( o, p )
    hex = extend(h, f)
    ok, s = is_square_with_sqrt(hex(a))
    return ok ? inf : v
  end

  w, aa = _quadratic_defect_unit(a, p)
  return w + v
end

@doc doc"""
    quadratic_defect(a::NfOrdElem, p) -> Union{Inf, PosInf}

Returns the valuation of the quadratic defect of the element $a$ at $p$, which
can either be prime object or an infinite place of the parent of $a$.
"""
function quadratic_defect(a::Union{NfRelOrdElem, NfAbsOrdElem}, p::Union{NfAbsOrdIdl, NfRelOrdIdl})
  return quadratic_defect(elem_in_nf(a), p)
end

################################################################################
#
#  Hilbert symbol
#
################################################################################

function hilbert_symbol(a::NumFieldElem, b::IntegerUnion, p::Union{NfAbsOrdIdl, NfRelOrdIdl})
  return hilbert_symbol(a, parent(a)(b), p)
end

function hilbert_symbol(a::IntegerUnion, b::NumFieldElem, p::Union{NfAbsOrdIdl, NfRelOrdIdl})
  return hilbert_symbol(b, a, p)
end

@doc Markdown.doc"""
    hilbert_symbol(a::NumFieldElem, b::NumFieldElem, p::NfOrdIdl) -> Int

Returns the local Hilbert symbol $(a,b)_p$.
"""
function hilbert_symbol(a::T, b::T, p::Union{NfAbsOrdIdl, NfRelOrdIdl}) where {T <: NumFieldElem}
  (iszero(a) || iszero(b)) && error("arguments must be non-zero")
  o = order(p)
  f = nf(o)
  f !== parent(a) && error("Incompatible parents")
  pi = f(uniformizer(p))
  v = valuation(a,p)
  w = valuation(b,p)

  if isodd(v)
    if iseven(w)
      a,b,v,w = b,a,w,v
    else
      a = -a*b
      v = v+w
    end
  end

  # now v is even, make a a local unit
  a = a // pi^v

  if !is_dyadic(p)
    return isodd(w) && iszero(quadratic_defect(a, p)) ? -1 : 1
  end

  v, a = _quadratic_defect_unit(a, p)

  b = b // pi^(2*fld(w, 2)) # fld(x, y) = div(x, y, RoundDown), i.e., round towards -oo
  w = mod(w, 2)
  # turn b into a uniformizer
  if isfinite(v) && isodd(v)
    if w == 0
      b = (1-a)*b // pi^(v-1)
      w = 1
      @assert valuation(b, p) == 1
    end
    k, h = ResidueField(o, p)
    h = extend(h, f)
  end

  # lift v until it becomes infinite or even
  while isfinite(v) && isodd(v)
    t = pi^(v-1)*b
    ok, s = is_square_with_sqrt( h( (a-1) // t) )
    a = a * (1 - (h\(s))^2 * t)
    v, a = _quadratic_defect_unit(a, p)
  end

  return isfinite(v) && isodd(w) ? -1 : 1
end

function hilbert_symbol(a::NumFieldElem, b::IntegerUnion, p::Plc)
  return hilbert_symbol(a, parent(a)(b), p)
end

function hilbert_symbol(a::IntegerUnion, b::NumFieldElem, p::Plc)
  return hilbert_symbol(b, a, p)
end

@doc Markdown.doc"""
    hilbert_symbol(a::nf_elem, b::nf_elem, p::InfPlc) -> Int

Returns the local Hilbert symbol $(a,b)_p$.
"""
function hilbert_symbol(a::T, b::T, p::Plc) where {T <: NumFieldElem}
  return is_complex(p) || is_positive(a, p) || is_positive(b, p) ? 1 : -1
end

function hilbert_symbol(a::IntegerUnion, b::IntegerUnion, p::IntegerUnion)
  return hilbert_symbol(fmpz(a), fmpz(b), fmpz(p))
end

function hilbert_symbol(a::IntegerUnion, b::IntegerUnion, p::PosInf)
  return hilbert_symbol(a, b, 0)
end

@doc Markdown.doc"""
    hilbert_symbol(a::fmpz, b::fmpz, p::fmpz) -> Int

Returns the local Hilbert symbol $(a,b)_p$.
"""
function hilbert_symbol(a::fmpz, b::fmpz, p::fmpz)
  if p <= 0
    return (a < 0 && b < 0) ? -1 : 1
  end
  v = valuation(a,p)
  w = valuation(b,p)

  if isodd(v)
    if iseven(w)
      a,b,v,w = b,a,w,v
    else
      a,v = -a*b,v+w
    end
  end

  a = divexact(a, p^v)

  if isodd(p)
    return (isodd(w) && jacobi_symbol( mod(a, p), p) == -1) ? -1 : 1
  end

  a = mod(a, 8)
  if a == 1
    return 1
  elseif a == 5
    return isodd(w) ? -1 : 1
  end

  if isodd(w)
    b = divexact(b*(1-a), p^(w+1))
  else
    b = divexact(b, p^w)
  end
  @assert valuation(b, p) == 0
  b = mod(b, 8)

  return (b == 3) || (b == 7) ? -1 : 1
end

function hilbert_symbol(a::Union{fmpq,fmpz,Integer,Rational{<:Integer}},
                        b::Union{fmpq,fmpz,Integer,Rational{<:Integer}},
                        p::IntegerUnion)
  return hilbert_symbol(fmpq(a), fmpq(b), fmpz(p))
end

@doc Markdown.doc"""
    hilbert_symbol(a::Union{fmpq,fmpz,Int,Rational{Int}}, b::Union{fmpq,fmpz,Int,Rational{Int}}, p::Union{fmpz,Int}) -> {-1, +1}

Returns the local Hilbert symbol $(a,b)_p$.
"""
function hilbert_symbol(a::fmpq, b::fmpq, p::fmpz)
  a = FlintQQ(a)
  b = FlintQQ(b)
  hilbert_symbol(numerator(a) * denominator(a), numerator(b) * denominator(b), p)
end
