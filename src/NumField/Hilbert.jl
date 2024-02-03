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

function quadratic_defect(a::Union{Rational{<:Integer},IntegerUnion,QQFieldElem}, p::IntegerUnion)
  return quadratic_defect(QQFieldElem(a), ZZRingElem(p))
end

@doc doc"""
    quadratic_defect(a::Union{NumFieldElem,Rational,QQFieldElem}, p) -> Union{Inf, PosInf}

Returns the valuation of the quadratic defect of the element $a$ at $p$, which
can either be prime object or an infinite place of the parent of $a$.
"""
quadratic_defect(a, p)

function quadratic_defect(a::QQFieldElem, p::ZZRingElem)
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

function _quadratic_defect_unit(a::NumFieldElem, p::Union{AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal})
  @assert valuation(a, p) == 0 && is_dyadic(p)
  o = order(p)
  f = nf(o)
  parent(a) != f && error("incompatible arguments")
  k, h = residue_field(o, p)
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
    kx, x = polynomial_ring(k, cached = false)
    d = x^2 + x + hex((a-1)//4)
    if !is_irreducible(d)
      return inf, one(f)
    end
  end
  return w, a
end

function quadratic_defect(a::NumFieldElem, p::Union{AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal})
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
    k, h = residue_field( o, p )
    hex = extend(h, f)
    ok, s = is_square_with_sqrt(hex(a))
    return ok ? inf : v
  end

  w, aa = _quadratic_defect_unit(a, p)
  return w + v
end

@doc doc"""
    quadratic_defect(a::AbsSimpleNumFieldOrderElem, p) -> Union{Inf, PosInf}

Returns the valuation of the quadratic defect of the element $a$ at $p$, which
can either be prime object or an infinite place of the parent of $a$.
"""
function quadratic_defect(a::NumFieldOrderElem, p::Union{AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal})
  return quadratic_defect(elem_in_nf(a), p)
end

function quadratic_defect(a::IntegerUnion, p::Union{AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal})
  return quadratic_defect(nf(order(p))(a), p)
end

################################################################################
#
#  Hilbert symbol
#
################################################################################

function hilbert_symbol(a::NumFieldElem, b::IntegerUnion, p::Union{AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal})
  return hilbert_symbol(a, parent(a)(b), p)
end

function hilbert_symbol(a::IntegerUnion, b::NumFieldElem, p::Union{AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal})
  return hilbert_symbol(b, a, p)
end

# This is an implementation of local Hilbert symbol computations by M. Kirschmer
# using quadratic defects.
#
# References:
# [O'M71] O. T. O'Meara, "Introduction to quadratic forms", volume 117 of
#             Grundlehren der Mathematischen Weissenschaften, 1971.
#
# [Voi12] J. Voight, "IDENTIFYING THE MATRIX RING: ALGORITHMS FOR QUATERNION
#             ALGEBRAS AND QUADRATIC FORMS", In Quadratic and higher degree
#             forms, volume 31 of Dev. Math., pages 255-298, 2012.
@doc raw"""
    hilbert_symbol(a::NumFieldElem, b::NumFieldElem, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> Int

Returns the local Hilbert symbol $(a,b)_p$.
"""
function hilbert_symbol(a::T, b::T, p::Union{AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal}) where {T <: NumFieldElem}
  @req !iszero(a) && !iszero(b) "Arguments must be non-zero"
  o = order(p)
  f = nf(o)
  @req f === parent(a) "Incompatible parents"
  pi = f(uniformizer(p))

  v = valuation(a,p)
  w = valuation(b,p)

  # We want to put ourselves in the case where a is a local unit and b
  # has p-valuation 0 or 1.
  #
  # If a has even p-valuation and b has odd p-valuation, we exchange
  # a and b. If both have odd p-valuations, then we replace a by -ab
  # since
  #
  # (-ab, b)_p = (a,b)_p * (-1,b)_p = (a,b)_p
  #
  # and in that case the new a has even p-valuation
  if isodd(v)
    if iseven(w)
      a,b,v,w = b,a,w,v
    else
      a = -a*b
      v = v+w
    end
  end

  # Now v is even, so we can turn a into a local unit
  a = a // pi^v

  # If p is not dyadic, according to [Voi12, Corollary 5.6], the local
  # Hilbert symbol is equal to the local Legendre symbol of a at p, to the
  # power w.
  #
  # The local Legendre symbol measures whether a is a local square modulo p:
  # if the local quadratic defect of a has p-valuation greater or equal
  # than 1, then the local Legendre symbol is necessarily 1, and so is (a, b)_p.
  #
  # So eventually, the (a, b)_p = -1 if and only if the p-valuation of
  # the local quadratic defect of a is 0 AND w is odd.
  if !is_dyadic(p)
    return isodd(w) && iszero(quadratic_defect(a, p)) ? -1 : 1
  end

  # Now, if the local quadratic defect of a is even or infinite we can
  # already conclude:
  # - if it is infinite, then a is a local square and the local Hilbert
  #   symbol is 1 (because (c^2, b)_p = 1 for all b, c in o_p);
  # - if it is even, then by [OM71, 63:4] a is in the square class of a local
  #   unit whose defect is 4*o_p. In that case, [OM71, 63:11a] tells us that
  #   (a, b)_p = 1 if b has even p-valuation (i.e is in the square
  #   class of a local unit) and -1 otherwise (when b is in the square class
  #   of a uniformizer at p).
  #
  # If the p-valuation is odd, then we replace iteratively a by an element
  # which admit the same local Hilbert symbol with b, but at each iteration we
  # make the p-valuation of the local defect grow: hence, either it becomes
  # even at some point or diverges to infinity. We then use one of the previous
  # termination conditions to conclude.

  # We have that a is a local unit and p is dyadic. There are 3 possibilities:
  # - v is odd and smaller than the p-valuation of 4;
  # - v is the p-valuation of 4;
  # - v is infinity.
  #
  # In all cases, the new a is such that a-1 has p-valuation v and it is
  # in the same square class as the old a, so (a, b)_p is unchanged
  v, a = _quadratic_defect_unit(a, p)

  # We reduce the p-valuation of b to 0 or 1, depending on the parity
  # of w
  b = b // pi^(2*fld(w, 2)) # fld(x, y) = div(x, y, RoundDown), i.e., round towards -oo
  w = mod(w, 2)

  # If w = 1, then b is a local uniformizer at p. Otherwise, we use that
  # v is odd to turn b into a local uniformizer. This works because
  # pi^(v-1) is a square and
  #
  # (a, (1-a)*b)_p = (a, 1-a)_p * (a,b)_p = (a,b)_p
  #
  # by the properties of the Hilbert symbol.
  if isfinite(v) && isodd(v)
    if w == 0
      b = (1-a)*b // pi^(v-1)
      w = 1
      @assert valuation(b, p) == 1
    end
    k, h = residue_field(o, p)
    h = extend(h, f)
  end

  # From now on, we lift v until it becomes infinite or even. How it works:
  #
  # Since a-1 lives locally in p^v = b*p^(v-1), one can find a local unit
  # c such that a = 1 + c*b*pi^(v-1). Now, the residue field k is perfect, so
  # c = (a-1)/(b*pi^(v-1)) is a square s^2 modulo p, where s is a unit in o_p.
  # The important point here is the following. Since v-1 is even, s^2*pi^(v-1)
  # is a local square and
  #
  # (a*(1-s^2*b*pi^(v-1)), b)_p = (a, b)_p * (1-s^2*b*pi^(v-1), s^2*b*pi^(v-1))_p
  #                             = (a, b)_p
  #
  # and moreover
  #
  # a - a*s^2*b*pi^(v-1) = 1 + (c-s^2)*b*pi^(v-1) = 1 modulo p^(v+1)
  #
  # because b is a local uniformizer and c = s^2 modulo p.
  #
  # Hence, by changing a -> a * (1-s^2*b*pi^(v-1)), we have that
  # a-1 has p-valuation at least v+1 and (a, b)_p remains unchanged.
  #
  # We then proceed iteratively by computing the local quadratic defect of
  # the new a, and by replacing a by an element in its square which is one
  # modulo the defect.
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

@doc raw"""
    hilbert_symbol(a::AbsSimpleNumFieldElem, b::AbsSimpleNumFieldElem, p::InfPlc) -> Int

Returns the local Hilbert symbol $(a,b)_p$.
"""
function hilbert_symbol(a::T, b::T, p::Plc) where {T <: NumFieldElem}
  return (is_complex(p) || is_positive(a, p) || is_positive(b, p)) ? 1 : -1
end

function hilbert_symbol(a::IntegerUnion, b::IntegerUnion, p::IntegerUnion)
  return hilbert_symbol(ZZRingElem(a), ZZRingElem(b), ZZRingElem(p))
end

function hilbert_symbol(a::IntegerUnion, b::IntegerUnion, p::PosInf)
  return hilbert_symbol(a, b, 0)
end

@doc raw"""
    hilbert_symbol(a::ZZRingElem, b::ZZRingElem, p::ZZRingElem) -> Int

Returns the local Hilbert symbol $(a,b)_p$.
"""
function hilbert_symbol(a::ZZRingElem, b::ZZRingElem, p::ZZRingElem)
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

function hilbert_symbol(a::Union{QQFieldElem,ZZRingElem,Integer,Rational{<:Integer}},
                        b::Union{QQFieldElem,ZZRingElem,Integer,Rational{<:Integer}},
                        p::IntegerUnion)
  return hilbert_symbol(QQFieldElem(a), QQFieldElem(b), ZZRingElem(p))
end

@doc raw"""
    hilbert_symbol(a::Union{QQFieldElem,ZZRingElem,Int,Rational{Int}}, b::Union{QQFieldElem,ZZRingElem,Int,Rational{Int}}, p::Union{ZZRingElem,Int}) -> {-1, +1}

Returns the local Hilbert symbol $(a,b)_p$.
"""
function hilbert_symbol(a::QQFieldElem, b::QQFieldElem, p::ZZRingElem)
  a = FlintQQ(a)
  b = FlintQQ(b)
  hilbert_symbol(numerator(a) * denominator(a), numerator(b) * denominator(b), p)
end
