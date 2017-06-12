################################################################################
#
#  NfRel/NfRel.jl : Relative number field extensions
#
# This file is part of Hecke.
#
# Copyright (c) 2015, 2016, 2017: Claus Fieker, Tommy Hofmann
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
#  Copyright (C) 2017 Claus Fieker, Tommy Hofmann
#
################################################################################

export absolute_field

# In case the code has stabilized, the type definition should go into
# src/HeckeTypes.jl 

################################################################################
#
#  Types
#
################################################################################

type NfRel{T} <: Nemo.Field
  base_ring::Nemo.Field
  pol::GenPoly{T}
  S::Symbol

  function NfRel(f::GenPoly{T}, s::Symbol, cached::Bool = true)
    if haskey(NfRelID, (parent(f), f, s))
      return NfRelID[parent(f), f, s]
    else
      z = new()
      z.base_ring = base_ring(parent(f))
      z.pol = f
      z.S = s
      if cached
        NfRelID[parent(f), f, s] = z
      end
      return z
    end
  end
end

const NfRelID = Dict{Tuple{GenPolyRing, GenPoly, Symbol},
                     NfRel}()

type NfRelElem{T} <: Nemo.FieldElem
  data::GenPoly{T}
  parent::NfRel{T}

  NfRelElem(g::GenPoly{T}) = new{T}(g)
end

################################################################################
#
#  Copy
#
################################################################################

function Base.deepcopy_internal{T}(a::NfRelElem{T}, dict::ObjectIdDict)
  z = NfRelElem{T}(Base.deepcopy_internal(data(a), dict))
  z.parent = parent(a)
  return z
end

################################################################################
#
#  Comply with Nemo ring interface
#
################################################################################

Nemo.elem_type{T}(::Type{NfRel{T}}) = NfRelElem{T}

Nemo.elem_type{T}(::NfRel{T}) = NfRelElem{T}

Nemo.parent_type{T}(::Type{NfRelElem{T}}) = NfRel{T}

Nemo.needs_parentheses(::NfRelElem) = true

Nemo.isnegative(x::NfRelElem) = Nemo.isnegative(data(x))

Nemo.show_minus_one{T}(::Type{NfRelElem{T}}) = true

function Nemo.iszero(a::NfRelElem)
  reduce!(a)
  return iszero(data(a))
end

function Nemo.isone(a::NfRelElem)
  reduce!(a)
  return isone(data(a))
end

Nemo.zero(K::NfRel) = K(Nemo.zero(parent(K.pol)))

Nemo.one(K::NfRel) = K(Nemo.one(parent(K.pol)))

################################################################################
#
#  Promotion
#
################################################################################

Nemo.promote_rule{T <: Integer, S}(::Type{NfRelElem{S}}, ::Type{T}) = NfRelElem{S}

Nemo.promote_rule{T}(::Type{NfRelElem{T}}, ::Type{fmpz}) = NfRelElem{T}

Nemo.promote_rule{T}(::Type{NfRelElem{T}}, ::Type{fmpq}) = NfRelElem{T}

Nemo.promote_rule{T}(::Type{NfRelElem{T}}, ::Type{T}) = NfRelElem{T}

################################################################################
#
#  Field access
#
################################################################################

@inline Nemo.base_ring{T}(a::NfRel{T}) = a.base_ring::parent_type(T)

@inline Nemo.data(a::NfRelElem) = a.data

@inline Nemo.parent{T}(a::NfRelElem{T}) = a.parent::NfRel{T}

################################################################################
#
#  Reduction
#
################################################################################

function reduce!(a::NfRelElem)
  a.data = mod(a.data, parent(a).pol)
  return a
end
 
################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, a::NfRel)
  print(io, "Relative number field over\n")
  print(io, a.base_ring, "\n")
  print(io, " with defining polynomial ", a.pol)
end

function _show(io::IO, x::PolyElem, S::String)
   len = length(x)
   if len == 0
      print(io, base_ring(x)(0))
   else
      for i = 1:len - 1
         c = coeff(x, len - i)
         bracket = needs_parentheses(c)
         if !iszero(c)
            if i != 1 && !isnegative(c)
               print(io, "+")
            end
            if !isone(c) && (c != -1 || show_minus_one(typeof(c)))
               if bracket
                  print(io, "(")
               end
               show(io, c)
               if bracket
                  print(io, ")")
               end
               print(io, "*")
            end
            if c == -1 && !show_minus_one(typeof(c))
               print(io, "-")
            end
            print(io, string(S))
            if len - i != 1
               print(io, "^")
               print(io, len - i)
            end
         end
      end
      c = coeff(x, 0)
      bracket = needs_parentheses(c)
      if !iszero(c)
         if len != 1 && !isnegative(c)
            print(io, "+")
         end
         if bracket
            print(io, "(")
         end
         show(io, c)
         if bracket
            print(io, ")")
         end
      end
   end
end

function Base.show(io::IO, a::NfRelElem)
  f = data(a)
  _show(io, f, string(parent(a).S))
end

################################################################################
#
#  Constructors and parent object overloading
#
################################################################################

function number_field{T}(f::GenPoly{T}, s::String)
  S = Symbol(s)
  K = NfRel{T}(f, S)
  return K, K(gen(parent(f)))
end

function number_field{T}(f::GenPoly{T})
  return number_field(f, "_\$")
end
 
function (K::NfRel{T}){T}(a::GenPoly{T})
  z = NfRelElem{T}(mod(a, K.pol))
  z.parent = K
  return z
end

function (K::NfRel{T}){T}(a::T)
  parent(a) != base_ring(parent(K.pol)) == error("Cannot coerce")
  z = NfRelElem{T}(parent(K.pol)(a))
  z.parent = K
  return z
end

(K::NfRel)(a::Integer) = K(parent(K.pol)(a))

(K::NfRel){T <: Integer}(a::Rational{T}) = K(parent(K.pol)(a))

(K::NfRel)(a::fmpz) = K(parent(K.pol)(a))

(K::NfRel)(a::fmpq) = K(parent(K.pol)(a))

(K::NfRel)() = zero(K)

Nemo.gen(K::NfRel) = K(Nemo.gen(parent(K.pol)))

################################################################################
#
#  Unary operators
#
################################################################################

function Base.:(-)(a::NfRelElem)
  return parent(a)(-data(a))
end

################################################################################
#
#  Binary operators
#
################################################################################

function Base.:(+)(a::NfRelElem, b::NfRelElem)
  return parent(a)(data(a) + data(b))
end

function Base.:(-)(a::NfRelElem, b::NfRelElem)
  return parent(a)(data(a) - data(b))
end

function Base.:(*)(a::NfRelElem, b::NfRelElem)
  return parent(a)(data(a) * data(b))
end

function Nemo.divexact(a::NfRelElem, b::NfRelElem)
  b == 0 && error("Element not invertible")
  return a*inv(b)
end

Base.:(//)(a::NfRelElem, b::NfRelElem) = divexact(a, b)

################################################################################
#
#  Inversion
#
################################################################################

function Base.inv(a::NfRelElem)
  a == 0 && error("Element not invertible")
  g, s, _ = gcdx(data(a), parent(a).pol)
  @assert g == 1
  return parent(a)(s)
end

################################################################################
#
#  Powering
#
################################################################################

function Base.:(^)(a::NfRelElem, n::Int)
  K = parent(a)
  if iszero(a)
    return zero(K)
  end

  if n == 0
    return one(K)
  end

  if n < 0 && iszero(a)
    error("Element is not invertible")
  end

  return K(powmod(data(a), n, K.pol))
end

################################################################################
#
#  Comparison
#
################################################################################

function Base.:(==){T}(a::NfRelElem{T}, b::NfRelElem{T})
  reduce!(a)
  reduce!(b)
  return data(a) == data(b)
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function Nemo.mul!(c::NfRelElem, a::NfRelElem, b::NfRelElem)
  mul!(c.data, a.data, b.data)
  c = reduce!(c)
  return c
end

function Nemo.addeq!(b::NfRelElem, a::NfRelElem)
  addeq!(b.data, a.data)
  b = reduce!(b)
  return b
end

################################################################################
#
#  Isomorphism to absolute field (AnticNumberField)
#
################################################################################

function absolute_field(K::NfRel{nf_elem})
  Ka, a, b, c = _absolute_field(K)

  return Ka, NfRelToNf(K, Ka, a, b, c)
end

function _absolute_field(K::NfRel{nf_elem})
  f = K.pol
  kx = parent(f)
  k = base_ring(kx)
  Qx = parent(k.pol)

  l = 0
  g = f
  N = 0

  while true
    N = norm(g)
    @assert degree(N) == degree(g) * degree(k)

    if !isconstant(N) && issquarefree(N)
      break
    end

    l += 1
 
    g = compose(f, gen(kx) - l*gen(k))
  end

  Ka = NumberField(N)[1]
  KaT, T = PolynomialRing(Ka, "T")

  # map Ka -> K: gen(Ka) -> gen(K)+ k gen(k)

  # gen(k) -> Root(gcd(g, poly(k)))  #gcd should be linear:
  # g in kx = (Q[a])[x]. Want to map x -> gen(Ka), a -> T
  gg = zero(KaT)
  for i=degree(g):-1:0
    gg = gg*gen(Ka) + evaluate(Qx(coeff(g, i)), gen(KaT))
  end

  q = gcd(gg, evaluate(k.pol, gen(KaT)))
  @assert degree(q) == 1
  al = -trailing_coefficient(q)//lead(q)
  be = gen(Ka) - l*al
  ga = gen(K) + l*gen(k)

  #al -> gen(k) in Ka
  #be -> gen(K) in Ka
  #ga -> gen(Ka) in K
  return Ka, al, be, ga
end 

