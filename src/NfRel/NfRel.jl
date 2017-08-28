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
#  Copy
#
################################################################################

function Base.deepcopy_internal(a::NfRelElem{T}, dict::ObjectIdDict) where T
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

Nemo.promote_rule(::Type{NfRelElem{T}}, ::Type{fmpz}) where {T} = NfRelElem{T}

Nemo.promote_rule(::Type{NfRelElem{T}}, ::Type{fmpq}) where {T} = NfRelElem{T}

Nemo.promote_rule(::Type{NfRelElem{T}}, ::Type{T}) where {T} = NfRelElem{T}

function Nemo.promote_rule1(::Type{NfRelElem{T}}, ::Type{NfRelElem{U}}) where {T, U}
   Nemo.promote_rule(T, NfRelElem{U}) == T ? NfRelElem{T} : Union{}
end

function Nemo.promote_rule(::Type{NfRelElem{T}}, ::Type{U}) where {T, U} 
   Nemo.promote_rule(T, U) == T ? NfRelElem{T} : Nemo.promote_rule1(U, NfRelElem{T})
end

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

function number_field(f::GenPoly{T}, s::String) where T
  S = Symbol(s)
  K = NfRel{T}(f, S)
  return K, K(gen(parent(f)))
end

function number_field(f::GenPoly{T}) where T
  return number_field(f, "_\$")
end
 
function (K::NfRel{T})(a::GenPoly{T}) where T
  z = NfRelElem{T}(mod(a, K.pol))
  z.parent = K
  return z
end

function (K::NfRel{T})(a::T) where T
  parent(a) != base_ring(parent(K.pol)) == error("Cannot coerce")
  z = NfRelElem{T}(parent(K.pol)(a))
  z.parent = K
  return z
end

(K::NfRel)(a::Integer) = K(parent(K.pol)(a))

(K::NfRel)(a::Rational{T}) where {T <: Integer} = K(parent(K.pol)(a))

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

function Base.:(+)(a::NfRelElem{T}, b::NfRelElem{T}) where {T}
  return parent(a)(data(a) + data(b))
end

function Base.:(-)(a::NfRelElem{T}, b::NfRelElem{T}) where {T}
  return parent(a)(data(a) - data(b))
end

function Base.:(*)(a::NfRelElem{T}, b::NfRelElem{T}) where {T}
  return parent(a)(data(a) * data(b))
end

function Nemo.divexact(a::NfRelElem{T}, b::NfRelElem{T}) where {T}
  b == 0 && error("Element not invertible")
  return a*inv(b)
end

Base.:(//)(a::NfRelElem{T}, b::NfRelElem{T}) where {T} = divexact(a, b)

################################################################################
#
#  Inversion
#
################################################################################

# gcdx of GenPoly{nf_elem} needs this:
Nemo.canonical_unit(a::nf_elem) = a

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

function Base.:(==)(a::NfRelElem{T}, b::NfRelElem{T}) where T
  reduce!(a)
  reduce!(b)
  return data(a) == data(b)
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function Nemo.mul!(c::NfRelElem{T}, a::NfRelElem{T}, b::NfRelElem{T}) where {T}
  mul!(c.data, a.data, b.data)
  c = reduce!(c)
  return c
end

function Nemo.addeq!(b::NfRelElem{T}, a::NfRelElem{T}) where {T}
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

  return Ka, NfRelToNf(K, Ka, a, b, c), NfToNfMor(base_ring(K), Ka, a)
end

#Trager: p4, Algebraic Factoring and Rational Function Integration
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

function _absolute_field(K::NfRel{NfRelElem{nf_elem}})
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

  Ka = number_field(N)[1]
  println("have Ka=$Ka")
  KaT, T = PolynomialRing(Ka, "T")

  # map Ka -> K: gen(Ka) -> gen(K)+ k gen(k)

  # gen(k) -> Root(gcd(g, poly(k)))  #gcd should be linear:
  # g in kx = (Q[a])[x]. Want to map x -> gen(Ka), a -> T

  gg = zero(KaT)
  for i=degree(g):-1:0
    println("i: $i")
    gg = gg*gen(Ka) + coeff(g, i).data(gen(KaT))
  end

  q = gcd(gg, k.pol(gen(KaT)))
  @assert degree(q) == 1
  al = -trailing_coefficient(q)//lead(q)
  be = gen(Ka) - l*al
  ga = gen(K) + l*gen(k)

  #al -> gen(k) in Ka
  #be -> gen(K) in Ka
  #ga -> gen(Ka) in K
  return Ka, al, be, ga
end 

function Nemo.check_parent(a, b)
  return a==b
end

function Nemo.content(a::GenPoly{T}) where T <: Nemo.Field
  return base_ring(a)(1)
end
function Nemo.canonical_unit(a::NfRelElem)
  return parent(a)(1)
end

#function +(a::NfRelElem{NfRelElem{T}}, b::NfRelElem{T}) where T
#  c = deepcopy(a)
#  setcoeff!(c.data, 0, coeff(c.data, 0)+b)
#  return c
#end
#
#+(a::NfRelElem{T}, b::NfRelElem{NfRelElem{T}}) where T = b+a
#
#function *(a::NfRelElem{NfRelElem{T}}, b::NfRelElem{T}) where T
#  c = deepcopy(a)
#  setcoeff!(c.data, 0, coeff(c.data, 0)*b)
#  return c
#end
#
#*(a::NfRelElem{T}, b::NfRelElem{NfRelElem{T}}) where T = b*a

@inline coeff{T}(a::NfRelElem{T}, i::Int) = coeff(a.data, i)

@inline degree(L::Hecke.NfRel) = degree(L.pol)

#TODO: missing: norm, trace...

#######################################################################
# convenience constructions
#######################################################################
doc"""
    ispure_extension(K::NfRel) -> Bool
> Tests if $K$ is pure, ie. if the defining polynomial is $x^n-g$.
"""
function ispure_extension(K::NfRel)
  if !ismonic(K.pol)
    return false
  end
  return all(i->iszero(coeff(K.pol, i)), 1:degree(K)-1)
end

doc"""
    iskummer_extension(K::Hecke.NfRel{nf_elem}) -> Bool
> Tests if $K$ is Kummer, ie. if the defining polynomial is $x^n-g$ and
> if the coefficient field contains the $n$-th roots of unity.
"""
function iskummer_extension(K::Hecke.NfRel{nf_elem})
  if !ispure_extension(K)
    return false
  end

  k = base_ring(K)
  Zk = maximal_order(k)
  _, o = Hecke.torsion_units_gen_order(Zk)
  if o % degree(K) != 0
    return false
  end
  return true
end

doc"""
    pure_extension(n::Int, gen::FacElem{nf_elem, AnticNumberField}) -> NfRel{nf_elem}, NfRelElem
    pure_extension(n::Int, gen::nf_elem) -> NfRel{nf_elem}, NfRelElem
> Create the field extension with the defining polynomial $x^n-gen$.
"""
function pure_extension(n::Int, gen::FacElem{nf_elem, AnticNumberField})
  return pure_extension(n, evaluate(gen))
end

function pure_extension(n::Int, gen::nf_elem)
  k = parent(gen)
  kx, x = PolynomialRing(k)
  return number_field(x^n-gen)
end

function hash(a::Hecke.NfRelElem{nf_elem}, b::UInt)
  return hash(a.data, b)
end

################################################################################
#
#  Representation Matrix
#
################################################################################

function elem_to_mat_row!(M::GenMat{T}, i::Int, a::NfRelElem{T}) where T
  for c = 1:cols(M)
    M[i, c] = deepcopy(coeff(a, c - 1))
  end
  return nothing
end

function elem_from_mat_row(L::NfRel{T}, M::GenMat{T}, i::Int) where T
  t = L(1)
  a = L()
  for c = 1:cols(M)
    a += M[i, c]*t
    mul!(t, t, gen(L))
  end
  return a
end

function representation_mat(a::NfRelElem)
  L = a.parent
  n = degree(L)
  M = MatrixSpace(base_ring(L), n, n)()
  t = gen(L)
  b = deepcopy(a)
  for i = 1:n-1
    elem_to_mat_row!(M, i, b)
    mul!(b, b, t)
  end
  elem_to_mat_row!(M, n, b)
  return M
end

function norm(a::NfRelElem{nf_elem}, new::Bool = !true)
  if new && ismonic(parent(a).pol) #should be much faster - eventually
    return resultant_mod(a.data, parent(a).pol)
  end
  M = representation_mat(a)
  return det(M)
end


function norm(a::NfRelElem, new::Bool = true)
  if new && ismonic(parent(a).pol)
    return resultant(a.data, parent(a).pol)
  end
  M = representation_mat(a)
  return det(M)
end

function trace(a::NfRelElem)
  M = representation_mat(a)
  return trace(M)
end

######################################################################
# fun in towers..
######################################################################

isunit(a::NfRelElem) = !iszero(a)

absolute_degree(A::AnticNumberField) = degree(A)

function absolute_degree(A::NfRel)
  return absolute_degree(base_ring(A))*degree(A)
end

function trace(a::NfRelElem, k::Union{NfRel, AnticNumberField, FlintRationalField})
  b = trace(a)
  while parent(b) != k
    b = trace(b)
  end
  return b
end

function norm(a::NfRelElem, k::Union{NfRel, AnticNumberField, FlintRationalField})
  b = norm(a)
  while parent(b) != k
    b = norm(b)
  end
  return b
end

function absolute_trace(a::NfRelElem)
  return trace(a, FlintQQ)
end

function absolute_norm(a::NfRelElem)
  return norm(a, FlintQQ)
end

#TODO: investigate charpoly/ minpoly from power_sums, aka trace(a^i) and
#      Newton identities
#TODO: cache traces of powers of the generator on the field, then
#      the trace does not need the matrix

function charpoly(a::NfRelElem)
  M = representation_mat(a)
  R = PolynomialRing(base_ring(parent(a)))[1]
  return minpoly(R, M, true)
end

function minpoly(a::NfRelElem)
  M = representation_mat(a)
  R = PolynomialRing(base_ring(parent(a)))[1]
  return minpoly(R, M, false)
end

function charpoly(a::NfRelElem, k::Union{NfRel, AnticNumberField, FlintRationalField})
  f = charpoly(a)
  while base_ring(f) != k
    f = norm(f)
  end
  return f
end

function absolute_charpoly(a::NfRelElem)
  return charpoly(a, FlintQQ)
end

function minpoly(a::NfRelElem, k::Union{NfRel, AnticNumberField, FlintRationalField})
  f = minpoly(a)
  while base_ring(f) != k
    f = norm(f)
    g = gcd(f, derivative(f))
    if !isone(g)
      f = divexact(f, g)
    end
  end
  return f
end

function absolute_minpoly(a::NfRelElem)
  return minpoly(a, FlintQQ)
end

#

(K::NfRel)(x::NfRelElem) = K(base_ring(K)(x))

(K::NfRel{T})(x::NfRelElem{T}) where {T} = K(x.data)

(K::NfRel{NfRelElem{T}})(x::NfRelElem{T}) where {T} = K(parent(K.pol)(x))

(K::NfRel{nf_elem})(x::nf_elem) = K(parent(K.pol)(x))

