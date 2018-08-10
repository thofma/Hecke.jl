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

function Nemo.zero!(a::NfRelElem)
  Nemo.zero!(a.data)
  return a
end

################################################################################
#
#  Promotion
#
################################################################################

if isdefined(Nemo, :promote_rule1)
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
else
  Nemo.promote_rule{T <: Integer, S}(::Type{NfRelElem{S}}, ::Type{T}) = NfRelElem{S}

  Nemo.promote_rule(::Type{NfRelElem{T}}, ::Type{fmpz}) where {T <: Nemo.RingElement} = NfRelElem{T}

  Nemo.promote_rule(::Type{NfRelElem{T}}, ::Type{fmpq}) where {T <: Nemo.RingElement} = NfRelElem{T}

  Nemo.promote_rule(::Type{NfRelElem{T}}, ::Type{T}) where {T} = NfRelElem{T}

  Nemo.promote_rule(::Type{NfRelElem{T}}, ::Type{NfRelElem{T}}) where T <: Nemo.RingElement = NfRelElem{T}
  
  function Nemo.promote_rule(::Type{NfRelElem{T}}, ::Type{U}) where {T <: Nemo.RingElement, U <: Nemo.RingElement}
    Nemo.promote_rule(T, U) == T ? NfRelElem{T} : Union{}
  end
end

################################################################################
#
#  Field access
#
################################################################################

@inline Nemo.base_ring{T}(a::NfRel{T}) = a.base_ring::parent_type(T)
@inline base_field{T}(a::NfRel{T}) = a.base_ring::parent_type(T)

@inline Nemo.data(a::NfRelElem) = a.data

@inline Nemo.parent{T}(a::NfRelElem{T}) = a.parent::NfRel{T}

issimple(a::NfRel) = true

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

doc"""
    number_field(f::Generic.Poly{T}, s::String, cached::Bool = false) where T
> Given an irreducible polynomial $f$ over some number field $K$,
> create the field $K[t]/f$.
> $f$ must be irreducible - although this is not tested.
"""
function number_field(f::Generic.Poly{T}, s::String, cached::Bool = false) where T
  S = Symbol(s)
  K = NfRel{T}(f, S, cached)
  return K, K(gen(parent(f)))
end

doc"""
    number_field(f::Generic.Poly{T}, cached::Bool = false) where T
> Given an irreducible polynomial $f$ over some number field $K$,
> create the field $K[t]/f$.
> $f$ must be irreducible - although this is not tested.
"""
function number_field(f::Generic.Poly{T}, cached::Bool = false) where T
  return number_field(f, "_\$", cached)
end
 
function (K::NfRel{T})(a::Generic.Poly{T}) where T
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

function (K::NfRel{T})(a::Vector{T}) where T
  @assert length(a) <= degree(K)
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

function Base.:(^)(a::NfRelElem, b::fmpz)
  if b < 0
    return inv(a)^(-b)
  elseif b == 0
    return parent(a)(1)
  elseif b == 1
    return deepcopy(a)
  elseif mod(b, 2) == 0
    c = a^(div(b, 2))
    return c*c
  elseif mod(b, 2) == 1
    return a^(b - 1)*a
  end
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

if !isdefined(Nemo, :promote_rule1)
  function Base.:(==)(a::NfRelElem{T}, b::Union{Integer, Rational}) where T
    return a == parent(a)(b)
  end
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

function Nemo.add!(c::NfRelElem{T}, a::NfRelElem{T}, b::NfRelElem{T}) where {T}
  add!(c.data, a.data, b.data)
  c = reduce!(c)
  return c
end

################################################################################
#
#  Isomorphism to absolute field (AnticNumberField)
#
################################################################################

doc"""
    absolute_field(K::NfRel{nf_elem}, cached::Bool = false) -> AnticNumberField, Map, Map
> Given an extension $K/k/Q$, find an isomorphic extensino of $Q$.
"""
function absolute_field(K::NfRel{nf_elem}, cached::Bool = false)
  Ka, a, b, c = _absolute_field(K, cached)
  return Ka, NfRelToNf(K, Ka, a, b, c), NfToNfMor(base_ring(K), Ka, a)
end

doc"""
    absolute_field(K::NfRel{NfRelElem}, cached::Bool = false) -> NfRel, Map, Map
> Given an extension $E/K/k$, find an isomorphic extension of $k$.
> In a tower, only the top-most steps are collapsed.
"""
function absolute_field(K::NfRel{NfRelElem{T}}, cached::Bool = false) where T
  Ka, a, b, c = _absolute_field(K)
  return Ka, NfRelRelToNfRel(K, Ka, a, b, c), NfRelToNfRelMor(base_ring(K), Ka, a)
end


#Trager: p4, Algebraic Factoring and Rational Function Integration
function _absolute_field(K::NfRel, cached::Bool = false)
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

  Ka = NumberField(N, "_\$", cached = cached)[1]

  KaT, T = PolynomialRing(Ka, "T", cached = false)

  # map Ka -> K: gen(Ka) -> gen(K)+ k gen(k)

  # gen(k) -> Root(gcd(g, poly(k)))  #gcd should be linear:
  # g in kx = (Q[a])[x]. Want to map x -> gen(Ka), a -> T

  gg = zero(KaT)
  for i=degree(g):-1:0
    gg = gg*gen(Ka) + Qx(coeff(g, i))(gen(KaT))
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

function Nemo.content(a::Generic.Poly{T}) where T <: Nemo.Field
  return base_ring(a)(1)
end

Nemo.canonical_unit(a::NfRelElem) = a

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
@inline setcoeff!{T}(a::NfRelElem{T}, i::Int, c::T) = setcoeff!(a.data, i, c)

@inline degree(L::Hecke.NfRel) = degree(L.pol)

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
  kx, x = PolynomialRing(k, cached = false)
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

function elem_to_mat_row!(M::Generic.Mat{T}, i::Int, a::NfRelElem{T}) where T
  for c = 1:cols(M)
    M[i, c] = deepcopy(coeff(a, c - 1))
  end
  return nothing
end

function elem_from_mat_row(L::NfRel{T}, M::Generic.Mat{T}, i::Int) where T
  t = L(1)
  a = L()
  for c = 1:cols(M)
    a += M[i, c]*t
    mul!(t, t, gen(L))
  end
  return a
end

function representation_matrix(a::NfRelElem)
  L = a.parent
  n = degree(L)
  M = zero_matrix(base_ring(L), n, n)
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
  M = representation_matrix(a)
  return det(M)
end


function norm(a::NfRelElem, new::Bool = true)
  if new && ismonic(parent(a).pol)
    return resultant(a.data, parent(a).pol)
  end
  M = representation_matrix(a)
  return det(M)
end

function trace(a::NfRelElem)
  M = representation_matrix(a)
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
  M = representation_matrix(a)
  R = PolynomialRing(base_ring(parent(a)), cached = false)[1]
  return minpoly(R, M, true)
end

function minpoly(a::NfRelElem)
  M = representation_matrix(a)
  R = PolynomialRing(base_ring(parent(a)), cached = false)[1]
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

(K::NfRel)(x::nf_elem) = K(base_ring(K)(x))

(K::NfRel{T})(x::NfRelElem{T}) where {T} = K(x.data)

(K::NfRel{NfRelElem{T}})(x::NfRelElem{T}) where {T} = K(parent(K.pol)(x))

(K::NfRel{nf_elem})(x::nf_elem) = K(parent(K.pol)(x))

#

function (R::Generic.PolyRing{nf_elem})(a::NfRelElem{nf_elem})
  if base_ring(R)==base_ring(parent(a))
    return a.data
  end
  error("wrong ring")
end

function (R::Generic.PolyRing{NfRelElem{T}})(a::NfRelElem{NfRelElem{T}}) where T
  if base_ring(R)==base_ring(parent(a))
    return a.data
  end
  error("wrong ring")
end

function factor(f::Generic.Poly{NfRelElem{T}}) where T
  K = base_ring(f)
  Ka, rel_abs, _ = absolute_field(K)
  function map_poly(P::Ring, mp::Map, f::Generic.Poly)
    return P([mp(coeff(f, i)) for i=0:degree(f)])
  end

  fa = map_poly(PolynomialRing(Ka, "T", cached=false)[1], rel_abs, f)
  lf = factor(fa)
  res = Fac(map_poly(parent(f), inv(rel_abs), lf.unit), Dict(map_poly(parent(f), inv(rel_abs), k)=>v for (k,v) = lf.fac))

  return res
end

function factor(f::PolyElem, K::Nemo.Field)
  Kt, t = PolynomialRing(K, cached = false)
  return factor(Kt([K(coeff(f, i)) for i=0:degree(f)]))
end

function roots(f::PolyElem, K::Nemo.Field)
  Kt, t = PolynomialRing(K, cached = false)
  return roots(Kt([K(coeff(f, i)) for i=0:degree(f)]))
end

function roots(f::Generic.Poly{NfRelElem{T}}) where T
  lf = factor(f)
  @assert degree(lf.unit) == 0
  scale = inv(coeff(lf.unit, 0))
  return [-constant_coefficient(x)*scale for x = keys(lf.fac) if degree(x)==1]
end

################################################################################
#
#  issubfield and isisomorphic
#
################################################################################

doc"""
***
      issubfield(K::NfRel, L::NfRel) -> Bool, NfRelToNfRelMor

> Returns "true" and an injection from $K$ to $L$ if $K$ is a subfield of $L$.
> Otherwise the function returns "false" and a morphism mapping everything to 0.
"""
function issubfield(K::NfRel, L::NfRel)
  @assert base_ring(K) == base_ring(L)
  f = K.pol
  g = L.pol
  if mod(degree(g), degree(f)) != 0
    return false, NfRelToNfRelMor(K, L, L())
  end
  Lx, x = L["x"]
  fL = Lx()
  for i = 0:degree(f)
    setcoeff!(fL, i, L(coeff(f, i)))
  end
  fac = factor(fL)
  for (a, b) in fac
    if degree(a) == 1
      c1 = coeff(a, 0)
      c2 = coeff(a, 1)
      h = parent(K.pol)(-c1*inv(c2))
      return true, NfRelToNfRelMor(K, L, h(gen(L)))
    end
  end
  return false, NfRelToNfRelMor(K, L, L())
end

doc"""
***
      isisomorphic(K::NfRel, L::NfRel) -> Bool, NfRelToNfRelMor

> Returns "true" and an isomorphism from $K$ to $L$ if $K$ and $L$ are isomorphic.
> Otherwise the function returns "false" and a morphism mapping everything to 0.
"""
function isisomorphic(K::NfRel, L::NfRel)
  @assert base_ring(K) == base_ring(L)
  f = K.pol
  g = L.pol
  if degree(f) != degree(g)
    return false, NfRelToNfRelMor(K, L, L())
  end
  return issubfield(K, L)
end

doc"""
    discriminant(K::AnticNumberField) -> fmpq
    discriminant(K::NfRel) -> 
> The discriminant of the defining polynomial of $K$ {\bf not} the discriminant 
> of the maximal order.
"""
function Nemo.discriminant(K::AnticNumberField)
  return discriminant(K.pol)
end

function Nemo.discriminant(K::NfRel)
  d = discriminant(K.pol)
  return d
end

doc"""
    discriminant(K::AnticNumberField, FlintQQ) -> fmpq
    discriminant(K::NfRel, FlintQQ) -> 
> The absolute discriminant of the defining polynomial of $K$ {\bf not} the discriminant 
> of the maximal order. Ie the norm of the discriminant time the power of the discriminant
> of the base field.
"""
function Nemo.discriminant(K::AnticNumberField, ::FlintRationalField)
  return discriminant(K)
end

function Nemo.discriminant(K::NfRel, ::FlintRationalField)
  d = norm(discriminant(K)) * discriminant(base_field(K))^degree(K)
  return d
end


