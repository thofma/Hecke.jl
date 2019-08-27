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


################################################################################
#
#  Copy
#
################################################################################

function Base.deepcopy_internal(a::NfRelElem{T}, dict::IdDict) where T
  z = NfRelElem{T}(Base.deepcopy_internal(data(a), dict))
  z.parent = parent(a)
  return z
end

################################################################################
#
#  Comply with ring interface
#
################################################################################

elem_type(::Type{NfRel{T}}) where {T} = NfRelElem{T}

elem_type(::NfRel{T}) where {T} = NfRelElem{T}

parent_type(::Type{NfRelElem{T}}) where {T} = NfRel{T}

needs_parentheses(::NfRelElem) = true

isnegative(x::NfRelElem) = isnegative(data(x))

show_minus_one(::Type{NfRelElem{T}}) where {T} = true

function iszero(a::NfRelElem)
  reduce!(a)
  return iszero(data(a))
end

function isone(a::NfRelElem)
  reduce!(a)
  return isone(data(a))
end

zero(K::NfRel) = K(zero(parent(K.pol)))

one(K::NfRel) = K(one(parent(K.pol)))

function zero!(a::NfRelElem)
  zero!(a.data)
  return a
end

################################################################################
#
#  Promotion
#
################################################################################

promote_rule(::Type{NfRelElem{S}}, ::Type{T}) where {T <: Integer, S} = NfRelElem{S}

promote_rule(::Type{NfRelElem{T}}, ::Type{fmpz}) where {T <: RingElement} = NfRelElem{T}

promote_rule(::Type{NfRelElem{T}}, ::Type{fmpq}) where {T <: RingElement} = NfRelElem{T}

promote_rule(::Type{NfRelElem{T}}, ::Type{T}) where {T} = NfRelElem{T}

promote_rule(::Type{NfRelElem{T}}, ::Type{NfRelElem{T}}) where T <: RingElement = NfRelElem{T}

function promote_rule(::Type{NfRelElem{T}}, ::Type{U}) where {T <: RingElement, U <: RingElement}
  promote_rule(T, U) == T ? NfRelElem{T} : Union{}
end

################################################################################
#
#  Order types
#
################################################################################

order_type(K::NfRel{T}) where {T} = NfRelOrd{T, frac_ideal_type(order_type(base_field(K)))}

order_type(::Type{NfRel{T}}) where {T} = NfRelOrd{T, frac_ideal_type(order_type(parent_type(T)))}

################################################################################
#
#  Field access
#
################################################################################

@inline base_field(a::NfRel{T}) where {T} = a.base_ring::parent_type(T)

@inline data(a::NfRelElem) = a.data

@inline parent(a::NfRelElem{T}) where {T} = a.parent::NfRel{T}

@inline issimple(a::NfRel) = true

################################################################################
#
#  Coefficient setting and getting
#
################################################################################

@inline coeff(a::NfRelElem{T}, i::Int) where {T} = coeff(a.data, i)

@inline setcoeff!(a::NfRelElem{T}, i::Int, c::T) where {T} = setcoeff!(a.data, i, c)

# copy does not do anything (so far), this is only for compatibility with coeffs(::AbsAlgAssElem)
function coeffs(a::NfRelElem{T}; copy::Bool = false) where {T}
  return T[coeff(a, i) for i = 0:degree(parent(a)) - 1 ]
end

################################################################################
#
#  Constructors
#
################################################################################

(K::NfRel)(x::NfRelElem) = K(base_field(K)(x))

(K::NfRel)(x::nf_elem) = K(base_field(K)(x))

(K::NfRel{T})(x::NfRelElem{T}) where {T} = K(x.data)

(K::NfRel{NfRelElem{T}})(x::NfRelElem{T}) where {T} = K(parent(K.pol)(x))

(K::NfRel{nf_elem})(x::nf_elem) = K(parent(K.pol)(x))


################################################################################
#
#  Degree
#
################################################################################

@inline degree(L::Hecke.NfRel) = degree(L.pol)

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

function NumberField(f::PolyElem{T}, s::String;
                     cached::Bool = false, check::Bool = false)  where {T <: NumFieldElem}
  S = Symbol(s)
  check && !isirreducible(f) && throw(error("Polynomial must be irreducible"))
  K = NfRel{T}(f, S, cached)
  return K, K(gen(parent(f)))
end

function NumberField(f::PolyElem{<: NumFieldElem}; cached::Bool = false, check::Bool = false)
  return NumberField(f, "_\$", cached = cached, check = check)
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

(K::NfRel)(a::Integer) = K(parent(K.pol)(a))

(K::NfRel)(a::Rational{T}) where {T <: Integer} = K(parent(K.pol)(a))

(K::NfRel)(a::fmpz) = K(parent(K.pol)(a))

(K::NfRel)(a::fmpq) = K(parent(K.pol)(a))

(K::NfRel)() = zero(K)

gen(K::NfRel) = K(gen(parent(K.pol)))

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

function divexact(a::NfRelElem{T}, b::NfRelElem{T}) where {T}
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
  a == 0 && throw(error("Element not invertible"))
  g, s, _ = gcdx(data(a), parent(a).pol)
  @assert g == 1
  return parent(a)(s)
end

################################################################################
#
#  Powering
#
################################################################################

Base.:(^)(a::NfRelElem, n::UInt) = a^Int(n)

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
#  Ad hoc operators
#
################################################################################

function Base.:(*)(a::NfRelElem{T}, b::T) where {T <: NumFieldElem}
  return parent(a)(data(a) * b)
end

Base.:(*)(a::T, b::NfRelElem{T}) where {T <: NumFieldElem} = b * a

function Base.:(+)(a::NfRelElem{T}, b::T) where {T <: NumFieldElem}
  return parent(a)(data(a) + b)
end

Base.:(+)(a::T, b::NfRelElem{T}) where {T <: NumFieldElem} = b + a

function Base.:(-)(a::NfRelElem{T}, b::T) where {T <: NumFieldElem}
  return parent(a)(data(a) - b)
end

function Base.:(-)(a::T, b::NfRelElem{T}) where {T <: NumFieldElem}
  return parent(b)(a - data(b))
end

function divexact(a::NfRelElem{T}, b::T) where {T <: NumFieldElem}
  return parent(a)(divexact(data(a), b))
end

Base.:(//)(a::NfRelElem{T}, b::T) where {T <: NumFieldElem} = divexact(a, b)

for F in [fmpz, fmpq, Int]
  @eval begin
    function Base.:(*)(a::NfRelElem{T}, b::$F) where {T <: NumFieldElem}
      return parent(a)(data(a) * b)
    end

    Base.:(*)(a::$F, b::NfRelElem{T}) where {T <: NumFieldElem} = b * a

    function Base.:(+)(a::NfRelElem{T}, b::$F) where {T <: NumFieldElem}
      return parent(a)(data(a) + b)
    end

    Base.:(+)(a::$F, b::NfRelElem{T}) where {T <: NumFieldElem} = b + a

    function Base.:(-)(a::NfRelElem{T}, b::$F) where {T <: NumFieldElem}
      return parent(a)(data(a) - b)
    end

    function Base.:(-)(a::$F, b::NfRelElem{T}) where {T <: NumFieldElem}
      return parent(b)(a - data(b))
    end
    
    function divexact(a::NfRelElem{T}, b::$F) where {T <: NumFieldElem}
      return parent(a)(divexact(data(a), b))
    end

    Base.:(//)(a::NfRelElem{T}, b::$F) where {T <: NumFieldElem} = divexact(a, b)
  end
end


################################################################################
#
#  Unsafe operations
#
################################################################################

function mul!(c::NfRelElem{T}, a::NfRelElem{T}, b::NfRelElem{T}) where {T}
  mul!(c.data, a.data, b.data)
  c = reduce!(c)
  return c
end

function mul!(c::NfRelElem{T}, a::NfRelElem{T}, b::T) where {T}
  mul!(c.data, a.data, b)
  c = reduce!(c)
  return c
end

function addeq!(b::NfRelElem{T}, a::NfRelElem{T}) where {T}
  addeq!(b.data, a.data)
  b = reduce!(b)
  return b
end

function add!(c::NfRelElem{T}, a::NfRelElem{T}, b::NfRelElem{T}) where {T}
  add!(c.data, a.data, b.data)
  c = reduce!(c)
  return c
end

################################################################################
#
#  Isomorphism to absolute field (AnticNumberField)
#
################################################################################

#@doc Markdown.doc"""
#    absolute_field(K::NfRel{nf_elem}, cached::Bool = false) -> AnticNumberField, Map, Map
#Given an extension $K/k/Q$, find an isomorphic extension of $Q$.
#"""
function absolute_field(K::NfRel{nf_elem}, cached::Bool = false)
  Ka, a, b, c = _absolute_field(K, cached)
  #return Ka, NfRelToNf(K, Ka, a, b, c), hom(base_ring(K), Ka, a, check = false)
  return Ka, NfToNfRel(Ka, K, a, b, c), hom(base_field(K), Ka, a, check = false)
end

#@doc Markdown.doc"""
#    absolute_field(K::NfRel{NfRelElem}, cached::Bool = false) -> NfRel, Map, Map
#Given an extension $E/K/k$, find an isomorphic extension of $k$.
#In a tower, only the top-most steps are collapsed.
#"""
function absolute_field(K::NfRel{NfRelElem{T}}, cached::Bool = false) where T
  @show "here"
  Ka, a, b, c = _absolute_field(K)
  return Ka, NfRelToNfRelRel(Ka, K, a, b, c), hom(base_field(K), Ka, a, check = false)
end


#Trager: p4, Algebraic Factoring and Rational Function Integration
function _absolute_field(K::NfRel, cached::Bool = false)
  f = K.pol
  kx = parent(f)
  k = base_ring(kx)
  Qx = parent(k.pol)

  l = 0
  g = f
  N = norm(g)

  while true
    @assert degree(N) == degree(g) * degree(k)

    if !isconstant(N) && issquarefree(N)
      break
    end

    l += 1
 
    g = compose(f, gen(kx) - l*gen(k))
    N = norm(g)
  end

  Ka, gKa = NumberField(N, "x", cached = cached, check = false)

  KaT, T = PolynomialRing(Ka, "T", cached = false)

  # map Ka -> K: gen(Ka) -> gen(K)+ k gen(k)

  # gen(k) -> Root(gcd(g, poly(k)))  #gcd should be linear:
  # g in kx = (Q[a])[x]. Want to map x -> gen(Ka), a -> T

  gg = zero(KaT)
  for i=degree(g):-1:0
    auxp = change_ring(Qx(coeff(g, i)), KaT)
    gg = gg*gKa
    add!(gg, gg, auxp)
    #gg = gg*gKa + auxp
  end
  
  q = gcd(gg, change_ring(k.pol, KaT))
  @assert degree(q) == 1
  al = -trailing_coefficient(q)//lead(q)
  be = gKa - l*al
  ga = gen(K) + l*gen(k)

  #al -> gen(k) in Ka
  #be -> gen(K) in Ka
  #ga -> gen(Ka) in K
  return Ka, al, be, ga
end 

function check_parent(a, b)
  return a==b
end

function hash(a::Hecke.NfRelElem{nf_elem}, b::UInt)
  return hash(a.data, b)
end

################################################################################
#
#  Basis & representation matrix
#
################################################################################

function basis_mat(v::Vector{<: NfRelElem})
  K = parent(v[1])
  k = base_field(K)
  z = zero_matrix(k, length(v), degree(K))
  for i in 1:length(v)
    for j in 0:(degree(K) - 1)
      z[i, j + 1] = coeff(v[i], j)
    end
  end
  return z
end

function elem_to_mat_row!(M::Generic.Mat{T}, i::Int, a::NfRelElem{T}) where T
  for c = 1:ncols(M)
    M[i, c] = deepcopy(coeff(a, c - 1))
  end
  return nothing
end

function elem_from_mat_row(L::NfRel{T}, M::Generic.Mat{T}, i::Int) where T
  t = L(1)
  a = L()
  for c = 1:ncols(M)
    a += M[i, c]*t
    mul!(t, t, gen(L))
  end
  return a
end

function representation_matrix(a::NfRelElem)
  L = a.parent
  n = degree(L)
  M = zero_matrix(base_field(L), n, n)
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

function tr(a::NfRelElem)
  M = representation_matrix(a)
  return tr(M)
end

################################################################################
#
#  Minimal and characteristic polynomial
#
################################################################################

function _poly_norm_to(f, k::T) where {T}
  if base_ring(f) isa T
    @assert base_ring(f) == k
    return f
  else
    return _poly_norm_to(norm(f), k)
  end
end

#TODO: investigate charpoly/ minpoly from power_sums, aka tr(a^i) and
#      Newton identities
#TODO: cache traces of powers of the generator on the field, then
#      the trace does not need the matrix

@doc Markdown.doc"""
    charpoly(a::NfRelElem) -> PolyElem

Given an element $a$ in an extension $L/K$, this function returns the
characteristic polynomial of $a$ over $K$.
"""
function charpoly(a::NfRelElem)
  M = representation_matrix(a)
  R = PolynomialRing(base_field(parent(a)), cached = false)[1]
  return charpoly(R, M)
end

@doc Markdown.doc"""
    minpoly(a::NfRelElem) -> PolyElem

Given an element $a$ in an extension $L/K$, this function returns the minimal
polynomial of $a$ of $K$.
"""
function minpoly(a::NfRelElem)
  M = representation_matrix(a)
  R = PolynomialRing(base_field(parent(a)), cached = false)[1]
  return minpoly(R, M, false)
end

function charpoly(a::NfRelElem, k::Union{NfRel, AnticNumberField, FlintRationalField})
  f = charpoly(a)
  return _poly_norm_to(f, k)
end

function absolute_charpoly(a::NfRelElem)
  return charpoly(a, FlintQQ)
end

function minpoly(a::NfRelElem, k::Union{NfRel, AnticNumberField, FlintRationalField})

  if parent(a) == k
    R, y  = PolynomialRing(k, cached = false)
    return y - a
  end

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

#

function (R::Generic.PolyRing{nf_elem})(a::NfRelElem{nf_elem})
  if base_ring(R)==base_field(parent(a))
    return a.data
  end
  error("wrong ring")
end

function (R::Generic.PolyRing{NfRelElem{T}})(a::NfRelElem{NfRelElem{T}}) where T
  if base_ring(R)==base_field(parent(a))
    return a.data
  end
  error("wrong ring")
end

################################################################################
#
#  issubfield and isisomorphic
#
################################################################################

function issubfield(K::NfRel, L::NfRel)
  @assert base_field(K) == base_field(L)
  f = K.pol
  g = L.pol
  if mod(degree(g), degree(f)) != 0
    return false, hom(K, L, zero(L), check = false)
  end
  Lx, x = PolynomialRing(L, "x", cached = false)
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
      return true, hom(K, L, h(gen(L)), check = false)
    end
  end
  return false, hom(K, L, zero(L), check = false)
end

function isisomorphic(K::NfRel, L::NfRel)
  @assert base_field(K) == base_field(L)
  f = K.pol
  g = L.pol
  if degree(f) != degree(g)
    return false, hom(K, L, zero(L), check = false)
  end
  return issubfield(K, L)
end

################################################################################
#
#  Normal basis
#
################################################################################

# Mostly the same as in the absolute case
function normal_basis(L::NfRel{nf_elem})
  O = EquationOrder(L)
  K = base_field(L)
  OK = base_ring(O)
  d = discriminant(O)

  for p in PrimeIdealsSet(OK, degree(L), -1, indexdivisors = false, ramified = false)
    if valuation(d, p) != 0
      continue
    end

    # Check if p is totally split
    F, mF = ResidueField(OK, p)
    mmF = extend(mF, K)
    Ft, t = PolynomialRing(F, "t", cached = false)
    ft = nf_elem_poly_to_fq_poly(Ft, mmF, L.pol)
    pt = powmod(t, order(F), ft)

    if degree(gcd(ft, pt - t)) == degree(ft)
      # Lift an idempotent of O/pO
      immF = pseudo_inv(mmF)
      fac = factor(ft)
      gt = divexact(ft, first(keys(fac.fac)))
      g = fq_poly_to_nf_elem_poly(parent(L.pol), immF, gt)
      return L(g)
    end
  end
end
