################################################################################
#
#  NfAbs/NonSimple.jl : non-simple absolute fields
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
#  Copyright (C) 2017 Tommy Hofmann, Claus Fieker
#
################################################################################

function Nemo.PolynomialRing(R::Nemo.Ring, n::Int, s::String="x"; cached::Bool = false, ordering::Symbol = :lex)
  return Nemo.PolynomialRing(R, ["$s$i" for i=1:n], cached = cached, ordering = ordering)
end

mutable struct NfAbsNS <: Nemo.Field
  pol::Array{fmpq_mpoly, 1}
  S::Array{Symbol, 1}
  basis#::Vector{NfAbsNSElem}
  degree::Int
  degrees::Vector{Int}

  function NfAbsNS(f::Array{fmpq_mpoly, 1}, S::Array{Symbol, 1}; cached::Bool = false)
    r = new()
    r.pol = f
    r.S = S
    return r
  end
end

mutable struct NfAbsNSElem <: Nemo.FieldElem
  data::fmpq_mpoly
  parent::NfAbsNS

  NfAbsNSElem(g::fmpq_mpoly) = new(g)
end

@inline degree(K::NfAbsNS) = K.degree

@inline degrees(K::NfAbsNS) = K.degrees

@inline ngens(K::NfAbsNS) = length(K.pol)

################################################################################
#
#  Copy
#
################################################################################

function Base.deepcopy_internal(a::NfAbsNSElem, dict::ObjectIdDict)
  z = NfAbsNSElem(Base.deepcopy_internal(data(a), dict))
  z.parent = parent(a)
  return z
end

#julia's a^i needs copy
function Base.copy(a::NfAbsNSElem)
  return parent(a)(a.data)
end

################################################################################
#
#  Comply with Nemo ring interface
#
################################################################################

elem_type(::Type{NfAbsNS}) = NfAbsNSElem

elem_type(::NfAbsNS) = NfAbsNSElem

parent_type(::Type{NfAbsNSElem}) = NfAbsNS

needs_parentheses(::NfAbsNSElem) = true

isnegative(x::NfAbsNSElem) = Nemo.isnegative(data(x))

show_minus_one(::Type{NfAbsNSElem}) = true

function iszero(a::NfAbsNSElem)
  reduce!(a)
  return iszero(data(a))
end

function isone(a::NfAbsNSElem)
  reduce!(a)
  return isone(data(a))
end

Nemo.zero(K::NfAbsNS) = K(Nemo.zero(parent(K.pol[1])))

Nemo.one(K::NfAbsNS) = K(Nemo.one(parent(K.pol[1])))

Nemo.one(a::NfAbsNSElem) = one(a.parent)

################################################################################
#
#  Promotion
#
################################################################################

if isdefined(Nemo, :promote_rule1)
  Nemo.promote_rule{T <: Integer}(::Type{NfAbsNSElem}, ::Type{T}) = NfAbsNSElem

  Nemo.promote_rule(::Type{NfAbsNSElem}, ::Type{fmpz}) = NfAbsNSElem

  Nemo.promote_rule(::Type{NfAbsNSElem}, ::Type{fmpq}) = NfAbsNSElem

  function Nemo.promote_rule(::Type{NfAbsNSElem}, ::Type{U}) where {U}
    Nemo.promote_rule(fmpq, U) == fmpq ? NfAbsNSElem : Nemo.promote_rule1(U, NfAbsNSElem)
  end
else
  Nemo.promote_rule{T <: Integer}(::Type{NfAbsNSElem}, ::Type{T}) = NfAbsNSElem

  Nemo.promote_rule(::Type{NfAbsNSElem}, ::Type{fmpz}) = NfAbsNSElem

  Nemo.promote_rule(::Type{NfAbsNSElem}, ::Type{fmpq}) = NfAbsNSElem

  function Nemo.promote_rule(::Type{NfAbsNSElem}, ::Type{U}) where {U <: Nemo.RingElement}
    Nemo.promote_rule(fmpq, U) == fmpq ? NfAbsNSElem : Union{}
  end
end

################################################################################
#
#  Field access
#
################################################################################

@inline Nemo.data(a::NfAbsNSElem) = a.data

@inline Nemo.parent(a::NfAbsNSElem) = a.parent::NfAbsNS

issimple(a::NfAbsNS) = false

issimple(::Type{NfAbsNS}) = false

function basis(K::NfAbsNS)
  if isdefined(K, :basis)
    return copy(K.basis)
  else
    g = gens(K)
    b = NfAbsNSElem[]
    for i in CartesianRange(Tuple(1:degrees(K)[i] for i in 1:ngens(K)))
      push!(b, prod(g[j]^(i[j] - 1) for j=1:length(i)))
    end
    #b = Vector{NfAbsNSElem}(degree(K))
    #for (l, i) in enumerate(CartesianRange(Tuple(1:degrees(K)[i] for i in 1:ngens(K))))
    #  b[l] = prod(g[j]^(i[j] - 1) for j=1:length(i))
    #end
    K.basis = b
    return copy(b)
  end
end

# Given an exponent vector b, the following function returns the index of
# the basis element corresponding to b.
function monomial_to_index(K::NfAbsNS, b::Vector{T}) where {T}
  n = ngens(K)
  idx = b[n]
  for j in n-1:-1:1
    idx *= degrees(K)[j]
    idx += b[j]
  end
  return Int(idx + 1)
end

################################################################################
#
#  Reduction
#
################################################################################

function reduce!(a::NfAbsNSElem)
  q, a.data = divrem(a.data, parent(a).pol)
  return a
end

################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, a::NfAbsNS)
  print(io, "Non-simple number field with defining polynomials ", a.pol)
end

#TODO: this is a terrible show func.
function Base.show(io::IO, a::NfAbsNSElem)
  f = data(a)
  show(io, f)
end

################################################################################
#
#  Constructors and parent object overloading
#
################################################################################

function number_field(f::Array{fmpq_poly, 1}, s::String="_\$")
  S = Symbol(s)
  Qx, x = PolynomialRing(FlintQQ, length(f), s)
  K = NfAbsNS([f[i](x[i]) for i=1:length(f)], [Symbol("$s$i") for i=1:length(f)])
  K.degrees = [ degree(f[i]) for i in 1:length(f) ]
  K.degree = prod(K.degrees)
  return K, gens(K)
end

gens(K::NfAbsNS) = [K(x) for x = gens(parent(K.pol[1]))]

function (K::NfAbsNS)(a::fmpq_mpoly)
  q, w = divrem(a, K.pol)
  z = NfAbsNSElem(w)
  z.parent = K
  return z
end

(K::NfAbsNS)(a::Integer) = K(parent(K.pol[1])(a))

(K::NfAbsNS)(a::Rational{T}) where {T <: Integer} = K(parent(K.pol[1])(a))

(K::NfAbsNS)(a::fmpz) = K(parent(K.pol[1])(a))

(K::NfAbsNS)(a::fmpq) = K(parent(K.pol[1])(a))

(K::NfAbsNS)() = zero(K)

################################################################################
#
#  Unary operators
#
################################################################################

function Base.:(-)(a::NfAbsNSElem)
  return parent(a)(-data(a))
end

################################################################################
#
#  Binary operators
#
################################################################################

function Base.:(+)(a::NfAbsNSElem, b::NfAbsNSElem)
  return parent(a)(data(a) + data(b))
end

function Base.:(-)(a::NfAbsNSElem, b::NfAbsNSElem)
  return parent(a)(data(a) - data(b))
end

function Base.:(*)(a::NfAbsNSElem, b::NfAbsNSElem)
  return parent(a)(data(a) * data(b))
end

function Base.:(//)(a::NfAbsNSElem, b::NfAbsNSElem)
  return div(a, b)
end

function Nemo.div(a::NfAbsNSElem, b::NfAbsNSElem)
  return a * inv(b)
end

Nemo.divexact(a::NfAbsNSElem, b::NfAbsNSElem) = div(a, b)

################################################################################
#
#  Powering
#
################################################################################

function Base.:(^)(a::NfAbsNSElem, b::Integer)
  if b < 0
    return inv(a)^(-b)
  elseif b == 0
    return one(parent(a))
  elseif b == 1
    return deepcopy(a)
  elseif mod(b, 2) == 0
    c = a^(div(b, 2))
    return c*c
  elseif mod(b, 2) == 1
    return a^(b - 1)*a
  end
end

function Base.:(^)(a::NfAbsNSElem, b::fmpz)
  if b < 0
    return inv(a)^(-b)
  elseif b == 0
    return one(parent(a))
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

function Base.:(==)(a::NfAbsNSElem, b::NfAbsNSElem)
  reduce!(a)
  reduce!(b)
  return data(a) == data(b)
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function Nemo.mul!(c::NfAbsNSElem, a::NfAbsNSElem, b::NfAbsNSElem)
  mul!(c.data, a.data, b.data)
  c = reduce!(c)
  return c
end

function Nemo.addeq!(b::NfAbsNSElem, a::NfAbsNSElem)
  addeq!(b.data, a.data)
  b = reduce!(b)
  return b
end

###############################################################################
# other stuff, trivia and non-trivia
###############################################################################

function total_degree(f::fmpq_mpoly)
  return Int(maximum(degree(f, i) for i=1:nvars(parent(f))))
end

################################################################################
#
#  Conversion to matrix
#
################################################################################

function elem_to_mat_row!(M::fmpq_mat, i::Int, a::NfAbsNSElem)
  K = parent(a)
  for j in 1:cols(M)
    M[i, j] = zero(FlintQQ)
  end
  adata = data(a)
  for j in 1:length(adata)
    exps = Nemo._get_termexp_ui(adata, j)
    k = monomial_to_index(parent(a), exps)
    M[i, k] = coeff(adata, j)
  end
  return M
end

function elem_from_mat_row(K::NfAbsNS, M::fmpq_mat, i::Int)
  a = K()
  b = basis(K)
  for c = 1:cols(M)
    a += M[i, c]*b[c]
  end
  return a
end

function SRow(a::NfAbsNSElem)
  sr = SRow(FlintQQ)
  adata = data(a)
  for i=1:length(adata)
    # TODO: Do this inplace with preallocated exps array
    exps = Nemo._get_termexp_ui(adata, i)
    push!(sr.pos, monomial_to_index(parent(a), exps))
    push!(sr.values, coeff(adata, i))
  end
  p = sortperm(sr.pos)
  sr.pos = sr.pos[p]
  sr.values = sr.values[p]
  return sr
end

function minpoly_dense(a::NfAbsNSElem)
  K = parent(a)
  n = degree(K)
  M = zero_matrix(FlintQQ, degree(K)+1, degree(K))
  z = a^0
  elem_to_mat_row!(M, 1, z)
  z *= a
  elem_to_mat_row!(M, 2, z)
  i = 2
  while true
    if n % (i-1) == 0 && rank(M) < i
      N = nullspace(sub(M, 1:i, 1:cols(M))')
      @assert N[1] == 1
      f = PolynomialRing(FlintQQ,"t", cached=false)[1]([N[2][j, 1] for j=1:i])
      return f*inv(lead(f))
    end
    z *= a
    elem_to_mat_row!(M, i+1, z)
    i += 1
  end
end

function minpoly_sparse(a::NfAbsNSElem)
  K = parent(a)
  n = degree(K)
  M = SMat(FlintQQ)
  z = a^0
  sz = SRow(z)
  i = 0
  push!(sz.values, FlintQQ(1))
  push!(sz.pos, n+i+1)
  push!(M, sz)
  z *= a
  sz = SRow(z)
  i = 1
  while true
    if n % i == 0
      echelon!(M)
      fl, so = cansolve_ut(sub(M, 1:i, 1:n), sz)
      if fl
        so = mul(so, sub(M, 1:i, n+1:cols(M)))
        Qt, t = PolynomialRing(FlintQQ, "t", cached = false)
        # TH: If so is the zero vector, we cannot use the iteration,
        # so we do it by hand.
        if length(so.pos) == 0
          f = t^i
        else
          f = t^i - sum(c*t^(k-1) for (k,c) = so)
        end
        return f
      end
    end  
    push!(sz.values, FlintQQ(1))
    push!(sz.pos, n+i+1)
    push!(M, sz)
    z *= a
    sz = SRow(z)
    i += 1
    if i > degree(parent(a))
      error("too large")
    end
  end
end

function minpoly(a::NfAbsNSElem)
  return minpoly_sparse(a)
end

function inv(a::NfAbsNSElem)
  if iszero(a)
    error("division by zero")
  end
  f = minpoly(a)
  z = coeff(f, degree(f))
  for i=degree(f)-1:-1:1
    z = z*a + coeff(f, i)
  end
  return -z*inv(coeff(f, 0))
end

function charpoly(a::NfAbsNSElem)
  f = minpoly(a)
  return f^div(degree(parent(a)), degree(f))
end

function norm(a::NfAbsNSElem)
  f = minpoly(a)
  return (-1)^degree(parent(a)) * coeff(f, 0)^div(degree(parent(a)), degree(f))
end

function trace(a::NfAbsNSElem)
  f = minpoly(a)
  return -coeff(f, degree(f)-1)*div(degree(parent(a)), degree(f))
end

function representation_matrix(a::NfAbsNSElem)
  K = parent(a)
  b = basis(K)
  M = zero_matrix(FlintQQ, degree(K), degree(K))
  for i=1:degree(K)
    elem_to_mat_row!(M, i, a*b[i])
  end
  return M
end


function msubst(f::fmpq_mpoly, v::Array{NfAbsNSElem, 1})
  n = length(v)
  @assert n == ngens(parent(f))
  r = FlintQQ()
  for i=1:length(f)
    r += f.coeffs[i]*prod(v[j]^f.exps[j, i] for j=1:n)
  end
  return r
end
