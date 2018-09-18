################################################################################
#
#  NfAbs/NonSimple.jl : non-simple absolute number fields
#
# This file is part of Hecke.
#
# Copyright (c) 2015, 2016, 2017, 2018: Claus Fieker, Tommy Hofmann
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
#  Copyright (C) 2018 Tommy Hofmann, Claus Fieker
#
################################################################################

export NfAbsNS, NfAbsNSElem

export issimple, simple_extension

@inline base_ring(K::NfAbsNS) = FlintQQ

@inline degree(K::NfAbsNS) = K.degree

@inline degrees(K::NfAbsNS) = K.degrees

@inline ngens(K::NfAbsNS) = length(K.pol)

function _get_maximal_order(K::NfAbsNS)
  if isdefined(K, :O)
    return K.O
  else
    throw(AccessorNotSetError())
  end
end

function _set_maximal_order(K::NfAbsNS, O::NfAbsOrd{NfAbsNS, NfAbsNSElem})
  K.O = O
end

################################################################################
#
#  Copy
#
################################################################################

function Base.deepcopy_internal(a::NfAbsNSElem, dict::IdDict)
  # TODO: Fix this once deepcopy is fixed for fmpq_mpoly
  # z = NfAbsNSElem(Base.deepcopy_internal(data(a), dict))
  z = NfAbsNSElem(Base.deepcopy(data(a)))
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

dot(a::NfAbsNSElem, b::Union{Integer, fmpz}) = a * b

dot(a::Union{Integer, fmpz}, b::NfAbsNSElem) = b * a

################################################################################
#
#  Random
#
################################################################################

function rand(K::NfAbsNS, r::UnitRange)
  # TODO: This is super slow
  b = basis(K)
  z = K()
  for i in 1:degree(K)
    z += rand(r) * b[i]
  end
  return z
end

################################################################################
#
#  Promotion
#
################################################################################

Nemo.promote_rule(::Type{NfAbsNSElem}, ::Type{T}) where {T <: Integer} = NfAbsNSElem

Nemo.promote_rule(::Type{NfAbsNSElem}, ::Type{fmpz}) = NfAbsNSElem

Nemo.promote_rule(::Type{NfAbsNSElem}, ::Type{fmpq}) = NfAbsNSElem

function Nemo.promote_rule(::Type{NfAbsNSElem}, ::Type{U}) where {U <: Nemo.RingElement}
  Nemo.promote_rule(fmpq, U) == fmpq ? NfAbsNSElem : Union{}
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
    return copy(K.basis)::Vector{NfAbsNSElem}
  else
    g = gens(K)
    b = NfAbsNSElem[]
    for i in CartesianIndices(Tuple(1:degrees(K)[i] for i in 1:ngens(K)))
      push!(b, prod(g[j]^(i[j] - 1) for j=1:length(i)))
    end
    K.basis = b
    return copy(b)::Vector{NfAbsNSElem}
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
  else#if mod(b, 2) == 1
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
  else# mod(b, 2) == 1
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

function Nemo.add!(c::NfAbsNSElem, a::NfAbsNSElem, b::NfAbsNSElem)
  add!(c.data, a.data, b.data)
  c = reduce!(c)
  return c
end

function Nemo.addeq!(b::NfAbsNSElem, a::NfAbsNSElem)
  addeq!(b.data, a.data)
  b = reduce!(b)
  return b
end

#

function Nemo.mul!(c::NfAbsNSElem, a::NfAbsNSElem, b::fmpz)
  mul!(c.data, a.data, parent(c.data)(b))
  c = reduce!(c)
  return c
end

################################################################################
#
#  Conversion to matrix
#
################################################################################

function elem_to_mat_row!(M::fmpz_mat, i::Int, d::fmpz, a::NfAbsNSElem)
  K = parent(a)
  # TODO: This is super bad
  # Proper implementation needs access to the content of the underlying
  # fmpq_mpoly

  for j in 1:cols(M)
    M[i, j] = zero(FlintZZ)
  end

  one!(d)

  if length(data(a)) == 0
    return nothing
  end

  z = zero_matrix(FlintQQ, 1, cols(M))
  elem_to_mat_row!(z, 1, a)
  z_q = FakeFmpqMat(z)

  for j in 1:cols(M)
    M[i, j] = z_q.num[1, j]
  end

  ccall((:fmpz_set, :libflint), Nothing, (Ref{fmpz}, Ref{fmpz}), d, z_q.den)

  return nothing
end

function elem_to_mat_row!(M::fmpq_mat, i::Int, a::NfAbsNSElem)
  K = parent(a)
  for j in 1:cols(M)
    M[i, j] = zero(FlintQQ)
  end
  adata = data(a)
  for j in 1:length(adata)
    exps = Nemo._get_termexp_ui(adata, j)
    k = monomial_to_index(K, exps)
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

function elem_from_mat_row(K::NfAbsNS, M::fmpz_mat, i::Int, d::fmpz)
  a = K()
  b = basis(K)
  for c = 1:cols(M)
    a += M[i, c]*b[c]
  end
  return divexact(a, d)
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

################################################################################
#
#  Minimal polynomial
#
################################################################################

function minpoly_dense(a::NfAbsNSElem)
  K = parent(a)
  n = degree(K)
  M = zero_matrix(FlintQQ, degree(K)+1, degree(K))
  z = a^0
  elem_to_mat_row!(M, 1, z)
  z *= a
  elem_to_mat_row!(M, 2, z)
  i = 2
  Qt, _ = PolynomialRing(FlintQQ,"t", cached=false)
  while true
    if n % (i-1) == 0 && rank(M) < i
      N = nullspace(sub(M, 1:i, 1:cols(M))')
      @assert N[1] == 1
      v = Vector{fmpq}(undef, i)
      for j in 1:i
        v[j] = N[2][j, 1]
      end
      #f = Qt([N[2][j, 1] for j=1:i])
      f = Qt(v)
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
  M = sparse_matrix(FlintQQ)
  z = a^0
  sz = SRow(z)
  i = 0
  push!(sz.values, FlintQQ(1))
  push!(sz.pos, n+i+1)
  push!(M, sz)
  z *= a
  sz = SRow(z)
  i = 1
  Qt, t = PolynomialRing(FlintQQ, "t", cached = false)
  while true
    if n % i == 0
      echelon!(M)
      fl, so = cansolve_ut(sub(M, 1:i, 1:n), sz)
      if fl
        so = mul(so, sub(M, 1:i, n+1:cols(M)))
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

################################################################################
#
#  Characteristic polynomial
#
################################################################################

function charpoly(a::NfAbsNSElem)
  f = minpoly(a)
  return f^div(degree(parent(a)), degree(f))
end

################################################################################
#
#  Inverse
#
################################################################################

function inv(a::NfAbsNSElem)
  if iszero(a)
    error("division by zero")
  end
  f = minpoly(a)
  z = parent(a)(coeff(f, degree(f)))
  for i=degree(f)-1:-1:1
    z = z*a + coeff(f, i)
  end
  return -z*inv(coeff(f, 0))
end

################################################################################
#
#  Norm
#
################################################################################

function norm(a::NfAbsNSElem)
  f = minpoly(a)
  return (-1)^degree(parent(a)) * coeff(f, 0)^div(degree(parent(a)), degree(f))
end

################################################################################
#
#  Trace
#
################################################################################

function tr(a::NfAbsNSElem)
  f = minpoly(a)
  return -coeff(f, degree(f)-1)*div(degree(parent(a)), degree(f))
end

################################################################################
#
#  Representation matrix
#
################################################################################

function representation_matrix(a::NfAbsNSElem)
  K = parent(a)
  b = basis(K)
  M = zero_matrix(FlintQQ, degree(K), degree(K))
  for i=1:degree(K)
    elem_to_mat_row!(M, i, a*b[i])
  end
  return M
end

function representation_matrix_q(a::NfAbsNSElem)
  M = representation_matrix(a)
  # TODO: This is suboptimal.
  Mf = FakeFmpqMat(M)
  return Mf.num, Mf.den
end

################################################################################
#
#  Substitution
#
################################################################################

# TODO: Preallocate the exps array
function msubst(f::fmpq_mpoly, v::Array{T, 1}) where {T}
  n = length(v)
  @assert n == nvars(parent(f))
  r = FlintQQ()
  for i=1:length(f)
    exps = Nemo._get_termexp_ui(f, i)
    r += coeff(f, i) * prod(v[j]^exps[j] for j=1:n)
  end
  return r
end

################################################################################
#
#  Morphisms
#
################################################################################

mutable struct NfAbsToNfAbsNS <: Map{AnticNumberField, NfAbsNS, HeckeMap, NfAbsToNfAbsNS}
  header::MapHeader{AnticNumberField, NfAbsNS}
  prim_img::NfAbsNSElem
  emb::Array{nf_elem, 1}

  function NfAbsToNfAbsNS(K::AnticNumberField, L::NfAbsNS, a::NfAbsNSElem, emb::Array{nf_elem, 1})
    function image(x::nf_elem)
      # x is an element of K
      f = x.parent.pol.parent(x)
      return f(a)
    end

    function preimage(x::NfAbsNSElem)
      return msubst(data(x), emb)
    end

    z = new()
    z.prim_img = a
    z.emb = emb
    z.header = MapHeader(K, L, image, preimage)
    return z
  end  

  function NfAbsToNfAbsNS(K::AnticNumberField, L::NfAbsNS, a::NfAbsNSElem)
    function image(x::nf_elem)
      # x is an element of K
      f = x.parent.pol.parent(x)
      return f(a)
    end

    z = new()
    z.prim_img = a
    z.header = MapHeader(K, L, image)
    return z
  end  
end

mutable struct NfAbsNSToNfAbsNS <: Map{NfAbsNS, NfAbsNS, HeckeMap, NfAbsNSToNfAbsNS}
  header::MapHeader{NfAbsNS, NfAbsNS}
  emb::Array{NfAbsNSElem, 1}

  function NfAbsNSToNfAbsNS(K::NfAbsNS, L::NfAbsNS, emb::Array{NfAbsNSElem, 1})
    function image(x::NfAbsNSElem)
      # x is an element of K
      return msubst(data(x), emb)
    end

    z = new()
    z.emb = emb
    z.header = MapHeader(K, L, image)
    return z
  end  
end

# TODO: The following is opposite to our new convention
function Base.:(*)(f::NfAbsNSToNfAbsNS, g::NfAbsNSToNfAbsNS)
  domain(f) == codomain(g) || throw("Maps not compatible")
  a = gens(domain(g))
  return NfAbsNSToNfAbsNS(domain(g), codomain(f), [ f(g(x)) for x in a])
end

function Base.:(==)(f::NfAbsNSToNfAbsNS, g::NfAbsNSToNfAbsNS)
  if domain(f) != domain(g) || codomain(f) != codomain(g)
    return false
  end

  L = domain(f)

  for a in gens(L)
    if f(a) != g(a)
      return false
    end
  end

  return true
end

################################################################################
#
#  Simple extensions
#
################################################################################
@doc Markdown.doc"""
    simple_extension(K::NfAbsNS) -> AnticNumberField, Map
> For a non-simple extension $K$ of $Q$, find a primitive element and thus
> an isomorphic simple extension of $Q$. The map realises this isomorphism.
"""
function simple_extension(K::NfAbsNS)
  n = ngens(K)
  g = gens(K)

  pe = g[1]
  i = 1
  ind = Int[1]
  f = minpoly(pe)
  #TODO: use resultants rather than minpoly??
  while i < n
    i += 1
    j = 1
    f = minpoly(pe + j * g[i])
    while degree(f) < prod(total_degree(K.pol[k]) for k in 1:i)
      j += 1
      f = minpoly(pe + j * g[i])
    end
    push!(ind, j)
    pe += j * g[i]
  end
  Ka, a = number_field(f)
  k = base_ring(K)
  M = zero_matrix(k, degree(K), degree(K))
  z = one(K)
  elem_to_mat_row!(M, 1, z)
  elem_to_mat_row!(M, 2, pe)
  z *= pe
  for i=3:degree(K)
    z *= pe
    elem_to_mat_row!(M, i, z)
  end
  N = zero_matrix(k, 1, degree(K))
  b = basis(Ka)
  emb = typeof(b)()
  for i=1:n
    elem_to_mat_row!(N, 1, g[i])
    s = solve(M', N')
    push!(emb, sum(b[j] * s[j,1] for j in 1:degree(Ka)))
  end

  return Ka, NfAbsToNfAbsNS(Ka, K, pe, emb)
end

################################################################################
#
#  Composite of linearly disjoint fields
#
################################################################################

function islinearly_disjoint(K1::AnticNumberField, K2::AnticNumberField)
  
  if gcd(degree(K1), degree(K2)) == 1
    return true
  end
  d1 = numerator(discriminant(K1.pol))
  d2 = numerator(discriminant(K2.pol))
  if gcd(d1, d2) == 1
    return true
  end
  #= 
  #TODO: if the maximal orders are known, this is a better condition 
  O1 = maximal_order(K1)
  O2 = maximal_order(K2)
  if gcd(discriminant(O1), discriminant(O2)) == 1
    return true
  end
  =#
  
  K2t, t = PolynomialRing(K2, "t", cached= false)
  ft = K2t(K1.pol)
  return isirreducible(ft)
  
end


function NumberField(K1::AnticNumberField, K2::AnticNumberField; cached::Bool = false, check::Bool = false)

  if check
    #I have to check that the fields are linearly disjoint
    @assert islinearly_disjoint(K1, K2)
  end
  
  K , l= number_field([K1.pol, K2.pol], "_\$")
  mp1 = NfAbsToNfAbsNS(K1, K, l[1])
  mp2 = NfAbsToNfAbsNS(K2, K, l[2])
  return K, mp1, mp2

end

################################################################################
#
#  Constructors and parent object overloading
#
################################################################################

@doc Markdown.doc"""
    number_field(f::Array{fmpq_poly, 1}, s::String="_\$") -> NfAbsNS
> Let $f = (f_1, \ldots, f_n)$ be univariate rational polynomials, then
> we construct 
 $$K = Q[t_1, \ldots, t_n]/\langle f_1(t_1), \ldots, f_n(t_n)\rangle$$
> The ideal bust be maximal, however, this is not tested.
"""
function NumberField(f::Array{fmpq_poly, 1}, s::String="_\$"; cached::Bool = false, check::Bool = false)
  S = Symbol(s)
  n = length(f)
  Qx, x = PolynomialRing(FlintQQ, n, s)
  K = NfAbsNS(fmpq_mpoly[f[i](x[i]) for i=1:n],
              Symbol[Symbol("$s$i") for i=1:n], cached)
  K.degrees = [degree(f[i]) for i in 1:n]
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
