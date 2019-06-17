################################################################################
#
#  NfRel/NfRel_ns.jl : non-simple relative fields
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

export NfRel_ns, simple_extension

#= trivial example
Qx, x = PolynomialRing(FlintQQ)
QQ = number_field(x-1)[1]
QQt, t = QQ["t"]
K, gK = number_field([t^2-2, t^2-3, t^2-5, t^2-7])
[ minpoly(x) for x = gK]
S, mS = Hecke.simple_extension(K)
mS(gen(S))
mS\gens(K)[2]
=#

#to make the MPoly module happy, divrem needs it...
function Nemo.div(a::nf_elem, b::nf_elem)
  return a//b
end

function Nemo.rem(a::nf_elem, b::nf_elem)
  return parent(a)(0)
end

#non-simple fields are quotients by multivariate polynomials
#this could be extended to arbitrary zero-dimensional quotients, but
#I don't need this here.

#mostly copied from NfRel I am afraid..

################################################################################
#
#  Copy
#
################################################################################

function Base.deepcopy_internal(a::NfRel_nsElem{T}, dict::IdDict) where T
  z = NfRel_nsElem{T}(Base.deepcopy_internal(data(a), dict))
  z.parent = parent(a)
  return z
end

#julia's a^i needs copy
function Base.copy(a::NfRel_nsElem)
  return parent(a)(a.data)
end

################################################################################
#
#  Comply with Nemo ring interface
#
################################################################################

Nemo.elem_type(::Type{NfRel_ns{T}}) where {T} = NfRel_nsElem{T}

Nemo.elem_type(::NfRel_ns{T}) where {T} = NfRel_nsElem{T}

Nemo.parent_type(::Type{NfRel_nsElem{T}}) where {T} = NfRel_ns{T}

order_type(K::NfRel_ns{T}) where {T} = NfRelOrd{T, frac_ideal_type(order_type(base_field(K)))}

order_type(::Type{NfRel_ns{T}}) where {T} = NfRelOrd{T, frac_ideal_type(order_type(parent_type(T)))}

Nemo.needs_parentheses(::NfRel_nsElem) = true

Nemo.isnegative(x::NfRel_nsElem) = Nemo.isnegative(data(x))

Nemo.show_minus_one(::Type{NfRel_nsElem{T}}) where {T} = true

function Nemo.iszero(a::NfRel_nsElem)
  reduce!(a)
  return iszero(data(a))
end

function Nemo.isone(a::NfRel_nsElem)
  reduce!(a)
  return isone(data(a))
end

Nemo.zero(K::NfRel_ns) = K(Nemo.zero(parent(K.pol[1])))

Nemo.one(K::NfRel_ns) = K(Nemo.one(parent(K.pol[1])))

Nemo.one(a::NfRel_nsElem) = one(a.parent)

(K::NfRel_ns{T})(a::NfRel_nsElem) where {T} = a

################################################################################
#
#  Promotion
#
################################################################################

Nemo.promote_rule(::Type{NfRel_nsElem{S}}, ::Type{T}) where {T <: Integer, S} = NfRel_nsElem{S}

Nemo.promote_rule(::Type{NfRel_nsElem{T}}, ::Type{fmpz}) where {T <: Nemo.RingElement} = NfRel_nsElem{T}

Nemo.promote_rule(::Type{NfRel_nsElem{T}}, ::Type{fmpq}) where {T <: Nemo.RingElement} = NfRel_nsElem{T}

Nemo.promote_rule(::Type{NfRel_nsElem{T}}, ::Type{T}) where {T} = NfRel_nsElem{T}

Nemo.promote_rule(::Type{NfRel_nsElem{T}}, ::Type{NfRel_nsElem{T}}) where T <: Nemo.RingElement = NfRel_nsElem{T}

function Nemo.promote_rule(::Type{NfRel_nsElem{T}}, ::Type{U}) where {T <: Nemo.RingElement, U <: Nemo.RingElement}
  Nemo.promote_rule(T, U) == T ? NfRel_nsElem{T} : Union{}
end

################################################################################
#
#  Field access
#
################################################################################

@inline base_field(a::NfRel_ns{T}) where {T} = a.base_ring::parent_type(T)

@inline Nemo.data(a::NfRel_nsElem) = a.data

@inline Nemo.parent(a::NfRel_nsElem{T}) where {T} = a.parent::NfRel_ns{T}

issimple(a::NfRel_ns) = false

################################################################################
#
#  Reduction
#
################################################################################

function reduce!(a::NfRel_nsElem)
  q, a.data = divrem(a.data, parent(a).pol)
  return a
end
 
################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, a::NfRel_ns)
  print(io, "non-simple Relative number field over\n")
  print(io, base_field(a), "\n")
  print(io, " with defining polynomials ", a.pol)
end

#TODO: this is a terrible show func.
function Base.show(io::IO, a::NfRel_nsElem)
  f = data(a)
  AbstractAlgebra.Generic._show(io, f, [string(s) for s = a.parent.S])
  return nothing
end

################################################################################
#
#  Constructors and parent object overloading
#
################################################################################
@doc Markdown.doc"""
    number_field(f::Array{Generic.Poly{T}, 1}, s::String="_\$") where T -> NfRel_ns

Given polynomials $f = (f_1, \ldots, f_n)$ over some number field $k$, construct
$K = k[t_1, \ldots, t_n]/\langle f_1(t_1), \ldots, f_n(t_n)\rangle$
The ideal in the quotient must be maximal - although this is not tested.
"""
function Nemo.NumberField(f::Array{Generic.Poly{T}, 1}, s::String="_\$"; cached::Bool = false, check::Bool = false) where T
  S = Symbol(s)
  R = base_ring(f[1])
  Rx, x = PolynomialRing(R, length(f), s)
  K = NfRel_ns(f, [f[i](x[i]) for i=1:length(f)], [Symbol("$s$i") for i=1:length(f)])
  return K, gens(K)
end

Nemo.gens(K::NfRel_ns) = [K(x) for x = gens(parent(K.pol[1]))]

function (K::NfRel_ns{T})(a::Generic.MPoly{T}) where T
  q, w = divrem(a, K.pol)
  z = NfRel_nsElem{T}(w)
  z.parent = K
  return z
end

function (K::NfRel_ns{T})(a::T) where T
  parent(a) != base_ring(parent(K.pol[1])) == error("Cannot coerce")
  z = NfRel_nsElem{T}(parent(K.pol[1])(a))
  z.parent = K
  return z
end

function (K::NfRel_ns{T})(a::NfRel_nsElem{T}) where T
  parent(a) != K == error("Cannot coerce")
  return a
end

(K::NfRel_ns)(a::Integer) = K(parent(K.pol[1])(a))

(K::NfRel_ns)(a::Rational{T}) where {T <: Integer} = K(parent(K.pol[1])(a))

(K::NfRel_ns)(a::fmpz) = K(parent(K.pol[1])(a))

(K::NfRel_ns)(a::fmpq) = K(parent(K.pol[1])(a))

(K::NfRel_ns)() = zero(K)

Nemo.gen(K::NfRel_ns) = K(Nemo.gen(parent(K.pol[1])))

################################################################################
#
#  Unary operators
#
################################################################################

function Base.:(-)(a::NfRel_nsElem)
  return parent(a)(-data(a))
end

################################################################################
#
#  Binary operators
#
################################################################################

function Base.:(+)(a::NfRel_nsElem{T}, b::NfRel_nsElem{T}) where {T}
  return parent(a)(data(a) + data(b))
end

function Base.:(-)(a::NfRel_nsElem{T}, b::NfRel_nsElem{T}) where {T}
  return parent(a)(data(a) - data(b))
end

function Base.:(*)(a::NfRel_nsElem{T}, b::NfRel_nsElem{T}) where {T}
  return parent(a)(data(a) * data(b))
end

function Base.:(//)(a::NfRel_nsElem{T}, b::NfRel_nsElem{T}) where {T}
  return div(a, b)
end

function Nemo.div(a::NfRel_nsElem{T}, b::NfRel_nsElem{T}) where {T}
  return a*inv(b)
end

Nemo.divexact(a::NfRel_nsElem, b::NfRel_nsElem) = div(a, b)
################################################################################
#
#  Powering
#
################################################################################
#via julia

function Base.:(^)(a::NfRel_nsElem{T}, b::Integer) where T 
  if b < 0
    return inv(a)^(-b)
  elseif b == 0
    return one(parent(a))
  elseif b == 1
    return deepcopy(a)
  elseif mod(b, 2) == 0
    c = a^(div(b, 2))
    return c*c
  else mod(b, 2) == 1
    return a^(b - 1)*a
  end
end

function Base.:(^)(a::NfRel_nsElem{T}, b::fmpz) where T
  if b < 0
    return inv(a)^(-b)
  elseif b == 0
    return parent(a)(1)
  elseif b == 1
    return deepcopy(a)
  elseif mod(b, 2) == 0
    c = a^(div(b, 2))
    return c*c
  else mod(b, 2) == 1
    return a^(b - 1)*a
  end
end

################################################################################
#
#  Comparison
#
################################################################################

function Base.:(==)(a::NfRel_nsElem{T}, b::NfRel_nsElem{T}) where T
  reduce!(a)
  reduce!(b)
  return data(a) == data(b)
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function Nemo.mul!(c::NfRel_nsElem{T}, a::NfRel_nsElem{T}, b::NfRel_nsElem{T}) where {T}
  mul!(c.data, a.data, b.data)
  c = reduce!(c)
  return c
end

function Nemo.addeq!(b::NfRel_nsElem{T}, a::NfRel_nsElem{T}) where {T}
  addeq!(b.data, a.data)
  b = reduce!(b)
  return b
end

function Base.hash(a::NfRel_nsElem{nf_elem}, b::UInt)
  reduce!(a)
  return hash(a.data, b)
end

###############################################################################
# other stuff, trivia and non-trivia
###############################################################################

function Nemo.degree(K::NfRel_ns)
  return prod([total_degree(x) for x=K.pol])
end

function (R::Generic.PolyRing{nf_elem})(f::Generic.MPoly)
  if length(f)==0
    return R()
  end
  j = 1
  c = 0
  while j<= ngens(parent(f))
    if f.exps[j, 1] != 0
      if c==0
        c = j
      else 
        error("poly is not univariate")
      end
    end
    j += 1
  end
  g = R()
  for i=1:length(f)
    setcoeff!(g, Int(f.exps[c, i]), f.coeffs[i])
  end
  return g
end

#non-optimal...
function basis(K::NfRel_ns)
  b = NfRel_nsElem[]
  g = gens(K)
  for i=CartesianIndices(Tuple(1:total_degree(f) for f = K.pol))
    push!(b, prod(g[j]^(i[j]-1) for j=1:length(i)))
  end
  return b
end

function basis_mat(a::Vector{NfRel_nsElem{T}}) where {T <: NumFieldElem}
  @assert length(a) > 0
  K = parent(a[1])
  M = zero_matrix(base_field(K), length(a), degree(K))
  for i in 1:length(a)
    elem_to_mat_row!(M, i, a[i])
  end
  return M
end

function elem_to_mat_row!(M::Generic.Mat{T}, i::Int, a::NfRel_nsElem{T}) where T
  a.parent
  K = parent(a)
  #C = CartesianIndices(Tuple(0:total_degree(f)-1 for f = K.pol))
  #L = LinearIndices(C)
  #CC = [UInt[c[i] for i=length(K.pol):-1:1] for c = C]
  for j=1:ncols(M)
    M[i, j] = zero(base_field(K))
  end
  for j=1:length(a.data)
    #p = findfirst(isequal(a.data.exps[:, j]), CC)
    #@assert p !== nothing
    M[i, monomial_to_index(j, a)] = a.data.coeffs[j]
  end
end

function elem_from_mat_row(K::NfRel_ns{T}, M::Generic.Mat{T}, i::Int) where T
  a = K()
  t = K()
  b = basis(K)
  for c = 1:ncols(M)
    a.parent = K
    b[c].parent = K
    a = a + M[i, c]*b[c]
    b[c].parent
  end
  a.parent
  return a
end

function monomial_to_index(i::Int, a::NfRel_nsElem)
  K = parent(a)
  n = ngens(K)
  idx = a.data.exps[1, i]
  for j=2:n
    idx *= total_degree(K.pol[n - j + 1])
    idx += a.data.exps[j, i]
  end
  return Int(idx+1)
end

function SRow(a::NfRel_nsElem)
  sr = SRow(base_field(parent(a)))
  for i=1:length(a.data)
    push!(sr.pos, monomial_to_index(i, a))
    push!(sr.values, a.data.coeffs[i])
  end
  p = sortperm(sr.pos)
  sr.pos = sr.pos[p]
  sr.values = sr.values[p]
  return sr
end

function SRow(a::NfRelElem)
  sr = SRow(base_field(parent(a)))
  for i=0:length(a.data)
    c = coeff(a.data, i)
    if !iszero(c)
      push!(sr.pos, i+1)
      push!(sr.values, c)
    end  
  end
  return sr
end
  
function minpoly_dense(a::NfRel_nsElem)
  K = parent(a)
  n = degree(K)
  k = base_field(K)
  M = zero_matrix(k, degree(K)+1, degree(K))
  z = one(K)
  elem_to_mat_row!(M, 1, z)
  z *= a
  elem_to_mat_row!(M, 2, z)
  i = 2
  while true
    if n % (i-1) == 0 && rank(M) < i
      N = nullspace(sub(M, 1:i, 1:ncols(M))')
      @assert N[1] == 1
      f = PolynomialRing(k,"t", cached=false)[1]([N[2][j, 1] for j=1:i])
      return f*inv(lead(f))
    end
    z *= a
    elem_to_mat_row!(M, i+1, z)
    i += 1
  end
end

function Base.Matrix(a::SMat)
  A = zero_matrix(base_ring(a), nrows(a), ncols(a))
  for i = 1:nrows(a)
    for (k, c) = a[i]
      A[i, k] = c
    end
  end
  return A
end  

function minpoly_sparse(a::NfRel_nsElem)
  K = parent(a)
  n = degree(K)
  k = base_field(K)
  M = sparse_matrix(k)
  z = one(K)
  sz = SRow(z)
  i = 0
  push!(sz.values, k(1))
  push!(sz.pos, n+i+1)
  push!(M, sz)
  z *= a
  sz = SRow(z)
  i = 1
  kt, t = PolynomialRing(k, "t", cached = false)
  f = kt()
  while true
    if n % i == 0
      echelon!(M)
      fl, so = can_solve_ut(sub(M, 1:i, 1:n), sz)
      if fl
        so = mul(so, sub(M, 1:i, n+1:ncols(M)))
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
    push!(sz.values, k(1))
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

function minpoly(a::NfRel_nsElem)
  return minpoly_sparse(a)
end

function minpoly(a::NfRel_nsElem{nf_elem}, ::FlintRationalField)
  f = minpoly(a)
  n = norm(f)
  g = gcd(n, derivative(n))
  if isone(g)
    return n
  end
  n = divexact(n, g)
  return n
end

absolute_minpoly(a::NfRel_nsElem{nf_elem}) = minpoly(a, FlintQQ)

function inv(a::NfRel_nsElem)
  if iszero(a)
    error("division by zero")
  end
  K = parent(a)
  f = minpoly(a)
  z = K(coeff(f, degree(f)))
  for i=degree(f)-1:-1:1
    z = z*a + coeff(f, i)
  end
  return -z*inv(coeff(f, 0))
end

function charpoly(a::NfRel_nsElem)
  f = minpoly(a)
  return f^div(degree(parent(a)), degree(f))
end

function norm(a::NfRel_nsElem)
  f = minpoly(a)
  return (-1)^degree(parent(a)) * coeff(f, 0)^div(degree(parent(a)), degree(f))
end

function tr(a::NfRel_nsElem)
  f = minpoly(a)
  return -coeff(f, degree(f)-1)*div(degree(parent(a)), degree(f))
end

#TODO: also provide a sparse version
function representation_matrix(a::NfRel_nsElem)
  K = parent(a)
  b = basis(K)
  k = base_field(K)
  M = zero_matrix(k, degree(K), degree(K))
  for i=1:degree(K)
    elem_to_mat_row!(M, i, a*b[i])
  end
  return M
end

@inline ngens(K::NfRel_ns) = length(K.pol)

mutable struct NfRelToNfRel_nsMor{T} <: Map{NfRel{T}, NfRel_ns{T}, HeckeMap, NfRelToNfRel_nsMor}
  header::MapHeader{NfRel{T}, NfRel_ns{T}}
  prim_img::NfRel_nsElem{T}
  emb::Array{NfRelElem{T}, 1}
  coeff_aut::NfToNfMor

  function NfRelToNfRel_nsMor(K::NfRel{T}, L::NfRel_ns{T}, a::NfRel_nsElem{T}, emb::Array{NfRelElem{T}, 1}) where {T}
    function image(x::NfRelElem{T})
      # x is an element of K
      f = data(x)
      # First evaluate the coefficients of f at a to get a polynomial over L
      # Then evaluate at b
      return f(a)
    end

    function preimage(x::NfRel_nsElem{T})
      return msubst(x.data, emb)
    end

    z = new{T}()
    z.prim_img = a
    z.emb = emb
    z.header = MapHeader(K, L, image, preimage)
    return z
  end  

  function NfRelToNfRel_nsMor(K::NfRel{T}, L::NfRel_ns{T}, a::NfRel_nsElem{T}) where {T}
    function image(x::NfRelElem{T})
      # x is an element of K
      f = data(x)
      # First evaluate the coefficients of f at a to get a polynomial over L
      # Then evaluate at b
      return f(a)
    end

    z = new{T}()
    z.prim_img = a
    z.header = MapHeader(K, L, image)
    return z
  end  

  function NfRelToNfRel_nsMor(K::NfRel{T}, L::NfRel_ns{T}, aut::Map, a::NfRel_nsElem{T}) where {T}
    aut = NfToNfMor(domain(aut), codomain(aut), aut(gen(domain(aut))))
    function image(x::NfRelElem{T})
      # x is an element of K
      f = deepcopy(data(x))
      for i=0:degree(f)
        setcoeff!(f, i, aut(coeff(f, i)))
      end
      # First evaluate the coefficients of f at a to get a polynomial over L
      # Then evaluate at b
      return f(a)
    end

    z = new{T}()
    z.prim_img = a
    z.coeff_aut = aut
    z.header = MapHeader(K, L, image)
    return z
  end  


end

mutable struct NfRel_nsToNfRel_nsMor{T} <: Map{NfRel_ns{T}, NfRel_ns{T}, HeckeMap, NfRel_nsToNfRel_nsMor}
  header::MapHeader{NfRel_ns{T}, NfRel_ns{T}}
  emb::Array{NfRel_nsElem{T}, 1}
  coeff_aut::NfToNfMor

  function NfRel_nsToNfRel_nsMor(K::NfRel_ns{T}, L::NfRel_ns{T}, emb::Array{NfRel_nsElem{T}, 1}) where {T}
    function image(x::NfRel_nsElem{T})
      # x is an element of K
      # First evaluate the coefficients of f at a to get a polynomial over L
      # Then evaluate at b
      return msubst(x.data, emb)
    end

    z = new{T}()
    z.coeff_aut = id_hom(base_field(K))
    z.emb = emb
    z.header = MapHeader(K, L, image)
    return z
  end  

  function NfRel_nsToNfRel_nsMor(K::NfRel_ns{T}, L::NfRel_ns{T}, aut::Map, emb::Array{NfRel_nsElem{T}, 1}) where {T}
    function image(x::NfRel_nsElem{T})
      # x is an element of K
      # First evaluate the coefficients of f at a to get a polynomial over L
      # Then evaluate at b
      f = x.data
      Kbxyz = parent(f)
      k = nvars(Kbxyz)
      Lbxyz = PolynomialRing(base_field(L), k)[1]
      coeffs = Vector{T}(undef, length(f.coeffs))
      for i = 1:length(coeffs)
        coeffs[i] = aut(f.coeffs[i])
      end
      g = Lbxyz(coeffs, f.exps)
      return msubst(g, emb)
    end

    z = new{T}()
    z.emb = emb
    z.coeff_aut = aut
    z.header = MapHeader(K, L, image)
    return z
  end  
end

id_hom(K::NfRel_ns) = NfRel_nsToNfRel_nsMor(K, K, gens(K))

function Base.hash(f::NfRel_nsToNfRel_nsMor{T}, u::UInt64) where T
  #I combine the hash functions for the automorphism of the base field and the hash function for the images of the generators.
  a = hash(f.coeff_aut, u)
  for i = 1:length(f.emb)
    a = hash(f.emb[i], a)
  end
  return a
end

function Base.:(*)(f::NfRel_nsToNfRel_nsMor{T}, g::NfRel_nsToNfRel_nsMor{T}) where {T}
  codomain(f) == domain(g) || throw("Maps not compatible")

  a = gens(domain(g))
  return NfRel_nsToNfRel_nsMor(domain(g), codomain(f), f.coeff_aut * g.coeff_aut, [ g(f(x)) for x in a])
end

function Base.:(==)(f::NfRel_nsToNfRel_nsMor{T}, g::NfRel_nsToNfRel_nsMor{T}) where {T}
  if domain(f) != domain(g) || codomain(f) != codomain(g)
    return false
  end

  L = domain(f)
  K = base_field(L)

  if f.coeff_aut.prim_img != g.coeff_aut.prim_img
    return false
  end

  for i = 1:ngens(L)
    if f.emb[i] != g.emb[i]
      return false
    end
  end

  return true
end

@inline ngens(R::Nemo.Generic.MPolyRing) = R.num_vars

function _prod(A, b)
  for a in A
    b = b * a
  end
  return b
end

#aparently, should be called evaluate, talk to Bill...
#definitely non-optimal, in particular for automorphisms
function msubst(f::Generic.MPoly{T}, v::Array{NfRelElem{T}, 1}) where T
  k = base_ring(parent(f))
  n = length(v)
  @assert n == ngens(parent(f))
  r = zero(parent(v[1]))
  L = parent(v[1])
  for i=1:length(f)
    #@show prod(v[j]^f.exps[j, i] for j=1:n)
    s = _prod((v[j]^f.exps[n - j + 1, i] for j=1:n), one(L))
    r += f.coeffs[i]* s
  end
  return r
end
function msubst(f::Generic.MPoly{T}, v::Array{NfRel_nsElem{T}, 1}) where T
  k = base_ring(parent(f))
  n = length(v)
  @assert n == ngens(parent(f))
  r = zero(k)
  for i=1:length(f)
    r += f.coeffs[i]*prod(v[j]^f.exps[n - j + 1, i] for j=1:n)
  end
  return r
end


#find isomorphic simple field AND the map
@doc Markdown.doc"""
    simple_extension(K::NfRel_ns{nf_elem}) -> NfRel, Map

Compute a simple field L as an extension of the base field of K and an isomorphism
between L and K 

"""
function simple_extension(K::NfRel_ns{T}) where {T}
  n = ngens(K)
  g = gens(K)
  if n == 1
    fl, p = isunivariate(K.pol[1])
    Ks, gKs = number_field(p, cached = false, check = false)
    return Ks, NfRelToNfRel_nsMor(Ks, K, g[1], [gKs])
  end
  if lcm([total_degree(K.pol[i]) for i = 1:length(K.pol)]) == degree(K)
    #The sum of the primitive elements is the right element
    pe = sum(g[i] for i = 1:length(g))
    f = minpoly(pe)
  else
    pe = g[1]
    i = 1
    f = minpoly(pe)
    #todo: use resultants rather than minpoly??
    while i < n
      i += 1
      pe += g[i]
      f = minpoly(pe)
      while degree(f) < prod(total_degree(K.pol[k]) for k=1:i)
        pe += g[i]
        f = minpoly(pe)
      end
    end
  end
  Ka, a = number_field(f, check = false)
  k = base_field(K)
  M = zero_matrix(k, degree(K), degree(K))
  z = one(K)
  elem_to_mat_row!(M, 1, z)
  elem_to_mat_row!(M, 2, pe)
  mul!(z, z, pe)
  for i=3:degree(K)
    mul!(z, z, pe)
    elem_to_mat_row!(M, i, z)
  end
  N = zero_matrix(k, 1, degree(K))
  b1 = basis(Ka)
  emb = Array{NfRelElem{T}, 1}(undef, n)
  for i = 1:n
    elem_to_mat_row!(N, 1, g[i])
    s = solve(M', N')
    emb[i] = zero(Ka)
    for j = 1:degree(Ka)
      emb[i] += b1[j]*s[j, 1]
    end
  end

  return Ka, NfRelToNfRel_nsMor(Ka, K, pe, emb)
end

@doc Markdown.doc"""
    simple_extension(K::NfRel_ns{nf_elem}, FlintQQ) -> AnticNumberField, Map, Map

    absolute_field(K::NfRel_ns{nf_elem}) -> AnticNumberField, Map, Map

Compute an isomorphic field as an extension of $Q$ together with the isomorphism 
(1st map) and the embedding of the base field (2nd map).
"""
function simple_extension(K::NfRel_ns{nf_elem}, ::FlintRationalField)
  Ks, mp = simple_extension(K)
  Ka, m1, m2 = absolute_field(Ks)
  return Ka, m1*mp, m2
end

absolute_field(K::NfRel_ns{nf_elem}) = simple_extension(K, FlintQQ)

#trivia, missing in NfRel
function basis(K::NfRel)
  a = gen(K)
  z = one(K)
  b = [z, a]
  while length(b) < degree(K)
    push!(b, b[end]*a)
  end
  return b
end  

function Base.one(a::NfRelElem)
  return one(parent(a))
end

function Base.copy(a::NfRelElem)
  return parent(a)(a.data)
end

function Nemo.discriminant(K::NfRel_ns)
  p = [isunivariate(x)[2] for x = K.pol]
  d = discriminant(p[1])
  n = degree(p[1])
  for i=2:length(p)
    d = d^degree(p[i]) * discriminant(p[i])^n
    n *= degree(p[i])
  end
  return d
end

function Nemo.discriminant(K::NfRel_ns, ::FlintRationalField)
  d = norm(discriminant(K)) * discriminant(base_field(K))^degree(K)
  return d
end
