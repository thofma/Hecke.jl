################################################################################
#
#  NfRel/NfRelNS.jl : non-simple relative fields
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

export NfRelNS, simple_extension

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

function Base.deepcopy_internal(a::NfRelNSElem{T}, dict::IdDict) where T
  z = NfRelNSElem{T}(Base.deepcopy_internal(data(a), dict))
  z.parent = parent(a)
  return z
end

#julia's a^i needs copy
function Base.copy(a::NfRelNSElem)
  return parent(a)(a.data)
end

################################################################################
#
#  Comply with Nemo ring interface
#
################################################################################

Nemo.elem_type(::Type{NfRelNS{T}}) where {T} = NfRelNSElem{T}

Nemo.elem_type(::NfRelNS{T}) where {T} = NfRelNSElem{T}

Nemo.parent_type(::Type{NfRelNSElem{T}}) where {T} = NfRelNS{T}

order_type(K::NfRelNS{T}) where {T} = NfRelOrd{T, fractional_ideal_type(order_type(base_field(K)))}

order_type(::Type{NfRelNS{T}}) where {T} = NfRelOrd{T, fractional_ideal_type(order_type(parent_type(T)))}

Nemo.needs_parentheses(::NfRelNSElem) = true

Nemo.isnegative(x::NfRelNSElem) = Nemo.isnegative(data(x))

Nemo.show_minus_one(::Type{NfRelNSElem{T}}) where {T} = true

function Nemo.iszero(a::NfRelNSElem)
  reduce!(a)
  return iszero(data(a))
end

function Nemo.isone(a::NfRelNSElem)
  reduce!(a)
  return isone(data(a))
end

Nemo.zero(K::NfRelNS) = K(Nemo.zero(parent(K.pol[1])))

Nemo.one(K::NfRelNS) = K(Nemo.one(parent(K.pol[1])))

Nemo.one(a::NfRelNSElem) = one(a.parent)

(K::NfRelNS{T})(a::NfRelNSElem) where {T} = a

################################################################################
#
#  Promotion
#
################################################################################

Nemo.promote_rule(::Type{NfRelNSElem{S}}, ::Type{T}) where {T <: Integer, S} = NfRelNSElem{S}

Nemo.promote_rule(::Type{NfRelNSElem{T}}, ::Type{fmpz}) where {T <: Nemo.RingElement} = NfRelNSElem{T}

Nemo.promote_rule(::Type{NfRelNSElem{T}}, ::Type{fmpq}) where {T <: Nemo.RingElement} = NfRelNSElem{T}

Nemo.promote_rule(::Type{NfRelNSElem{T}}, ::Type{T}) where {T} = NfRelNSElem{T}

Nemo.promote_rule(::Type{NfRelNSElem{T}}, ::Type{NfRelNSElem{T}}) where T <: Nemo.RingElement = NfRelNSElem{T}

function Nemo.promote_rule(::Type{NfRelNSElem{T}}, ::Type{U}) where {T <: Nemo.RingElement, U <: Nemo.RingElement}
  Nemo.promote_rule(T, U) == T ? NfRelNSElem{T} : Union{}
end

################################################################################
#
#  Field access
#
################################################################################

@inline base_field(a::NfRelNS{T}) where {T} = a.base_ring::parent_type(T)

@inline Nemo.data(a::NfRelNSElem) = a.data

@inline Nemo.parent(a::NfRelNSElem{T}) where {T} = a.parent::NfRelNS{T}

issimple(a::NfRelNS) = false

################################################################################
#
#  Reduction
#
################################################################################

function reduce!(a::NfRelNSElem)
  q, a.data = divrem(a.data, parent(a).pol)
  return a
end
 
################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, a::NfRelNS)
  print(io, "non-simple Relative number field over\n")
  print(io, base_field(a), "\n")
  print(io, " with defining polynomials ", a.pol)
end

#TODO: this is a terrible show func.
function Base.show(io::IO, a::NfRelNSElem)
  f = data(a)
  AbstractAlgebra.Generic._show(io, f, [string(s) for s = a.parent.S])
  return nothing
end

################################################################################
#
#  Constructors and parent object overloading
#
################################################################################

function NumberField(f::Array{Generic.Poly{T}, 1}, s::String="_\$"; cached::Bool = false, check::Bool = true) where T
  S = Symbol(s)
  R = base_ring(f[1])
  Rx, x = PolynomialRing(R, length(f), s)
  K = NfRelNS(f, [f[i](x[i]) for i=1:length(f)], [Symbol("$s$i") for i=1:length(f)])
  if check
    if !_check_consistency(K)
      error("The fields are not linearly disjoint!")
    end
  end
  return K, gens(K)
end

Nemo.gens(K::NfRelNS) = [K(x) for x = gens(parent(K.pol[1]))]

function (K::NfRelNS{T})(a::Generic.MPoly{T}) where T
  q, w = divrem(a, K.pol)
  z = NfRelNSElem{T}(w)
  z.parent = K
  return z
end

function (K::NfRelNS{T})(a::T) where T
  parent(a) != base_ring(parent(K.pol[1])) == error("Cannot coerce")
  z = NfRelNSElem{T}(parent(K.pol[1])(a))
  z.parent = K
  return z
end

function (K::NfRelNS{T})(a::NfRelNSElem{T}) where T
  parent(a) != K == error("Cannot coerce")
  return a
end

(K::NfRelNS)(a::Integer) = K(parent(K.pol[1])(a))

(K::NfRelNS)(a::Rational{T}) where {T <: Integer} = K(parent(K.pol[1])(a))

(K::NfRelNS)(a::fmpz) = K(parent(K.pol[1])(a))

(K::NfRelNS)(a::fmpq) = K(parent(K.pol[1])(a))

(K::NfRelNS)() = zero(K)

Nemo.gen(K::NfRelNS) = K(Nemo.gen(parent(K.pol[1])))

################################################################################
#
#  Unary operators
#
################################################################################

function Base.:(-)(a::NfRelNSElem)
  return parent(a)(-data(a))
end

################################################################################
#
#  Binary operators
#
################################################################################

function Base.:(+)(a::NfRelNSElem{T}, b::NfRelNSElem{T}) where {T}
  parent(a) == parent(b) || force_op(+, a, b)::NfRelNSElem{T}
  return parent(a)(data(a) + data(b))
end

function Base.:(-)(a::NfRelNSElem{T}, b::NfRelNSElem{T}) where {T}
  parent(a) == parent(b) || force_op(-, a, b)::NfRelNSElem{T}
  return parent(a)(data(a) - data(b))
end

function Base.:(*)(a::NfRelNSElem{T}, b::NfRelNSElem{T}) where {T}
  parent(a) == parent(b) || force_op(+, a, b)::NfRelNSElem{T}
  return parent(a)(data(a) * data(b))
end

function Base.:(//)(a::NfRelNSElem{T}, b::NfRelNSElem{T}) where {T}
  return div(a, b)
end

function Nemo.div(a::NfRelNSElem{T}, b::NfRelNSElem{T}) where {T}
  parent(a) == parent(b) || force_op(div, a, b)::NfRelNSElem{T}
  return a*inv(b)
end

Nemo.divexact(a::NfRelNSElem, b::NfRelNSElem) = div(a, b)
################################################################################
#
#  Powering
#
################################################################################
#via julia

function Base.:(^)(a::NfRelNSElem{T}, b::Integer) where T 
  if b < 0
    return inv(a)^(-b)
  elseif b == 0
    return one(parent(a))
  elseif b == 1
    return deepcopy(a)
  elseif mod(b, 2) == 0
    c = a^(div(b, 2))
    return c*c
  else 
    return a^(b - 1)*a
  end
end

function Base.:(^)(a::NfRelNSElem{T}, b::fmpz) where T
  if b < 0
    return inv(a)^(-b)
  elseif b == 0
    return parent(a)(1)
  elseif b == 1
    return deepcopy(a)
  elseif mod(b, 2) == 0
    c = a^(div(b, 2))
    return c*c
  else 
    return a^(b - 1)*a
  end
end

################################################################################
#
#  Comparison
#
################################################################################

function Base.:(==)(a::NfRelNSElem{T}, b::NfRelNSElem{T}) where T
  reduce!(a)
  reduce!(b)
  parent(a) == parent(b) || force_op(==, a, b)::Bool
  return data(a) == data(b)
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function Nemo.mul!(c::NfRelNSElem{T}, a::NfRelNSElem{T}, b::NfRelNSElem{T}) where {T}
  mul!(c.data, a.data, b.data)
  c = reduce!(c)
  return c
end

function Nemo.mul!(c::NfRelNSElem{T}, a::NfRelNSElem{T}, b::Int) where {T}
  return a*b
end

function Nemo.addeq!(b::NfRelNSElem{T}, a::NfRelNSElem{T}) where {T}
  addeq!(b.data, a.data)
  b = reduce!(b)
  return b
end

function Nemo.add!(c::NfRelNSElem{T}, a::NfRelNSElem{T}, b::NfRelNSElem{T}) where {T}
  c.data = add!(c.data, a.data, b.data)
  c = reduce!(c)
  return c
end

function Base.hash(a::NfRelNSElem{nf_elem}, b::UInt)
  reduce!(a)
  return hash(a.data, b)
end

###############################################################################
# other stuff, trivia and non-trivia
###############################################################################

function Nemo.degree(K::NfRelNS)
  return prod(Int[total_degree(x) for x=K.pol])
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
function basis(K::NfRelNS)
  pols = K.pol
  gL = gens(K)
  B = Vector{elem_type(K)}(undef, degree(K))
  B[1] = one(K)
  ind = total_degree(pols[1])
  genjj = gL[1]
  for i = 2:ind
    B[i] = genjj*B[i-1]
  end
  for jj = 2:length(pols)
    genjj = gL[jj]
    el = deepcopy(genjj)
    new_deg = total_degree(pols[jj])
    for i = 2:new_deg
      for j = 1:ind
        B[(i-1)* ind + j] = B[j]* el 
      end
      mul!(el, el, genjj)
    end
    ind *= new_deg
  end
  return B
end

function basis_matrix(a::Vector{NfRelNSElem{T}}) where {T <: NumFieldElem}
  @assert length(a) > 0
  K = parent(a[1])
  M = zero_matrix(base_field(K), length(a), degree(K))
  for i in 1:length(a)
    elem_to_mat_row!(M, i, a[i])
  end
  return M
end

function elem_to_mat_row!(M::Generic.Mat{T}, i::Int, a::NfRelNSElem{T}) where T
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

function elem_from_mat_row(K::NfRelNS{T}, M::Generic.Mat{T}, i::Int) where T
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

function monomial_to_index(i::Int, a::NfRelNSElem)
  K = parent(a)
  n = ngens(K)
  idx = a.data.exps[1, i]
  for j=2:n
    idx *= total_degree(K.pol[n - j + 1])
    idx += a.data.exps[j, i]
  end
  return Int(idx+1)
end

function SRow(a::NfRelNSElem)
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
  
function minpoly_dense(a::NfRelNSElem)
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

function minpoly_sparse(a::NfRelNSElem)
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

function minpoly(a::NfRelNSElem)
  return minpoly_sparse(a)
end

function minpoly(a::NfRelNSElem{nf_elem}, ::FlintRationalField)
  f = minpoly(a)
  n = norm(f)
  g = gcd(n, derivative(n))
  if isone(g)
    return n
  end
  n = divexact(n, g)
  return n
end

absolute_minpoly(a::NfRelNSElem{nf_elem}) = minpoly(a, FlintQQ)

function inv(a::NfRelNSElem)
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

function charpoly(a::NfRelNSElem)
  f = minpoly(a)
  return f^div(degree(parent(a)), degree(f))
end

function norm(a::NfRelNSElem)
  f = minpoly(a)
  return (-1)^degree(parent(a)) * coeff(f, 0)^div(degree(parent(a)), degree(f))
end


function assure_has_traces(L::NfRelNS{T}) where T
  if isdefined(L, :basis_traces)
    return nothing
  end
  gL = gens(L)
  n = length(gL)
  traces = Vector{Vector{T}}(undef, n)
  for i = 1:n
    pol = L.pol[i]
    v = Vector{T}(undef, total_degree(pol)-1)
    traces[i] = v
    if iszero(length(v))
      continue
    end
    exps = Int[0 for i = 1:n]
    exps[i] = total_degree(pol)-1
    v[1] = -coeff(pol, exps)
    el = gL[i]
    for j = 2:length(v)
      el *= gL[i]
      f_el = minpoly(el)
      v[j] = -divexact(total_degree(pol), degree(f_el))*coeff(f_el, degree(f_el)-1)
    end
  end
  L.basis_traces = traces
  return nothing
end

function tr(a::NfRelNSElem)
  K = parent(a)
  assure_has_traces(K)
  traces = K.basis_traces
  b = data(a)
  pols = K.pol
  n = length(pols)
  res = zero(base_field(K))
  for i = 1:length(b)
    exps = b.exps[:, i]
    temp = b.coeffs[i]
    for j = length(pols):-1:1
      if iszero(exps[j])
        temp *= total_degree(pols[n-j+1])
      else
        temp *= K.basis_traces[n-j+1][exps[j]]
      end
    end
    res += temp
  end
  @hassert :NfRel 1 res == tr_via_minpoly(a)
  return res
end

function tr_via_minpoly(a::NfRelNSElem)
  f = minpoly(a)
  return -coeff(f, degree(f)-1)*div(degree(parent(a)), degree(f))
end

function resultant(f::Generic.MPoly, g::Generic.MPoly, i::Int)
  Kt = parent(f)
  gKt = gens(Kt)
  n = nvars(Kt)
  @assert i <= n
  Ky, gKy = PolynomialRing(base_ring(Kt), n-1, cached = false)
  Kyt, t = PolynomialRing(Ky, "t", cached = false)
  vals = elem_type(Kyt)[]
  for j = 1:n
    if i == j
      push!(vals, t)
    elseif i < j
      push!(vals, Kyt(gKy[j-1]))
    else
      push!(vals, Kyt(gKy[j]))
    end
  end
  fnew = evaluate(f, vals)
  gnew = evaluate(g, vals)
  res = resultant(fnew, gnew)
  new_vals = elem_type(Kt)[]
  for j = 1:n-1
    if j < i
      push!(new_vals, gKt[j])
    else
      push!(new_vals, gKt[j+1])
    end
  end
  return evaluate(res, new_vals)
end

function rand(L::NfRelNS, rg::UnitRange)
  B = absolute_basis(L)
  return rand(B, rg)
end


function mod(a::NfRelNSElem{T}, p::fmpz) where T
  K = parent(a)
  b = data(a)
  Kx = parent(b)
  bnew = map_coeffs(x -> mod(x, p), b, parent = Kx)
  return K(bnew)
end

#TODO: also provide a sparse version
function representation_matrix(a::NfRelNSElem)
  K = parent(a)
  b = basis(K)
  k = base_field(K)
  M = zero_matrix(k, degree(K), degree(K))
  t = zero(K)
  for i=1:degree(K)
    mul!(t, a, b[i])
    elem_to_mat_row!(M, i, t)
  end
  return M
end

@inline ngens(K::NfRelNS) = length(K.pol)

mutable struct NfRelToNfRelNSMor{T} <: Map{NfRel{T}, NfRelNS{T}, HeckeMap, NfRelToNfRelNSMor}
  header::MapHeader{NfRel{T}, NfRelNS{T}}
  prim_img::NfRelNSElem{T}
  emb::Array{NfRelElem{T}, 1}
  coeff_aut::NfToNfMor

  function NfRelToNfRelNSMor(K::NfRel{T}, L::NfRelNS{T}, a::NfRelNSElem{T}, emb::Array{NfRelElem{T}, 1}) where {T}
    function image(x::NfRelElem{T})
      # x is an element of K
      f = data(x)
      # First evaluate the coefficients of f at a to get a polynomial over L
      # Then evaluate at b
      return f(a)
    end

    function preimage(x::NfRelNSElem{T})
      return msubst(x.data, emb)
    end

    z = new{T}()
    z.prim_img = a
    z.emb = emb
    z.header = MapHeader(K, L, image, preimage)
    return z
  end  

  function NfRelToNfRelNSMor(K::NfRel{T}, L::NfRelNS{T}, a::NfRelNSElem{T}) where {T}
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

  function NfRelToNfRelNSMor(K::NfRel{T}, L::NfRelNS{T}, aut::Map, a::NfRelNSElem{T}) where {T}
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

mutable struct NfRelNSToNfRelNSMor{T} <: Map{NfRelNS{T}, NfRelNS{T}, HeckeMap, NfRelNSToNfRelNSMor}
  header::MapHeader{NfRelNS{T}, NfRelNS{T}}
  emb::Array{NfRelNSElem{T}, 1}
  coeff_aut::NfToNfMor

  function NfRelNSToNfRelNSMor(K::NfRelNS{T}, L::NfRelNS{T}, emb::Array{NfRelNSElem{T}, 1}) where {T}
    function image(x::NfRelNSElem{T})
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

  function NfRelNSToNfRelNSMor(K::NfRelNS{T}, L::NfRelNS{T}, aut::NfToNfMor, emb::Array{NfRelNSElem{T}, 1}) where {T}
    function image(x::NfRelNSElem{T})
      # x is an element of K
      # First evaluate the coefficients of f at a to get a polynomial over L
      # Then evaluate at b
      f = x.data
      Kbxyz = parent(f)
      k = nvars(Kbxyz)
      Lbxyz = PolynomialRing(base_field(L), k, cached = false)[1]
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

id_hom(K::NfRelNS) = NfRelNSToNfRelNSMor(K, K, gens(K))


function hom(K::NfRelNSToNfRelNSMor{T}, L::NfRelNSToNfRelNSMor{T}, emb::Array{NfRelNSElem{T}, 1}; check = true) where {T}
  if check && T == nf_elem
    @assert isconsistent(f)
  end
  return NfRelNSToNfRelNSMor(K, L, emb)
end

function hom(K::NfRelNSToNfRelNSMor{nf_elem}, L::NfRelNSToNfRelNSMor{nf_elem}, coeff_aut::NfToNfMor, emb::Array{NfRelNSElem{nf_elem}, 1}; check = true)
  if check 
    @assert isconsistent(f)
  end
  return NfRelNSToNfRelNSMor(K, L, coeff_aut, emb)
end

function Base.hash(f::NfRelNSToNfRelNSMor{T}, u::UInt64) where T
  #I combine the hash functions for the automorphism of the base field and the hash function for the images of the generators.
  a = hash(f.coeff_aut, u)
  for i = 1:length(f.emb)
    a = hash(f.emb[i], a)
  end
  return a
end

function isconsistent(f::NfRelToNfRelMor{nf_elem})
  K = domain(f)
  p = K.pol
  p1 = map_coeffs(f.coeff_aut, p, cached = false)
  if !iszero(p1(f.prim_img))
    error("Wrong")
  end
  return true
end

function isconsistent(f::NfRelNSToNfRelNSMor{nf_elem})  
  K = domain(f)
  for i = 1:length(K.pol)
    p = map_coeffs(f.coeff_aut, K.pol[i])
    if !iszero(msubst(p, f.emb))
      error("wrong!")
    end
  end
  return true
end

function Base.:(*)(f::NfRelNSToNfRelNSMor{T}, g::NfRelNSToNfRelNSMor{T}) where {T}
  codomain(f) == domain(g) || throw("Maps not compatible")

  a = gens(domain(g))
  return NfRelNSToNfRelNSMor(domain(g), codomain(f), f.coeff_aut * g.coeff_aut, [ g(f(x)) for x in a])
end

function Base.:(==)(f::NfRelNSToNfRelNSMor{T}, g::NfRelNSToNfRelNSMor{T}) where {T}
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
function msubst(f::Generic.MPoly{T}, v::Array{NfRelNSElem{T}, 1}) where T
  k = base_ring(parent(f))
  n = length(v)
  @assert n == ngens(parent(f))
  r = zero(k)
  for i=1:length(f)
    r += f.coeffs[i]*prod(v[j]^f.exps[n - j + 1, i] for j=1:n)
  end
  return r
end

function simple_extension(K::NfRelNS{T}) where {T}
  n = ngens(K)
  g = gens(K)
  if n == 1
    fl, p = isunivariate(K.pol[1])
    Ks, gKs = number_field(p, cached = false, check = false)
    return Ks, NfRelToNfRelNSMor(Ks, K, g[1], [gKs])
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

  return Ka, NfRelToNfRelNSMor(Ka, K, pe, emb)
end

@doc Markdown.doc"""
    simple_extension(K::NfRelNS{nf_elem}, FlintQQ) -> AnticNumberField, Map, Map

    absolute_field(K::NfRelNS{nf_elem}) -> AnticNumberField, Map, Map

Compute an isomorphic field as an extension of $Q$ together with the isomorphism 
(1st map) and the embedding of the base field (2nd map).
"""
function simple_extension(K::NfRelNS{nf_elem}, ::FlintRationalField)
  Ks, mp = simple_extension(K)
  Ka, m1, m2 = absolute_field(Ks)
  return Ka, m1*mp, m2
end

absolute_field(K::NfRelNS{nf_elem}) = simple_extension(K, FlintQQ)

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

function Nemo.discriminant(K::NfRelNS)
  p = [isunivariate(x)[2] for x = K.pol]
  d = discriminant(p[1])
  n = degree(p[1])
  for i=2:length(p)
    d = d^degree(p[i]) * discriminant(p[i])^n
    n *= degree(p[i])
  end
  return d
end

function Nemo.discriminant(K::NfRelNS, ::FlintRationalField)
  d = norm(discriminant(K)) * discriminant(base_field(K))^degree(K)
  return d
end


################################################################################
#
#  Permutation group from NfRelNSToNfRelNSMor
#
################################################################################

function _get_poly_from_elem(a::NfRelNSElem{nf_elem}, Qxy)
  K = base_field(parent(a))
  Qx = parent(K.pol)
  p = change_base_ring(a.data, x -> evaluate(Qx(x), gen(Qxy, nvars(Qxy))))
  p1 = evaluate(p, [i for i in 1:ngens(parent(a))], gens(Qxy)[1:end-1])
  res = coeff(p1, [0 for i = 1:nvars(parent(p1))])
  return res
end

function multivariate_from_tower(f::Generic.MPoly{nf_elem}, Qxy)
  M = MPolyBuildCtx(Qxy)
  K = base_ring(f)
  Qx = parent(K.pol)
  cvzip = zip(coeffs(f), exponent_vectors(f))
  for (c, v) in cvzip
    pc = Qx(c)
    for i = degree(pc):-1:0
      cpc = coeff(pc, i)
      if iszero(cpc)
        continue
      end
      vn = vcat(v, i)
      push_term!(M, cpc, vn)
    end
  end
  return finish(M)::fmpq_mpoly
end

function (Rxy::NmodMPolyRing)(f::fmpq_mpoly)
  R = base_ring(Rxy)
  res = change_base_ring(f, x -> divexact(R(numerator(x)), R(denominator(x))), Rxy)
  return res
end

function _get_polys_from_auto(f::NfRelNSToNfRelNSMor{nf_elem}, Qxy)
  res = Vector{elem_type(Qxy)}(undef, nvars(Qxy))
  fK = f.coeff_aut
  ap = fK.prim_img
  K = parent(ap)
  res[nvars(Qxy)] = evaluate(parent(K.pol)(ap), gen(Qxy, nvars(Qxy)))
  for i = 1:nvars(Qxy)-1
    res[i] = multivariate_from_tower(f.emb[i].data, Qxy)
  end
  return res
end

function Base.hash(f::nmod_mpoly, h::UInt)
  return UInt(1)
end

function permutation_group1(G::Vector{NfRelNSToNfRelNSMor{nf_elem}})
  L = domain(G[1])
  K = base_field(L)
  dK = absolute_degree(L)
  d1 = numerator(discriminant(L, FlintQQ))
  p = 2
  while divisible(d1, p)
    p = next_prime(p)
  end
  R = ResidueRing(FlintZZ, p, cached = false)
  Rm, gRm = PolynomialRing(R, ngens(L)+1, cached = false)
  fmod = Vector{nmod_mpoly}(undef, ngens(L)+1)
  RQm, gRQm = PolynomialRing(FlintQQ, ngens(L)+1, cached = false)
  p1 = K.pol
  p1Q = evaluate(p1, gRQm[end])
  fmod[1] = Rm(p1Q)
  for i = 1:ngens(L)
    pp = L.pol[i]
    pp1 = multivariate_from_tower(pp, RQm)
    fmod[i+1] = Rm(pp1)
  end
  permutations = Array{Array{Int, 1},1}(undef, length(G))
  for i = 1:length(G)
    permutations[i] = Vector{Int}(undef, dK)
  end
  pols = Vector{Vector{nmod_mpoly}}(undef, dK)
  pols[1] = gRm
  ind = 2
  gpols = nmod_mpoly[Rm(elel) for elel in _get_polys_from_auto(G[1], RQm)]
  if gpols != gRm
    pols[ind] = gpols
    ind += 1
    gpol = nmod_mpoly[compose_mod(gpols[i], [j for j = 1:nvars(Rm)], pols[2], fmod) for i = 1:length(gpols)]
    while gRm != gpol
      pols[ind] = gpol
      ind += 1
      gpol = nmod_mpoly[compose_mod(gpol[i], [j for j in 1:nvars(Rm)], pols[2], fmod) for i = 1:length(gpols)]
    end
  end
  for i in 2:length(G)
    pi = nmod_mpoly[Rm(x) for x in _get_polys_from_auto(G[i], RQm)]
    if !(pi in pols[1:ind-1])
      previous_order = ind - 1
      pols[ind] = pi
      ind += 1
      for j in 2:previous_order
        pols[ind] = nmod_mpoly[compose_mod(pols[j][s], Int[z for z in 1:nvars(Rm)], pi, fmod) for s = 1:length(pi)]
        ind += 1
      end
      if ind - 1 == dK
        break
      end
      rep_pos = previous_order + 1
      while rep_pos <= ind - 1
        for k in 1:i
          po = nmod_mpoly[Rm(elel) for elel in _get_polys_from_auto(G[k], RQm)]
          att = nmod_mpoly[compose_mod(pols[rep_pos][s], Int[i for i in 1:nvars(Rm)], po, fmod) for s = 1:length(pols[rep_pos])]
          if !(att in pols[1:ind-1])
            pols[ind] = att
            ind += 1
            for j in 2:previous_order
              pols[ind] = nmod_mpoly[compose_mod(pols[j][s], Int[z for z in 1:nvars(Rm)], att, fmod) for s = 1:length(pols[j])]
              ind += 1
            end
            if ind - 1 == dK
              break
            end
          end
        end
        rep_pos = rep_pos + previous_order
      end
    end
  end
  #Now, I have the images mod p
  Dcreation = Vector{Tuple{Vector{nmod_mpoly}, Int}}(undef, length(pols))
  for i = 1:length(pols)
    Dcreation[i] = (pols[i], i)
  end

  gen_pols = Vector{nmod_mpoly}[nmod_mpoly[Rm(y) for y in _get_polys_from_auto(x, RQm)] for x in G]
  D = Dict(Dcreation)
  for s = 1:length(G)
    permutations[s][1] = D[gen_pols[s]]
    for i = 2:length(pols)
      permutations[s][i] = D[nmod_mpoly[compose_mod(gen_pols[s][t], Int[i for i in 1:nvars(Rm)], pols[i], fmod) for t = 1:length(gen_pols[s])]]
    end
  end
  return permutations
end


@doc Markdown.doc"""
    compose_mod(a::AbstractAlgebra.MPolyElem{T}, vars::Vector{Int}, vals::Vector{MPolyElem{T}}, mod::Vector{MPolyElem{T}}) where T <: FieldElement
Evaluate the polynomial by substituting in the supplied values in the array `vals` for
the corresponding variables with indices given by the array `vars`. The evaluation will
succeed if multiplication is defined between elements of the coefficient ring of $a$ and
elements of `vals`. The result will be reduced modulo "mod". If "mod" is a Groebner basis for the ideal 
the elements generate. 
"""
function compose_mod(a::S, vars::Vector{Int}, vals::Vector{S}, mod::Vector{S}) where S <:MPolyElem{T} where T <: RingElem
  unique(vars) != vars && error("Variables not unique")
  length(vars) != length(vals) && error("Number of variables does not match number of values")
  for i = 1:length(vars)
    if vars[i] < 1 || vars[i] > nvars(parent(a))
      error("Variable index not in range")
    end
  end
  if length(vars) == 0
    return a
  end
  powers = Dict{Int, S}[Dict{Int, S}() for i in 1:length(vals)]
  return _compose_mod(a, vars, vals, powers, mod)::S
end

function powmod(a::S, i::Union{Int, fmpz}, modu::Vector{S}) where S <:MPolyElem{T} where T <: RingElem
  if i == 0
    return one(parent(a))
  end
  if i == 1
    b = divrem(a, modu)[2]
    return b
  end
  if mod(i, 2) == 0
    j = div(i, 2)
    b = powmod(a, j, modu)
    b = b*b
    b = divrem(b, modu)[2]
    return b
  end
  b = divrem(a * powmod(a, i - 1, modu), modu)[2]
  return b
end

function mulmod(a::S, b::S, mod::Vector{S}) where S <:MPolyElem{T} where T <: RingElem
  return divrem(a*b, mod)[2]
end


function _compose_mod(a, vars, vals, powers, modu)
  S = parent(a)
  r = AbstractAlgebra.Generic.geobucket(S)
  cvzip = zip(coeffs(a), exponent_vectors(a))
  for (c, v) in cvzip
    t = one(S)
    for j = 1:length(vars)
      varnum = vars[j]
      exp = v[varnum]
      if !haskey(powers[j], exp)
        powers[j][exp] = powmod(vals[j], exp, modu)
      end
      t = mulmod(t, powers[j][exp], modu)
      v[varnum] = 0
    end
    M = MPolyBuildCtx(S)
    push_term!(M, c, v)
    push!(r, mulmod(t, finish(M), modu))
  end
  return finish(r)
end


function change_base_ring(p::MPolyElem{T}, g, new_polynomial_ring) where {T <: RingElement}
  cvzip = zip(coeffs(p), exponent_vectors(p))
  M = MPolyBuildCtx(new_polynomial_ring)
  for (c, v) in cvzip
    res = g(c)
    if !iszero(res)
      push_term!(M, g(c), v)
    end
  end
  return finish(M)::elem_type(new_polynomial_ring)
end
