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
function Base.div(a::nf_elem, b::nf_elem)
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

function zero!(a::NfRelNSElem)
  zero!(a.data)
  return a
end

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

function AbstractAlgebra.expressify(a::NfRelNSElem; context = nothing)
  return AbstractAlgebra.expressify(data(a), a.parent.S; context = context)
end

function Base.show(io::IO, a::NfRelNSElem)
  print(io, AbstractAlgebra.obj_to_string(a, context = io))
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

function number_field(::Type{NfAbsNS}, L::NfRelNS{nf_elem})
  @assert degree(base_field(L)) == 1
  Qx = PolynomialRing(FlintQQ, "x", cached = false)[1]
  pols = fmpq_poly[map_coeffs(FlintQQ, isunivariate(x)[2], parent = Qx) for x in L.pol]
  return number_field(pols, cached = false, check = false)
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

function Base.div(a::NfRelNSElem{T}, b::NfRelNSElem{T}) where {T}
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
  for j=1:ncols(M)
    M[i, j] = zero(base_field(K))
  end
  for j = 1:length(a.data)
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

function resultant(f::MPolyElem, g::MPolyElem, i::Int)
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

function simple_extension(K::NfRelNS{T}; cached = true) where {T}
  n = ngens(K)
  g = gens(K)
  if n == 1
    fl, p = isunivariate(K.pol[1])
    Ks, gKs = number_field(p, cached = cached, check = false)
    return Ks, hom(Ks, K, g[1], [gKs])
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
  Ka, a = number_field(f, cached = cached,  check = false)
  k = base_field(K)
  M = zero_matrix(k, degree(K), degree(K))
  z = one(K)
  elem_to_mat_row!(M, 1, z)
  elem_to_mat_row!(M, 2, pe)
  mul!(z, z, pe)
  for i = 3:degree(K)
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

  return Ka, hom(Ka, K, pe, emb)
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

function _sieve_primitive_elements(B::Vector{T}) where T <: NumFieldElem
  K = parent(B[1])
  n = absolute_degree(K)
  B1 = typeof(B)()
  k = div(n, 2)
  for x in B
    c = conjugates_arb(x, 16)
    @show c[1:k+1]
    isprimitive = true
    for i = 2:k+1
      for j = 1:i-1
        if overlaps(c[i], c[j])
          isprimitive = false
          break
        end
      end
      if !isprimitive
        break
      end
    end
    if isprimitive
      push!(B1, x)
    end
  end
  @show [absolute_minpoly(x) for x in B1]
  return B1
end

function _find_prime(L::NfRelNS{nf_elem})
  p = 2^10
  K = base_field(L)
  OK = maximal_order(K)
  OL = maximal_order(L)

  n_attempts = min(degree(L), 10)
  candidates = Vector{Tuple{NfOrdIdl, Int}}(undef, n_attempts)
  i = 1
  pols = L.pol
  threshold = absolute_degree(L)^2
  polsR = Vector{fq_poly}(undef, length(pols))
  while i < n_attempts+1
    p = next_prime(p)
    if isindex_divisor(OK, p)
      continue
    end
    lp = prime_decomposition(OK, p)
    P = lp[1][1]
    if isindex_divisor(OL, P)
      continue
    end
    F, mF = ResidueField(OK, P)
    mF1 = extend_easy(mF, K)
    is_proj = true
    for j = 1:length(pols)
      fF = isunivariate(map_coeffs(mF1, pols[j]))[2]
      if degree(fF) != total_degree(pols[j]) || !issquarefree(fF)
        is_proj = false
        break
      end
      polsR[j] = fF
    end
    if !is_proj
      continue
    end
    d = 1
    for j = 1:length(polsR)
      FS = factor_shape(polsR[j])
      d1 = lcm(Int[x for (x, v) in FS])
      d = lcm(d, d1)
    end
    if d < threshold
      candidates[i] = (P, d)
      i += 1
    end
  end
  res = candidates[1]
  for j = 2:n_attempts
    if candidates[j][2] < res[2]
      res = candidates[j]
    end
  end
  return res[1], res[2]
end

function _sieve_primitive_elements(B::Vector{NfRelNSElem{nf_elem}})
  Lrel = parent(B[1])
  #First, we choose the candidates
  Bnew = NfRelNSElem{nf_elem}[]
  nrep = min(3, absolute_degree(Lrel))
  for i = 1:length(B)
    push!(Bnew, B[i])
    for j = 1:nrep
      if i != j
        push!(Bnew, B[i]+B[j])
        push!(Bnew, B[i]-B[j])
      end
    end
  end
  #Now, we test for primitiveness.
  K = base_field(Lrel)
  OK = maximal_order(K)
  Zx = ZZ["x"][1]

  n = absolute_degree(Lrel)

  P, d = _find_prime(Lrel)
  p = minimum(P, copy = false)
  abs_deg = degree(P)*d
  #First, we search for elements that are primitive using block systems
  Fp = GF(p, cached = false)
  Fpx = PolynomialRing(Fp, cached = false)[1]
  F = FlintFiniteField(p, abs_deg, "w", cached = false)[1]
  Fx = PolynomialRing(F, cached = false)[1]
  rt_base_field = roots(Zx(K.pol), F)
  rt = Dict{fq, Vector{Vector{fq}}}()
  Rxy = PolynomialRing(F, ngens(Lrel), cached = false)[1]
  tmp = Fpx()
  for r in rt_base_field
    vr = Vector{Vector{fq}}()
    for f in Lrel.pol
      g = isunivariate(f)[2]
      coeff_gF = fq[]
      for i = 0:degree(g)
        nf_elem_to_gfp_fmpz_poly!(tmp, coeff(g, i))
        push!(coeff_gF, evaluate(tmp, r))
      end
      gF = Fx(coeff_gF)
      push!(vr, roots(gF))
    end
    rt[r] = vr
  end
  rt1 = Dict{fq, Vector{Vector{fq}}}()
  ind = 1
  nconjs_needed = div(n, 2)+1
  for (r, v) in rt
    rtv = Vector{Vector{fq}}()
    for i in CartesianIndices(Tuple(1:length(v[i]) for i in 1:length(v)))
      push!(rtv, [v[j][i[j]] for j = 1:length(v)])
      ind += 1
      if ind > nconjs_needed
        break
      end
    end
    rt1[r] = rtv
    if ind > nconjs_needed
      break
    end
  end
  indices = Int[]
  for i = 1:length(Bnew)
    if length(vars(Bnew[i].data)) < ngens(Lrel)
      continue
    end
    if _is_primitive_via_block(Bnew[i], rt1, Rxy, tmp)
      push!(indices, i)
    end
  end
  return Bnew[indices]
end




function _is_primitive_via_block(a::NfRelNSElem{nf_elem}, rt::Dict{fq, Vector{Vector{fq}}}, Rxy, tmp)
  n = degree(parent(a))
  pol = data(a)
  conjs = Set{fq}()
  for (r, vr) in rt
    ctx = MPolyBuildCtx(Rxy)
    for (c, v) in zip(coeffs(pol), exponent_vectors(pol))
      nf_elem_to_gfp_fmpz_poly!(tmp, c)
      push_term!(ctx, evaluate(tmp, r), v)
    end
    g = finish(ctx)
    for i = 1:length(vr)
      ev = evaluate(g, vr[i])
      if ev in conjs
        return false
      end
      push!(conjs, ev)
    end
  end
  return true
end


function simplified_absolute_field(L::NfRelNS; cached = false)
  OL = maximal_order(L)
  B = lll_basis(OL)
  B1 = _sieve_primitive_elements(B)
  a = B1[1]
  I = t2(a)
  for i = 2:min(50, length(B1))
    J = t2(B1[i])
    if J < I
      a = B1[i]
      I = J
    end
  end
  f = absolute_minpoly(a)
  @assert degree(f) == absolute_degree(L)
  K = number_field(f, check = false, cached = cached)[1]
  mp = hom(K, L, a)
  return K, mp
end
