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

order_type(K::NfRelNS{T}) where {T} = NfRelOrd{T, fractional_ideal_type(order_type(base_field(K))), NfRelNSElem{T}}

order_type(::Type{NfRelNS{T}}) where {T} = NfRelOrd{T, fractional_ideal_type(order_type(parent_type(T))), NfRelNSElem{T}}

function Nemo.iszero(a::NfRelNSElem)
  return iszero(data(a))
end

function Nemo.isone(a::NfRelNSElem)
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
#  Field access
#
################################################################################

@inline base_field(a::NfRelNS{T}) where {T} = a.base_ring::parent_type(T)

@inline Nemo.data(a::NfRelNSElem) = a.data

@inline Nemo.parent(a::NfRelNSElem{T}) where {T} = a.parent::NfRelNS{T}

is_simple(a::NfRelNS) = false

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
  print(io, "non-simple Relative number field with defining polynomials ", a.pol)
  print(io, " \n over ", base_field(a))
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

function NumberField(f::Vector{Generic.Poly{T}}, s::String="_\$"; cached::Bool = false, check::Bool = true) where T
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
  K = base_field(L)
  Kx, _ = PolynomialRing(K, "x", cached = false)
  pols = fmpq_poly[map_coefficients(FlintQQ, to_univariate(Kx, x), parent = Hecke.Globals.Qx) for x in L.pol]
  return number_field(pols, cached = false, check = false)
end

Nemo.gens(K::NfRelNS) = [K(x) for x = gens(parent(K.pol[1]))]

function (K::NfRelNS{T})(a::Generic.MPoly{T}) where T
  q, w = divrem(a, K.pol)
  z = NfRelNSElem{T}(w)
  z.parent = K
  return z
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

function Base.:(-)(a::NfRelNSElem{T}) where T
  z = NfRelNSElem{T}(-data(a))
  z.parent = parent(a)
  return z
  #return parent(a)(-data(a))
end

################################################################################
#
#  Binary operators
#
################################################################################

function Base.:(+)(a::NfRelNSElem{T}, b::NfRelNSElem{T}) where {T}
  parent(a) == parent(b) || force_op(+, a, b)::NfRelNSElem{T}
  z = NfRelNSElem{T}(data(a) + data(b))
  z.parent = parent(a)
  return z
end

function Base.:(-)(a::NfRelNSElem{T}, b::NfRelNSElem{T}) where {T}
  parent(a) == parent(b) || force_op(-, a, b)::NfRelNSElem{T}
  z = NfRelNSElem{T}(data(a) - data(b))
  z.parent = parent(a)
  return z
end

function Base.:(*)(a::NfRelNSElem{T}, b::NfRelNSElem{T}) where {T}
  parent(a) == parent(b) || force_op(+, a, b)::NfRelNSElem{T}
  return parent(a)(data(a) * data(b))
end

function Base.:(*)(a::NfRelNSElem{T}, b::Union{Int, fmpz}) where {T}
  z = NfRelNSElem{T}(data(a)*b)
  z.parent = parent(a)
  return z
end

function Base.:(//)(a::NfRelNSElem{T}, b::NfRelNSElem{T}) where {T}
  return div(a, b)
end

function Base.div(a::NfRelNSElem{T}, b::NfRelNSElem{T}) where {T}
  parent(a) == parent(b) || force_op(div, a, b)::NfRelNSElem{T}
  return a*inv(b)
end

Nemo.divexact(a::NfRelNSElem, b::NfRelNSElem; check::Bool = true) = div(a, b)

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
    mul!(c, c, c)
    return c
  else
    c = a^(b - 1)
    mul!(c, c, a)
    return c
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
    mul!(c, c, c)
    return c
  else
    c = a^(b - 1)
    mul!(c, c, a)
    return c
  end
end

################################################################################
#
#  Comparison
#
################################################################################

function Base.:(==)(a::NfRelNSElem{T}, b::NfRelNSElem{T}) where T
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

function Nemo.mul!(c::NfRelNSElem{T}, a::NfRelNSElem{T}, b::Union{Int, fmpz}) where {T}
  return a*b
end

function Nemo.addeq!(b::NfRelNSElem{T}, a::NfRelNSElem{T}) where {T}
  addeq!(b.data, a.data)
  return b
end

function Nemo.add!(c::NfRelNSElem{T}, a::NfRelNSElem{T}, b::NfRelNSElem{T}) where {T}
  c.data = add!(c.data, a.data, b.data)
  return c
end

function Base.hash(a::NfRelNSElem{nf_elem}, b::UInt)
  return hash(a.data, b)
end

###############################################################################
# other stuff, trivia and non-trivia
###############################################################################

function dot(v::Vector{T}, v1::Vector{fmpz}) where T <: NfRelNSElem
  @assert length(v) == length(v1)
  el = data(v[1])*v1[1]
  for j = 2:length(v)
    el += data(v[j])*v1[j]
  end
  z = T(el)
  z.parent = parent(v[1])
  return z
end

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

function basis(K::NfRelNS)
  k = base_field(K)
  kxy = parent(K.pol[1])
  B = Vector{elem_type(K)}(undef, degree(K))
  d = degrees(K)
  I = cartesian_product_iterator([0:d[i]-1 for i = 1:length(d)], inplace = true)
  for (i, e) in enumerate(I)
    t = kxy()
    setcoeff!(t, e, one(k))
    B[i] = K(t)
  end
  return B
end

function coefficients(a::NfRelNSElem; copy = false)
  L = parent(a)
  K = base_field(L)
  v = Vector{elem_type(K)}(undef, degree(L))
  for j = 1:degree(L)
    v[j] = zero(K)
  end
  for j = 1:length(a.data)
    v[monomial_to_index(j, a)] = a.data.coeffs[j]
  end
  return v
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
  K = parent(a)
  for j=1:ncols(M)
    M[i, j] = zero(base_field(K))
  end
  for j = 1:length(a.data)
    M[i, monomial_to_index(j, a)] = a.data.coeffs[j]
  end
  return nothing
end

function elem_from_mat_row(K::NfRelNS{T}, M::Generic.Mat{T}, i::Int) where T
  a = K()
  t = K()
  b = basis(K)
  for c = 1:ncols(M)
    a = a + M[i, c]*b[c]
  end
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
      return f*inv(leading_coefficient(f))
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
  push!(M, SRow(z))
  z *= a
  sz = SRow(z)
  i = 1
  kt, t = PolynomialRing(k, "t", cached = false)
  f = kt()
  while true
    if n % i == 0
      fl, so = can_solve_with_solution(M, sz)
      if fl
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
  K = base_field(L)
  Kx, _ = PolynomialRing(K, "x", cached = false)
  for i = 1:n
    pol = L.pol[i]
    d = total_degree(pol)
    if d == 1
      v = Vector{T}(undef, d-1)
      traces[i] = v
      continue
    end
    traces[i] = polynomial_to_power_sums(to_univariate(Kx, pol), d-1)
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
  @hassert :NfRel 9001 res == tr_via_minpoly(a)
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
  bnew = map_coefficients(x -> mod(x, p), b, parent = Kx)
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

function primitive_element(K::NfRelNS)
  g = gens(K)
  n = length(g)
  if n == 1
    return g[1]
  elseif lcm([total_degree(K.pol[i]) for i = 1:n]) == degree(K)
    return sum(g[i] for i = 1:n)
  end
  #TODO: Write a modular test for primitiveness
  pe = g[1]
  f = minpoly(pe)
  for i = 2:n
    pe += g[i]
    f = minpoly(pe)
    while degree(f) < prod(total_degree(K.pol[k]) for k=1:i)
      pe += g[i]
      f = minpoly(pe)
    end
  end
  return pe
end

function simple_extension(K::NfRelNS{T}; simplified::Bool = false, cached = true) where {T}
  if simplified
    return simplified_simple_extension(K; cached = cached)
  end
  n = ngens(K)
  g = gens(K)
  if n == 1
    kx, _ = PolynomialRing(base_field(K), "x", cached = false)
    p = to_univariate(kx, K.pol[1])
    Ks, gKs = number_field(p, cached = cached, check = false)
    return Ks, hom(Ks, K, g[1], inverse = [gKs])
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
  emb = Vector{NfRelElem{T}}(undef, n)
  for i = 1:n
    elem_to_mat_row!(N, 1, g[i])
    s = solve(transpose(M), transpose(N))
    emb[i] = zero(Ka)
    for j = 1:degree(Ka)
      emb[i] += b1[j]*s[j, 1]
    end
  end

  return Ka, hom(Ka, K, pe, inverse = emb)
end


#trivia, missing in NfRel
function basis(K::NfRel)
  a = gen(K)
  z = one(K)
  b = elem_type(K)[z, a]
  while length(b) < degree(K)
    push!(b, b[end]*a)
  end
  return b
end

function (K::NfRelNS)(a::Vector)
  return dot(a, basis(K))
end

function Base.one(a::NfRelElem)
  return one(parent(a))
end

function Base.copy(a::NfRelElem)
  return parent(a)(a.data)
end

function Nemo.discriminant(K::NfRelNS)
  kx, _ = PolynomialRing(base_field(K), "x", cached = false)
  p = [to_univariate(kx, x) for x = K.pol]
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

absolute_discriminant(K::NfRelNS) = discriminant(K, FlintQQ)

