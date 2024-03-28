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

@inline base_ring(K::AbsNonSimpleNumField) = FlintQQ

@inline base_field(K::AbsNonSimpleNumField) = FlintQQ

@inline degree(K::AbsNonSimpleNumField) = K.degree

@inline degrees(K::AbsNonSimpleNumField) = K.degrees

@inline number_of_generators(K::AbsNonSimpleNumField) = length(K.pol)

function is_maximal_order_known(K::AbsNonSimpleNumField)
  return has_attribute(K, :maximal_order)
end

################################################################################
#
#  Copy
#
################################################################################

function Base.deepcopy_internal(a::AbsNonSimpleNumFieldElem, dict::IdDict)
  # TODO: Fix this once deepcopy is fixed for QQMPolyRingElem
  # z = AbsNonSimpleNumFieldElem(Base.deepcopy_internal(data(a), dict))
  z = AbsNonSimpleNumFieldElem(parent(a), Base.deepcopy(data(a)))
  return z
end

#julia's a^i needs copy
function Base.copy(a::AbsNonSimpleNumFieldElem)
  return parent(a)(a.data)
end

################################################################################
#
#  Comply with Nemo ring interface
#
################################################################################

order_type(::AbsNonSimpleNumField) = AbsNumFieldOrder{AbsNonSimpleNumField, AbsNonSimpleNumFieldElem}

order_type(::Type{AbsNonSimpleNumField}) = AbsNumFieldOrder{AbsNonSimpleNumField, AbsNonSimpleNumFieldElem}

function iszero(a::AbsNonSimpleNumFieldElem)
  reduce!(a)
  return iszero(data(a))
end

function isone(a::AbsNonSimpleNumFieldElem)
  reduce!(a)
  return isone(data(a))
end

Nemo.zero(K::AbsNonSimpleNumField) = K(Nemo.zero(parent(K.pol[1])))

Nemo.one(K::AbsNonSimpleNumField) = K(Nemo.one(parent(K.pol[1])))

Nemo.one(a::AbsNonSimpleNumFieldElem) = one(a.parent)

function Nemo.zero!(a::AbsNonSimpleNumFieldElem)
  a.data = zero(a.data)
  return a
end

function Nemo.one!(a::AbsNonSimpleNumFieldElem)
  a.data = one(a.data)
  return a
end

################################################################################
#
#  Random
#
################################################################################

RandomExtensions.maketype(K::AbsNonSimpleNumField, r) = elem_type(K)

function rand(rng::AbstractRNG, sp::SamplerTrivial{<:Make2{AbsNonSimpleNumFieldElem,AbsNonSimpleNumField,<:AbstractUnitRange}})
  K, r = sp[][1:end]
  # TODO: This is super slow
  b = basis(K, copy = false)
  z::Random.gentype(sp) = K() # type-assert to help inference on Julia 1.0 and 1.1
  for i in 1:degree(K)
    z += rand(rng, r) * b[i]
  end
  return z
end

rand(K::AbsNonSimpleNumField, r::AbstractUnitRange) = rand(GLOBAL_RNG, K, r)
rand(rng::AbstractRNG, K::AbsNonSimpleNumField, r::AbstractUnitRange) = rand(rng, make(K, r))

################################################################################
#
#  Basis matrix
#
################################################################################

function basis_matrix(A::Array{AbsNonSimpleNumFieldElem})
  @assert length(A) > 0
  n = length(A)
  d = degree(parent(A[1]))

  MM = zero_matrix(FlintQQ, n, d)
  for i in 1:n
    elem_to_mat_row!(MM, i, A[i])
  end
  return MM
end

function basis_matrix(A::Vector{AbsNonSimpleNumFieldElem}, ::Type{FakeFmpqMat})
  return FakeFmpqMat(basis_matrix(A))
end

################################################################################
#
#  Field access
#
################################################################################

@inline Nemo.data(a::AbsNonSimpleNumFieldElem) = a.data

@inline Nemo.parent(a::AbsNonSimpleNumFieldElem) = a.parent::AbsNonSimpleNumField

is_simple(a::AbsNonSimpleNumField) = false

is_simple(::Type{AbsNonSimpleNumField}) = false

function basis(K::AbsNonSimpleNumField; copy::Bool = true)
  if isdefined(K, :basis)
    if copy
      return deepcopy(K.basis)::Vector{AbsNonSimpleNumFieldElem}
    else
      return K.basis::Vector{AbsNonSimpleNumFieldElem}
    end
  end
  Rx = parent(K.pol[1])
  b = Vector{AbsNonSimpleNumFieldElem}(undef, degree(K))
  ind = 1
  d = degrees(K)
  it = cartesian_product_iterator([0:d[i]-1 for i = 1:length(d)], inplace = true)
  for i in it
    el = Rx()
    setcoeff!(el, i, QQFieldElem(1))
    b[ind] = K(el, false)
    ind += 1
  end
  K.basis = b
  if copy
    return deepcopy(b)::Vector{AbsNonSimpleNumFieldElem}
  else
    return b::Vector{AbsNonSimpleNumFieldElem}
  end
end

# Given an exponent vector b, the following function returns the index of
# the basis element corresponding to b.
function monomial_to_index(K::AbsNonSimpleNumField, b::Vector{T}) where {T}
  n = ngens(K)
  idx = b[n]
  d = degrees(K)
  for j in n-1:-1:1
    idx *= d[j]
    idx += b[j]
  end
  return Int(idx + 1)
end

################################################################################
#
#  Reduction
#
################################################################################

function reduce!(a::AbsNonSimpleNumFieldElem)
  q, a.data = divrem(a.data, parent(a).pol)
  return a
end

################################################################################
#
#  Denominator
#
################################################################################

denominator(a::AbsNonSimpleNumFieldElem) = denominator(a.data)

################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, ::MIME"text/plain", a::AbsNonSimpleNumField)
  @show_name(io, a)
  @show_special(io, a)
  io = pretty(io)
  print(io, "Non-simple number field with defining polynomials [")
  join(io, defining_polynomials(a), ", ")
  println(io, "]")
  print(io, Indent(), "over ", Lowercase(), base_field(a))
  print(io, Dedent())
end

function Base.show(io::IO, a::AbsNonSimpleNumField)
  @show_name(io, a)
  @show_special(io, a)
  if get(io, :supercompact, false)
    print(io, "Non-simple number field")
  else
    io = pretty(io)
    print(io, "Non-simple number field of degree ", degree(a))
    print(IOContext(io, :supercompact => true), " over ", Lowercase(), base_field(a))
  end
end

function Base.show(io::IO, a::AbsNonSimpleNumFieldElem)
  print(io, AbstractAlgebra.obj_to_string(a, context = io))
end

function AbstractAlgebra.expressify(x::AbsNonSimpleNumFieldElem; context = nothing)
  return AbstractAlgebra.expressify(data(x), symbols(parent(x)), context = context)
end

################################################################################
#
#  Unary operators
#
################################################################################

function Base.:(-)(a::AbsNonSimpleNumFieldElem)
  return AbsNonSimpleNumFieldElem(parent(a), -data(a))
end

################################################################################
#
#  Binary operators
#
################################################################################

function Base.:(+)(a::AbsNonSimpleNumFieldElem, b::AbsNonSimpleNumFieldElem)
  parent(a) == parent(b) || force_op(+, a, b)::AbsNonSimpleNumFieldElem
  return AbsNonSimpleNumFieldElem(parent(a), data(a) + data(b))
end

function Base.:(-)(a::AbsNonSimpleNumFieldElem, b::AbsNonSimpleNumFieldElem)
  parent(a) == parent(b) || force_op(-, a, b)::AbsNonSimpleNumFieldElem
  return AbsNonSimpleNumFieldElem(parent(a), data(a) - data(b))
end

function Base.:(*)(a::AbsNonSimpleNumFieldElem, b::AbsNonSimpleNumFieldElem)
  parent(a) == parent(b) || force_op(*, a, b)::AbsNonSimpleNumFieldElem
  return parent(a)(data(a) * data(b))
end

function Base.:(//)(a::AbsNonSimpleNumFieldElem, b::AbsNonSimpleNumFieldElem)
  return div(a, b)
end

function Base.div(a::AbsNonSimpleNumFieldElem, b::AbsNonSimpleNumFieldElem)
  parent(a) == parent(b) || force_op(div, a, b)::AbsNonSimpleNumFieldElem
  return a * inv(b)
end

Nemo.divexact(a::AbsNonSimpleNumFieldElem, b::AbsNonSimpleNumFieldElem; check::Bool = false) = div(a, b)

################################################################################
#
#  Powering
#
################################################################################

function Base.:(^)(a::AbsNonSimpleNumFieldElem, b::Integer)
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

function Base.:(^)(a::AbsNonSimpleNumFieldElem, b::ZZRingElem)
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

function Base.:(==)(a::AbsNonSimpleNumFieldElem, b::AbsNonSimpleNumFieldElem)
  parent(a) == parent(b) || force_op(==, a, b)::Bool
  return data(a) == data(b)
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function Nemo.mul!(c::AbsNonSimpleNumFieldElem, a::AbsNonSimpleNumFieldElem, b::AbsNonSimpleNumFieldElem)
  mul!(c.data, a.data, b.data)
  c = reduce!(c)
  return c
end

function Nemo.add!(c::AbsNonSimpleNumFieldElem, a::AbsNonSimpleNumFieldElem, b::AbsNonSimpleNumFieldElem)
  add!(c.data, a.data, b.data)
  return c
end

function Nemo.add!(c::AbsNonSimpleNumFieldElem, a::AbsNonSimpleNumFieldElem, b::ZZRingElem)
  add!(c.data, a.data, parent(c.data)(b))
  return c
end

function Nemo.add!(c::AbsNonSimpleNumFieldElem, a::AbsNonSimpleNumFieldElem, b::Integer)
  add!(c.data, a.data, parent(c.data)(b))
  return c
end

function Nemo.addeq!(b::AbsNonSimpleNumFieldElem, a::AbsNonSimpleNumFieldElem)
  addeq!(b.data, a.data)
  b = reduce!(b)
  return b
end


function Nemo.mul!(c::AbsNonSimpleNumFieldElem, a::AbsNonSimpleNumFieldElem, b::ZZRingElem)
  mul!(c.data, a.data, b)
  return c
end

function Nemo.mul!(c::AbsNonSimpleNumFieldElem, a::AbsNonSimpleNumFieldElem, b::Integer)
  mul!(c.data, a.data, parent(c.data)(b))
  return c
end

################################################################################
#
#  Conversion to matrix
#
################################################################################

function elem_to_mat_row!(M::ZZMatrix, i::Int, d::ZZRingElem, a::AbsNonSimpleNumFieldElem)
  K = parent(a)
  # TODO: This is super bad
  # Proper implementation needs access to the content of the underlying
  # QQMPolyRingElem

  for j in 1:ncols(M)
    M[i, j] = zero(FlintZZ)
  end

  one!(d)

  if length(data(a)) == 0
    return nothing
  end

  z = zero_matrix(FlintQQ, 1, ncols(M))
  elem_to_mat_row!(z, 1, a)
  z_q = FakeFmpqMat(z)

  for j in 1:ncols(M)
    M[i, j] = z_q.num[1, j]
  end

  ccall((:fmpz_set, libflint), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}), d, z_q.den)

  return nothing
end

function elem_to_mat_row!(M::QQMatrix, i::Int, a::AbsNonSimpleNumFieldElem)
  K = parent(a)
  for j in 1:ncols(M)
    M[i, j] = zero(FlintQQ)
  end
  adata = data(a)
  for j in 1:length(adata)
    exps = exponent_vector(adata, j)
    k = monomial_to_index(K, exps)
    M[i, k] = coeff(adata, j)
  end
  return M
end

function elem_from_mat_row(K::AbsNonSimpleNumField, M::QQMatrix, i::Int)
  a = K()
  b = basis(K, copy = false)
  for c = 1:ncols(M)
    a += M[i, c]*b[c]
  end
  return a
end

function elem_from_mat_row(K::AbsNonSimpleNumField, M::ZZMatrix, i::Int, d::ZZRingElem)
  b = basis(K, copy = false)
  Qxy = parent(b[1].data)
  a = Qxy()
  tmp = Qxy()
  for c = 1:ncols(M)
    mul!(tmp, b[c].data, M[i, c])
    add!(a, a, tmp)
    #a += M[i, c]*b[c]
  end
  return divexact(K(a), d)
end

function SRow(a::AbsNonSimpleNumFieldElem)
  sr = SRow(FlintQQ)
  adata = data(a)
  for i=1:length(adata)
    # TODO: Do this inplace with preallocated exps array
    exps = exponent_vector(adata, i)
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
#  Discriminant
#
################################################################################

function discriminant(K::AbsNonSimpleNumField)
  Qx = FlintQQ["x"][1]
  d = QQFieldElem(1)
  for i = 1:length(K.pol)
    d *= discriminant(to_univariate(Qx,K.pol[i]))^(div(degree(K), total_degree(K.pol[i])))
  end
  return d
end


################################################################################
#
#  Minimal polynomial
#
################################################################################

function minpoly_dense(a::AbsNonSimpleNumFieldElem)
  K = parent(a)
  n = degree(K)
  M = zero_matrix(FlintQQ, degree(K)+1, degree(K))
  z = a^0
  elem_to_mat_row!(M, 1, z)
  z *= a
  elem_to_mat_row!(M, 2, z)
  i = 2
  Qt, _ = polynomial_ring(FlintQQ,"t", cached=false)
  while true
    if n % (i-1) == 0 && rank(M) < i
      N = kernel(transpose(sub(M, 1:i, 1:ncols(M))), side = :right)
      @assert ncols(N) == 1
      v = Vector{QQFieldElem}(undef, i)
      for j in 1:i
        v[j] = N[j, 1]
      end
      #f = Qt([N[2][j, 1] for j=1:i])
      f = Qt(v)
      return f*inv(leading_coefficient(f))
    end
    z *= a
    elem_to_mat_row!(M, i+1, z)
    i += 1
  end
end

function minpoly_sparse(a::AbsNonSimpleNumFieldElem)
  K = parent(a)
  n = degree(K)
  M = sparse_matrix(FlintQQ)
  z = a^0
  push!(M, SRow(z))
  z *= a
  sz = SRow(z)
  i = 1
  local so::typeof(sz)
  Qt, t = polynomial_ring(FlintQQ, "x", cached = false)
  while true
    if n % i == 0
      fl, _so = can_solve_with_solution(M, sz)
      so = typeof(sz)(_so)
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

function minpoly(a::AbsNonSimpleNumFieldElem)
  return minpoly_via_trace(a)::QQPolyRingElem
end

function minpoly(Qx::QQPolyRing, a::AbsNonSimpleNumFieldElem)
  return Qx(minpoly(a))
end

function minpoly(Rx::ZZPolyRing, a::AbsNonSimpleNumFieldElem)
  f = minpoly(a)
  if !isone(denominator(f))
    error("element is not integral")
  end
  return Rx(denominator(f)*f)
end

function minpoly(a::AbsNonSimpleNumFieldElem, R::ZZRing)
  return minpoly(polynomial_ring(R, cached = false)[1], a)
end

function minpoly(a::AbsNonSimpleNumFieldElem, ::QQField)
  return minpoly(a)
end

################################################################################
#
#  Characteristic polynomial
#
################################################################################

function charpoly(a::AbsNonSimpleNumFieldElem)
  f = minpoly(a)
  return f^div(degree(parent(a)), degree(f))
end

function charpoly(Rx::QQPolyRing, a::AbsNonSimpleNumFieldElem)
  return Qx(charpoly(a))
end

function charpoly(Rx::ZZPolyRing, a::AbsNonSimpleNumFieldElem)
  f = charpoly(a)
  if !isone(denominator(f))
    error("element is not integral")
  end
  return Rx(denominator(f)*f)
end

function charpoly(a::AbsNonSimpleNumFieldElem, R::ZZRing)
  return charpoly(polynomial_ring(R, cached = false)[1], a)
end

function charpoly(a::AbsNonSimpleNumFieldElem, ::QQField)
  return charpoly(a)
end

################################################################################
#
#  Inverse
#
################################################################################

function inv(a::AbsNonSimpleNumFieldElem)
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

function norm(a::AbsNonSimpleNumFieldElem)
  f = minpoly(a)
  return (-1)^degree(parent(a)) * coeff(f, 0)^div(degree(parent(a)), degree(f))
end

################################################################################
#
#  Representation matrix
#
################################################################################

function representation_matrix(a::AbsNonSimpleNumFieldElem)
  K = parent(a)
  b = basis(K, copy = false)
  M = zero_matrix(FlintQQ, degree(K), degree(K))
  for i=1:degree(K)
    elem_to_mat_row!(M, i, a*b[i])
  end
  return M
end

function representation_matrix_q(a::AbsNonSimpleNumFieldElem)
  M = representation_matrix(a)
  return _fmpq_mat_to_fmpz_mat_den(M)
end

################################################################################
#
#  mod function
#
################################################################################



function mod(a::AbsNonSimpleNumFieldElem, p::ZZRingElem)
  b = copy(a)
  mod!(b, p)
  return b
end

# TODO: Dan says that it is better to use a BuilderCtx if the result has
# denominator 1
function mod!(b::AbsNonSimpleNumFieldElem, p::ZZRingElem)
  for i=1:length(b.data)
    el = coeff(b.data, i)
    dnew, cp = ppio(denominator(el), p)
    el *= cp
    n = mod(numerator(el), dnew * p)
    setcoeff!(b.data, i, QQFieldElem(n, dnew))
  end
  combine_like_terms!(b.data)
  return b
end

################################################################################
#
#  Substitution
#
################################################################################

#function is_univariate(f::QQMPolyRingElem)
#  deg = 0
#  var = 0
#  for i = 1:length(f)
#    exps = exponent_vector(f, i)
#    for j = 1:length(exps)
#      if !iszero(exps[j])
#        if iszero(var)
#          var = j
#          deg = exps[j]
#        elseif var != j
#          return false, QQPolyRingElem()
#        elseif deg < exps[j]
#          deg = exps[j]
#        end
#      end
#    end
#  end
#
#  Qx = polynomial_ring(FlintQQ, "x")[1]
#  coeffs = Vector{QQFieldElem}(undef, deg+1)
#  if iszero(deg)
#    if iszero(f)
#      coeffs[1] = 0
#      return true, Qx(coeffs)
#    end
#    #f is a constant
#    coeffs[1] = coeff(f, 1)
#    return true, Qx(coeffs)
#  end
#  for i = 1:length(f)
#    exps = exponent_vector(f, i)
#    coeffs[exps[var]+1] = coeff(f, i)
#  end
#  for i = 1:length(coeffs)
#    if !isassigned(coeffs, i)
#      coeffs[i] = QQFieldElem(0)
#    end
#  end
#  return true, Qx(coeffs)
#
#end

# TODO: - Preallocate the exps array
#       - Do we still need this?
function msubst(f::QQMPolyRingElem, v::Vector{T}) where {T}
  n = length(v)
  @assert n == nvars(parent(f))
  variables = vars(f)
  if length(f) == 0
    return zero(QQFieldElem) * one(parent(v[1]))
  end
  if length(variables) == 1
    fl = is_univariate(f)
    p = to_univariate(Globals.Qx, f)
    @assert fl
    #I need the variable. Awful
    vect_exp = exponent_vector(variables[1], 1)
    i = 1
    while iszero(vect_exp[i])
      i += 1
    end
    return evaluate(p, v[i])
  end
  powers = Dict{Int, Dict{Int, T}}()
  for i = 1:n
    powers[i] = Dict{Int, T}()
  end
  exps = exponent_vector(f, length(f))
  powers[1][exps[1]] = v[1]^exps[1]
  r = coeff(f, length(f)) * powers[1][exps[1]]
  for j = 2:n
    if iszero(exps[j])
      continue
    end
    el = v[j]^exps[j]
    powers[j][exps[j]] = el
    r *= el
  end
  R = parent(r)
  for i = length(f)-1:-1:1
    exps = exponent_vector(f, i)
    #r += coeff(f, i) * prod(v[j]^exps[j] for j=1:n)
    r1 = coeff(f, i)*one(R)
    for j = 1:n
      if iszero(exps[j])
        continue
      end
      if haskey(powers[j], exps[j])
        r1 *= powers[j][exps[j]]
      else
        el = v[j]^exps[j]
        powers[j][exps[j]] = el
        r1 *= el
      end
    end
    r += r1
  end
  return r
end

################################################################################
#
#  Simple extensions
#
################################################################################

function simple_extension(K::AbsNonSimpleNumField; cached::Bool = true, check = true, simplified::Bool = false)
  if simplified
    return simplified_simple_extension(K, cached = cached)
  end
  n = ngens(K)
  g = gens(K)
  if n == 1
    #The extension is already simple
    f = to_univariate(Globals.Qx, K.pol[1])
    Ka, a = number_field(f, "a", cached = cached, check = check)
    mp = hom(Ka, K, g[1], inverse = [a])
    return Ka, mp
  end
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
  Ka, a = number_field(f, check = check, cached = cached)
  k = base_ring(K)
  M = zero_matrix(k, degree(K), degree(K))
  z = one(K)
  elem_to_mat_row!(M, 1, z)
  if degree(K) > 1
    elem_to_mat_row!(M, 2, pe)
    z = mul!(z, z, pe)
    for i=3:degree(K)
      z = mul!(z, z, pe)
      elem_to_mat_row!(M, i, z)
    end
  end
  N = zero_matrix(k, n, degree(K))
  for i = 1:n
    elem_to_mat_row!(N, i, g[i])
  end
  s = solve(transpose(M), transpose(N); side = :right)
  b = basis(Ka)
  emb = Vector{AbsSimpleNumFieldElem}(undef, n)
  for i = 1:n
    emb[i] = zero(Ka)
    for j = 1:degree(Ka)
      emb[i] += b[j] * s[j, i]
    end
  end
  h = hom(Ka, K, pe, inverse = emb)
  embed(h)
  embed(MapFromFunc(K, Ka, x->preimage(h, x)))
  return Ka, h
end

function number_field(K1::AbsSimpleNumField, K2::AbsSimpleNumField; cached::Bool = false, check::Bool = false)
  K , l = number_field([K1.pol, K2.pol], "_\$", check = check, cached = cached)
  mp1 = hom(K1, K, l[1], check = false)
  mp2 = hom(K2, K, l[2], check = false)
  embed(mp1)
  embed(mp2)
  return K, mp1, mp2
end

function number_field(fields::Vector{AbsSimpleNumField}; cached::Bool = true, check::Bool = true)
  pols = Vector{QQPolyRingElem}(undef, length(fields))
  for i = 1:length(fields)
    pols[i] = fields[i].pol
  end
  K, gK = number_field(pols, "\$", check = check, cached = cached)
  mps = Vector{morphism_type(AbsSimpleNumField, AbsNonSimpleNumField)}(undef, length(fields))
  for i = 1:length(fields)
    mps[i] = hom(fields[i], K, gK[i])
    if cached
      embed(mps[i])
    end
  end
  return K, mps
end

################################################################################
#
#  Constructors and parent object overloading
#
################################################################################

@doc raw"""
    number_field(f::Vector{QQPolyRingElem}, s::String="_\$") -> AbsNonSimpleNumField

Let $f = (f_1, \ldots, f_n)$ be univariate rational polynomials, then
we construct
 $$K = Q[t_1, \ldots, t_n]/\langle f_1(t_1), \ldots, f_n(t_n)\rangle .$$
The ideal must be maximal, however, this is not tested.
"""
function number_field(f::Vector{QQPolyRingElem}, s::String="_\$"; cached::Bool = false, check::Bool = true)
  n = length(f)
  if occursin('#', s)
    lS = Symbol[Symbol(replace(s, "#"=>"$i")) for i=1:n]
  else
    lS = Symbol[Symbol("$s$i") for i=1:n]
  end
  return number_field(f, lS, cached = cached, check = check)
end

function number_field(f::Vector{QQPolyRingElem}, s::Vector{String}; cached::Bool = false, check::Bool = true)
  lS = Symbol[Symbol(x) for x=s]
  return number_field(f, lS, cached = cached, check = check)
end

function number_field(f::Vector{QQPolyRingElem}, S::Vector{Symbol}; cached::Bool = false, check::Bool = true)
  length(S) == length(f) || error("number of names must match the number of polynomials")
  n = length(S)
  s = var(parent(f[1]))
  Qx, x = polynomial_ring(FlintQQ, ["$s$i" for i=1:n], cached = false)
  K = AbsNonSimpleNumField(f, QQMPolyRingElem[f[i](x[i]) for i=1:n], S, cached)
  K.degrees = [degree(f[i]) for i in 1:n]
  K.degree = prod(K.degrees)
  if check
    if !_check_consistency(K)
      error("The fields are not linearly disjoint!")
    end
  end
  return K, gens(K)
end

function number_field(f::Vector{ZZPolyRingElem}, s::String="_\$"; cached::Bool = false, check::Bool = true)
  Qx, _ = polynomial_ring(FlintQQ, var(parent(f[1])), cached = false)
  return number_field(QQPolyRingElem[Qx(x) for x = f], s, cached = cached, check = check)
end

function number_field(f::Vector{ZZPolyRingElem}, s::Vector{String}; cached::Bool = false, check::Bool = true)
  Qx, _ = polynomial_ring(FlintQQ, var(parent(f[1])), cached = false)
  return number_field(QQPolyRingElem[Qx(x) for x = f], s, cached = cached, check = check)
end

function number_field(f::Vector{ZZPolyRingElem}, S::Vector{Symbol}; cached::Bool = false, check::Bool = true)
  Qx, _ = polynomial_ring(FlintQQ, var(parent(f[1])), cached = false)
  return number_field(QQPolyRingElem[Qx(x) for x = f], S, cached = cached, check = check)
end

function gens(K::AbsNonSimpleNumField)
  l = Vector{AbsNonSimpleNumFieldElem}(undef, ngens(K))
  degs = degrees(K)
  gQxy = gens(parent(K.pol[1]))
  for i = 1:length(gQxy)
    if isone(degs[i])
      l[i] = K(gQxy[i])
    else
      l[i] = AbsNonSimpleNumFieldElem(K, gQxy[i])
    end
  end
  return l
end


function vars(E::AbsNonSimpleNumField)
  return E.S
end
function symbols(E::AbsNonSimpleNumField)
  return vars(E)
end

function Base.names(E::AbsNonSimpleNumField)
  v = vars(E)
  res = Vector{String}(undef, length(v))
  for i = 1:length(res)
    res[i] = string(v[i])
  end
  return res
end

function (K::AbsNonSimpleNumField)(a::QQMPolyRingElem, red::Bool = true)
  if red
    q, a = divrem(a, K.pol)
  end
  z = AbsNonSimpleNumFieldElem(K, a)
  return z
end

function (K::AbsNonSimpleNumField)(a::Vector{QQFieldElem})
  return dot(a, basis(K))
end

(K::AbsNonSimpleNumField)(a::Integer) = K(parent(K.pol[1])(a))

(K::AbsNonSimpleNumField)(a::Rational{T}) where {T <: Integer} = K(parent(K.pol[1])(a))

(K::AbsNonSimpleNumField)(a::ZZRingElem) = K(parent(K.pol[1])(a))

(K::AbsNonSimpleNumField)(a::QQFieldElem) = K(parent(K.pol[1])(a))

(K::AbsNonSimpleNumField)() = zero(K)

(K::AbsNonSimpleNumField)(a::NumFieldElem) = force_coerce(K, a)

function (K::AbsNonSimpleNumField)(a::AbsNonSimpleNumFieldElem)
  if parent(a) === K
    return deepcopy(a)
  end
  error("not compatible")
end

function show_sparse_cyclo(io::IO, a::AbsNonSimpleNumField)
  print(io, "Sparse cyclotomic field of order $(get_attribute(a, :cyclo))")
end

function cyclotomic_field(::Type{NonSimpleNumField}, n::Int, s::String="z"; cached::Bool = false)
  x = gen(Hecke.Globals.Zx)
  lf = factor(n)
  if n == 1
    lc = [1]
  else
    lc = [Int(p^k) for (p,k) = lf.fac]
  end
  lp = [cyclotomic(k, x) for k = lc]
  ls = ["$s($n)_$k" for k = lc]
  C, g = number_field(lp, ls, cached = cached, check = false)
  #the :decom array is necessary as this fixes the order of the
  #generators. The factorisation (Dict) does not give useful
  #info here.
  set_attribute!(C, :show => show_sparse_cyclo, :cyclo => n, :decom => lc)
  return C, g
end

function trace_assure(K::AbsNonSimpleNumField)
  if isdefined(K, :traces)
    return
  end
  Qx, x = polynomial_ring(FlintQQ, cached = false)
  K.traces = Vector{QQFieldElem}[total_degree(f) == 1 ? QQFieldElem[] : polynomial_to_power_sums(to_univariate(Qx, f), total_degree(f)-1) for f = K.pol]
end

#= Idea
  if k = Q[x,y]/<f, g>
    then
      tr(x^i) = power_sums(f)
      tr(y^i) = power_sums(g)
      tr(x^i y^j) = tr(x^i) tr(y^j):
        in the tower of fields:
          tr_<f,g>(xy) = tr_<f>(x (tr_<g> y)) = tr_f x * tr_g y
  so trace_assure computes trace(x^i)
  and tr assembles....
=#

function tr(a::AbsNonSimpleNumFieldElem)
  k = parent(a)
  if iszero(a)
    return QQFieldElem()
  end
  trace_assure(k)
  t = QQFieldElem()
  for trm = terms(a.data)
    c = coeff(trm, 1)::QQFieldElem
    e = exponent_vector(trm, 1)
    tt = QQFieldElem(1)
    for i=1:length(e)
      if e[i] != 0
        tt *= k.traces[i][e[i]]
      else
        tt *= total_degree(k.pol[i])
      end
    end
    t += c*tt
  end
  return t
end

#TODO:
#  test f mod p first
#  if all polys are monic, the test if traces have non-trivial gcd
function minpoly_via_trace(a::AbsNonSimpleNumFieldElem)
  k = parent(a)
  d = degree(k)
  b = a
  l = [tr(b)]
  i = 1
  while i <= d
    while d % i != 0
      b *= a
      push!(l, tr(b))
      i += 1
    end
    q = QQFieldElem(1, div(d, i))
    f = power_sums_to_polynomial([x*q for x = l])
    if iszero(subst(f, a))  #TODO: to checks first...
      return f::QQPolyRingElem
    end
    b *= a
    push!(l, tr(b))
    i += 1
  end
  error("cannot happen")
end

function is_norm_divisible(a::AbsNonSimpleNumFieldElem, n::ZZRingElem)
  return iszero(mod(norm(a), n))
end

function valuation(a::AbsNumFieldOrderElem, p::AbsNumFieldOrderIdeal)
  i = 1
  q = p
  while true
    if !(a in q)
      return i - 1
    end
    q = q * p
    i = i + 1
  end
end

#TODO: find a better algo.
function degree(a::AbsNonSimpleNumFieldElem)
  return degree(minpoly(a))
end

#TODO: Improve the algorithm
function primitive_element(K::AbsNonSimpleNumField)
  g = gens(K)
  pe = g[1]
  d = total_degree(K.pol[1])
  i = 1
  while i < length(g)
    i += 1
    d *= total_degree(K.pol[i])
    while true
      pe += g[i]
      f = minpoly(pe)
      degree(f) == d && break
    end
  end
  return pe
end

function factor(f::PolyRingElem{AbsNonSimpleNumFieldElem})
  Kx = parent(f)
  K = base_ring(f)

  iszero(f) && error("poly is zero")

  val = valuation(f, gen(Kx))
  if val > 0
    f = shift_right(f, val)
  end

  if degree(f) == 0
    r = Fac{typeof(f)}()
    r.fac = Dict{typeof(f), Int}()
    r.unit = Kx(leading_coefficient(f))
    if val > 0
      r.fac[gen(Kx)] = val
    end
    return r
  end

  f_orig = deepcopy(f)
  @vprintln :PolyFactor 1 "Factoring $f"

  @vtime :PolyFactor 2 g = gcd(f, derivative(f))
  if degree(g) > 0
    f = div(f, g)
  end


  if degree(f) == 1
    multip = div(degree(f_orig), degree(f))
    r = Fac{typeof(f)}()
    r.fac = Dict{typeof(f), Int}(f*(1//leading_coefficient(f)) => multip)
    r.unit = one(Kx) * leading_coefficient(f_orig)
    if val > 0
      r.fac[gen(Kx)] = val
    end
    return r
  end

  f = f*(1//leading_coefficient(f))

  k = 0
  g = f
  @vtime :PolyFactor 2 N = norm(g)

  pe = K()
  while is_constant(N) || !is_squarefree(N)
    k = k + 1
    if k == 1
      pe = primitive_element(K)
    end
    g = compose(f, gen(Kx) - k*pe, inner = :second)
    @vtime :PolyFactor 2 N = norm(g)
  end
  @vtime :PolyFactor 2 fac = factor(N)

  res = Dict{PolyRingElem{AbsNonSimpleNumFieldElem}, Int64}()

  for i in keys(fac.fac)
    t = change_base_ring(K, i, parent = Kx)
    t = compose(t, gen(Kx) + k*pe, inner = :second)
    @vtime :PolyFactor 2 t = gcd(f, t)
    res[t] = valuation(f_orig, t)
  end

  r = Fac{typeof(f)}()
  r.fac = res
  r.unit = Kx(1)
  if val > 0
    r.fac[gen(Kx)] = val
  end

  r.unit = one(Kx)* leading_coefficient(f_orig)//prod((leading_coefficient(p) for (p, e) in r))
  return r
end

################################################################################
#
#  Hashing
#
################################################################################

function Base.hash(a::AbsNonSimpleNumFieldElem, h::UInt)
  return Base.hash(a.data, h)
end

################################################################################
#
#  Coercion
#
################################################################################

function (K::QQField)(a::AbsNonSimpleNumFieldElem)
  @req is_constant(data(a)) "Element must be rational"
  return constant_coefficient(data(a))
end

function is_rational(a::AbsNonSimpleNumFieldElem)
  return is_constant(data(a))
end
