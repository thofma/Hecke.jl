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

@inline base_field(K::NfAbsNS) = FlintQQ

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

function _get_nf_equation_order(K::NfAbsNS)
  if isdefined(K, :equation_order)
    return K.equation_order::NfAbsOrd{NfAbsNS, NfAbsNSElem}
  else
    throw(AccessorNotSetError())
  end
end

function _set_nf_equation_order(K::NfAbsNS, O)
  K.equation_order = O
end

################################################################################
#
#  Copy
#
################################################################################

function Base.deepcopy_internal(a::NfAbsNSElem, dict::IdDict)
  # TODO: Fix this once deepcopy is fixed for fmpq_mpoly
  # z = NfAbsNSElem(Base.deepcopy_internal(data(a), dict))
  z = NfAbsNSElem(parent(a), Base.deepcopy(data(a)))
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

order_type(::NfAbsNS) = NfAbsOrd{NfAbsNS, NfAbsNSElem}

order_type(::Type{NfAbsNS}) = NfAbsOrd{NfAbsNS, NfAbsNSElem}

needs_parentheses(x::NfAbsNSElem) = needs_parentheses(data(x))

displayed_with_minus_in_front(x::NfAbsNSElem) = displayed_with_minus_in_front(data(x))

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

function Nemo.zero!(a::NfAbsNSElem)
  a.data = zero(a.data)
  return a
end

function Nemo.one!(a::NfAbsNSElem)
  a.data = one(a.data)
  return a
end

function Nemo.one!(a::fmpq_mpoly)
  ccall((:fmpq_mpoly_one, libflint), Nothing,
      (Ref{fmpq_mpoly}, Ref{FmpqMPolyRing}), a, parent(a))
  return a
end

################################################################################
#
#  Random
#
################################################################################

RandomExtensions.maketype(K::NfAbsNS, r) = elem_type(K)

function rand(rng::AbstractRNG, sp::SamplerTrivial{<:Make2{NfAbsNSElem,NfAbsNS,<:UnitRange}})
  K, r = sp[][1:end]
  # TODO: This is super slow
  b = basis(K, copy = false)
  z::Random.gentype(sp) = K() # type-assert to help inference on Julia 1.0 and 1.1
  for i in 1:degree(K)
    z += rand(rng, r) * b[i]
  end
  return z
end

rand(K::NfAbsNS, r::UnitRange) = rand(GLOBAL_RNG, K, r)
rand(rng::AbstractRNG, K::NfAbsNS, r::UnitRange) = rand(rng, make(K, r))

################################################################################
#
#  Basis matrix
#
################################################################################

function basis_matrix(A::Array{NfAbsNSElem})
  @assert length(A) > 0
  n = length(A)
  d = degree(parent(A[1]))

  MM = zero_matrix(FlintQQ, n, d)
  for i in 1:n
    elem_to_mat_row!(MM, i, A[i])
  end
  return MM
end

function basis_matrix(A::Vector{NfAbsNSElem}, ::Type{FakeFmpqMat})
  return FakeFmpqMat(basis_matrix(A))
end

################################################################################
#
#  Promotion
#
################################################################################

Nemo.promote_rule(::Type{NfAbsNSElem}, ::Type{T}) where {T <: Integer} = NfAbsNSElem

Nemo.promote_rule(::Type{NfAbsNSElem}, ::Type{fmpz}) = NfAbsNSElem

Nemo.promote_rule(::Type{NfAbsNSElem}, ::Type{fmpq}) = NfAbsNSElem

################################################################################
#
#  Field access
#
################################################################################

@inline Nemo.data(a::NfAbsNSElem) = a.data

@inline Nemo.parent(a::NfAbsNSElem) = a.parent::NfAbsNS

issimple(a::NfAbsNS) = false

issimple(::Type{NfAbsNS}) = false

function basis(K::NfAbsNS; copy::Bool = true)
  if isdefined(K, :basis)
    if copy
      return deepcopy(K.basis)::Vector{NfAbsNSElem}
    else
      return K.basis::Vector{NfAbsNSElem}
    end
  end
  g = gens(parent(K.pol[1]))
  b = Vector{NfAbsNSElem}(undef, degree(K))
  ind = 1
  for i in CartesianIndices(Tuple(1:degrees(K)[i] for i in 1:ngens(K)))
    b[ind] = K(prod(g[j]^(i[j] - 1) for j=1:length(i)), false)
    ind += 1
  end
  K.basis = b
  if copy
    return deepcopy(b)::Vector{NfAbsNSElem}
  else
    return b::Vector{NfAbsNSElem}
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
#  Denominator
#
################################################################################

denominator(a::NfAbsNSElem) = denominator(a.data)

################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, a::NfAbsNS)
  @show_name(io, a)
  @show_special(io, a)
  print(io, "Non-simple number field with defining polynomials ", a.pol)
end

#TODO: this is a terrible show func.
function Base.show(io::IO, a::NfAbsNSElem)
  x = data(a)
  if length(x) == 0
     print(io, "0")
  else
     cstr = ccall((:fmpq_mpoly_get_str_pretty, libflint), Ptr{UInt8},
         (Ref{fmpq_mpoly}, Ptr{Ptr{UInt8}}, Ref{FmpqMPolyRing}),
         x, [string(s) for s in symbols(parent(a))], x.parent)
     print(io, unsafe_string(cstr))

     ccall((:flint_free, libflint), Nothing, (Ptr{UInt8},), cstr)
  end

#  show(io, f)
end

################################################################################
#
#  Unary operators
#
################################################################################

function Base.:(-)(a::NfAbsNSElem)
  return NfAbsNSElem(parent(a), -data(a))
end

################################################################################
#
#  Binary operators
#
################################################################################

function Base.:(+)(a::NfAbsNSElem, b::NfAbsNSElem)
  parent(a) == parent(b) || force_op(+, a, b)::NfAbsNSElem
  return NfAbsNSElem(parent(a), data(a) + data(b))
end

function Base.:(-)(a::NfAbsNSElem, b::NfAbsNSElem)
  parent(a) == parent(b) || force_op(-, a, b)::NfAbsNSElem
  return NfAbsNSElem(parent(a), data(a) - data(b))
end

function Base.:(*)(a::NfAbsNSElem, b::NfAbsNSElem)
  parent(a) == parent(b) || force_op(*, a, b)::NfAbsNSElem
  return parent(a)(data(a) * data(b))
end

function Base.:(//)(a::NfAbsNSElem, b::NfAbsNSElem)
  return div(a, b)
end

function Base.div(a::NfAbsNSElem, b::NfAbsNSElem)
  parent(a) == parent(b) || force_op(div, a, b)::NfAbsNSElem
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
  parent(a) == parent(b) || force_op(==, a, b)::Bool
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
  return c
end

function Nemo.add!(c::NfAbsNSElem, a::NfAbsNSElem, b::fmpz)
  add!(c.data, a.data, parent(c.data)(b))
  return c
end

function Nemo.add!(c::NfAbsNSElem, a::NfAbsNSElem, b::Integer)
  add!(c.data, a.data, parent(c.data)(b))
  return c
end

function Nemo.addeq!(b::NfAbsNSElem, a::NfAbsNSElem)
  addeq!(b.data, a.data)
  b = reduce!(b)
  return b
end


function Nemo.mul!(c::NfAbsNSElem, a::NfAbsNSElem, b::fmpz)
  mul!(c.data, a.data, b)
  return c
end

function Nemo.mul!(c::NfAbsNSElem, a::NfAbsNSElem, b::Integer)
  mul!(c.data, a.data, parent(c.data)(b))
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

  ccall((:fmpz_set, libflint), Nothing, (Ref{fmpz}, Ref{fmpz}), d, z_q.den)

  return nothing
end

function elem_to_mat_row!(M::fmpq_mat, i::Int, a::NfAbsNSElem)
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

function elem_from_mat_row(K::NfAbsNS, M::fmpq_mat, i::Int)
  a = K()
  b = basis(K, copy = false)
  for c = 1:ncols(M)
    a += M[i, c]*b[c]
  end
  return a
end

function elem_from_mat_row(K::NfAbsNS, M::fmpz_mat, i::Int, d::fmpz)
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

function SRow(a::NfAbsNSElem)
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

function discriminant(K::NfAbsNS)
  Qx = FlintQQ["x"][1]
  d = fmpq(1)
  for i = 1:length(K.pol)
    d *= discriminant(Qx(K.pol[i]))^(div(degree(K), total_degree(K.pol[i])))
  end
  return d
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
      N = nullspace(sub(M, 1:i, 1:ncols(M))')
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
  Qt, t = PolynomialRing(FlintQQ, "x", cached = false)
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
  return minpoly_via_trace(a)::fmpq_poly
end

function minpoly(Qx::FmpqPolyRing, a::NfAbsNSElem)
  return Qx(minpoly(a))
end

function minpoly(Rx::FmpzPolyRing, a::NfAbsNSElem)
  f = minpoly(a)
  if !isone(denominator(f))
    error("element is not integral")
  end
  return Rx(denominator(f)*f)
end

function minpoly(a::NfAbsNSElem, R::FlintIntegerRing)
  return minpoly(PolynomialRing(R, cached = false)[1], a)
end

function minpoly(a::NfAbsNSElem, ::FlintRationalField)
  return minpoly(a)
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

function charpoly(Rx::FmpqPolyRing, a::NfAbsNSElem)
  return Qx(charpoly(a))
end

function charpoly(Rx::FmpzPolyRing, a::NfAbsNSElem)
  f = charpoly(a)
  if !isone(denominator(f))
    error("element is not integral")
  end
  return Rx(denominator(f)*f)
end

function charpoly(a::NfAbsNSElem, R::FlintIntegerRing)
  return charpoly(PolynomialRing(R, cached = false)[1], a)
end

function charpoly(a::NfAbsNSElem, ::FlintRationalField)
  return charpoly(a)
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
#  Representation matrix
#
################################################################################

function representation_matrix(a::NfAbsNSElem)
  K = parent(a)
  b = basis(K, copy = false)
  M = zero_matrix(FlintQQ, degree(K), degree(K))
  for i=1:degree(K)
    elem_to_mat_row!(M, i, a*b[i])
  end
  return M
end

function representation_matrix_q(a::NfAbsNSElem)
  M = representation_matrix(a)
  return _fmpq_mat_to_fmpz_mat_den(M)
end

################################################################################
#
#  mod function
#
################################################################################



function mod(a::NfAbsNSElem, p::fmpz)
  b = copy(a)
  mod!(b, p)
  return b
end

function mod!(b::NfAbsNSElem, p::fmpz)
  for i=1:length(b.data)
    el = coeff(b.data, i)
    dnew, cp = ppio(denominator(el), p)
    el *= cp
    n = mod(numerator(el), dnew * p)
    setcoeff!(b.data, i, fmpq(n, dnew))
  end
  return b
end

################################################################################
#
#  Substitution
#
################################################################################

function isunivariate(f::fmpq_mpoly)
  deg = 0
  var = 0
  for i = 1:length(f)
    exps = exponent_vector(f, i)
    for j = 1:length(exps)
      if !iszero(exps[j])
        if iszero(var)
          var = j
          deg = exps[j]
        elseif var != j
          return false, fmpq_poly()
        elseif deg < exps[j]
          deg = exps[j]
        end
      end
    end
  end

  Qx = PolynomialRing(FlintQQ, "x")[1]
  coeffs = Vector{fmpq}(undef, deg+1)
  if iszero(deg)
    if iszero(f)
      coeffs[1] = 0
      return true, Qx(coeffs)
    end
    #f is a constant
    coeffs[1] = coeff(f, 1)
    return true, Qx(coeffs)
  end
  for i = 1:length(f)
    exps = exponent_vector(f, i)
    coeffs[exps[var]+1] = coeff(f, i)
  end
  for i = 1:length(coeffs)
    if !isassigned(coeffs, i)
      coeffs[i] = fmpq(0)
    end
  end
  return true, Qx(coeffs)

end

# TODO: Preallocate the exps array
function msubst(f::fmpq_mpoly, v::Array{T, 1}) where {T}
  n = length(v)
  @assert n == nvars(parent(f))
  variables = vars(f)
  if length(variables) == 1
    fl, p = isunivariate(f)
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

function simple_extension(K::NfAbsNS; cached = true, check = true)
  n = ngens(K)
  g = gens(K)
  if n == 1
    #The extension is already simple
    f = isunivariate(K.pol[1])[2]
    Ka, a = NumberField(f, "a", cached = false, check = check)
    mp = NfAbsToNfAbsNS(Ka, K, g[1], [a])
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
  Ka, a = number_field(f, check = check, cached = false)
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
  s = solve(M', N')
  b = basis(Ka)
  emb = Vector{nf_elem}(undef, n)
  for i = 1:n
    emb[i] = zero(Ka)
    for j = 1:degree(Ka)
      emb[i] += b[j] * s[j, i]
    end
  end
  h = NfAbsToNfAbsNS(Ka, K, pe, emb)
  embed(h)
  embed(MapFromFunc(x->preimage(h, x), K, Ka))
  return Ka, h
end

function NumberField(K1::AnticNumberField, K2::AnticNumberField; cached::Bool = false, check::Bool = false)
  K , l = number_field([K1.pol, K2.pol], "_\$", check = check, cached = cached)
  mp1 = NfAbsToNfAbsNS(K1, K, l[1])
  mp2 = NfAbsToNfAbsNS(K2, K, l[2])
  embed(mp1)
  embed(mp2)
  return K, mp1, mp2
end

function NumberField(fields::Vector{AnticNumberField}; cached::Bool = true, check::Bool = true)
  pols = Vector{fmpq_poly}(undef, length(fields))
  for i = 1:length(fields)
    pols[i] = fields[i].pol
  end
  K, gK = number_field(pols, "\$", check = check, cached = cached)
  mps = Vector{NfAbsToNfAbsNS}(undef, length(fields))
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

@doc Markdown.doc"""
    number_field(f::Array{fmpq_poly, 1}, s::String="_\$") -> NfAbsNS
Let $f = (f_1, \ldots, f_n)$ be univariate rational polynomials, then
we construct
 $$K = Q[t_1, \ldots, t_n]/\langle f_1(t_1), \ldots, f_n(t_n)\rangle .$$
The ideal must be maximal, however, this is not tested.
"""
function NumberField(f::Array{fmpq_poly, 1}, s::String="_\$"; cached::Bool = false, check::Bool = true)
  n = length(f)
  if occursin('#', s)
    lS = Symbol[Symbol(replace(s, "#"=>"$i")) for i=1:n]
  else
    lS = Symbol[Symbol("$s$i") for i=1:n]
  end
  return NumberField(f, lS, cached = cached, check = check)
end

function NumberField(f::Array{fmpq_poly, 1}, s::Array{String, 1}; cached::Bool = false, check::Bool = true)
  lS = Symbol[Symbol(x) for x=s]
  return NumberField(f, lS, cached = cached, check = check)
end

function NumberField(f::Array{fmpq_poly, 1}, S::Array{Symbol, 1}; cached::Bool = false, check::Bool = true)
  length(S) == length(f) || error("number of names must match the number of polynomials")
  n = length(S)
  s = var(parent(f[1]))
  Qx, x = PolynomialRing(FlintQQ, ["$s$i" for i=1:n], cached = false)
  K = NfAbsNS(fmpq_mpoly[f[i](x[i]) for i=1:n], S, cached)
  K.degrees = [degree(f[i]) for i in 1:n]
  K.degree = prod(K.degrees)
  if check
    if !_check_consistency(K)
      error("The fields are not linearly disjoint!")
    end
  end
  return K, gens(K)
end

function NumberField(f::Array{fmpz_poly, 1}, s::String="_\$"; cached::Bool = false, check::Bool = true)
  Qx, _ = PolynomialRing(FlintQQ, var(parent(f[1])), cached = false)
  return NumberField(fmpq_poly[Qx(x) for x = f], s, cached = cached, check = check)
end

function NumberField(f::Array{fmpz_poly, 1}, s::Array{String, 1}; cached::Bool = false, check::Bool = true)
  Qx, _ = PolynomialRing(FlintQQ, var(parent(f[1])), cached = false)
  return NumberField(fmpq_poly[Qx(x) for x = f], s, cached = cached, check = check)
end

function NumberField(f::Array{fmpz_poly, 1}, S::Array{Symbol, 1}; cached::Bool = false, check::Bool = true)
  Qx, _ = PolynomialRing(FlintQQ, var(parent(f[1])), cached = false)
  return NumberField(fmpq_poly[Qx(x) for x = f], S, cached = cached, check = check)
end

function gens(K::NfAbsNS)
  l = Vector{NfAbsNSElem}(undef, ngens(K))
  degs = degrees(K)
  gQxy = gens(parent(K.pol[1]))
  for i = 1:length(gQxy)
    if isone(degs[i])
      l[i] = K(gQxy[i])
    else
      l[i] = NfAbsNSElem(K, gQxy[i])
    end
  end
  return l
end


function vars(E::NfAbsNS)
  return E.S
end
function symbols(E::NfAbsNS)
  return vars(E)
end
function Base.names(E::NfAbsNS)
  return map(string, vars(E))
end

function (K::NfAbsNS)(a::fmpq_mpoly, red::Bool = true)
  if red
    q, a = divrem(a, K.pol)
  end
  z = NfAbsNSElem(K, a)
  return z
end

(K::NfAbsNS)(a::Integer) = K(parent(K.pol[1])(a))

(K::NfAbsNS)(a::Rational{T}) where {T <: Integer} = K(parent(K.pol[1])(a))

(K::NfAbsNS)(a::fmpz) = K(parent(K.pol[1])(a))

(K::NfAbsNS)(a::fmpq) = K(parent(K.pol[1])(a))

(K::NfAbsNS)() = zero(K)

(K::NfAbsNS)(a::NumFieldElem) = force_coerce(K, a)

function (K::NfAbsNS)(a::NfAbsNSElem)
  if parent(a) === K
    return deepcopy(a)
  end
  error("not compatible")
end

function show_sparse_cyclo(io::IO, a::NfAbsNS)
  print(io, "Sparse cyclotomic field of order $(get_special(a, :cyclo))")
end

function cyclotomic_field(::Type{NonSimpleNumField}, n::Int; cached::Bool = false)
  lf = factor(n)
  x = gen(Hecke.Globals.Zx)
  lp = [cyclotomic(Int(p^k), x) for (p,k) = lf.fac]
  ls = ["z($n)_$(p^k)" for (p,k) = lf.fac]
  C, g = number_field(lp, ls, cached = cached, check = false)
  set_special(C, :show => show_sparse_cyclo, :cyclo => n)
  return C, g
end

function trace_assure(K::NfAbsNS)
  if isdefined(K, :traces)
    return
  end
  Qx, x = PolynomialRing(FlintQQ, cached = false)
  K.traces = [polynomial_to_power_sums(Qx(f), total_degree(f)-1) for f = K.pol]
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

function tr(a::NfAbsNSElem)
  k = parent(a)
  if iszero(a)
    return fmpq()
  end
  trace_assure(k)
  t = fmpq()
  for trm = terms(a.data)
    c = coeff(trm, 1)::fmpq
    e = exponent_vector(trm, 1)
    tt = fmpq(1)
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
function minpoly_via_trace(a::NfAbsNSElem)
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
    q = fmpq(1, div(d, i))
    f = power_sums_to_polynomial([x*q for x = l])
    if iszero(subst(f, a))  #TODO: to checks first...
      return f::fmpq_poly
    end
    b *= a
    push!(l, tr(b))
    i += 1
  end
  error("cannot happen")
end

function isnorm_divisible(a::NfAbsNSElem, n::fmpz)
  return iszero(mod(norm(a), n))
end

function valuation(a::NfAbsOrdElem, p::NfAbsOrdIdl)
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
function degree(a::NfAbsNSElem)
  return degree(minpoly(a))
end

function degree(a::nf_elem)
  return degree(minpoly(a))
end

#TODO: Improve the algorithm
function primitive_element(K::NfAbsNS)
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

@doc Markdown.doc"""
    factor(f::PolyElem{NfAbsNSElem}) -> Fac{Generic.Poly{NfAbsNSElem}}

The factorisation of $f$ (using Trager's method).
"""
function factor(f::PolyElem{NfAbsNSElem})
  Kx = parent(f)
  K = base_ring(f)

  iszero(f) && error("poly is zero")

  if degree(f) == 0
    r = Fac{typeof(f)}()
    r.fac = Dict{typeof(f), Int}()
    r.unit = Kx(lead(f))
    return r
  end

  f_orig = deepcopy(f)
  @vprint :PolyFactor 1 "Factoring $f\n"
  @vtime :PolyFactor 2 g = gcd(f, derivative(f))
  if degree(g) > 0
    f = div(f, g)
  end


  if degree(f) == 1
    multip = div(degree(f_orig), degree(f))
    r = Fac{typeof(f)}()
    r.fac = Dict{typeof(f), Int}(f*(1//lead(f)) => multip)
    r.unit = one(Kx) * lead(f_orig)
    return r
  end

  f = f*(1//lead(f))

  k = 0
  g = f
  @vtime :PolyFactor 2 N = norm(g)

  pe = K()
  while isconstant(N) || !issquarefree(N)
    k = k + 1
    if k == 1
      pe = primitive_element(K)
    end
    g = compose(f, gen(Kx) - k*pe)
    @vtime :PolyFactor 2 N = norm(g)
  end
  @vtime :PolyFactor 2 fac = factor(N)

  res = Dict{PolyElem{NfAbsNSElem}, Int64}()

  for i in keys(fac.fac)
    t = change_base_ring(K, i, parent = Kx)
    t = compose(t, gen(Kx) + k*pe)
    @vtime :PolyFactor 2 t = gcd(f, t)
    res[t] = 1
  end

  r = Fac{typeof(f)}()
  r.fac = res
  r.unit = Kx(1)

  if f != f_orig
    error("factoring with mult not implemented")
  end
  r.unit = one(Kx)* lead(f_orig)//prod((lead(p) for (p, e) in r))
  return r
end

################################################################################
#
#  Hashing
#
################################################################################

function Base.hash(a::NfAbsNSElem, h::UInt)
  return Base.hash(a.data, h)
end
