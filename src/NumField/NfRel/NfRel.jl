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

export absolute_representation_matrix
export cyclotomic_field_as_cm_extension

add_assertion_scope(:NfRel)

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
#  Order types
#
################################################################################

order_type(K::NfRel{T}) where {T} = NfRelOrd{T, fractional_ideal_type(order_type(base_field(K))), NfRelElem{T}}

order_type(::Type{NfRel{T}}) where {T} = NfRelOrd{T, fractional_ideal_type(order_type(parent_type(T))), NfRelElem{T}}

################################################################################
#
#  Field access
#
################################################################################

@inline base_field(a::NfRel{T}) where {T} = a.base_ring::parent_type(T)

@inline data(a::NfRelElem) = a.data

@inline parent(a::NfRelElem{T}) where {T} = a.parent::NfRel{T}

@inline is_simple(a::NfRel) = true

################################################################################
#
#  Coefficient setting and getting
#
################################################################################

@inline coeff(a::NfRelElem{T}, i::Int) where {T} = coeff(a.data, i)

@inline setcoeff!(a::NfRelElem{T}, i::Int, c::T) where {T} = setcoeff!(a.data, i, c)

# copy does not do anything (so far), this is only for compatibility with coefficients(::AbsAlgAssElem)
function coefficients(a::NfRelElem{T}; copy::Bool = false) where {T}
  return T[coeff(a, i) for i = 0:degree(parent(a)) - 1 ]
end

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
#  mod(::NfRelElem, ::ZZRingElem) as in the absolute case
#
################################################################################

function mod(a::NfRelElem{T}, p::ZZRingElem) where T <: NumFieldElem
  K = parent(a)
  b = data(a)
  coeffs = Vector{T}(undef, degree(K)+1)
  for i = 0:degree(K)
    coeffs[i+1] = mod(coeff(b, i), p)
  end
  Kx = parent(b)
  return K(Kx(coeffs))
end

################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, a::NfRel)
  print(io, "Relative number field with defining polynomial ", a.pol)
  print(io, "\n over ", a.base_ring)
end

function AbstractAlgebra.expressify(a::NfRelElem; context = nothing)
  return AbstractAlgebra.expressify(data(a), var(parent(a)), context = context)
end

function Base.show(io::IO, a::NfRelElem)
  print(io, AbstractAlgebra.obj_to_string(a, context = io))
end

################################################################################
#
#  Constructors and parent object overloading
#
################################################################################

function number_field(f::PolyElem{T}, S::Symbol;
                     cached::Bool = false, check::Bool = true)  where {T <: NumFieldElem}
  check && !is_irreducible(f) && error("Polynomial must be irreducible")
  K = NfRel{T}(f, S, cached)
  return K, K(gen(parent(f)))
end

function number_field(f::PolyElem{T}, s::String;
                     cached::Bool = false, check::Bool = true)  where {T <: NumFieldElem}
    S = Symbol(s)
    return number_field(f, S, cached = cached, check = check)
end
function number_field(f::PolyElem{<: NumFieldElem}; cached::Bool = false, check::Bool = true)
  return number_field(f, "_\$", cached = cached, check = check)
end

#Conversion to absolute non simple
function number_field(::Type{AnticNumberField}, L::NfRel{nf_elem})
  @assert degree(base_field(L)) == 1
  pol = to_univariate(Globals.Qx, map_coefficients(FlintQQ, L.pol))
  return number_field(pol, check = false)
end

function (K::NfRel{T})(a::Generic.Poly{T}) where T <: NumFieldElem
  z = NfRelElem{T}(mod(a, K.pol))
  z.parent = K
  return z
end

function (K::NfRel{T})(a::T) where T <: NumFieldElem
  parent(a) != base_ring(parent(K.pol)) && error("Cannot coerce")
  z = NfRelElem{T}(parent(K.pol)(a))
  z.parent = K
  return z
end

(K::NfRel)(a::Integer) = K(parent(K.pol)(a))

(K::NfRel)(a::Rational{T}) where {T <: Integer} = K(parent(K.pol)(a))

(K::NfRel)(a::ZZRingElem) = K(parent(K.pol)(a))

(K::NfRel)(a::QQFieldElem) = K(parent(K.pol)(a))

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
  parent(a) == parent(b) || force_op(+, a, b)::NfRelElem{T}
  return parent(a)(data(a) + data(b))
end

function Base.:(-)(a::NfRelElem{T}, b::NfRelElem{T}) where {T}
  parent(a) == parent(b) || force_op(-, a, b)::NfRelElem{T}
  return parent(a)(data(a) - data(b))
end

function Base.:(*)(a::NfRelElem{T}, b::NfRelElem{T}) where {T}
  parent(a) == parent(b) || force_op(*, a, b)::NfRelElem{T}
  return parent(a)(data(a) * data(b))
end

function divexact(a::NfRelElem{T}, b::NfRelElem{T}; check::Bool = true) where {T}
  b == 0 && error("Element not invertible")
  parent(a) == parent(b) || force_op(divexact, a, b)::NfRelElem{T}
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

  return K(powermod(data(a), n, K.pol))
end

function Base.:(^)(a::NfRelElem, b::ZZRingElem)
  if fits(Int, b)
    return a^Int(b)
  end
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
    #mod(b, 2) == 1
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
  parent(a) == parent(b) || force_op(==, a, b)::Bool
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

for F in [ZZRingElem, QQFieldElem, Int]
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

function check_parent(a, b)
  return a==b
end

################################################################################
#
#  Hash function
#
################################################################################

function hash(a::Hecke.NfRelElem{nf_elem}, b::UInt)
  return hash(a.data, b)
end

################################################################################
#
#  Coercion and in function
#
################################################################################


function (K::AnticNumberField)(a::NfRelElem{nf_elem})
  K != base_field(parent(a)) && return force_coerce_throwing(K, a)
  for i in 2:degree(parent(a))
    @assert iszero(coeff(a, i - 1))
  end
  return coeff(a, 0)
end

function in(a::NfRelElem{nf_elem}, K::AnticNumberField)
  L = parent(a)
  @assert base_field(L) == K
  for i in 2:degree(parent(a))
    if !iszero(coeff(a, i - 1))
      return false
    end
  end
  return true
end


################################################################################
#
#  Basis & representation matrix
#
################################################################################

function basis_matrix(v::Vector{<: NfRelElem})
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

@doc raw"""
    absolute_representation_matrix(a::NfRelElem) -> MatrixElem

Return the absolute representation matrix of `a`, that is the matrix
representing multiplication with `a` with respect to a $\mathbb{Q}$-basis
of the parent of `a` (see [`absolute_basis(::NfRel)`](@ref)).
"""
function absolute_representation_matrix(a::NfRelElem)
  E = parent(a)
  n = absolute_degree(E)
  B = absolute_basis(E)
  m = zero_matrix(QQ, n, n)
  for i in 1:n
    bb = B[i]
    v = absolute_coordinates(a*bb)
    m[i,:] = transpose(matrix(v))
  end
  return m
end

function norm(a::NfRelElem{nf_elem}, new::Bool = !true)
  if new && is_monic(parent(a).pol) #should be much faster - eventually
    return resultant_mod(parent(a).pol, a.data)
  end
  M = representation_matrix(a)
  return det(M)
end

function norm(a::NfRelElem, new::Bool = true)
  if new && is_monic(parent(a).pol)
    return resultant(parent(a).pol, a.data)
  end
  M = representation_matrix(a)
  return det(M)
end

################################################################################
#
#  Trace
#
################################################################################

function assure_trace_basis(K::NfRel{T}) where T
  if isdefined(K, :trace_basis)
    return nothing
  end
  F = base_field(K)
  trace_basis = T[F(degree(K))]
  append!(trace_basis, polynomial_to_power_sums(K.pol, degree(K)-1))
  K.trace_basis = trace_basis
  return nothing
end

function tr(a::NfRelElem)
  K = parent(a)
  assure_trace_basis(K)
  t = coeff(a, 0)*K.trace_basis[1]
  for i = 2:degree(K)
    c = coeff(a, i-1)
    if !iszero(c)
      t += c*K.trace_basis[i]
    end
  end
  return t
end

function tr(a::NfRelElem{nf_elem})
  K = parent(a)
  assure_trace_basis(K)
  t = coeff(a, 0)*K.trace_basis[1]
  for i = 2:degree(K)
    c = coeff(a, i-1)
    if !iszero(c)
      add!(t, t, c*K.trace_basis[i])
    end
  end
  return t
end

################################################################################
#
#  Minimal and characteristic polynomial
#
################################################################################

function _poly_norm_to(f, k::T) where {T}
  if base_ring(f) isa T
    @assert (base_ring(f) isa QQField && k isa QQField) || base_ring(f) == k
    return f
  else
    return _poly_norm_to(norm(f), k)
  end
end

#TODO: investigate charpoly/ minpoly from power_sums, aka tr(a^i) and
#      Newton identities
#TODO: cache traces of powers of the generator on the field, then
#      the trace does not need the matrix

function charpoly(a::NfRelElem)
  M = representation_matrix(a)
  R = polynomial_ring(base_field(parent(a)), cached = false)[1]
  return charpoly(R, M)
end

function minpoly(a::NfRelElem{S}) where {S}
  M = representation_matrix(a)
  R = polynomial_ring(base_field(parent(a)), cached = false)[1]
  return minpoly(R, M, false)::Generic.Poly{S}
end

function charpoly(a::NfRelElem, k::Union{NfRel, AnticNumberField, QQField})
  f = charpoly(a)
  return _poly_norm_to(f, k)
end

function absolute_charpoly(a::NfRelElem)
  return charpoly(a, FlintQQ)
end

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
#  is_subfield and is_isomorphic_with_map
#
################################################################################

function is_subfield(K::NfRel, L::NfRel)
  @assert base_field(K) == base_field(L)
  f = K.pol
  g = L.pol
  if mod(degree(g), degree(f)) != 0
    return false, hom(K, L, zero(L), check = false)
  end
  Lx, x = polynomial_ring(L, "x", cached = false)
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

function is_isomorphic_with_map(K::NfRel, L::NfRel)
  @assert base_field(K) == base_field(L)
  f = K.pol
  g = L.pol
  if degree(f) != degree(g)
    return false, hom(K, L, zero(L), check = false)
  end
  return is_subfield(K, L)
end

################################################################################
#
#  Normal basis
#
################################################################################

# Mostly the same as in the absolute case
function normal_basis(L::NfRel{nf_elem}, check::Bool = false)
  O = EquationOrder(L)
  K = base_field(L)
  OK = base_ring(O)
  d = discriminant(O)

  for p in PrimeIdealsSet(OK, degree(L), -1, indexdivisors = false, ramified = false)
    if valuation(d, p) != 0
      continue
    end

    # Check if p is totally split
    F, mF = residue_field(OK, p)
    mmF = extend(mF, K)
    Ft, t = polynomial_ring(F, "t", cached = false)
    ft = map_coefficients(mmF, L.pol, parent = Ft)
    pt = powermod(t, order(F), ft)

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

################################################################################
#
#  Linear disjointness
#
################################################################################

function is_linearly_disjoint(K1::NfRel, K2::NfRel)
  if base_field(K1) != base_field(K2)
    error("Number fields must have the same base field")
  end

  if gcd(degree(K1), degree(K2)) == 1
    return true
  end

  f = change_base_ring(K2, defining_polynomial(K1))
  return is_irreducible(f)
end

################################################################################
#
#  Random elements
#
################################################################################

RandomExtensions.maketype(L::NfRel, B) = elem_type(L)

function rand(rng::AbstractRNG, sp::SamplerTrivial{<:Make2{<:NfRelElem,<:NfRel,<:UnitRange}})
  L, B = sp[][1:end]
  k = base_field(L)
  pb = basis(L)
  z = zero(L)
  for i = 1:length(pb)
    t = rand(rng, k, B)
    z += t*pb[i]
  end
  return z
end

rand(L::NfRel, B::UnitRange{Int}) = rand(GLOBAL_RNG, L, B)
rand(rng::AbstractRNG, L::NfRel, B::UnitRange{Int}) = rand(rng, make(L, B))

################################################################################
#
#  Find Kummer generator
#
################################################################################

@doc raw"""
    kummer_generator(K::NfRel{nf_elem}) -> nf_elem

Given an extension $K/k$ which is a cyclic Kummer extension of degree $n$, returns an element $a\in k$
such that $K = k(\sqrt[n]{a})$. Throws an error if the extension is not a cyclic Kummer extension.
"""
function kummer_generator(K::NfRel{nf_elem})
  n = degree(K)
  k = base_field(K)
  tuo, gen_tu = _torsion_units_gen(k)
  if !divisible(tuo, n)
    error("Not a Kummer extension!")
  end
  zeta = gen_tu^divexact(tuo, n)
  roots = powers(zeta, n-1)
  auts = automorphism_list(K)
  if length(auts) != n
    error("Not a Kummer extension!")
  end
  #TODO: Not very serious, fix this.
  gens = small_generating_set(auts, *)
  if length(gens) > 1
    error("Not a Kummer extension!")
  end
  gen_aut = gens[1]
  a = zero(K)
  stable = 10
  inter = 1
  first = true
  while iszero(a)
    stable -= 1
    if iszero(stable)
      inter += 1
      stable = 10
    end
    if first
      first = false
      b = gen(K)
    else
      b = rand(K, -inter:inter)
    end
    a = b
    new_b = b
    for i = 1:n-1
      new_b = gen_aut(new_b)
      a += roots[i+1]*new_b
    end

  end
  res = k(a^n)
  #We even reduce the support....
  res1 = reduce_mod_powers(res, n)
  return res1
end

################################################################################
#
#  Signature
#
################################################################################

function signature(L::NfRel)
  c = get_attribute(L, :signature)
  if c isa Tuple{Int, Int}
    return c::Tuple{Int, Int}
  end
  K = base_field(L)
  rlp = real_embeddings(K)
  rL = 0
  for P in rlp
    rL += n_real_roots(defining_polynomial(L), P)
  end
  @assert mod(absolute_degree(L) - rL, 2) == 0
  r, s = rL, div(absolute_degree(L) - rL, 2)
  set_attribute!(L, :signature => (r, s))
  return r, s
end

function is_totally_real(L::NfRel)
  r, s = signature(L)
  return s == 0
end

function is_totally_complex(L::NfRel)
  r, s = signature(L)
  return r == 0
end

###############################################################################
#
#  Cyclotomic field as CM-extension
#
###############################################################################

@doc raw"""
    cyclotomic_field_as_cm_extension(n::Int; cached::Bool = true)
					                  -> NfRel, NfRelElem
Given an integer `n`, return the `n`-th cyclotomic field $E = \mathbb{Q}(\zeta_n)$
seen as a quadratic extension of its maximal real subfield `K` generated by
$\zeta_n+zeta_n^{-1}$.

# Example
```jldoctest
julia> E, b = cyclotomic_field_as_cm_extension(6)
(Relative number field with defining polynomial t^2 - t + 1
 over Maximal real subfield of cyclotomic field of order 6, z_6)

julia> base_field(E)
Maximal real subfield of cyclotomic field of order 6

```
"""
function cyclotomic_field_as_cm_extension(n::Int; cached::Bool = true)
  K, a = CyclotomicRealSubfield(n, Symbol("(z_$n + 1//z_$n)"), cached = cached)
  Kt, t = polynomial_ring(K, "t", cached = false)
  E, b = number_field(t^2-a*t+1, "z_$n", cached = cached)
  set_attribute!(E, :cyclo, n)
  return E, b
end

