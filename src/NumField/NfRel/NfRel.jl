################################################################################
#
#  RelSimpleNumField/RelSimpleNumField.jl : Relative number field extensions
#
################################################################################

################################################################################
#
#  Copy
#
################################################################################

function Base.deepcopy_internal(a::RelSimpleNumFieldElem{T}, dict::IdDict) where T
  z = RelSimpleNumFieldElem{T}(Base.deepcopy_internal(data(a), dict))
  z.parent = parent(a)
  return z
end

################################################################################
#
#  Comply with ring interface
#
################################################################################

function iszero(a::RelSimpleNumFieldElem)
  reduce!(a)
  return iszero(data(a))
end

function isone(a::RelSimpleNumFieldElem)
  reduce!(a)
  return isone(data(a))
end

zero(K::RelSimpleNumField) = K(zero(parent(K.pol)))

one(K::RelSimpleNumField) = K(one(parent(K.pol)))

function zero!(a::RelSimpleNumFieldElem)
  zero!(a.data)
  return a
end

################################################################################
#
#  Order types
#
################################################################################

order_type(::Type{RelSimpleNumField{T}}) where {T} = RelNumFieldOrder{T, fractional_ideal_type(order_type(parent_type(T))), RelSimpleNumFieldElem{T}}

################################################################################
#
#  Field access
#
################################################################################

@inline base_field(a::RelSimpleNumField{T}) where {T} = a.base_ring::parent_type(T)

@inline data(a::RelSimpleNumFieldElem) = a.data

@inline parent(a::RelSimpleNumFieldElem{T}) where {T} = a.parent::RelSimpleNumField{T}

@inline is_simple(a::RelSimpleNumField) = true

################################################################################
#
#  Coefficient setting and getting
#
################################################################################

@inline coeff(a::RelSimpleNumFieldElem{T}, i::Int) where {T} = coeff(a.data, i)

@inline setcoeff!(a::RelSimpleNumFieldElem{T}, i::Int, c::T) where {T} = setcoeff!(a.data, i, c)

# copy does not do anything (so far), this is only for compatibility with coefficients(::AbstractAssociativeAlgebraElem)
function coefficients(a::RelSimpleNumFieldElem{T}; copy::Bool = false) where {T}
  return T[coeff(a, i) for i = 0:degree(parent(a)) - 1 ]
end

################################################################################
#
#  Degree
#
################################################################################

@inline degree(L::Hecke.RelSimpleNumField) = degree(L.pol)

################################################################################
#
#  Reduction
#
################################################################################

function reduce!(a::RelSimpleNumFieldElem)
  a.data = mod(a.data, parent(a).pol)
  return a
end

################################################################################
#
#  mod(::RelSimpleNumFieldElem, ::ZZRingElem) as in the absolute case
#
################################################################################

function mod(a::RelSimpleNumFieldElem{T}, p::ZZRingElem) where T <: NumFieldElem
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

function Base.show(io::IO, ::MIME"text/plain", a::RelSimpleNumField)
  println(io, "Relative number field with defining polynomial ", a.pol)
  io = pretty(io)
  print(io, Indent(), "over ", Lowercase())
  show(io, MIME"text/plain"(), base_field(a))
  print(io, Dedent())
end

function Base.show(io::IO, a::RelSimpleNumField)
  if is_terse(io)
    print(io, "Relative number field")
  else
    io = pretty(io)
    print(io, "Relative number field of degree ", degree(a), " over ")
    print(terse(io), Lowercase(), base_field(a))
  end
end

function AbstractAlgebra.expressify(a::RelSimpleNumFieldElem; context = nothing)
  return AbstractAlgebra.expressify(data(a), var(parent(a)), context = context)
end

function Base.show(io::IO, a::RelSimpleNumFieldElem)
  print(io, AbstractAlgebra.obj_to_string(a, context = io))
end

################################################################################
#
#  Constructors and parent object overloading
#
################################################################################

function number_field(f::PolyRingElem{T}, S::VarName = "_\$";
                     cached::Bool = false, check::Bool = true)  where {T <: NumFieldElem}
  check && !is_irreducible(f) && error("Polynomial must be irreducible")
  K = RelSimpleNumField{T}(f, Symbol(S), cached)
  return K, K(gen(parent(f)))
end

#Conversion to absolute non simple
function number_field(::Type{AbsSimpleNumField}, L::RelSimpleNumField{AbsSimpleNumFieldElem}; check::Bool = true, cached::Bool = true)
  @assert degree(base_field(L)) == 1
  pol = to_univariate(Globals.Qx, map_coefficients(QQ, L.pol, cached = false))
  return number_field(pol, check = false, cached = cached)
end

function (K::RelSimpleNumField{T})(a::Generic.Poly{T}) where T <: NumFieldElem
  z = RelSimpleNumFieldElem{T}(mod(a, K.pol))
  z.parent = K
  return z
end

function (K::RelSimpleNumField{T})(a::T) where T <: NumFieldElem
  parent(a) != base_ring(parent(K.pol)) && error("Cannot coerce")
  z = RelSimpleNumFieldElem{T}(parent(K.pol)(a))
  z.parent = K
  return z
end

(K::RelSimpleNumField)(a::Integer) = K(parent(K.pol)(a))

(K::RelSimpleNumField)(a::Rational{T}) where {T <: Integer} = K(parent(K.pol)(a))

(K::RelSimpleNumField)(a::ZZRingElem) = K(parent(K.pol)(a))

(K::RelSimpleNumField)(a::QQFieldElem) = K(parent(K.pol)(a))

(K::RelSimpleNumField)() = zero(K)

gen(K::RelSimpleNumField) = K(gen(parent(K.pol)))

################################################################################
#
#  Unary operators
#
################################################################################

function Base.:(-)(a::RelSimpleNumFieldElem)
  return parent(a)(-data(a))
end

################################################################################
#
#  Binary operators
#
################################################################################

function Base.:(+)(a::RelSimpleNumFieldElem{T}, b::RelSimpleNumFieldElem{T}) where {T}
  parent(a) == parent(b) || force_op(+, a, b)::RelSimpleNumFieldElem{T}
  return parent(a)(data(a) + data(b))
end

function Base.:(-)(a::RelSimpleNumFieldElem{T}, b::RelSimpleNumFieldElem{T}) where {T}
  parent(a) == parent(b) || force_op(-, a, b)::RelSimpleNumFieldElem{T}
  return parent(a)(data(a) - data(b))
end

function Base.:(*)(a::RelSimpleNumFieldElem{T}, b::RelSimpleNumFieldElem{T}) where {T}
  parent(a) == parent(b) || force_op(*, a, b)::RelSimpleNumFieldElem{T}
  return parent(a)(data(a) * data(b))
end

function divexact(a::RelSimpleNumFieldElem{T}, b::RelSimpleNumFieldElem{T}; check::Bool = true) where {T}
  b == 0 && error("Element not invertible")
  parent(a) == parent(b) || force_op(divexact, a, b)::RelSimpleNumFieldElem{T}
  return a*inv(b)
end

Base.:(//)(a::RelSimpleNumFieldElem{T}, b::RelSimpleNumFieldElem{T}) where {T} = divexact(a, b)

################################################################################
#
#  Inversion
#
################################################################################

function Base.inv(a::RelSimpleNumFieldElem)
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

Base.:(^)(a::RelSimpleNumFieldElem, n::UInt) = a^Int(n)

function Base.:(^)(a::RelSimpleNumFieldElem, n::Int)
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

function Base.:(^)(a::RelSimpleNumFieldElem, b::ZZRingElem)
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

function Base.:(==)(a::RelSimpleNumFieldElem{T}, b::RelSimpleNumFieldElem{T}) where T
  reduce!(a)
  reduce!(b)
  parent(a) == parent(b) || force_op(==, a, b)::Bool
  return data(a) == data(b)
end

if !isdefined(Nemo, :promote_rule1)
  function Base.:(==)(a::RelSimpleNumFieldElem{T}, b::Union{Integer, Rational}) where T
    return a == parent(a)(b)
  end
end

################################################################################
#
#  Ad hoc operators
#
################################################################################

function Base.:(*)(a::RelSimpleNumFieldElem{T}, b::T) where {T <: NumFieldElem}
  return parent(a)(data(a) * b)
end

Base.:(*)(a::T, b::RelSimpleNumFieldElem{T}) where {T <: NumFieldElem} = b * a

function Base.:(+)(a::RelSimpleNumFieldElem{T}, b::T) where {T <: NumFieldElem}
  return parent(a)(data(a) + b)
end

Base.:(+)(a::T, b::RelSimpleNumFieldElem{T}) where {T <: NumFieldElem} = b + a

function Base.:(-)(a::RelSimpleNumFieldElem{T}, b::T) where {T <: NumFieldElem}
  return parent(a)(data(a) - b)
end

function Base.:(-)(a::T, b::RelSimpleNumFieldElem{T}) where {T <: NumFieldElem}
  return parent(b)(a - data(b))
end

function divexact(a::RelSimpleNumFieldElem{T}, b::T; check::Bool=true) where {T <: NumFieldElem}
  return parent(a)(divexact(data(a), b; check=check))
end

Base.:(//)(a::RelSimpleNumFieldElem{T}, b::T) where {T <: NumFieldElem} = divexact(a, b)

for F in [ZZRingElem, QQFieldElem, Int]
  @eval begin
    function Base.:(*)(a::RelSimpleNumFieldElem{T}, b::$F) where {T <: NumFieldElem}
      return parent(a)(data(a) * b)
    end

    Base.:(*)(a::$F, b::RelSimpleNumFieldElem{T}) where {T <: NumFieldElem} = b * a

    function Base.:(+)(a::RelSimpleNumFieldElem{T}, b::$F) where {T <: NumFieldElem}
      return parent(a)(data(a) + b)
    end

    Base.:(+)(a::$F, b::RelSimpleNumFieldElem{T}) where {T <: NumFieldElem} = b + a

    function Base.:(-)(a::RelSimpleNumFieldElem{T}, b::$F) where {T <: NumFieldElem}
      return parent(a)(data(a) - b)
    end

    function Base.:(-)(a::$F, b::RelSimpleNumFieldElem{T}) where {T <: NumFieldElem}
      return parent(b)(a - data(b))
    end

    function divexact(a::RelSimpleNumFieldElem{T}, b::$F; check::Bool=true) where {T <: NumFieldElem}
      return parent(a)(divexact(data(a), b; check=check))
    end

    Base.:(//)(a::RelSimpleNumFieldElem{T}, b::$F) where {T <: NumFieldElem} = divexact(a, b)
  end
end


################################################################################
#
#  Unsafe operations
#
################################################################################

function mul!(c::RelSimpleNumFieldElem{T}, a::RelSimpleNumFieldElem{T}, b::RelSimpleNumFieldElem{T}) where {T}
  mul!(c.data, a.data, b.data)
  c = reduce!(c)
  return c
end

function mul!(c::RelSimpleNumFieldElem{T}, a::RelSimpleNumFieldElem{T}, b::T) where {T}
  mul!(c.data, a.data, b)
  c = reduce!(c)
  return c
end

function add!(c::RelSimpleNumFieldElem{T}, a::RelSimpleNumFieldElem{T}, b::RelSimpleNumFieldElem{T}) where {T}
  add!(c.data, a.data, b.data)
  c = reduce!(c)
  return c
end

################################################################################
#
#  Hash function
#
################################################################################

function hash(a::Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}, b::UInt)
  return hash(a.data, b)
end

################################################################################
#
#  Coercion and in function
#
################################################################################


function (K::AbsSimpleNumField)(a::RelSimpleNumFieldElem{AbsSimpleNumFieldElem})
  K != base_field(parent(a)) && return force_coerce_throwing(K, a)
  for i in 2:degree(parent(a))
    @assert iszero(coeff(a, i - 1))
  end
  return coeff(a, 0)
end

function in(a::RelSimpleNumFieldElem{AbsSimpleNumFieldElem}, K::AbsSimpleNumField)
  L = parent(a)
  @assert base_field(L) == K
  for i in 2:degree(parent(a))
    if !iszero(coeff(a, i - 1))
      return false
    end
  end
  return true
end

function (K::QQField)(a::RelSimpleNumFieldElem)
  for i in 2:degree(parent(a))
    @req iszero(coeff(a, i - 1)) "Element must be rational"
  end
  return QQ(coeff(a, 0))
end

function is_rational(a::RelSimpleNumFieldElem)
  for i in 2:degree(parent(a))
    if !iszero(coeff(a, i - 1))
      return false
    end
  end
  return is_rational(coeff(a, 0))
end

################################################################################
#
#  Basis & representation matrix
#
################################################################################

function basis_matrix(v::Vector{<: RelSimpleNumFieldElem})
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

function elem_to_mat_row!(M::Generic.Mat{T}, i::Int, a::RelSimpleNumFieldElem{T}) where T
  for c = 1:ncols(M)
    M[i, c] = deepcopy(coeff(a, c - 1))
  end
  return nothing
end

function elem_from_mat_row(L::RelSimpleNumField{T}, M::Generic.Mat{T}, i::Int) where T
  t = L(1)
  a = L()
  for c = 1:ncols(M)
    a += M[i, c]*t
    mul!(t, t, gen(L))
  end
  return a
end

function representation_matrix(a::RelSimpleNumFieldElem)
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
    absolute_representation_matrix(a::RelSimpleNumFieldElem) -> MatrixElem

Return the absolute representation matrix of `a`, that is the matrix
representing multiplication with `a` with respect to a $\mathbb{Q}$-basis
of the parent of `a` (see [`absolute_basis(::RelSimpleNumField)`](@ref)).
"""
function absolute_representation_matrix(a::RelSimpleNumFieldElem)
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

function norm(a::RelSimpleNumFieldElem{AbsSimpleNumFieldElem}, new::Bool = !true)
  if new && is_monic(parent(a).pol) #should be much faster - eventually
    return resultant_mod(parent(a).pol, a.data)
  end
  M = representation_matrix(a)
  return det(M)
end

function norm(a::RelSimpleNumFieldElem, new::Bool = true)
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

function assure_trace_basis(K::RelSimpleNumField{T}) where T
  if isdefined(K, :trace_basis)
    return nothing
  end
  F = base_field(K)
  trace_basis = T[F(degree(K))]
  append!(trace_basis, polynomial_to_power_sums(K.pol, degree(K)-1))
  K.trace_basis = trace_basis
  return nothing
end

function tr(a::RelSimpleNumFieldElem)
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

function tr(a::RelSimpleNumFieldElem{AbsSimpleNumFieldElem})
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

function charpoly(a::RelSimpleNumFieldElem)
  M = representation_matrix(a)
  R = polynomial_ring(base_field(parent(a)), cached = false)[1]
  return charpoly(R, M)
end

function minpoly(a::RelSimpleNumFieldElem{S}) where {S}
  M = representation_matrix(a)
  R = polynomial_ring(base_field(parent(a)), cached = false)[1]
  return minpoly(R, M, false)::Generic.Poly{S}
end

function charpoly(a::RelSimpleNumFieldElem, k::Union{RelSimpleNumField, AbsSimpleNumField, QQField})
  f = charpoly(a)
  return _poly_norm_to(f, k)
end

function absolute_charpoly(a::RelSimpleNumFieldElem)
  return charpoly(a, QQ)
end

function (R::Generic.PolyRing{AbsSimpleNumFieldElem})(a::RelSimpleNumFieldElem{AbsSimpleNumFieldElem})
  if base_ring(R)==base_field(parent(a))
    return a.data
  end
  error("wrong ring")
end

function (R::Generic.PolyRing{RelSimpleNumFieldElem{T}})(a::RelSimpleNumFieldElem{RelSimpleNumFieldElem{T}}) where T
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

function is_subfield(K::RelSimpleNumField, L::RelSimpleNumField)
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

function is_isomorphic_with_map(K::RelSimpleNumField, L::RelSimpleNumField)
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
function normal_basis(L::RelSimpleNumField{AbsSimpleNumFieldElem}, check::Bool = false)
  O = equation_order(L)
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

function is_linearly_disjoint(K1::RelSimpleNumField, K2::RelSimpleNumField)
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

RandomExtensions.maketype(L::RelSimpleNumField, B) = elem_type(L)

function rand(rng::AbstractRNG, sp::SamplerTrivial{<:Make2{<:RelSimpleNumFieldElem,<:RelSimpleNumField,<:AbstractUnitRange}})
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

rand(L::RelSimpleNumField, B::AbstractUnitRange{Int}) = rand(GLOBAL_RNG, L, B)
rand(rng::AbstractRNG, L::RelSimpleNumField, B::AbstractUnitRange{Int}) = rand(rng, make(L, B))

################################################################################
#
#  Find Kummer generator
#
################################################################################

@doc raw"""
    kummer_generator(K::RelSimpleNumField{AbsSimpleNumFieldElem}) -> AbsSimpleNumFieldElem

Given an extension $K/k$ which is a cyclic Kummer extension of degree $n$, returns an element $a\in k$
such that $K = k(\sqrt[n]{a})$. Throws an error if the extension is not a cyclic Kummer extension.
"""
function kummer_generator(K::RelSimpleNumField{AbsSimpleNumFieldElem})
  n = degree(K)
  k = base_field(K)
  tuo, gen_tu = _torsion_units_gen(k)
  if !is_divisible_by(tuo, n)
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

function signature(L::RelSimpleNumField)
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

function is_totally_real(L::RelSimpleNumField)
  r, s = signature(L)
  return s == 0
end

function is_totally_complex(L::RelSimpleNumField)
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
					                  -> RelSimpleNumField, RelSimpleNumFieldElem
Given an integer `n`, return the `n`-th cyclotomic field $E = \mathbb{Q}(\zeta_n)$
seen as a quadratic extension of its maximal real subfield `K` generated by
$\zeta_n+zeta_n^{-1}$.

# Example
```jldoctest
julia> E, b = cyclotomic_field_as_cm_extension(6)
(Relative number field of degree 2 over maximal real subfield of cyclotomic field of order 6, z_6)

julia> base_field(E)
Number field with defining polynomial $ - 1
  over rational field

```
"""
function cyclotomic_field_as_cm_extension(n::Int; cached::Bool = true)
  K, a = cyclotomic_real_subfield(n, Symbol("(z_$n + 1//z_$n)"), cached = cached)
  Kt, t = polynomial_ring(K, "t", cached = false)
  E, b = number_field(t^2-a*t+1, "z_$n", cached = cached)
  set_attribute!(E, :cyclo, n)
  return E, b
end

#################################################################################
##
##  Integral multiple
##
#################################################################################
#
#function _integral_multiplicator(a::RelSimpleNumFieldElem)
#  f = minpoly(a)
#  return lcm(ZZRingElem[_integral_multiplicator(c) for c in coefficients(f)])
#end
