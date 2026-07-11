# Support for generic maximal orders over any PID
#
#   final result:
#     integral_closure(R, F)
#     where R is "any" PID and F a finite extension of some quotient field of R
#
#   R needs to support
#    - euclidean (hnf, pseudo_inv, gcd, lcm, mod, div, divrem)
#    - factorisation
#    - a useful residue_field (need to know characteristic and finiteness)
#    - integral_split, numerator, denominator
#      given a in Frac(R), decompose into num, den
#      (all Localisations of Z have QQ as quotient field,
#      Q[x], Z[x] and Localisation(Q(x), degree) use Q(t))
#    - is_domain_type
#
# Seems to work for
# -  R = ZZ, F = AbsSimpleNumField
# -  R = LocalizedEuclideanRing{ZZRingElem}, F = AbsSimpleNumField
#
# -  R = k[x], F = FunctionField (for k = QQ, F_q)
# -  R = localization(k(x), degree), F = FunctionField
# -  R = Z[x], F = FunctionField/ QQ(t)

import AbstractAlgebra: expressify

################################################################################
#
#  Creation
#
################################################################################

order(R::Ring, F::Field) = GenOrd(R, F)

order(O::GenOrd, T::MatElem, d::RingElem; check::Bool = true) = GenOrd(O, T, d; check = check)

################################################################################
#
#  Type gymnastics
#
################################################################################

function elem_type(::Type{GenOrd{S, T}}) where {S, T}
  return GenOrdElem{elem_type(S), elem_type(T)}
end

function parent_type(::Type{GenOrdElem{S, T}}) where {S, T}
  return GenOrd{parent_type(S), parent_type(T)}
end

# prepare for algebras, which are not domains
is_domain_type(::Type{GenOrdElem{S, T}}) where {S, T} = is_domain_type(S)

ideal_type(::Type{GenOrd{S, T}}) where {S, T} = GenOrdIdl{S, T}
fractional_ideal_type(::Type{GenOrd{S, T}}) where {S, T} = GenOrdFracIdl{S, T}

################################################################################
#
#  Show
#
################################################################################

function Base.show(io::IO, O::GenOrd)
  print(io, AbstractAlgebra.obj_to_string(O, context = io))
end

function AbstractAlgebra.expressify(O::GenOrd; context = nothing)
  return Expr(:sequence, Expr(:text, "Generic order in "),
                expressify(O.F, context = context),
                Expr(:text, " over "),
                expressify(O.R, context = context))
end

################################################################################
#
#  Field access
#
################################################################################

base_ring(O::GenOrd) = O.R

base_ring_type(::Type{GenOrd{S, T}}) where {S, T} = T

coefficient_ring(O::GenOrd) = O.R

field(O::GenOrd) = O.F

@inline is_equation_order(O::GenOrd) = O.is_equation_order

degree(O::GenOrd) = degree(field(O))

basis_matrix(O::GenOrd{S}) where {S} = O.trans::dense_matrix_type(elem_type(base_field_type(S)))
basis_matrix_inverse(O::GenOrd{S}) where {S} = O.itrans::dense_matrix_type(elem_type(base_field_type(S)))

function _make_canonical_in(O::GenOrd{S, T}, x) where {S, T}
  y = O.R(x)
  iszero(y) && return y::elem_type(T)
  return divexact(y, canonical_unit(y))::elem_type(T)
end

################################################################################
#
#  Basis
#
################################################################################

function basis(O::GenOrd; copy::Bool = true)
  get_attribute!(O, :basis) do
    if is_equation_order(O)
      return map(O, basis(field(O)))
    else
      return [O(O.F(vec(collect(basis_matrix(O)[i,:])))) for i=1:degree(O)]
    end
  end::Vector{elem_type(O)}
end


################################################################################
#
#  Elements
#
################################################################################

################################################################################
#
#  Field access
#
################################################################################

function parent(a::GenOrdElem{S, T}) where {S, T}
  return a.parent::GenOrd{parent_type(S), parent_type(T)}
end

function data(a::GenOrdElem)
  return a.data
end

################################################################################
#
#  Show
#
################################################################################

function Base.show(io::IO, a::GenOrdElem)
  print(io, AbstractAlgebra.obj_to_string(a.data, context = io))
end

function expressify(a::GenOrdElem; context = nothing)
  return expressify(data(a), context = context)
end

################################################################################
#
#  Creation
#
################################################################################

zero(R::GenOrd) = R(zero(field(R)), check = false)

one(R::GenOrd) = R(one(field(R)), check = false)

(R::GenOrd)() = zero(R)

function (R::GenOrd{S, T})(a::RingElement; check::Bool = true) where {S, T}
  if parent(a) === field(R)
    return GenOrdElem(R, a, check)
  elseif AbstractAlgebra.promote_rule(elem_type(T), typeof(a)) === elem_type(T)
    # a can be coerced into base_ring(R)
    # make sure to go through the base field (where base ring lives)
    F = field(R)
    return GenOrdElem(R, F(base_field(F)(a)), false)
  else
    return GenOrdElem(R, field(R)(a), true)
  end
end

function (O::GenOrd{S, T})(c::Vector) where {S, T}
  if is_equation_order(O)
    return O(O.F(c))
  else
    M = basis_matrix(O)
    return O(O.F(vec(collect(map(base_ring(M), c)*M))))
  end
end

################################################################################
#
#  Containment
#
################################################################################

function in(a::FieldElem, O::GenOrd)
  @req parent(a) === field(O) "Element and order must come from the same field"
  return is_one(integral_split(a, O)[2])
end

in(a::GenOrdElem, O::GenOrd) = data(a) in O

################################################################################
#
#  Predicates
#
################################################################################

is_zero(a::GenOrdElem) = is_zero(data(a))

is_one(a::GenOrdElem) = is_one(data(a))

################################################################################
#
#  Units
#
################################################################################

is_unit(a::GenOrdElem) = is_unit(norm(a))

################################################################################
#
#  Canonical unit
#
################################################################################

canonical_unit(a::GenOrdElem) = one(parent(a))

################################################################################
#
#  Copy
#
################################################################################

function Base.deepcopy_internal(a::GenOrdElem, dict::IdDict)
  return GenOrdElem(parent(a), Base.deepcopy_internal(data(a), dict))
end

################################################################################
#
#  Hash
#
################################################################################

function Base.hash(a::GenOrdElem, h::UInt)
  b = 0x52da43cd011aacd1%UInt
  return xor(b, hash(data(a), h))
end

################################################################################
#
#  Promote rule
#
################################################################################

function AbstractAlgebra.promote_rule(::Type{GenOrdElem{S, T}}, ::Type{U}) where {S, T, U <: NCRingElem}
  if AbstractAlgebra.promote_rule(T, U) === T
    return GenOrdElem{S, T}
  end
  return Union{}
end

################################################################################
#
#  Arithmetic
#
################################################################################

function +(a::GenOrdElem, b::GenOrdElem)
  check_parent(a, b)
  return GenOrdElem(parent(a), a.data + b.data)
end

function -(a::GenOrdElem, b::GenOrdElem)
  check_parent(a, b)
  return GenOrdElem(parent(a), a.data - b.data)
end

-(a::GenOrdElem) = GenOrdElem(parent(a), -a.data)

function *(a::GenOrdElem, b::GenOrdElem)
  check_parent(a, b)
  return GenOrdElem(parent(a), a.data * b.data)
end

function ==(a::GenOrdElem, b::GenOrdElem)
  check_parent(a, b)
  return parent(a) == parent(b) && a.data == b.data
end

Base.:^(a::GenOrdElem, n::Integer) = parent(a)(a.data^n)

function divexact(a::GenOrdElem, b::GenOrdElem; check::Bool = true)
  check_parent(a, b)
  c = divexact(data(a), data(b))
  return parent(a)(c)
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function mul!(a::GenOrdElem, b::GenOrdElem, c::GenOrdElem)
  a.data = Hecke.mul!(a.data, b.data, c.data)
  return a
end

function add!(a::GenOrdElem, b::GenOrdElem, c::GenOrdElem)
  a.data = Hecke.add!(a.data, b.data, c.data)
  return a
end

################################################################################
#
#  Trace and norm
#
################################################################################

function tr(a::GenOrdElem)
  return base_ring(parent(a))(trace(data(a)))
end

function norm(a::GenOrdElem)
  return base_ring(parent(a))(norm(data(a)))
end

################################################################################
#
#  Coordinates
#
################################################################################

function coordinates(a::FieldElem, O::GenOrd)
  if is_equation_order(O)
    return coordinates(a)
  else
    return coordinates(a) * basis_matrix_inverse(O)
  end
end

function coordinates(a::GenOrdElem)
  return coordinates(a.data, parent(a))
end

function coordinates(a::Generic.FunctionFieldElem)
  return [coeff(a, i) for i=0:degree(parent(a))-1]
end

################################################################################
#
#  Representation matrix
#
################################################################################

# For an element x of an order O we might write
#   x = sum x_i * b_i, where {b_i} is the basis of O
# This gives us RM(x) = sum x_i RM(b_i) where RM is representation matrix

@attr Vector{dense_matrix_type(elem_type(T))} function _basis_representation_matrices(O::GenOrd{S, T}) where {S, T}
  return [_representation_matrix_direct(b) for b in basis(O)]
end

# this is direct "by the book" implementation
function _representation_matrix_direct(a::GenOrdElem)
  O = parent(a)
  b = basis(O)
  n = degree(O)
  R = base_ring(O)

  m = zero_matrix(R, n, n)
  for i in 1:n
    c = coordinates(b[i]*a)
    for j in 1:n
      num, den = integral_split(c[j], R)
      @assert isone(den)
      m[i, j] = num
    end
  end

  return m
end

# this is implementation for coordinate vector over the base ring
function _representation_matrix(O::GenOrd, v::AbstractVector)
  n = degree(O)
  R = base_ring(O)
  RB = _basis_representation_matrices(O)

  @assert length(v) == n

  m = zero_matrix(R, n, n)
  t = R()
  for ci in 1:n
    c = v[ci]
    is_zero(c) && continue

    Rci = RB[ci]
    @inbounds for i in 1:n, j in 1:n
      m[i, j] = addmul!(m[i, j], c, Rci[i, j], t)
    end
  end
  return m
end

function representation_matrix(a::GenOrdElem)
  O = parent(a)
  R = base_ring(O)

  v = map(coordinates(a)) do x
    num, den = integral_split(x, R)
    @assert isone(den)
    num
  end

  return _representation_matrix(O, v)
end

################################################################################
#
#  Characteristic polynomial
#
################################################################################

function charpoly(a::GenOrdElem)
  return charpoly(representation_matrix(a))
end

function charpoly(R::PolyRing, a::GenOrdElem)
  return charpoly(R, representation_matrix(a))
end

################################################################################
#
#  Minimal polynomial
#
################################################################################

function minpoly(a::GenOrdElem)
  return minpoly(representation_matrix(a))
end

function minpoly(R::PolyRing, a::GenOrdElem)
  return minpoly(R, representation_matrix(a))
end

################################################################################
#
#  Integral split
#
################################################################################

@doc raw"""
    integral_split(a::FieldElem, O::Ring)

For an element of the quotient field of some ring $O$, decompose
$a$ as
an element $n$ in $O$ and some denominator $d$, either in $O$ or the
coefficient ring of $O$.

# EXAMPLES
```julia
julia> integral_split(1//3, ZZ)
(1, 3)

julia> k, a = quadratic_field(5);

julia> zk = maximal_order(k);

julia> integral_split(1//a, zk)
(5, [-1 2])
```
"""
function Hecke.integral_split(a::Generic.FunctionFieldElem, O::GenOrd)
  d = integral_split(coordinates(a, O), base_ring(O))[2]
  k = base_ring(parent(a))
  if d isa ZZPolyRingElem
    @assert k isa AbstractAlgebra.Generic.RationalFunctionField{QQFieldElem, QQPolyRingElem}
    dd = change_base_ring(QQ, d; parent = base_ring(Generic.underlying_fraction_field(k)))
    return O(dd*a, check = false), d
  end
  return O(k(d)*a, check = false), d
end

function Hecke.integral_split(a::AbsSimpleNumFieldElem, O::GenOrd)
  d = integral_split(coordinates(a, O), base_ring(O))[2]
  return O(d.data*a, check =false), d #evil, but no legal way found
end

function Hecke.integral_split(a::AbsSimpleNumFieldElem, O::GenOrd{<:Field, ZZRing})
  d = integral_split(coordinates(a, O), base_ring(O))[2]
  return O(d*a, check = false), d #evil, but no legal way found
end

################################################################################
#
#  Modular arithmetic
#
################################################################################

function mod(a::GenOrdElem, p::RingElem)
  O = parent(a)
  R = parent(p)
  @assert base_ring(O) === R
  S = base_field(field(O))

  if is_equation_order(O)
    mu = elem_type(O.R)[O.R(x) % p for x = coefficients(a.data)]
    return O(O.F(mu))
  else
    a = map(x->S(R(x) % p), coordinates(a))
    b = a*basis_matrix(O)
    return O(O.F(b))
  end
end

function powermod(a::GenOrdElem, n::ZZRingElem, p::RingElem)
  c = one(parent(a))
  for i = bits(n)
    c *= c
    if i
      c *= a
    end
    c = mod(c, p)
  end
  return c
end

################################################################################
#
#  Ring of multipliers
#
################################################################################

function ring_of_multipliers(O::GenOrd{S, T}, I::MatElem{P}, p::P, is_prime::Bool = false) where {S, T, P}
  #TODO: modular big hnf, peu-a-peu, not all in one
  @vprintln :GenOrd 2 "ring of multipliers module $p (is_prime: $is_prime) of ideal with basis matrix $I"
  II, d = pseudo_inv(I)
  @assert II*I == d

  m = reduce(hcat, [divexact(representation_matrix(O(vec(collect(I[i, :]))))*II, d) for i=1:nrows(I)])
  m = transpose(m)

  mm = is_prime ? _ring_of_multipliers_reduce_prime(m, p, degree(O)) :
                  _ring_of_multipliers_reduce_nonprime(m, p, degree(O))
  H = hnf_modular(mm, p, is_prime)

  @vtime :GenOrd 2 Hi, d = pseudo_inv(H)
  return GenOrd(O, transpose(Hi), d, check = false)::GenOrd{S, T}
end

# ring_of_multipliers function-barrier helpers: it fixes the return type
function _ring_of_multipliers_reduce_prime(m::M, p, n) where {M <: MatElem}
  _, mR = residue_field(parent(p), p)

  mp = map_entries(mR, m)
  mm = rref(mp[1:n, 1:n])[2]
  for i = 2:n
    mm = rref(vcat(mm, rref(mp[(i-1)*n+1:i*n, 1:n])[2]))[2]
    @assert iszero(mm[n+1:end, :])
    mm = mm[1:n, 1:n]
  end
  return map_entries(x -> preimage(mR, x), mm)::typeof(m)
end

function _ring_of_multipliers_reduce_nonprime(m::M, p, n) where {M <: MatElem}
  _, mR = residue_ring(parent(p), p)

  mp = map_entries(mR, m)
  mm = hnf(mp[1:n, 1:n])
  for i = 2:n
    mm = hnf(vcat(mm, hnf(mp[(i-1)*n+1:i*n, 1:n])))
    @assert iszero(mm[n+1:end, :])
    mm = mm[1:n, 1:n]
  end
  return map_entries(x -> preimage(mR, x), mm)::typeof(m)
end

function ring_of_multipliers(O::GenOrd, I::MatElem)
  #TODO: modular big hnf, peu-a-peu, not all in one
  @vprintln :GenOrd 2 "ring of multipliers of ideal with basis matrix $I"
  II, d = pseudo_inv(I)
  @assert II*I == d

  m = reduce(hcat, [divexact(representation_matrix(O(vec(collect(I[i, :]))))*II, d) for i=1:nrows(I)])
  m = transpose(m)
  n = degree(O)
  mm = hnf(m[1:n, 1:n])
  for i=2:n
    mm = vcat(mm, hnf(m[(i-1)*n+1:i*n, 1:n]))
    mm = hnf(mm)[1:n, 1:n]
  end
  H = mm

  @vtime :GenOrd 2 Hi, d = pseudo_inv(H)

  O = GenOrd(O, transpose(Hi), d, check = false)
  return O
end

################################################################################
#
#  Trace matrix
#
################################################################################

trace_matrix(O::GenOrd) = _trace_matrix(O, base_ring(O), identity)
trace_matrix(b::Vector{<:GenOrdElem}) = _trace_matrix(b, base_ring(b[1]), identity)

# Build the trace matrix directly over R, applying f to each entry.
# Used to materialise the trace matrix in a residue field / coefficient field
#   without an extra map_entries pass.
function _trace_matrix(b::Vector{<:GenOrdElem}, R::Ring, f)
  n = length(b)
  m = zero_matrix(R, n, n)
  for i = 1:n
    m[i, i] = f(trace(b[i]*b[i]))
    for j = i+1:n
      m[i, j] = m[j, i] = f(trace(b[i]*b[j]))
    end
  end
  return m
end

# Trace matrix of the order basis, built from the cached representation matrices.
#   Row i of RM(b_j) is the coordinate vector of b_i*b_j, so
#     tr(b_i b_j) = sum_k RM(b_j)[i, k] * tr(b_k),
#   i.e. column j of the trace matrix is RM(b_j) * t with t = (tr(b_k))_k.
# This reuses _basis_representation_matrices(O) and avoids the n^2 field products b_i*b_j
function _trace_matrix(O::GenOrd, R::Ring, f)
  n = degree(O)
  S = base_ring(O)
  RB = _basis_representation_matrices(O)
  t = matrix(S, n, 1, elem_type(S)[trace(b) for b in basis(O)])

  p = S()

  m = zero_matrix(R, n, n)
  for i in 1:n
    m[i, i] = f(_trace_matrix_entry(RB, t, i, i, p))
    for j in i+1:n
      m[i, j] = m[j, i] = f(_trace_matrix_entry(RB, t, i, j, p))
    end
  end
  return m
end

# (i, j) entry of the trace matrix [tr(b_i b_j)] from the cached representation matrices
# row i of RM(b_j) is the coordinate vector of b_i*b_j, hence
#   tr(b_i b_j) = sum_l RM(b_j)[i, l] * tr(b_l).
# p is reused scratch for the products.
function _trace_matrix_entry(RB, tvec, i::Int, j::Int, p)
  Rj = RB[j]
  s = parent(p)()
  for l in 1:length(tvec)
    s = addmul!(s, Rj[i, l], tvec[l], p)
  end
  return s
end


function trace_matrix(b::Vector{<:GenOrdElem}, c::Vector{<:GenOrdElem}, exp::ZZRingElem = ZZRingElem(1))
  O = parent(b[1])
  m = zero_matrix(coefficient_ring(O), length(b), length(c))
  for i=1:length(b)
    for j=1:length(c)
      m[i,j] = trace((b[i]*c[j])^exp)
    end
  end
  return m
end

################################################################################
#
#  p-maximal overorder
#
################################################################################

function Hecke.pmaximal_overorder(O::GenOrd, p::RingElem, is_prime::Bool = false)
  @vprintln :GenOrd 1 "computing a $p-maximal overorder"
  R, _ = residue_field(parent(p), p)

  if characteristic(R) == 0 || characteristic(R) > degree(O)
    @vprintln :GenOrd 1 "using trace-radical for $p"
    return _pmaximal_overorder_radical(O, p, is_prime, radical_basis_trace)
  elseif isa(R, Generic.RationalFunctionField)
    @vprintln :GenOrd 1 "non-perfect case for radical for $p"
    return _pmaximal_overorder_radical(O, p, is_prime, radical_basis_power_non_perfect)
  else
    @vprintln :GenOrd 1 "using radical-by-power for $p"
    return _pmaximal_overorder_radical(O, p, is_prime, radical_basis_power)
  end
end

# Function-barrier helper: F will be a concrete type here
function _pmaximal_overorder_radical(O::GenOrd, p::RingElem, is_prime::Bool, rad::F) where {F}
  while true #TODO: check the discriminant to maybe skip the last iteration
    I = rad(O, p)
    Onew = ring_of_multipliers(O, I, p, is_prime)
    if discriminant(O) == discriminant(Onew)
      return O
    end
    O = Onew
  end
end

################################################################################
#
#  Integral closure
#
################################################################################

@doc raw"""
    integral_closure(R, F)

Computes the integral closure of the ring $R$ in the field $F$. $F$ needs
to be a finite extension over the fraction field of $R$. The algorithm
uses a variant of the Round-2 method.

Currently supported are

- $R$ the integers and $F$ an (absolute simple) number field. Here the result is an number
  field order.
- $R$ a localisation of the integers and $F$ an (absolute simple) number. Here the result is
  a generic order.
- $R$ a univariate polynomial ring over a field $k$ and $F$ a function field (finite extension of $k(t)$.
- $R$ the degree-localisation of a univariate polynomial ring over a field $k$ amd $F$ a finite extension of $k(t)$
- $R$ a univariate polynomial ring over the integers and $F$ a finite extension of $Q(t)$ for the rational field $Q$.

# EXAMPLES
```julia
julia> k, a = quadratic_field(12);

julia> integral_closure(ZZ, k)

Maximal order of real quadratic field defined by x^2 - 12
with basis AbsSimpleNumFieldElem[1, 1//2*sqrt(12)]
```
"""
function integral_closure(::ZZRing, F::AbsSimpleNumField)
  return Hecke.maximal_order(F)
end

function integral_closure(S::LocalizedEuclideanRing{ZZRingElem}, F::AbsSimpleNumField)
  return _integral_closure(S, F)
end

function integral_closure(S::PolyRing{T}, F::Generic.FunctionField{T, U}) where {T, U}
  return _integral_closure(S, F)
end

function integral_closure(S::KInftyRing{T, U}, F::Generic.FunctionField{T, U}) where {T, U}
  return _integral_closure(S, F)
end

function _integral_closure(S::AbstractAlgebra.Ring, F::AbstractAlgebra.Field)
  O = GenOrd(S, F)
  return Hecke.maximal_order(O)
end

################################################################################
#
#  Transition matrix
#
################################################################################

function trans_mat(O::GenOrd{S}, OO::GenOrd{S}) where S
  if is_equation_order(O)
    return basis_matrix(OO)
  else
    return is_equation_order(OO) ? basis_matrix_inverse(O) : basis_matrix(OO) * basis_matrix_inverse(O)
  end
end

################################################################################
#
#  Maximal order
#
################################################################################

function Hecke.maximal_order(O::GenOrd)
  @vprintln :GenOrd 1 "starting maximal order..."
  S = base_ring(O)
  d = discriminant(O)
  @vprintln :GenOrd 2 "factoring the discriminant..."
  @vtime :GenOrd 2 ld = factor(d)
  local Op
  first = true
  for (p ,k) in ld
    if k < 2
      continue
    end
    OO = pmaximal_overorder(O, p, true)
    is_equation_order(OO) && continue

    T = integral_split(trans_mat(O, OO), S)
    isone(T[2]) && continue
    if first
      Op = T
      first = false
    else
      Op = (Hecke._hnf(vcat(Op[1]*T[2], T[1]*Op[2]), :lowerleft)[degree(O)+1:end, :], T[2]*Op[2])
    end
  end
  if first
    return O
  else
    return GenOrd(O, Op[1], Op[2])
  end
end

################################################################################
#
#  Discriminant
#
################################################################################

function Hecke.discriminant(O::GenOrd)
  if is_monic(defining_polynomial(O.F))
    # a polynomial discriminant is only well-defined up to a power of leading coefficient
    d = discriminant(O.F)
    if !is_equation_order(O)
      d *= det(basis_matrix(O))^2
    end
  else
    # going through trace matrix is correct in every order
    d = det(trace_matrix(O))
  end
  return O.R(d)
end

################################################################################
#
#  Basis in field
#
################################################################################

function Hecke.basis(O::GenOrd, F::Generic.FunctionField)
  return map(F, basis(O))
end

function (K::AbsSimpleNumField)(b::GenOrdElem)
  O = parent(b)
  @assert O.F == K
  return b.data
end

function Hecke.basis(O::GenOrd, F::AbsSimpleNumField)
  return map(F, basis(O))
end

#=
function (R::PolyRing{T})(a::Generic.RationalFunctionFieldElem{T}) where {T}
  @assert isone(denominator(a))
  return R(numerator(a))
end
=#

# we don't have ideals, so radical is given via a matrix where
# rows are an S-basis
#in pos. char: O/p -> O/p : x-> x^(p^l) has the radical as kernel, perfect field
function radical_basis_power(O::GenOrd, p::RingElem)
  F, mF = residue_field(parent(p), p)

  q = order(F)
  d = q
  @assert q > 0
  while d < degree(O)
    d *= q
  end

  b = basis(O)
  m = zero_matrix(F, degree(O), degree(O))
  for i=1:degree(O)
    c = coordinates(powermod(b[i], d, p))
    for j=1:degree(O)
      m[j,i] = mF(O.R(c[j]))
    end
  end
  B = kernel(m; side = :right)
#  @assert m*B == 0

  M2 = transpose(B)
  M2 = map_entries(x->preimage(mF, x), M2)
  return hnf_modular(M2, p, true, :lowerleft)
end

#in char 0 and small char: rad = {x : Tr(xO) in pR} perfect field
function radical_basis_trace(O::GenOrd{S, T}, p::RingElem) where {S, T}
  R, mR = residue_field(parent(p), p)
  M = _trace_matrix(O, R, mR)
  B = kernel(M; side = :right)
  M2 = transpose(map_entries(x->preimage(mR, x), B))
  return hnf_modular(M2, p, true, :lowerleft)
end

#pos. char, non-perfect (residue) field
function radical_basis_power_non_perfect(O::GenOrd, p::RingElem)
  F, mF = residue_field(parent(p), p)
  @assert isa(F, Generic.RationalFunctionField) && characteristic(F) != 0
  q = characteristic(F)
  @assert q > 0
  while q < degree(O)
    q *= characteristic(F)
  end
#=
  rad is still kernel of O/pO -> O/pO x -> x^(p^l), but
  this map is F_p linear, but not F-linear where F is the residue field.
  We need lin. comb. where the coefficients are all p^l-th powers, so we
  think in terms of a field extension
  F = F_p(t)/F_p(s) for s = t^(p^l)
  we want the kernel over F_p(s), not F_p(t)
=#

  q = Int(q)
  b = basis(O)
  dd = denominator(F(1))
  mm = zero_matrix(F, degree(O), degree(O))
  m = zero_matrix(F, q*degree(O), degree(O))
  for i=1:degree(O)
    c = coordinates(powermod(b[i], ZZRingElem(q), p))
    for j=1:degree(O)
      d = mF(O.R(c[j]))
      d2 = denominator(d)
      l = lcm(dd, d2)
      d *= l
      if l != dd
        mm *= divexact(l, dd)
      end
      dd = l
      mm[i,j] = d
    end
  end

  for i=1:degree(O)
    for j=1:degree(O)
      d = numerator(mm[i,j])
      for k=0:degree(d)
        iszero(coeff(d, k)) && continue
        m[(j-1)*q+(k%q)+1,i] += gen(parent(d))^div(k, q)*coeff(d, k)
      end
    end
  end
  B = kernel(m; side = :right)

  M2 = transpose(B)
  M2 = map_entries(x->preimage(mF, x), M2)
  return hnf_modular(M2, p, true, :lowerleft)
end

################################################################################
#
#  Different
#
################################################################################

# Inverse of a square matrix, fraction-free:
# clear a common denominator d to get N over base ring; pseudo_inv(N) gives
# X, dd with N*X = dd*I (dd = +-det N) via fraction-free LU, so inv(T) = (d/dd)*X.
# Keeps elimination in base ring! This is especially important for function fields.
# NOTE: for finite order all the denominators are 1, so the function could be simplified
#   but this is not true for infinite order, so we keep the trivial lcm gathering
# NOTE: this is NOT a replacement for general matrix inv
# Trace matrix is dense with polynomial entries of moderate degrees, so normal inv
#   will spend a lot of time doing divexact bringing to reduced row-echelon
# But, for example, basis_matrix or inv used in colon have a triangular matrix
#   and in this case general matrix inv is immediate (back substitution essentially)
#   while pseudo_inv needs to do some work.
#
# Exception: over QQ, inv is FLINT's fmpq_mat_inv, which already clears
# denominators and eliminates fraction-free in C. The explicit clearing below
# would only add Julia-level lcm/coercion overhead, so delegate to inv there.
_fraction_free_inv(T::QQMatrix) = inv(T)

function _fraction_free_inv(T::MatElem)
  @req nrows(T) == ncols(T) "matrix must be square"
  n = nrows(T)
  K = base_ring(T)

  # clear denominators
  d = mapreduce(denominator, lcm, T)
  # construct the matrix N (T = 1/d * N)
  N = matrix(parent(d), [numerator(T[i, j]*d) for i in 1:n, j in 1:n])

  X, dd = pseudo_inv(N)
  return K(d//dd)*change_base_ring(K, X)
end

@doc raw"""
    codifferent(O::GenOrd) -> GenOrdFracIdl

The codifferent ideal of $O$, i.e. the trace-dual of $O$.
"""
function codifferent(O::GenOrd)
  K = base_field(field(O))
  return fractional_ideal(O, _fraction_free_inv(_trace_matrix(O, K, K)))
end

function different(x::GenOrdElem)
  if iszero(x)
    return x
  end
  f = minpoly(x)
  if degree(f) < degree(parent(x))
    return parent(x)(0)
  end
  return derivative(f)(x)
end

@doc raw"""
    different(O::GenOrd) -> GenOrdIdl

The different ideal of $O$, that is, the ideal generated by all differents
of elements in $R$.
For Gorenstein orders, this is also the inverse ideal of the co-different.
"""
function different(O::GenOrd)
  return inv(codifferent(O))
end

###############################################################################
#
#   Conformance test element generation
#
###############################################################################

function ConformanceTests.generate_element(O::GenOrd{<:Any, ZZRing})
  B = basis(O)
  return sum(rand(-10:10) * B[i] for i in 1:degree(O))
end
