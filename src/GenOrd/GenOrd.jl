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

Order(R::Ring, F::Field) = GenOrd(R, F)

Order(O::GenOrd, T::MatElem, d::RingElem; check::Bool = true) = GenOrd(O, T, d; check = check)

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

_is_standard(O::GenOrd) = O.is_standard

degree(O::GenOrd) = degree(field(O))

basis_matrix(O::GenOrd{S}) where {S} = O.trans::dense_matrix_type(elem_type(base_field(field(O))))

basis_matrix_inverse(O::GenOrd{S}) where {S} = O.itrans::dense_matrix_type(elem_type(base_field(field(O))))

################################################################################
#
#  Basis
#
################################################################################

function basis(O::GenOrd; copy::Bool = true)
  get_attribute!(O, :basis) do
    if _is_standard(O)
      return map(O, basis(field(O)))
    else
      return [O(O.F(vec(collect(O.trans[i,:])))) for i=1:degree(O)]
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
  return expressify(base_ring(R), context = context)
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
    # so a can be coerced into base_ring(R), remove the check
    return GenOrdElem(R, field(R)(a), false)
  else
    return GenOrdElem(R, field(R)(a), true)
  end
end

function (O::GenOrd)(c::Vector)
  if _is_standard(O)
    return O(O.F(c))
  else
    return O(O.F(vec(collect(map(base_ring(O.trans), c)*O.trans))))
  end
end

################################################################################
#
#  Containment
#
################################################################################

function in(a::GenOrdElem, O::GenOrd)
  @assert field(parent(a)) === field(O)
  return isone(integral_split(data(a), O)[2])
end

function Base.in(a::FieldElem, O::GenOrd)
  @assert parent(a) === field(O)
  return isone(integral_split(data(a), O)[2])
end

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
  c = coordinates(a)
  if _is_standard(O)
    d = coordinates(a)
  else
    d = coordinates(a) * basis_matrix_inverse(O)
  end
  return d
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

function representation_matrix(a::GenOrdElem)
  O = parent(a)
  b = basis(O)
  m = zero_matrix(base_ring(O), degree(O), degree(O))
  for i in 1:degree(O)
    c = coordinates(b[i]*a)
    for j in 1:degree(O)
      m[i, j] = numerator(c[j], base_ring(O))
      @assert isone(denominator(c[j], base_ring(O)))
    end
  end
  return m
end

################################################################################
#
#  Characteristic polynomial
#
################################################################################

function charpoly(a::GenOrdElem)
  return charpoly(representation_matrix(a))
end

################################################################################
#
#  Minimal polynomial
#
################################################################################

function minpoly(a::GenOrdElem)
  return minpoly(representation_matrix(a))
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
  return O(base_ring(parent(a))(d)*a, check = false), d
end

function Hecke.integral_split(a::AbsSimpleNumFieldElem, O::GenOrd)
  d = integral_split(coordinates(a, O), base_ring(O))[2]
  return O(d.data*a, check =false), d #evil, but no legal way found
end

function Hecke.integral_split(a::AbsSimpleNumFieldElem, O::GenOrd{<: Any, ZZRing})
  d = integral_split(coordinates(a, O), base_ring(O))[2]
  return O(d*a, check = false), d #evil, but no legal way found
end

#############################3333333333333333333333############################3
#
#  Modular arithmetic
#
################################################################################

function mod(a::GenOrdElem, p::RingElem)
  O = parent(a)
  R = parent(p)
  @assert base_ring(O) === R
  S = base_field(field(O))

  if _is_standard(O)
    mu = elem_type(O.R)[O.R(x) % p for x = coefficients(a.data)]
    return O(O.F(mu))
  else
    a = map(x->S(R(x) % p), coordinates(a))
    b = a*O.trans
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

function ring_of_multipliers(O::GenOrd, I::MatElem{T}, p::T, is_prime::Bool = false) where {T}
  #TODO: modular big hnf, peu-a-peu, not all in one
  @vprintln :AbsNumFieldOrder 2 "ring of multipliers module $p (is_prime: $is_prime) of ideal with basis matrix $I"
  II, d = pseudo_inv(I)
  @assert II*I == d

  m = reduce(hcat, [divexact(representation_matrix(O(vec(collect(I[i, :]))))*II, d) for i=1:nrows(I)])
  m = transpose(m)
  if is_prime
    x = residue_field(parent(p), p)
    if isa(x, Tuple)
      R, mR = x
    else
      R = x
      mR = MapFromFunc(parent(p), R, x->R(x), x->lift(x))
    end
    ref = x->rref(x)[2]
  else
    x = residue_ring(parent(p), p)
    if isa(x, Tuple)
      R, mR = x
    else
      R = x
      mR = MapFromFunc(parent(p), R, x->R(x), x->lift(x))
    end
#    R = parent(p)
#    mR = MapFromFunc(R, R, x->x, x->x)
    ref = hnf
  end
  m = map_entries(mR, m)

  n = degree(O)
  mm = ref(m[1:n, 1:n])
  for i=2:n
    mm = vcat(mm, ref(m[(i-1)*n+1:i*n, 1:n]))
    mm = ref(mm)
    @assert iszero(mm[n+1:end, :])
    mm = mm[1:n, 1:n]
  end
#  H = hnf(map_entries(x->preimage(mR, x), mm))
  H = hnf_modular(map_entries(x->preimage(mR, x), mm), p, is_prime)

  @vtime :AbsNumFieldOrder 2 Hi, d = pseudo_inv(H)

  O = GenOrd(O, transpose(Hi), d, check = false)
  return O
end

function ring_of_multipliers(O::GenOrd, I::MatElem)
  #TODO: modular big hnf, peu-a-peu, not all in one
  @vprintln :AbsNumFieldOrder 2 "ring of multipliers of ideal with basis matrix $I"
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

  @vtime :AbsNumFieldOrder 2 Hi, d = pseudo_inv(H)

  O = GenOrd(O, transpose(Hi), d, check = false)
  return O
end

################################################################################
#
#  Trace matrix
#
################################################################################

function trace_matrix(O::GenOrd)
  return trace_matrix(basis(O))
end

function trace_matrix(b::Vector{<:GenOrdElem})
  O = parent(b[1])
  m = zero_matrix(base_ring(O), length(b), length(b))
  for i=1:length(b)
    m[i, i] = trace(b[i]*b[i])
    for j=i+1:length(b)
      m[i, j] = m[j, i] = trace(b[i]*b[j])
    end
  end
  return m
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
  @vprintln :AbsNumFieldOrder 1 "computing a $p-maximal orderorder"

  t = residue_field(parent(p), p)

  if isa(t, Tuple)
    R, mR = t
  else
    R = t
    mR = MapFromFunc(parent(p), R, x->R(x), y->lift(y))
  end
#  @assert characteristic(F) == 0 || (isfinite(F) && characteristic(F) > degree(O))
  if characteristic(R) == 0 || characteristic(R) > degree(O)
    @vprintln :AbsNumFieldOrder 1 "using trace-radical for $p"
    rad = radical_basis_trace
  elseif isa(R, Generic.RationalFunctionField)
    @vprintln :AbsNumFieldOrder 1 "non-perfect case for radical for $p"
    rad = radical_basis_power_non_perfect
  else
    @vprintln :AbsNumFieldOrder 1 "using radical-by-power for $p"
    rad = radical_basis_power
  end
  while true #TODO: check the discriminant to maybe skip the last iteration
    I = rad(O, p)
    S = ring_of_multipliers(O, I, p, is_prime)
    if discriminant(O) == discriminant(S)
      return O
    end
    O = S
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

Maximal order of Real quadratic field defined by x^2 - 12
with basis AbsSimpleNumFieldElem[1, 1//2*sqrt(12)]
```
"""
function integral_closure(::ZZRing, F::AbsSimpleNumField)
  return Hecke.maximal_order(F)
end

function integral_closure(S::LocalizedEuclideanRing{ZZRingElem}, F::AbsSimpleNumField)
  return _integral_closure(S, F)
end

function integral_closure(S::PolyRing{T}, F::Generic.FunctionField{T}) where {T}
  return _integral_closure(S, F)
end

function integral_closure(S::KInftyRing{T}, F::Generic.FunctionField{T}) where {T}
  return _integral_closure(S, F)
end

function _integral_closure(S::AbstractAlgebra.Ring, F::AbstractAlgebra.Ring)
  O = GenOrd(S, F)
  return Hecke.maximal_order(O)
end

################################################################################
#
#  Transition matrix
#
################################################################################

function trans_mat(O::GenOrd, OO::GenOrd)
  if isdefined(O, :trans)
    if isdefined(OO, :trans)
      return OO.trans*O.itrans
    else
      return O.itrans
    end
  else
    if isdefined(OO, :trans)
      return OO.trans
    else
      error("no matrices, giving up")
    end
  end
end

################################################################################
#
#  Maximal order
#
################################################################################

function Hecke.maximal_order(O::GenOrd)
  @vprintln :AbsNumFieldOrder 1 "starting maximal order..."
  S = base_ring(O)
  d = discriminant(O)
  @vprintln :AbsNumFieldOrder 2 "factoring the discriminant..."
  @vtime :AbsNumFieldOrder 2 ld = factor(d)
  local Op
  first = true
  for (p,k) = ld.fac
    if k<2
      continue
    end
    OO = pmaximal_overorder(O, p, true)
    if !isdefined(OO, :trans)
      continue
    end
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
  d = discriminant(O.F)
  if isdefined(O, :trans)
    d *= det(O.trans)^2
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
  t = residue_field(parent(p), p)
  if isa(t, Tuple)
    F, mF = t
  else
    F = t
    mF = MapFromFunc(parent(p), F, x->F(x), y->lift(y))
  end
#  @assert characteristic(F) == 0 || (isfinite(F) && characteristic(F) > degree(O))
  q = characteristic(F)
  @assert q > 0
  while q < degree(O)
    q *= characteristic(F)
  end

  b = basis(O)
  m = zero_matrix(F, degree(O), degree(O))
  for i=1:degree(O)
    c = coordinates(powermod(b[i], q, p))
    for j=1:degree(O)
      m[j,i] = mF(O.R(c[j]))
    end
  end
  B = kernel(m; side = :right)

  M2 = transpose(B)
  M2 = map_entries(x->preimage(mF, x), M2)
  M3 = Hecke.hnf_modular(M2, p, true)
  return M3 #[O(vec(collect((M3[i, :])))) for i=1:degree(O)]
end

#in char 0 and small char: rad = {x : Tr(xO) in pR} perfect field
function radical_basis_trace(O::GenOrd, p::RingElem)
  T = trace_matrix(O)

  t = residue_field(parent(p), p)
  if isa(t, Tuple)
    R, mR = t
  else
    R = t
    mR = MapFromFunc(parent(p), R, x->R(x), y->lift(y))
  end

  TT = map_entries(mR, T)
  B = kernel(TT; side = :right)
  M2 = transpose(map_entries(x->preimage(mR, x), B))
  M3 = Hecke.hnf_modular(M2, p, true)
  return M3 #[O(vec(collect((M3[i, :])))) for i=1:degree(O)]
end

#pos. char, non-perfect (residue) field
function radical_basis_power_non_perfect(O::GenOrd, p::RingElem)
  t = residue_field(parent(p), p)
  if isa(t, Tuple)
    F, mF = t
  else
    F = t
    mF = MapFromFunc(parent(p), F, x->F(x), y->lift(y))
  end
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
  M3 = Hecke.hnf_modular(M2, p, true)
  return return M3 #[O(vec(collect((M3[i, :])))) for i=1:degree(O)]
end

################################################################################
#
#  Different
#
################################################################################


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

@doc raw"""
    codifferent(R::AbsNumFieldOrder) -> AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}

The codifferent ideal of $R$, i.e. the trace-dual of $R$.
"""
function codifferent(O::GenOrd)
   B = basis(O)
   R = base_ring(O.F)
   n = degree(O)
   mat_entries = elem_type(R)[]
   for u in B
     for v in B
       push!(mat_entries, R(trace(u*v)))
     end
   end
  return fractional_ideal(O, inv(matrix(R, n, n, mat_entries)))
end
