"""
Support for generic maximal orders over any PID

  final result:
    integral_closure(R, F)
    where R is "any" PID and F a finite extension of some quotient field of R

  R needs to support
   - euclidean (hnf, pseudo_inv, gcd, lcm, mod, div, divrem)
   - factorisation
   - a useful residue_field (need to know characteristic and finiteness)
   - integral_split, numerator, denominator
     given a in Frac(R), decompose into num, den
     (all Localisations of Z have QQ as quotient field,
     Q[x], Z[x] and Localisation(Q(x), degree) use Q(t))
   - is_domain_type

Seems to work for
-  R = ZZ, F = AbsSimpleNumField
-  R = LocalizedEuclideanRing{ZZRingElem}, F = AbsSimpleNumField

-  R = k[x], F = FunctionField (for k = QQ, F_q)
-  R = localization(k(x), degree), F = FunctionField
-  R = Z[x], F = FunctionField/ QQ(t)
"""
module GenericRound2

using Hecke
import Hecke.AbstractAlgebra, Hecke.Nemo
import Base: +, -, *, gcd, lcm, divrem, div, rem, mod, ^, ==
export integral_closure
import AbstractAlgebra: expressify

#TODO: type parametrisation....
mutable struct Order{S, T} <: AbstractAlgebra.Ring
  F::S
  R::T
  trans#::dense_matrix_type(base_ring(S))
  itrans#::dense_matrix_type(base_ring(S))
  is_standard::Bool

  function order(R::AbstractAlgebra.Ring, F::AbstractAlgebra.Field, empty::Bool = false; check::Bool = true)
    #empty allows to create an Order that is none:
    # Z[x]/3x+1 is no order. This will be "fixed" by using any_order, but
    #the initial shell needs to be empty (illegal)
    r = new{typeof(F), typeof(R)}()
    r.F = F
    r.R = R
    r.is_standard = true
    empty && return r
    Qt = base_ring(F)
    d = reduce(lcm, map(x->denominator(x, R), coefficients(defining_polynomial(F))))
    f = map_coefficients(x->Qt(d*numerator(x, R)),defining_polynomial(F))
    if !is_monic(f) #need Lenstra Order
      d = degree(F)
      M = zero_matrix(Qt, d, d)
      M[1, 1] = one(Qt)
      for i in 2:d
        for j in i:-1:2
          M[i, j] = coeff(f, d - (i - j))
        end
      end
      O = order(r, M, one(Qt), check = check)
      return O
    end
    return r
  end

  function order(O::Order, T::MatElem, d::RingElem; check::Bool = true)
    F = base_ring(O.F)
    T = map_entries(F, T)
    T = divexact(T, base_ring(T)(d))
    Ti = inv(T)
    r = order(O.R, O.F, true)
    if isdefined(O, :trans)
      r.trans = T*O.trans
      r.itrans = O.itrans*Ti
    else
      r.trans = T
      r.itrans = Ti
    end
    check && map(representation_matrix, basis(r))
    r.is_standard = false
    return r
  end
end

_is_standard(O::Order) = O.is_standard

function Base.show(io::IO, O::Order)
  print(io, AbstractAlgebra.obj_to_string(O, context = io))
end

function expressify(O::Order; context = nothing)
  return Expr(:sequence, Expr(:text, "generic order in "),
                expressify(O.F, context = context),
                Expr(:text, " over "),
                expressify(O.R, context = context))
end

Hecke.base_ring(O::Order) = O.R

basis_matrix(O::Order{S}) = O.trans::dense_matrix_type(elem_type(S))

basis_matrix_inverse(O::Order{S}) = O.itrans::dense_matrix_type(elem_type(S))

mutable struct OrderElem <: RingElem
  parent :: Order
  data :: FieldElem
  coord :: Vector{RingElem}

  function OrderElem(O::Order, f::FieldElem)
    @assert parent(f) == O.F
    r = new()
    r.parent = O
    r.data = f
    return r
  end
  function OrderElem(O::Order, f::ZZRingElem)
    return OrderElem(O, O.F(f))
  end
end

_is_standard(O) = O.is_standard

basis_matrix(O::Order{S}) = O.trans::dense_matrix_type(elem_type(S))

basis_matrix_inverse(O::Order{S}) = O.itrans::dense_matrix_type(elem_type(S))

function Base.show(io::IO, a::OrderElem)
  print(io, AbstractAlgebra.obj_to_string(a.data, context = io))
end

function expressify(a::OrderElem; context = nothing)
  return expressify(base_ring(R), context = context)
end

Nemo.elem_type(::Order) = OrderElem
Nemo.parent_type(::OrderElem) = Order
Nemo.parent_type(::Type{OrderElem}) = Order
Nemo.is_domain_type(::Type{OrderElem}) = true

Base.parent(a::OrderElem) = a.parent

(R::Order)(a::FieldElem) = OrderElem(R, a)
(R::Order)(a::ZZRingElem) = OrderElem(R, a)
(R::Order)(a::Integer) = OrderElem(R, ZZRingElem(a))
(R::Order)(a::OrderElem) = OrderElem(R, a.data)
(R::Order)() = R(0)


Nemo.iszero(a::OrderElem) = iszero(a.c)
Nemo.isone(a::OrderElem) = isone(a.c) && isone(a.f) && isone(a.g)

Nemo.zero(R::Order) = R(0)
Nemo.one(R::Order) = R(1)
Nemo.canonical_unit(a::OrderElem) = OrderElem(parent(a), ZZRingElem(1))

Base.deepcopy_internal(a::OrderElem, dict::IdDict) = OrderElem(parent(a), Base.deepcopy_internal(a.data, dict))

+(a::OrderElem, b::OrderElem) = check_parent(a, b) && OrderElem(parent(a), a.data + b.data)
-(a::OrderElem, b::OrderElem) = check_parent(a, b) && OrderElem(parent(a), a.data - b.data)
-(a::OrderElem) = OrderElem(parent(a), -a.data)
*(a::OrderElem, b::OrderElem) = check_parent(a, b) && OrderElem(parent(a), a.data * b.data)

==(a::OrderElem, b::OrderElem) = check_parent(a, b) && parent(a) == parent(b) && a.data == b.data

function Hecke.mul!(a::OrderElem, b::OrderElem, c::OrderElem)
  a.data = Hecke.mul!(a.data, b.data, c.data)
  return a
end

function Hecke.add!(a::OrderElem, b::OrderElem, c::OrderElem)
  a.data = Hecke.add!(a.data, b.data, c.data)
  return a
end

function Hecke.tr(a::OrderElem)
  return parent(a).R(trace(a.data))
end

function Hecke.coordinates(a::OrderElem)
  c = coordinates(a.data)
  O = parent(a)
  if isdefined(O, :itrans)
    d = matrix(c)'*O.itrans
  else
    d = matrix(c)'
  end
  return d
end

function Hecke.coordinates(a::Generic.FunctionFieldElem)
  return [coeff(a, i) for i=0:degree(parent(a))-1]
end

Hecke.degree(O::Order) = degree(O.F)

function Hecke.basis(O::Order)
  if isdefined(O, :itrans)
    return [O(O.F(vec(collect(O.trans[i,:])))) for i=1:degree(O)]
  else
    return map(O, basis(O.F))
  end
end

function (O::Order)(c::Vector)
  if isdefined(O, :itrans)
    return O(O.F(vec(collect(matrix(map(base_ring(O.trans), c))'*O.trans))))
  else
    return O(O.F(c))
  end
end

Base.:^(a::OrderElem, n::Integer) = parent(a)(a.data^n)

function Hecke.representation_matrix(a::OrderElem)
  O = parent(a)
  b = basis(O)
  m = zero_matrix(base_ring(O), degree(O), degree(O))
  for i=1:degree(O)
    c = coordinates(b[i]*a)
    for j=1:degree(O)
      m[i,j] = numerator(c[j], base_ring(O))
      @assert isone(denominator(c[j], base_ring(O)))
    end
  end
  return m
end

function Hecke.charpoly(a::OrderElem)
  return charpoly(representation_matrix(a))
end

function Hecke.minpoly(a::OrderElem)
  return minpoly(representation_matrix(a))
end

######################################################################
#
# pure function field
#
######################################################################
struct FFElemCoeffs{T <: RingElement}
   f::T
end

function Nemo.coefficients(f::Generic.FunctionFieldElem)
   return FFElemCoeffs(f)
end

function Base.iterate(PC::FFElemCoeffs, st::Int = -1)
   st += 1
   if st > degree(parent(PC.f))
       return nothing
   else
       return coeff(PC.f, st), st
   end
end
Base.length(PC::FFElemCoeffs) = degree(parent(PC.f))

#####################################################################
#
# towards round2:
#   p-radical
#     via powers in perfect field case, finite char.
#     via powers in F_p(t) (non-perfect)
#     via trace if char 0 or char > degree
#   ring of multipliers
#

function Hecke.mod(a::OrderElem, p::RingElem)
  O = parent(a)
  R = parent(p)
  S = base_ring(O.F)

  if isdefined(O, :itrans)
    a = map(x->S(R(x) % p), coordinates(a))
    b = a*O.trans
    return O(O.F(vec(collect(b'))))
  else
    return O(O.F([O.R(x) % p for x = coefficients(a.data)]))
  end
end

function Hecke.powermod(a::OrderElem, n::ZZRingElem, p::RingElem)
  c = parent(a)(1)
  for i = Hecke.bits(n)
    c *= c
    if i
      c *= a
    end
    c = Hecke.mod(c, p)
  end
  return c
end

# we don't have ideals, so radical is given via a matrix where
# rows are an S-basis
#in pos. char: O/p -> O/p : x-> x^(p^l) has the radical as kernel, perfect field
function radical_basis_power(O::Order, p::RingElem)
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

  M2 = B'
  M2 = map_entries(x->preimage(mF, x), M2)
  M3 = Hecke.hnf(vcat(M2, p*identity_matrix(parent(p), degree(O))))[1:degree(O), :]
  return M3 #[O(vec(collect((M3[i, :])))) for i=1:degree(O)]
end

#in char 0 and small char: rad = {x : Tr(xO) in pR} perfect field
function radical_basis_trace(O::Order, p::RingElem)
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
  M2 = map_entries(x->preimage(mR, x), B)'
  M3 = Hecke.hnf(vcat(M2, p*identity_matrix(parent(p), degree(O))))[1:degree(O), :]
  return return M3 #[O(vec(collect((M3[i, :])))) for i=1:degree(O)]
end

#pos. char, non-perfect (residue) field
function radical_basis_power_non_perfect(O::Order, p::RingElem)
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

  M2 = B'
  M2 = map_entries(x->preimage(mF, x), M2)
  M3 = Hecke.hnf(vcat(M2, p*identity_matrix(parent(p), degree(O))))[1:degree(O), :]
  return return M3 #[O(vec(collect((M3[i, :])))) for i=1:degree(O)]
end

function Hecke.representation_matrix(a::Generic.FunctionFieldElem)
  F = parent(a)
  g = gen(F)
  m = zero_matrix(base_ring(F), degree(F), degree(F))
  b = a
  for i=1:degree(F)
    for j=1:degree(F)
      m[i,j] = coeff(b, j-1)
    end
    if i<degree(F)
      b *= g
    end
  end
  return m
end

function ring_of_multipliers(O::Order, I::MatElem)
  #TODO: modular big hnf, peu-a-peu, not all in one
  @vprintln :AbsNumFieldOrder 2 "ring of multipliers of ideal with basis matrix $I"
  II, d = pseudo_inv(I)
  @assert II*I == d
#  return II, d, [representation_matrix(O(vec(collect(I[i, :])))) for i=1:nrows(I)]
  m = reduce(hcat, [divexact(representation_matrix(O(vec(collect(I[i, :]))))*II, d) for i=1:nrows(I)])
  m = m'
  n = degree(O)
  mm = hnf(m[1:n, 1:n])
  for i=2:n
    mm = vcat(mm, hnf(m[(i-1)*n+1:i*n, 1:n]))
    mm = hnf(mm)[1:n, 1:n]
  end
  H = mm

  @vtime :AbsNumFieldOrder 2 Hi, d = pseudo_inv(H)

  O = order(O, Hi', d)
  return O
end

function Hecke.trace_matrix(O::Order)
  return trace_matrix(basis(O))
end

function Hecke.trace_matrix(b::Vector{OrderElem})
  O = parent(b[1])
  m = zero_matrix(O.R, length(b), length(b))
  for i=1:length(b)
    m[i,i] = trace(b[i]*b[i])
    for j=i+1:length(b)
      m[i,j] = m[j,i] = trace(b[i]*b[j])
    end
  end
  return m
end

function Hecke.trace_matrix(b::Vector{OrderElem}, c::Vector{OrderElem}, exp::ZZRingElem = ZZRingElem(1))
  O = parent(b[1])
  m = zero_matrix(O.R, length(b), length(c))
  for i=1:length(b)
    for j=1:length(c)
      m[i,j] = trace((b[i]*c[j])^exp)
    end
  end
  return m
end

function Hecke.pmaximal_overorder(O::Order, p::RingElem)
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
    S = ring_of_multipliers(O, I)
    if discriminant(O) == discriminant(S)
      return O
    end
    O = S
  end
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
  O = order(S, F)
  return Hecke.maximal_order(O)
end

function Hecke.maximal_order(O::Order)
  S = base_ring(O)
  d = discriminant(O)
  ld = factor(d)
  local Op
  first = true
  for (p,k) = ld.fac
    if k<2
      continue
    end
    OO = pmaximal_overorder(O, p)
    if !isdefined(OO, :trans)
      continue
    end
    T = integral_split(OO.trans, S)
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
    return order(O, Op[1], Op[2])
  end
end

function Hecke.discriminant(O::Order)
  d = discriminant(O.F)
  if isdefined(O, :trans)
    d *= det(O.trans)^2
  end
  return O.R(d)
end

function Hecke.basis(O::Order, F::Generic.FunctionField)
  return map(F, basis(O))
end

function Hecke.basis(F::Generic.FunctionField)
  a = gen(F)
  bas = [a^0, a]
  while length(bas) < degree(F)
    push!(bas, bas[end]*a)
  end
  return bas
end

Hecke.base_ring(::AbsSimpleNumField) = QQ

function (R::PolyRing{T})(a::Generic.RationalFunctionFieldElem{T}) where {T}
  @assert isone(denominator(a))
  return R(numerator(a))
end

function (F::Generic.FunctionField{T})(p::PolyRingElem{<:AbstractAlgebra.Generic.RationalFunctionFieldElem{T}}) where {T}
  @assert parent(p) == parent(F.pol)
  @assert degree(p) < degree(F) # the reduction is not implemented
  R = parent(gen(F).num)
  S = base_ring(R)
  d = reduce(lcm, map(denominator, coefficients(p)), init = one(S))
  return F(map_coefficients(S, d*p, parent = R), d)
end

function (F::Generic.FunctionField)(c::Vector{<:RingElem})
  return F(parent(F.pol)(map(base_ring(F), c)))
end

(F::Generic.FunctionField)(a::OrderElem) = a.data

function Hecke.charpoly(a::Generic.FunctionFieldElem)
  return charpoly(representation_matrix(a))
end

function Hecke.minpoly(a::Generic.FunctionFieldElem)
  return minpoly(representation_matrix(a))
end

function Hecke.discriminant(F::Generic.FunctionField)
  return discriminant(defining_polynomial(F))
end

#######################################################################
#
# support for ZZ
#
#######################################################################
Hecke.denominator(a::QQFieldElem, ::ZZRing) = denominator(a)
Hecke.numerator(a::QQFieldElem, ::ZZRing) = numerator(a)
Hecke.integral_split(a::QQFieldElem, ::ZZRing) = (numerator(a), denominator(a))

#######################################################################
#
# support for LocalizedEuclideanRing{ZZRingElem}
#
#######################################################################
function Hecke.integral_split(a::QQFieldElem, R::LocalizedEuclideanRing{ZZRingElem})
  d = denominator(a)
  p = R.prime
  q,w = Hecke.ppio(d, p)
  if R.comp # den can ONLY use prime
    return R(numerator(a)//q), R(w)
  else
    return R(numerator(a)//w), R(q)
  end
end
Hecke.denominator(a::QQFieldElem, R::LocalizedEuclideanRing{ZZRingElem}) = integral_split(a, R)[2]
Hecke.numerator(a::QQFieldElem, R::LocalizedEuclideanRing{ZZRingElem}) = integral_split(a, R)[1]
(::QQField)(a::LocalizedEuclideanRingElem{ZZRingElem}) = data(a)

function Hecke.factor(a::LocalizedEuclideanRingElem{ZZRingElem})
  c = canonical_unit(a)
  b = a*inv(c)
  L = parent(a)
  @assert isone(denominator(data(b)))
  lf = factor(numerator(data(b)))
  return Fac(c, Dict(L(p)=>v for (p,v) = lf.fac))
end

function Hecke.residue_field(R::LocalizedEuclideanRing{ZZRingElem}, p::LocalizedEuclideanRingElem{ZZRingElem})
  pp = numerator(data(p))
  @assert is_prime(pp) && isone(denominator(p))
  F = GF(pp)
  return F, MapFromFunc(R, F, x->F(data(x)), y->R(lift(y)))
end

Hecke.is_domain_type(::Type{LocalizedEuclideanRingElem{ZZRingElem}}) = true

#######################################################################
#
# support for RationalFunctionFieldElem{T}
#
#######################################################################
# RationalFunctionFieldElem{T}, KInftyRing{T}

Base.denominator(x::AbstractAlgebra.Generic.RationalFunctionFieldElem{T}, R::KInftyRing{T}) where {T} = Hecke.integral_split(x, R)[2]
Base.numerator(x::AbstractAlgebra.Generic.RationalFunctionFieldElem{T}, R::KInftyRing{T}) where {T} = Hecke.integral_split(x, R)[1]

function Hecke.integral_split(x::AbstractAlgebra.Generic.RationalFunctionFieldElem{T}, R::KInftyRing{T}) where {T}
  if iszero(x)
    return zero(R), one(R)
  end
  a = degree(numerator(x))
  b = degree(denominator(x))
  if b >= a
    return R(x), one(R)
  end
  t = gen(parent(x))
  return R(x*t^(b-a)), R(t^(b-a))
end

(R::Generic.RationalFunctionField{QQFieldElem})(x::KInftyElem{QQFieldElem}) = x.d

# RationalFunctionFieldElem{T}, PolyRing{T}
function Hecke.numerator(a::Generic.RationalFunctionFieldElem{T}, S::PolyRing{T}) where {T}
  return numerator(a)
end

function Hecke.denominator(a::Generic.RationalFunctionFieldElem{T}, S::PolyRing{T}) where {T}
  return denominator(a)
end

function Hecke.integral_split(a::Generic.RationalFunctionFieldElem{T}, S::PolyRing{T}) where {T}
  return numerator(a), denominator(a)
end

function Hecke.factor(R::Generic.PolyRing{T}, a::Generic.RationalFunctionFieldElem{T}) where {T}
  @assert parent(numerator(a)) == R
  f1 = factor(numerator(a))
  f2 = factor(denominator(a))
  for (p,e) = f2.fac
    @assert !haskey(f1.fac, p)
    f1.fac[p] = -e
  end
  f1.unit = divexact(f1.unit, f2.unit)
  return f1
end

########################################################################
#
# Matrices
#
########################################################################
function Hecke.integral_split(M::MatElem{<:AbstractAlgebra.FieldElem}, S::Generic.Ring)
  m = zero_matrix(S, nrows(M), ncols(M))
  den = one(S)
  for i=1:nrows(M)
    for j=1:ncols(M)
      n, d = integral_split(M[i,j], S)
      q, r = divrem(den, d)
      if iszero(r)
        m[i,j] = n*q
      else
        t = lcm(den, d)
        m *= divexact(t, den)
        m[i,j] = n*divexact(t, d)
        den = t
      end
    end
  end
  return m, den
end

end  # ModuleRound2

"""
  The ring ZZ<x> := {c f/g | c in ZZ, f, g in ZZ[x], primitive, pos leading coeff}
  is a PID, even euclidean

  The key interest is
  IntCls(Z[x], F) = IntCls(Z<x>, F) cap IntCls(Q[x], F)
  Since Z<x> and Q[x] are PID (even euclidean) the last 2 can be
  computed using the Round2

  The name is bad, but stems from Florian Hess' PhD thesis,
  Chapter 2.10
  (Actually he covers that for a Dedekind ring R we have that
   R<x> is also Dedekind. The Round2, fundamentally would work
   for Dedekind rings, using PMats)
"""
module HessQRModule
using Hecke
import Hecke.AbstractAlgebra, Hecke.Nemo
import Base: +, -, *, gcd, lcm, divrem, div, rem, mod, ^, ==
export HessQR
import AbstractAlgebra: expressify

struct HessQR <: AbstractAlgebra.Ring
  R::ZZPolyRing
  Qt::Generic.RationalFunctionField{QQFieldElem}

  function HessQR(R::ZZPolyRing, Qt::Generic.RationalFunctionField)
    new(R, Qt)
  end
end

function Base.show(io::IO, R::HessQR)
  print(io, AbstractAlgebra.obj_to_string(R, context = io))
end

function expressify(R::HessQR; context = nothing)
  return Expr(:sequence, Expr(:text, "extended valuation ring over "),
                         expressify(R.R, context = context),
                         Expr(:text, " in "),
                         expressify(R.Qt, context = context))
end

mutable struct HessQRElem <: RingElem
  parent::HessQR
  c::ZZRingElem
  f::ZZPolyRingElem
  g::ZZPolyRingElem

  function HessQRElem(P::HessQR, c::ZZRingElem, f::ZZPolyRingElem, g::ZZPolyRingElem)
    if iszero(c) || iszero(f)
      r = new(P, ZZRingElem(0), zero(P.R), one(P.R))
      @assert parent(r.f) == P.R
      @assert parent(r.g) == P.R
      return r
    end
    if parent(f) != P.R
      f = map_coefficients(ZZ, f, parent = P.R)
    end
    if parent(g) != P.R
      g = map_coefficients(ZZ, g, parent = P.R)
    end
    gc = gcd(f, g)
    f = divexact(f, gc)
    g = divexact(g, gc)
    cf = content(f)*sign(leading_coefficient(f))
    cg = content(g)*sign(leading_coefficient(g))
    @assert (c*cf) % cg == 0
    r = new(P, divexact(c*cf, cg), divexact(f, cf), divexact(g, cg))
    @assert parent(r.f) == P.R
    @assert parent(r.g) == P.R
    return r
  end
  function HessQRElem(P::HessQR, q::Generic.RationalFunctionFieldElem{QQFieldElem})
    f = numerator(q)
    g = denominator(q)
    return HessQRElem(P, f, g)
  end
  function HessQRElem(P::HessQR, f::QQPolyRingElem)
    return HessQRElem(P, f, one(parent(f)))
  end
  function HessQRElem(P::HessQR, f::QQPolyRingElem, g::QQPolyRingElem)
    df = reduce(lcm, map(denominator, coefficients(f)), init = ZZRingElem(1))
    dg = reduce(lcm, map(denominator, coefficients(g)), init = ZZRingElem(1))
    ff = map_coefficients(ZZ, df*f, parent = P.R)
    gg = map_coefficients(ZZ, dg*g, parent = P.R)
    #ff/df//gg/dg = dg/df * ff/gg
    return HessQRElem(P, divexact(dg, df), ff, gg)
  end
  function HessQRElem(P::HessQR, c::ZZRingElem)
    r = new(P, c, one(P.R), one(P.R))
    @assert parent(r.f) == P.R
    @assert parent(r.g) == P.R
    return r
  end
  function HessQRElem(P::HessQR, c::ZZPolyRingElem)
    d = content(c)*sign(leading_coefficient(c))
    r = new(P, d, divexact(c, d), one(P.R))
    @assert parent(r.f) == P.R
    @assert parent(r.g) == P.R
    return r
  end
end

function Base.show(io::IO, a::HessQRElem)
  print(io, AbstractAlgebra.obj_to_string(a, context = io))
end

function expressify(a::HessQRElem; context = nothing)
  return  Expr(:call, :*, expressify(a.c, context = context),
             Expr(:call, ://, expressify(a.f, context = context),
                              expressify(a.g, context = context)))
end

function Hecke.integral_split(a::Generic.RationalFunctionFieldElem{QQFieldElem}, S::HessQR)
  if iszero(a)
    return zero(S), one(S)
  end
  n = numerator(a)
  d = denominator(a)
  dn = reduce(lcm, map(denominator, coefficients(n)), init = ZZRingElem(1))
  dd = reduce(lcm, map(denominator, coefficients(d)), init = ZZRingElem(1))
  zn = S.R(n*dn)
  zd = S.R(d*dd)
  cn = content(zn)
  cd = content(zd)
  zn = divexact(zn, cn)
  zd = divexact(zd, cd)
  cn *= dd
  cd *= dn
  g = gcd(cn, cd)
  cn = divexact(cn, g)
  cd = divexact(cd, g)
  return HessQRElem(S, cn, zn, zd), S(cd)
end

function Hecke.numerator(a::Generic.RationalFunctionFieldElem, S::HessQR)
  return integral_split(a, S)[1]
end

function Hecke.denominator(a::Generic.RationalFunctionFieldElem, S::HessQR)
  return integral_split(a, S)[2]
end

Nemo.elem_type(::HessQR) = HessQRElem
Nemo.elem_type(::Type{HessQR}) = HessQRElem
Nemo.parent_type(::HessQRElem) = HessQR
Nemo.parent_type(::Type{HessQRElem}) = HessQR
Nemo.is_domain_type(::Type{HessQRElem}) = true

Base.parent(a::HessQRElem) = a.parent

(R::HessQR)(a::Generic.RationalFunctionFieldElem{QQFieldElem}) = HessQRElem(R, a)
(R::HessQR)(a::ZZRingElem) = HessQRElem(R, a)
(R::HessQR)(a::Integer) = HessQRElem(R, ZZRingElem(a))
(R::HessQR)(a::ZZPolyRingElem) = HessQRElem(R, a)
(R::HessQR)(a::QQPolyRingElem) = HessQRElem(R, a)
(R::HessQR)(a::HessQRElem) = a
(R::HessQR)() = R(0)

(F::Generic.RationalFunctionField)(a::HessQRElem) = a.c*F(a.f)//F(a.g)


Nemo.iszero(a::HessQRElem) = iszero(a.c)
Nemo.isone(a::HessQRElem) = isone(a.c) && isone(a.f) && isone(a.g)

Nemo.zero(R::HessQR) = R(0)
Nemo.one(R::HessQR) = R(1)
Nemo.canonical_unit(a::HessQRElem) = HessQRElem(parent(a), ZZRingElem(sign(a.c)), a.f, a.g)

Base.deepcopy_internal(a::HessQRElem, dict::IdDict) = HessQRElem(parent(a), Base.deepcopy_internal(a.c, dict), Base.deepcopy_internal(a.f, dict), Base.deepcopy_internal(a.g, dict))

Base.hash(a::HessQRElem, u::UInt=UInt(12376599)) = hash(a.g, hash(a.f, hash(a.c, u)))

+(a::HessQRElem, b::HessQRElem) = check_parent(a, b) && HessQRElem(parent(a), ZZRingElem(1), a.c*a.f*b.g+b.c*b.f*a.g, a.g*b.g)
-(a::HessQRElem, b::HessQRElem) = check_parent(a, b) && HessQRElem(parent(a), ZZRingElem(1), a.c*a.f*b.g-b.c*b.f*a.g, a.g*b.g)
-(a::HessQRElem) = HessQRElem(parent(a), -a.c, a.f, a.g)
*(a::HessQRElem, b::HessQRElem) = check_parent(a, b) && HessQRElem(parent(a), a.c*b.c, a.f*b.f, a.g*b.g)

==(a::HessQRElem, b::HessQRElem) = check_parent(a, b) && a.c*a.f == b.c *b.f && a.g == b.g

Base.:^(a::HessQRElem, n::Int) = HessQRElem(parent(a), a.c^n, a.f^n, a.g^n)

function Hecke.mul!(a::HessQRElem, b::HessQRElem, c::HessQRElem)
  d = b*c
  @assert parent(a.f) == parent(d.f)
  @assert parent(a.g) == parent(d.g)
  a.c = d.c
  a.f = d.f
  a.g = d.g
  return a
end

function Hecke.add!(a::HessQRElem, b::HessQRElem, c::HessQRElem)
  d = b+c
  @assert parent(a.f) == parent(d.f)
  @assert parent(a.g) == parent(d.g)
  a.c = d.c
  a.f = d.f
  a.g = d.g
  return a
end

function divrem(a::HessQRElem, b::HessQRElem)
  check_parent(a, b)
  if iszero(b)
    error("div by 0")
  end
  if iszero(a)
    return a, a
  end
  #= af/g mod b:
    it is enough to figure this out for b in Z>0, the rest is units
    that will disappaear into the quotient q

    - c = cont(g mod d), then since cont(g) is 1, c is a unit mod d
    - cd = 1 mod d, then
    - cont(g(cx^?+1) mod d) = 1 if ? = deg(g)+1 (or larger):
      g(cx?+1) = cg x^? + g and cont(cg mod d = 1)...
    - af/g -d/(cx^?+1) now has a denominator with cont( mod d) = 1
    - af/g - (af - du)/(g - dv) =
      (af(g-dv) -g(af-du))/(g(g-dv)) = d*..., so once cont(g %d) =1,
      we can replace f and g mod d (and figure out the quotient afterwards)

    - for d = p a prime, the rep is unique, thus F_p(t)
  =#
  r = rem(a,b)
  return divexact(a-r, b), r

  return HessQRElem(parent(a), q, a.f*b.g, a.g*b.f), HessQRElem(parent(a), r, a.f, a.g)
end

function div(a::HessQRElem, b::HessQRElem)
  check_parent(a, b)
  if iszero(a)
    return a
  end
  return divexact(a-rem(a, b), b)
  q = div(a.c, b.c)
  return HessQRElem(parent(a), q, a.f*b.g, a.g*b.f)
end

function rem(a::HessQRElem, b::HessQRElem)
  check_parent(a, b)
  if iszero(a)
    return a
  end
  #see above for reasoning
  d = abs(b.c)
  if isone(d)
    return zero(parent(a))
  end
  R = parent(a).R
  gd = mod(a.g, d)
  c = content(gd)
  if !isone(c)
    ci = invmod(c, d)
    e = ci*gen(parent(gd))^(degree(a.g)+1)+1
  else
    ci = ZZRingElem(1)
    e = parent(gd)(1)
  end
  f = a.c*a.f*e
  g = a.g*e
  gd = mod(g, d)
  @assert content(gd) == 1

  fd = mod(f, d)
  @assert content(fd) < d
  r = HessQRElem(parent(a), ZZRingElem(1), fd, gd)
  @assert abs(r.c) < d
  return r
end

function Nemo.divexact(a::HessQRElem, b::HessQRElem; check::Bool = false)
  check_parent(a, b)
  q = HessQRElem(parent(a), divexact(a.c, b.c; check = true), a.f*b.g, a.g*b.f)
  @assert q*b == a
  return q
end

function gcd(a::HessQRElem, b::HessQRElem)
  return HessQRElem(parent(a), gcd(a.c, b.c))
end

function Nemo.gcdx(a::HessQRElem, b::HessQRElem)
  check_parent(a, b)
  R = parent(a)
  g, u, v = Nemo.gcdx(a.c, b.c)
  q,w, e =  R(g), HessQRElem(R, u, a.g, a.f), HessQRElem(R, v, b.g, b.f)
  @assert q == w*a+e*b
  return q, w, e
end

function lcm(a::HessQRElem, b::HessQRElem)
  check_parent(a, b)
  return HessQRElem(parent(a), lcm(a.c, b.c))
end

Hecke.is_unit(a::HessQRElem) = is_unit(a.c)

function Nemo.residue_field(a::HessQR, b::HessQRElem)
  @assert parent(b) == a
  @assert is_prime(b.c)
  F = GF(b.c)
  Ft, t = rational_function_field(F, String(var(a.R)), cached = false)
  R = parent(numerator(t))
  return Ft, MapFromFunc(a, Ft,
                         x->F(x.c)*Ft(map_coefficients(F, x.f, parent = R))//Ft(map_coefficients(F, x.g, parent = R)),
                         y->HessQRElem(a, ZZRingElem(1), map_coefficients(lift, numerator(y)), map_coefficients(lift, denominator(y))))
end

function Nemo.residue_ring(a::HessQR, b::HessQRElem)
  F, _ = residue_ring(ZZ, b.c)
  return F, MapFromFunc(a, F, x->F(x.c), y->a(lift(y)))
end

function Hecke.factor(a::HessQRElem)
  f = factor(a.c)
  R = parent(a)
  return Fac(R(a.f), Dict((R(p),k) for (p,k) = f.fac))
end

function Hecke.factor(R::HessQR, a::Generic.RationalFunctionFieldElem)
  d1 = reduce(lcm, map(denominator, coefficients(numerator(a))), init = ZZRingElem(1))
  f1 = factor(R(d1*numerator(a)))
  d2 = reduce(lcm, map(denominator, coefficients(denominator(a))), init = ZZRingElem(1))
  f2 = factor(R(d1*denominator(a)))

  for (p,k) = f2.fac
    if haskey(f1.fac, p)
      f1.fac[p] -= k
    else
      f1.fac[p] = k
    end
  end
  f1.unit = divexact(f1.unit, f2.unit)
  return f1
end

function Hecke.is_constant(a::HessQRElem)
  return iszero(a) || (is_constant(a.f) && is_constant(a.g))
end

end

using .HessQRModule
using .GenericRound2

export HessQR, integral_closure

module HessMain
using Hecke
using ..HessQRModule, ..GenericRound2

function GenericRound2.integral_closure(S::HessQR, F::Generic.FunctionField{T}) where {T}
  return GenericRound2._integral_closure(S, F)
end

function _gcdx(a::QQFieldElem, b::QQFieldElem)
  l = lcm(denominator(a), denominator(b))
  g, e, f = gcdx(numerator(a*l), numerator(b*l))
  return g//l, e, f
end

#=
  base case:
  given
    a 0
    b c
  where a, b, c are polynomials, deg b < deg c
  do Q[x]-col transforms and Z<x>-row transforms (HessQR) to get diagonal.

  Several steps.
  Input
  a*alpha 0
  b*beta  c*gamma
  where a, b, c in Q, alpha, beta, gamma in Z[x], primitive

  Step 1:
  alpha is a Z<x> unit, so
  ->
    a       0
    b*beta  c*gamma
  is valid row-transform

  Step 2:
    g = gcd(a, b) = ea + fb (via common denominator of a, b, g), so in particular
    a/g, b/g, e, f in Z

    more row-tranforms:
    e*beta       f          a      0           g*beta   c*f*gamma
    -b/g*beta    a/g    *   b*beta c gamma  =  0        a/g*c*gamma

    det(trans) = (ea+fb)/g * beta = beta is a Z<x> unit

  Step 3:
    Q[x] col. operations: since deg beta < deg gamma we get
    g*beta (c*f*gamma mod g*beta)
    0      a/g*c*gamma

  Step 4: row and col swap
    a/g*c*gamma 0
    d*delta     g*beta  (d*delta :=  (c*f*gamma mod g*beta))

    and deg delta < deg beta

  This is iterated until delta == 0
=#

function two_by_two(Q::MatElem{<:Generic.RationalFunctionFieldElem{_T}}, R::PolyRing{_T}, S::HessQR) where {_T}
  @assert size(Q) == (2,2)

  Qt = base_ring(Q)
  T1 = identity_matrix(Qt, 2)
  T2 = identity_matrix(Qt, 2)
  while !iszero(Q[2,1])
    @assert all(x->isone(denominator(x, R)), Q)
    @assert iszero(Q[1,2])
    @assert degree(numerator(Q[2,1])) < degree(numerator(Q[2,2]))

    n, d = integral_split(Q[1,1], S)
    @assert is_constant(d)
    a = n.c//d.c
    Q[1,1] = a
    c = Qt(n)//Qt(d)*inv(Q[1,1])
    @assert is_unit(c)
    T1[1,:] *= inv(c)
    n, d = integral_split(Q[2,1], S)
    b = n.c//d.c
    beta = Q[2,1]//b

    g, e, f = _gcdx(a, b)
    T = matrix(Qt, 2, 2, [e*beta, Qt(f), -Q[2,1]//g, Q[1,1]//g])
    Q = T*Q
    @assert iszero(Q[2,1])
    T1 = T*T1

    if iszero(Q[1,2])
      return Q, T1, T2
    end

    n, d = integral_split(Q[1,1], R)
    @assert isone(d)
    nn, d = integral_split(Q[1,2], R)
    @assert isone(d)
    @assert degree(nn) > degree(n)
    q, r = divrem(nn, n)

    T = matrix(Qt, 2, 2, [Qt(1), -q, Qt(0), Qt(1)])
    Q = Q*T
    T2 = T2 * T

    swap_cols!(Q, 1, 2)
    swap_cols!(T2, 1, 2)
    swap_rows!(Q, 1, 2)
    swap_rows!(T1, 1, 2)
  end

  return Q, T1, T2
end

function GenericRound2.integral_closure(Zx::ZZPolyRing, F::Generic.FunctionField)
  Qt = base_ring(F)
  t = gen(Qt)
  S = HessQR(Zx, Qt)
  R = parent(numerator(t))
  o1 = integral_closure(S, F)
  o2 = integral_closure(R, F)
  if isdefined(o1, :trans)
    T = o1.trans
  else
    T = identity_matrix(Qt, degree(F))
  end
  if isdefined(o2, :itrans)
    T = T * o2.itrans
  end
  q, w = integral_split(T, R)
  h, T2 = Hecke._hnf_with_transform(q', :upperright)
  T = map_entries(Qt, h')
#TODO: we don't need TT2 other than to debug assertions
# make it optional? tricky to also do this in two_by_two...
  TT2 = map_entries(Qt, T2')
  TT1 = identity_matrix(Qt, degree(F))
  cnt = 0
#  @assert TT1*o1.trans*o2.itrans*TT2 == divexact(T, Qt(w))
  for i=1:degree(F)
    for j=i+1:degree(F)
      q, t1, t2 = two_by_two(T[ [i,j], [i,j]], R, S)
      T[[i,j], [i,j]] = q
      TT = identity_matrix(Qt, degree(F))
      TT[[i,j], [i,j]] = t1
      TT1 = TT*TT1
      TT[[i,j], [i,j]] = t2
      TT2 = TT2 * TT
#  @assert TT1*o1.trans*o2.itrans*TT2 == divexact(T, Qt(w))
    end
  end


  @assert is_diagonal(T)
  T = divexact(T, Qt(w))
  @assert TT1*o1.trans*o2.itrans*TT2 == T
  # the diagonal in Q(t) is splint into a/b * alpha/beta where
  #  a/b in Q (hence a unit there)
  # and alpha, beta in Z[x] primitive, so alpha/beta is a unit in Z<x>
  for i=1:degree(F)
    n, d = integral_split(T[i,i], S)
    @assert is_constant(d)
    u = Qt(n.f)//Qt(n.g)
#    @assert n.c//d.c*u == T[i,i]
    TT2[:, i] *= Qt(d.c)*inv(Qt(n.c))
    TT1[i, :] *= inv(u)
    T[i,i] = 1
#  @assert TT1*o1.trans*o2.itrans*TT2 == T
  end

  TT1 = TT1
  n, d = integral_split(TT1, Zx)
  @assert map_entries(Qt, n) == TT1 * Qt(d)
  o3 = GenericRound2.order(Zx, F)
  if isdefined(o1, :trans)
    return GenericRound2.order(o3, integral_split(map_entries(Qt, TT1)*o1.trans, Zx)..., check = false)
  else
    return GenericRound2.order(o3, integral_split(map_entries(Qt, TT1), Zx)..., check = false)
  end
  return GenericRound2.order(o1, TT1, one(S)), GenericRound2.order(o2, inv(TT2'), one(base_ring(TT2)))
end

function Base.denominator(a::Generic.RationalFunctionFieldElem{QQFieldElem}, S::ZZPolyRing)
  return integral_split(a, S)[2]
end

function Base.numerator(a::Generic.RationalFunctionFieldElem{QQFieldElem}, S::ZZPolyRing)
  return integral_split(a, S)[1]
end

function Hecke.integral_split(a::Generic.RationalFunctionFieldElem{QQFieldElem}, S::ZZPolyRing)
  #TODO: feels too complicated....
  if iszero(a)
    return zero(S), one(S)
  end
  n = numerator(a)
  d = denominator(a)
  dn = reduce(lcm, map(denominator, coefficients(n)), init = ZZRingElem(1))
  dd = reduce(lcm, map(denominator, coefficients(d)), init = ZZRingElem(1))
  zn = S(n*dn)
  zd = S(d*dd)
  cn = content(zn)
  cd = content(zd)
  zn = divexact(zn, cn)
  zd = divexact(zd, cd)
  cn *= dd
  cd *= dn
  g = gcd(cn, cd)
  cn = divexact(cn, g)
  cd = divexact(cd, g)
  return cn*zn, cd*zd
end

function (S::ZZPolyRing)(a::Generic.RationalFunctionFieldElem{QQFieldElem})
  n, d = integral_split(a, S)
  @assert isone(d)
  return n
end

end

using .HessMain


#=
  this should work:

Hecke.example("Round2.jl")

?GenericRound2

Qt, t = rational_function_field(QQ, "t")
Qtx, x = polynomial_ring(Qt, "x")
F, a = function_field(x^6+27*t^2+108*t+108, "a")
integral_closure(parent(denominator(t)), F)
integral_closure(localization(Qt, degree), F)
integral_closure(Hecke.Globals.Zx, F)
basis(ans, F)
derivative(F.pol)(gen(F)) .* ans #should be integral

k, a = wildanger_field(3, 8*13)
integral_closure(ZZ, k)
integral_closure(localization(ZZ, 2), k)

more interesting and MUCH harder:

G, b = function_field(x^6 + (140*t - 70)*x^3 + 8788*t^2 - 8788*t + 2197, "b")

=#

module FactorFF
using Hecke

function Hecke.norm(f::PolyRingElem{<: Generic.FunctionFieldElem})
    K = base_ring(f)
    P = polynomial_to_power_sums(f, degree(f)*degree(K))
    PQ = elem_type(base_field(K))[tr(x) for x in P]
    return power_sums_to_polynomial(PQ)
end

function from_mpoly(f::MPolyRingElem, S::PolyRing{<:Generic.RationalFunctionFieldElem})
  @assert ngens(parent(f)) == 2
  @assert base_ring(f) == base_ring(base_ring(S))
  R = parent(numerator(gen(base_ring(S))))
  @assert isa(R, PolyRing)
  F = [zero(R) for i=0:degree(f, 1)]
  for (c, e) = zip(coefficients(f), exponent_vectors(f))
    setcoeff!(F[e[1]+1], e[2], c)
  end
  o = one(parent(F[1]))
  return S(map(x->base_ring(S)(x//o), F))
end

function Hecke.factor(f::Generic.Poly{<:Generic.RationalFunctionFieldElem})
  Pf = parent(f)
  R, r = polynomial_ring(base_ring(base_ring(f)), 2)
  d = lcm(map(denominator, coefficients(f)))
  Fc = MPolyBuildCtx(R)
  for i=0:degree(f)
    c = numerator(coeff(f, i)*d)
    for j=0:degree(c)
      push_term!(Fc, coeff(c, j), [i,j])
    end
  end
  lf = factor(finish(Fc))
  @assert is_constant(lf.unit)

  return Fac(Pf(constant_coefficient(lf.unit)), Dict((from_mpoly(k, Pf), e) for (k,e) = lf.fac))
end

function Hecke.factor(F::Generic.FunctionField{T}, f::Generic.Poly{<:Generic.RationalFunctionFieldElem{T}}) where {T}
  return factor(map_coefficients(F, f))
end
#plain vanilla Trager, possibly doomed in pos. small char.
function Hecke.factor(f::Generic.Poly{<:Generic.FunctionFieldElem})
  if !is_squarefree(f)
    sf = gcd(f, derivative(f))
    f = divexact(f, sf)
  else
    sf = one(parent(f))
  end
  lc = leading_coefficient(f)
  f = divexact(f, lc)
  i = 0
  local N
  g = f
  t = gen(parent(f))
  a = gen(base_ring(t))

  while true
    N = norm(g)
    if is_squarefree(N)
      break
    end
    i += 1
    g = evaluate(g, t-a)
    if i > 10
      error("not plausible")
    end
  end

  fN = factor(N)
  @assert isone(fN.unit)
  D = Fac(parent(f)(lc), Dict((gcd(map_coefficients(base_ring(f), p, parent = parent(f)), g)(t+i*a), k) for (p,k) = fN.fac))
  if !isone(sf)
    for k = keys(D.fac)
      D.fac[k] += valuation(sf, k)
    end
  end
  return D
end

#TODO: don't think this strategy is optimal, but it works...
function Hecke.splitting_field(f::Generic.Poly{<:Generic.RationalFunctionFieldElem})
  f = divexact(f, gcd(f, derivative(f)))

  lf = factor(f)
  lf = [x for x = keys(lf.fac) if degree(x) > 1]
  if length(lf) == 0
    return base_ring(f)
  end

  while true
    G, b = function_field(lf[1], "b", cached = false)
    if length(lf) == 1 && degree(G) < 3
      return G
    end

    f = prod(lf)

    GT, t = polynomial_ring(G, cached = false)
    g = divexact(map_coefficients(G, f, parent = GT), t-b)

    i = 0
    local N
    while true
      if !iszero(constant_coefficient(g))
        N = norm(g)
        if is_squarefree(N)
          break
        end
      end
      i += 1
      g = evaluate(g, t-b)
      if i > 10
        error("not plausible")
      end
    end

    fN = factor(N)
    lf = [x for x = keys(fN.fac) if degree(x) > degree(G)]
      #the gcd of x with deg(x) == deg(G) will yield a linear
      #factor, hence does not contribute further
    if length(lf) == 0
      return G
    end
  end
end


@doc raw"""
    swinnerton_dyer(V::Vector, x::Generic.Poly{<:Generic.RationalFunctionFieldElem})
    swinnerton_dyer(n::Int, x::Generic.Poly{<:Generic.RationalFunctionFieldElem})

Compute the minimal polynomial of $\sum \pm \sqrt{t+v_i}$ evaluated at $x$.
$t$ is the generator of the base field of the parent of $x$.

In the second variant, the polynomial has roots $\sum\pm\sqrt{t+i}$ for
  $i=1,\ldots,n$.
"""
function Hecke.swinnerton_dyer(V::Vector, x::Generic.Poly{<:Generic.RationalFunctionFieldElem})
  n = length(V)
  @assert characteristic(parent(x)) == 0 || characteristic(parent(x)) > length(V)
  S = base_ring(x)
  T = gen(S)
  X = gen(parent(x))
  l = [(X^2 + T + i) for i = V]
  l = [ vcat([2*one(S)], polynomial_to_power_sums(x, 2^n)) for x = l]
  while n > 1
    i = 1
    while 2*i <= n
      l[i] = [sum(binomial(ZZRingElem(h), ZZRingElem(j))*l[2*i-1][j+1]*l[2*i][h-j+1] for j=0:h) for h=0:length(l[1])-1]
      i += 1
    end
    if isodd(n)
      l[i] = l[n]
      n = i
    else
      n = i-1
    end
  end
  f = power_sums_to_polynomial(l[1][2:end], parent(x))
  if x == gen(parent(x))
    return f
  else
    return f(x)
  end
end

function Hecke.swinnerton_dyer(n::Int, x::Generic.Poly{<:Generic.RationalFunctionFieldElem})
  return swinnerton_dyer(x, collect(1:n))
end

end
