"""
Support for generic maximal orders over any PID

  final result:
    integral_closure(R, F)
    where R is "any" PID and F a finite extension of some quotient field of R

  R needs to support
   - euclidean (hnf, pseudo_inv, gcd, lcm, mod, div, divrem)
   - factorisation
   - a useful ResidueField (need to know characteristic and finiteness)
   - integral_split, numerator, denominator
     given a in Frac(R), decompose into num, den
     (all Localisations of Z have QQ as quotient field,
     Q[x], Z[x] and Localisation(Q(x), degree) use Q(t))
   - isdomain_type

Seems to work for
-  R = ZZ, F = AnticNumberField
-  R = Loc{fmpz}, F = AnticNumberField

-  R = k[x], F = FunctionField (for k = QQ, F_q)
-  R = Localization(k(x), degree), F = FunctionField
-  R = Z[x], F = FunctionField/ QQ(t)
"""
module GenericRound2

using Hecke
import AbstractAlgebra, Nemo
import Base: +, -, *, gcd, lcm, divrem, div, rem, mod, ^, ==
export integral_closure
import AbstractAlgebra: expressify

#TODO: type parametrisation....
mutable struct Order <: AbstractAlgebra.Ring
  F::AbstractAlgebra.Field
  R::AbstractAlgebra.Ring
  trans::MatElem #both matrices are over coefficient_ring(F)
  itrans::MatElem

  function Order(R::AbstractAlgebra.Ring, F::AbstractAlgebra.Field, empty::Bool = false; check::Bool = true)
    #empty allows to create an Order that is none:
    # Z[x]/3x+1 is no order. This will be "fixed" by using any_order, but
    #the intial shell needs to be empty (illegal)
    r = new()
    r.F = F
    r.R = R
    empty && return r
    Qt = coefficient_ring(F)
    d = reduce(lcm, map(x->denominator(x, R), coefficients(defining_polynomial(F))))
    f = map_coefficients(x->numerator(Qt(d)*x, R), defining_polynomial(F))
    if !ismonic(f) #need Lenstra Order
      d = degree(F)
      M = zero_matrix(Qt, d, d)
      M[1, 1] = one(Qt)
      for i in 2:d
        for j in i:-1:1
          M[i, j] = coeff(f, d - (i - j))
        end
      end
      O = Order(r, M, one(Qt), check = check)
      return O
    end
    return r
  end

  function Order(O::Order, T::MatElem, d::RingElem; check::Bool = true)
    F = coefficient_ring(O.F)
    T = map_entries(F, T)
    T = divexact(T, base_ring(T)(d))
    Ti = inv(T)
    r = Order(O.R, O.F, true)
    if isdefined(O, :trans)
      r.trans = T*O.trans
      r.itrans = O.itrans*Ti
    else
      r.trans = T
      r.itrans = Ti
    end
    check && map(representation_matrix, basis(r))
    return r
  end
end

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
Hecke.coefficient_ring(O::Order) = O.R

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
  function OrderElem(O::Order, f::fmpz)
    return OrderElem(O, O.F(f))
  end
end

function Base.show(io::IO, a::OrderElem)
  print(io, AbstractAlgebra.obj_to_string(a.data, context = io))
end

function expressify(a::OrderElem; context = nothing)
  return expressify(base_ring(R), context = context)
end

Nemo.elem_type(::Order) = OrderElem
Nemo.parent_type(::OrderElem) = Order
Nemo.parent_type(::Type{OrderElem}) = Order
Nemo.isdomain_type(::Type{OrderElem}) = true

Base.parent(a::OrderElem) = a.parent

(R::Order)(a::FieldElem) = OrderElem(R, a)
(R::Order)(a::fmpz) = OrderElem(R, a)
(R::Order)(a::Integer) = OrderElem(R, fmpz(a))
(R::Order)(a::OrderElem) = OrderElem(R, a.data)
(R::Order)() = R(0)


Nemo.iszero(a::OrderElem) = iszero(a.c)
Nemo.isone(a::OrderElem) = isone(a.c) && isone(a.f) && isone(a.g)

Nemo.zero(R::Order) = R(0)
Nemo.one(R::Order) = R(1)
Nemo.canonical_unit(a::OrderElem) = OrderElem(parent(a), fmpz(1))

Base.deepcopy_internal(a::OrderElem, dict::IdDict) = OrderElem(parent(a), Base.deepcopy_internal(a.data, dict))

check_parent(a::OrderElem, b::OrderElem) = parent(a) == parent(b) || error("Incompatible orders")

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

function Hecke.addeq!(a::OrderElem, b::OrderElem)
  a.data = Hecke.addeq!(a.data, b.data)
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

Hecke.coefficient_ring(F::Generic.FunctionField) = base_ring(F)

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
  S = coefficient_ring(O.F)

  if isdefined(O, :itrans)
    a = map(x->S(R(x) % p), coordinates(a))
    b = a*O.trans
    return O(O.F(vec(collect(b'))))
  else
    return O(O.F([O.R(x) % p for x = coefficients(a.data)]))
  end
end

function Hecke.powermod(a::OrderElem, n::fmpz, p::RingElem)
  c = parent(a)(1)
  for i = Hecke.BitsMod.bits(n)
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
  t = ResidueField(parent(p), p)
  if isa(t, Tuple)
    F, mF = t
  else
    F = t
    mF = MapFromFunc(x->F(x), y->lift(y), parent(p), F)
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
  k, B = kernel(m)

  M2 = B[:, 1:k]'
  M2 = map_entries(x->preimage(mF, x), M2)
  M3 = Hecke.hnf(vcat(M2, p*identity_matrix(parent(p), degree(O))))[1:degree(O), :]
  return M3 #[O(vec(collect((M3[i, :])))) for i=1:degree(O)]
end

#in char 0 and small char: rad = {x : Tr(xO) in pR} perfect field
function radical_basis_trace(O::Order, p::RingElem)
  T = trace_matrix(O)

  t = ResidueField(parent(p), p)
  if isa(t, Tuple)
    R, mR = t
  else
    R = t
    mR = MapFromFunc(x->R(x), y->lift(y), parent(p), R)
  end

  TT = map_entries(mR, T)
  k, B = kernel(TT)
  M2 = map_entries(x->preimage(mR, x), B[:, 1:k])'
  M3 = Hecke.hnf(vcat(M2, p*identity_matrix(parent(p), degree(O))))[1:degree(O), :]
  return return M3 #[O(vec(collect((M3[i, :])))) for i=1:degree(O)]
end

#pos. char, non-perfect (residue) field
function radical_basis_power_non_perfect(O::Order, p::RingElem)
  t = ResidueField(parent(p), p)
  if isa(t, Tuple)
    F, mF = t
  else
    F = t
    mF = MapFromFunc(x->F(x), y->lift(y), parent(p), F)
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
    c = coordinates(powermod(b[i], fmpz(q), p))
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
  k, B = kernel(m)

  M2 = B[:, 1:k]'
  M2 = map_entries(x->preimage(mF, x), M2)
  M3 = Hecke.hnf(vcat(M2, p*identity_matrix(parent(p), degree(O))))[1:degree(O), :]
  return return M3 #[O(vec(collect((M3[i, :])))) for i=1:degree(O)]
end

function Hecke.representation_matrix(a::Generic.FunctionFieldElem)
  F = parent(a)
  g = gen(F)
  m = zero_matrix(coefficient_ring(F), degree(F), degree(F))
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
  @vprint :NfOrd 2 "ring of multipliers of ideal with basis matrix $I\n"
  II, d = pseudo_inv(I)
  @assert II*I == d
#  return II, d, [representation_matrix(O(vec(collect(I[i, :])))) for i=1:nrows(I)]
  m = hcat([divexact(representation_matrix(O(vec(collect(I[i, :]))))*II, d) for i=1:nrows(I)]...)
  m = m'
  n = degree(O)
  mm = hnf(m[1:n, 1:n])
  for i=2:n
    mm = vcat(mm, hnf(m[(i-1)*n+1:i*n, 1:n]))
    mm = hnf(mm)[1:n, 1:n]
  end
  H = mm

  @vtime :NfOrd 2 Hi, d = pseudo_inv(H)

  O = Order(O, Hi', d)
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

function Hecke.trace_matrix(b::Vector{OrderElem}, c::Vector{OrderElem}, exp::fmpz = fmpz(1))
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
  t = ResidueField(parent(p), p)

  if isa(t, Tuple)
    R, mR = t
  else
    R = t
    mR = MapFromFunc(x->R(x), y->lift(y), parent(p), R)
  end
#  @assert characteristic(F) == 0 || (isfinite(F) && characteristic(F) > degree(O))
  if characteristic(R) == 0 || characteristic(R) > degree(O)
    @vprint :NfOrd 1 "using trace-radical for $p\n"
    rad = radical_basis_trace
  elseif isa(R, Generic.RationalFunctionField)
    @vprint :NfOrd 1 "non-perfect case for radical for $p\n"
    rad = radical_basis_power_non_perfect
  else
    @vprint :NfOrd 1 "using radical-by-power for $p\n"
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

function integral_closure(S::Loc{fmpz}, F::AnticNumberField)
  return _integral_closure(S, F)
end

function integral_closure(S::PolyRing{T}, F::Generic.FunctionField{T}) where {T}
  return _integral_closure(S, F)
end

function integral_closure(S::KInftyRing{T}, F::Generic.FunctionField{T}) where {T}
  return _integral_closure(S, F)
end

function _integral_closure(S::AbstractAlgebra.Ring, F::AbstractAlgebra.Ring)
  O = Order(S, F)
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
    return Order(O, Op[1], Op[2])
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

function (R::PolyRing{T})(a::Generic.Rat{T}) where {T}
  @assert isone(denominator(a))
  return R(numerator(a))
end

function Hecke.ResidueField(R::FmpqPolyRing, p::fmpq_poly)
  K, _ = number_field(p)
  return K, MapFromFunc(x->K(x), y->R(y), R, K)
end

function (F::Generic.FunctionField{T})(p::PolyElem{<:AbstractAlgebra.Generic.Rat{T}}) where {T <: FieldElem}
  @assert parent(p) == parent(F.pol)
  @assert degree(p) < degree(F) # the reduction is not implemented
  R = parent(gen(F).num)
  S = coefficient_ring(R)
  d = reduce(lcm, map(denominator, coefficients(p)), init = one(S))
  return F(map_coefficients(S, d*p, parent = R), d)
end

function (F::Generic.FunctionField)(c::Vector{<:RingElem})
  return F(parent(F.pol)(map(coefficient_ring(F), c)))
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
Hecke.denominator(a::fmpq, ::FlintIntegerRing) = denominator(a)
Hecke.numerator(a::fmpq, ::FlintIntegerRing) = numerator(a)
Hecke.integral_split(a::fmpq, ::FlintIntegerRing) = (numerator(a), denominator(a))

#######################################################################
#
# support for Loc{fmpz}
#
#######################################################################
function Hecke.integral_split(a::fmpq, R::Loc{fmpz})
  d = denominator(a)
  p = R.prime
  q,w = Hecke.ppio(d, p)
  if R.comp # den can ONLY use prime
    return R(numerator(a)//q), R(w)
  else
    return R(numerator(a)//w), R(q)
  end
end
Hecke.denominator(a::fmpq, R::Loc{fmpz}) = integral_split(a, R)[2]
Hecke.numerator(a::fmpq, R::Loc{fmpz}) = integral_split(a, R)[1]
(::FlintRationalField)(a::LocElem{fmpz}) = data(a)

function Hecke.factor(a::LocElem{fmpz})
  c = canonical_unit(a)
  b = a*inv(c)
  L = parent(a)
  @assert isone(denominator(data(b)))
  lf = factor(numerator(data(b)))
  return Fac(c, Dict(L(p)=>v for (p,v) = lf.fac))
end

function Hecke.ResidueField(R::Loc{fmpz}, p::LocElem{fmpz})
  pp = numerator(data(p))
  @assert isprime(pp) && isone(denominator(p))
  F = GF(pp)
  return F, MapFromFunc(x->F(data(x)), y->R(lift(y)), R, F)
end

Hecke.isdomain_type(::Type{LocElem{fmpz}}) = true

#######################################################################
#
# support for Rat{T}
#
#######################################################################
# Rat{T}, KInftyRing{T}

Base.denominator(x::AbstractAlgebra.Generic.Rat{T}, R::KInftyRing{T}) where {T} = Hecke.integral_split(x, R)[2]
Base.numerator(x::AbstractAlgebra.Generic.Rat{T}, R::KInftyRing{T}) where {T} = Hecke.integral_split(x, R)[1]

function Hecke.integral_split(x::AbstractAlgebra.Generic.Rat{T}, R::KInftyRing{T}) where {T}
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

(R::Generic.RationalFunctionField{fmpq})(x::KInftyElem{fmpq}) = x.d

# Rat{T}, PolyRing{T}
function Hecke.numerator(a::Generic.Rat{T}, S::PolyRing{T}) where {T}
  return numerator(a)
end

function Hecke.denominator(a::Generic.Rat{T}, S::PolyRing{T}) where {T}
  return denominator(a)
end

function Hecke.integral_split(a::Generic.Rat{T}, S::PolyRing{T}) where {T}
  return numerator(a), denominator(a)
end

function Hecke.factor(a::Generic.Rat{T}, R::Generic.PolyRing{T}) where {T}
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

using .GenericRound2

export integral_closure

