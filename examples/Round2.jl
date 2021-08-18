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
-  R = Localisation(k(x), degree), F = FunctionField
-  R = Z[x], F = FunctionField/ QQ(t)
"""
module GenericRound2

using Hecke
import AbstractAlgebra, Nemo
import Base: +, -, *, gcd, lcm, divrem, div, rem, mod, ^, ==
export integral_closure

#TODO: type parametrisation....
mutable struct Order <: AbstractAlgebra.Ring
  F::AbstractAlgebra.Field
  R::AbstractAlgebra.Ring
  trans::MatElem #both matrices are over base_ring(F)
  itrans::MatElem

  function Order(R::AbstractAlgebra.Ring, F::AbstractAlgebra.Field, empty::Bool = false)
    #empty allows to create an Order that is none:
    # Z[x]/3x+1 is no order. This will be "fixed" by using any_order, but
    #the intial shel needs to be empty (illegal)
    r = new()
    r.F = F
    r.R = R
    empty && return r
    Qt = base_ring(F)
    d = reduce(lcm, map(x->denominator(x, R), coefficients(defining_polynomial(F))))
    f = map_coefficients(x->Qt(d*numerator(x, R)),defining_polynomial(F))
    if !ismonic(f) #need Lenstra Order
      d = degree(F)
      M = zero_matrix(Qt, d, d)
      M[1, 1] = one(Qt)
      for i in 2:d
        for j in i:-1:2
          M[i, j] = coeff(f, d - (i - j))
        end
      end
      O = Order(r, M, one(Qt))
      return O
    end
    return r
  end

  function Order(O::Order, T::MatElem, d::RingElem)
    F = base_ring(O.F)
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
    return r
  end
end

function Base.show(io::IO, O::Order)
  println(io, "generic order over $(O.R) in $(O.F)")
end

Hecke.base_ring(O::Order) = O.R

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
  print(io, a.data)
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

+(a::OrderElem, b::OrderElem) = OrderElem(parent(a), a.data + b.data)
-(a::OrderElem, b::OrderElem) = OrderElem(parent(a), a.data - b.data)
-(a::OrderElem) = OrderElem(parent(a), -a.data)
*(a::OrderElem, b::OrderElem) = OrderElem(parent(a), a.data * b.data)

==(a::OrderElem, b::OrderElem) = parent(a) == parent(b) && a.data == b.data

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
  m = zero_matrix(O.R, degree(O), degree(O))
  for i=1:degree(O)
    c = coordinates(b[i]*a)
    for j=1:degree(O)
      m[i,j] = numerator(c[j], base_ring(O))
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

function radical_basis_power_non_perfect(O::Order, p::RingElem)
  t = ResidueField(parent(p), p)
  if isa(t, Tuple)
    F, mF = t
  else
    F = t
    mF = MapFromFunc(x->F(x), y->lift(y), parent(p), F)
  end
  @assert isa(F, Generic.RationalFunctionField) && characteristic(F) != 0
#  @assert characteristic(F) == 0 || (isfinite(F) && characteristic(F) > degree(O))
  q = characteristic(F)
  @assert q > 0
  while q < degree(O)
    q *= characteristic(F)
  end

  q = Int(q)
  b = basis(O)
  m = zero_matrix(F, q*degree(O), degree(O))
  for i=1:degree(O)
    c = coordinates(powermod(b[i], fmpz(q), p))
    for j=1:degree(O)
      d = mF(O.R(c[j]))
      @assert isone(denominator(d))
      d = numerator(d)
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
  II, d = pseudo_inv(I)
#  return II, d, [representation_matrix(O(vec(collect(I[i, :])))) for i=1:nrows(I)]
  m = hcat([divexact(representation_matrix(O(vec(collect(I[i, :]))))*II, d) for i=1:nrows(I)]...)
  H = hnf(m')[1:degree(O), 1:degree(O)]
  Hi, d = pseudo_inv(H)

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
    rad = radical_basis_trace
  elseif isa(R, Generic.RationalFunctionField)
    rad = radical_basis_power_non_perfect
  else
    rad = radical_basis_power
  end
  while true
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

Hecke.base_ring(::AnticNumberField) = FlintQQ

(R::PolyRing{T})(a::Generic.Rat{T}) where {T} = R(numerator(a))

function Hecke.ResidueField(R::FmpqPolyRing, p::fmpq_poly)
  K, _ = number_field(p)
  return K, MapFromFunc(x->K(x), y->R(y), R, K)
end

function (F::Generic.FunctionField)(p::PolyElem)
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

"""
  The ring ZZ<x> := {c f/g | c in ZZ, f, g in ZZ[x], primitive}
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
import AbstractAlgebra, Nemo
import Base: +, -, *, gcd, lcm, divrem, div, rem, mod, ^, ==
export HessQR

struct HessQR <: AbstractAlgebra.Ring
  R::FmpzPolyRing
  Qt::Generic.RationalFunctionField{fmpq}

  function HessQR(R::FmpzPolyRing, Qt::Generic.RationalFunctionField)
    new(R, Qt)
  end
end

mutable struct HessQRElem <: RingElem
  parent::HessQR
  c::fmpz
  f::fmpz_poly
  g::fmpz_poly

  function HessQRElem(P::HessQR, c::fmpz, f::fmpz_poly, g::fmpz_poly)
    if iszero(c) || iszero(f)
      r = new(P, fmpz(0), zero(P.R), one(P.R))
      @assert parent(r.f) == P.R
      @assert parent(r.g) == P.R
      return r
    end
    if parent(f) != P.R
      f = map_coefficients(FlintZZ, f, parent = P.R)
    end
    if parent(g) != P.R
      g = map_coefficients(FlintZZ, g, parent = P.R)
    end
    gc = gcd(f, g)
    f = divexact(f, gc)
    g = divexact(g, gc)
    cf = content(f)
    cg = content(g)
    @assert (c*cf) % cg == 0
    cu = canonical_unit(g)
    r = new(P, divexact(c*cf, cg), cu*divexact(f, cf), cu*divexact(g, cg))
    @assert parent(r.f) == P.R
    @assert parent(r.g) == P.R
    return r
  end
  function HessQRElem(P::HessQR, q::Generic.Rat{fmpq})
    f = numerator(q)
    g = denominator(q)
    return HessQRElem(P, f, g)
  end
  function HessQRElem(P::HessQR, f::fmpq_poly)
    return HessQRElem(P, f, one(parent(f)))
  end
  function HessQRElem(P::HessQR, f::fmpq_poly, g::fmpq_poly)
    df = reduce(lcm, map(denominator, coefficients(f)), init = fmpz(1))
    dg = reduce(lcm, map(denominator, coefficients(g)), init = fmpz(1))
    ff = map_coefficients(FlintZZ, df*f, parent = P.R)
    gg = map_coefficients(FlintZZ, dg*g, parent = P.R)
    #ff/df//gg/dg = dg/df * ff/gg
    return HessQRElem(P, divexact(dg, df), ff, gg)
  end
  function HessQRElem(P::HessQR, c::fmpz)
    r = new(P, c, one(P.R), one(P.R))
    @assert parent(r.f) == P.R
    @assert parent(r.g) == P.R
    return r
  end
  function HessQRElem(P::HessQR, c::fmpz_poly)
    d = content(c)
    r = new(P, d, divexact(c, d), one(P.R))
    @assert parent(r.f) == P.R
    @assert parent(r.g) == P.R
    return r
  end
end

function Base.show(io::IO, a::HessQRElem)
  print(io, "$(a.c) * ($(a.f))//($(a.g))")
end

function Hecke.integral_split(a::Generic.Rat{fmpq}, S::HessQR)
  if iszero(a)
    return zero(S), one(S)
  end
  n = numerator(a)
  d = denominator(a)
  dn = reduce(lcm, map(denominator, coefficients(n)), init = fmpz(1))
  dd = reduce(lcm, map(denominator, coefficients(d)), init = fmpz(1))
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

function Hecke.numerator(a::Generic.Rat, S::HessQR)
  return integral_split(a, S)[1]
end

function Hecke.denominator(a::Generic.Rat, S::HessQR)
  return integral_split(a, S)[2]
end

Nemo.elem_type(::HessQR) = HessQRElem
Nemo.elem_type(::Type{HessQR}) = HessQRElem
Nemo.parent_type(::HessQRElem) = HessQR
Nemo.parent_type(::Type{HessQRElem}) = HessQR
Nemo.isdomain_type(::Type{HessQRElem}) = true

Base.parent(a::HessQRElem) = a.parent

(R::HessQR)(a::Generic.Rat{fmpq}) = HessQRElem(R, a)
(R::HessQR)(a::fmpz) = HessQRElem(R, a)
(R::HessQR)(a::Integer) = HessQRElem(R, fmpz(a))
(R::HessQR)(a::fmpz_poly) = HessQRElem(R, a)
(R::HessQR)(a::fmpq_poly) = HessQRElem(R, a)
(R::HessQR)(a::HessQRElem) = a
(R::HessQR)() = R(0)

(F::Generic.RationalFunctionField)(a::HessQRElem) = a.c*F(a.f)//F(a.g)


Nemo.iszero(a::HessQRElem) = iszero(a.c)
Nemo.isone(a::HessQRElem) = isone(a.c) && isone(a.f) && isone(a.g)

Nemo.zero(R::HessQR) = R(0)
Nemo.one(R::HessQR) = R(1)
Nemo.canonical_unit(a::HessQRElem) = HessQRElem(parent(a), fmpz(1), a.f, a.g)

Base.deepcopy_internal(a::HessQRElem, dict::IdDict) = HessQRElem(parent(a), Base.deepcopy_internal(a.c, dict), Base.deepcopy_internal(a.f, dict), Base.deepcopy_internal(a.g, dict))

Base.hash(a::HessQRElem, u::UInt=UInt(12376599)) = hash(a.g, hash(a.f, hash(a.c, u)))

+(a::HessQRElem, b::HessQRElem) = HessQRElem(parent(a), fmpz(1), a.c*a.f*b.g+b.c*b.f*a.g, a.g*b.g)
-(a::HessQRElem, b::HessQRElem) = HessQRElem(parent(a), fmpz(1), a.c*a.f*b.g-b.c*b.f*a.g, a.g*b.g)
-(a::HessQRElem) = HessQRElem(parent(a), -a.c, a.f, a.g)
*(a::HessQRElem, b::HessQRElem) = HessQRElem(parent(a), a.c*b.c, a.f*b.f, a.g*b.g)

==(a::HessQRElem, b::HessQRElem) = parent(a) == parent(b) && a.c == b.c && a.f == b.f && a.g == b.g

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

function Hecke.addeq!(a::HessQRElem, b::HessQRElem)
  d = a+b
  @assert parent(a.f) == parent(d.f)
  @assert parent(a.g) == parent(d.g)
  a.c = d.c
  a.f = d.f
  a.g = d.g
  return a
end

function divrem(a::HessQRElem, b::HessQRElem)
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

    - for d = p a prime, the rep is unqiue, thus F_p(t)
  =#
  r = rem(a,b)
  return divexact(a-r, b), r

  return HessQRElem(parent(a), q, a.f*b.g, a.g*b.f), HessQRElem(parent(a), r, a.f, a.g)
end

function div(a::HessQRElem, b::HessQRElem)
  if iszero(a)
    return a
  end
  return divexact(a-rem(a, b), b)
  q = div(a.c, b.c)
  return HessQRElem(parent(a), q, a.f*b.g, a.g*b.f)
end

function rem(a::HessQRElem, b::HessQRElem)
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
  ci = invmod(c, d)
  e = gen(parent(gd))^(degree(a.g)+1)+1
  f = a.c*a.f*e
  g = a.g*e
  gd = mod(g, d)
  @assert content(gd) == 1

  fd = mod(f, d)

  return HessQRElem(parent(a), fmpz(1), fd, gd)
end

function Nemo.divexact(a::HessQRElem, b::HessQRElem)
  @assert parent(a) == parent(b)
  @assert parent(a.f) == parent(a).R
  @assert parent(a.g) == parent(a).R
  @assert parent(b.f) == parent(a).R
  @assert parent(b.g) == parent(a).R
  return HessQRElem(parent(a), divexact(a.c, b.c), a.f*b.g, a.g*b.f)
end

function gcd(a::HessQRElem, b::HessQRElem)
  return HessQRElem(parent(a), gcd(a.c, b.c))
end

function Nemo.gcdx(a::HessQRElem, b::HessQRElem)
  R = parent(a)
  g, u, v = Nemo.gcdx(a.c, b.c)
  return R(g), HessQRElem(R, u, a.g, a.f), HessQRElem(R, v, b.g, b.f)
end

function lcm(a::HessQRElem, b::HessQRElem)
  return HessQRElem(parent(a), lcm(a.c, b.c))
end

Hecke.isunit(a::HessQRElem) = isunit(a.c)

Nemo.dense_poly_type(::Type{gfp_fmpz_elem}) = gfp_fmpz_poly

function Nemo.ResidueField(a::HessQR, b::HessQRElem)
  @assert isprime(b.c)
  F = GF(b.c)
  Ft, t = RationalFunctionField(F, String(var(a.R)), cached = false)
  R = parent(numerator(t))
  return Ft, MapFromFunc(x->F(x.c)*Ft(map_coefficients(F, x.f, parent = R))//Ft(map_coefficients(F, x.g, parent = R)),
                         y->HessQRElem(a, fmpz(1), map_coefficients(lift, numerator(y)), map_coefficients(lift, denominator(y))), a, Ft)
end

function Nemo.ResidueRing(a::HessQR, b::HessQRElem)
  error("wrong wrong wrong")
  F = ResidueRing(FlintZZ, b.c)
  return F, MapFromFunc(x->F(x.c), y->a(lift(y)), a, F)
end

function Hecke.factor(a::HessQRElem)
  f = factor(a.c)
  R = parent(a)
  return Fac(R(a.f), Dict((R(p),k) for (p,k) = f.fac))
end

function Hecke.factor(a::Generic.Rat, R::HessQR)
  d1 = reduce(lcm, map(denominator, coefficients(numerator(a))), init = fmpz(1))
  f1 = factor(R(d1*numerator(a)))
  d2 = reduce(lcm, map(denominator, coefficients(denominator(a))), init = fmpz(1))
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

function GenericRound2.integral_closure(Zx::FmpzPolyRing, F::Generic.FunctionField)
  Qt = base_ring(F)
  t = gen(Qt)
  S = HessQR(Zx, Qt)
  o1 = integral_closure(S, F)
  o2 = integral_closure(parent(denominator(t)), F)
  T = o1.trans * o2.itrans
  q, w = integral_split(T, S)
  TT1 = identity_matrix(S, degree(F))
  TT2 = identity_matrix(base_ring(o2), degree(F))
  cnt = 0
  local H
  while !isdiagonal(q)
    h, T1 = Hecke._hnf_with_transform(q, :lowerleft)
    TT1 = T1*TT1
    T = map_entries(x->Qt(x)//Qt(w), h)
    qq, ww = integral_split(T', base_ring(o2))
    H, T2 = Hecke._hnf_with_transform(qq, :lowerleft)
    TT2 = T2*TT2
    T = map_entries(x->Qt(x)//Qt(ww), H)
    q, w = integral_split(T', S)
    cnt += 1
    cnt > 5 && error("asdas")
  end
  @assert isone(q)
  o3 = GenericRound2.Order(Zx, F)
  return GenericRound2.Order(o3, integral_split(map_entries(Qt, TT1)*o1.trans, Zx)...)
  return H, GenericRound2.Order(o1, TT1, one(S)), GenericRound2.Order(o2, inv(TT2'), one(base_ring(TT2)))
end

function Base.denominator(a::Generic.Rat{fmpq}, S::FmpzPolyRing)
  return integral_split(a, S)[2]
end

function Base.numerator(a::Generic.Rat{fmpq}, S::FmpzPolyRing)
  return integral_split(a, S)[1]
end

function Hecke.integral_split(a::Generic.Rat{fmpq}, S::FmpzPolyRing)
  if iszero(a)
    return zero(S), one(S)
  end
  n = numerator(a)
  d = denominator(a)
  dn = reduce(lcm, map(denominator, coefficients(n)), init = fmpz(1))
  dd = reduce(lcm, map(denominator, coefficients(d)), init = fmpz(1))
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

function (S::FmpzPolyRing)(a::Generic.Rat{fmpq})
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

Qt, t = RationalFunctionField(QQ, "t")
Qtx, x = PolynomialRing(Qt, "x")
F, a = FunctionField(x^6+27*t^2+108*t+108, "a")
integral_closure(parent(denominator(t)), F)
integral_closure(Localization(Qt, degree), F)
integral_closure(Hecke.Globals.Zx, F)
basis(ans, F)
derivative(F.pol)(gen(F)) .* ans #should be integral

k, a = wildanger_field(3, 8*13)
integral_closure(ZZ, k)
integral_closure(Localization(ZZ, 2), k)

=#
