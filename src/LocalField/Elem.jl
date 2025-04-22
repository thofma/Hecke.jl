import Base.setprecision
################################################################################
#
#  Show function
#
################################################################################

function AbstractAlgebra.expressify(a::LocalFieldElem; context = nothing)
  return AbstractAlgebra.expressify(a.data, var(parent(a)), context = context)
end

function Base.show(io::IO, a::LocalFieldElem)
  print(io, AbstractAlgebra.obj_to_string(a, context = io))
end

canonical_unit(x::LocalFieldElem) = x

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(x::LocalFieldElem{S, T}, dict::IdDict) where {S, T}
  return LocalFieldElem{S, T}(parent(x), Base.deepcopy_internal(x.data, dict), precision(x))
end

function Base.hash(a::LocalFieldElem, h::UInt)
  return hash(a.data, h)
end

################################################################################
#
#  Precision
#
################################################################################

function compute_precision(K::LocalField, a::Generic.Poly)
  prec = precision(coeff(a, 0))*ramification_index(K)
  degree(a) == 0 && return prec
  f = defining_polynomial(K)
  v = Int(numerator(valuation(coeff(f, 0))//degree(K) * ramification_index(K)))
  # TODO: Presumably, v is supposed to be the valuation of gen(K). Is this correct?
  vi = 0
  for i = 1:degree(a)
    vi += v
    c = coeff(a, i)
    prec = min(prec, precision(c)*ramification_index(K) + vi)
  end
  return prec
end

Nemo.precision(a::LocalFieldElem) = a.precision

function Nemo.precision(a::Generic.Poly{S}) where S <: LocalFieldElem
  if iszero(a)
    return precision(base_ring(a))
  end
  return minimum(precision, coefficients(a))
end

function Base.setprecision(a::LocalFieldElem, n::Int)
  b = deepcopy(a)
  return setprecision!(b, n)
end

function setprecision!(a::LocalFieldElem, n::Int)
  K = parent(a)
  e = ramification_index(K)
  d, r = divrem(n, e)
  if !iszero(r)
    d += 1
  end
  for i = 0:degree(a.data)
    setcoeff!(a.data, i, setprecision(coeff(a, i), d))
  end
  set_length!(a.data, normalise(a.data, length(a.data)))
  a.precision = n
  return a
end

################################################################################
#
#  Parent
#
################################################################################

parent(a::LocalFieldElem) = a.parent

parent_type(::Type{LocalFieldElem{S, T}}) where {S <: FieldElem, T <: LocalFieldParameter} = LocalField{S, T}

################################################################################
#
#   Coefficients
#
################################################################################

data(a::LocalFieldElem) = a.data
coeff(a::LocalFieldElem, i::Int) = coeff(data(a), i)
setcoeff!(a::LocalFieldElem, i::Int) = setcoeff!(data(a), i)

################################################################################
#
#   Coordinates
#
################################################################################

function coordinates(a::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  res = Vector{S}(undef, degree(parent(a)))
  for i = 0:length(res)-1
    res[i+1] = coeff(a, i)
  end
  return res
end

coordinates(a::PadicFieldElem) = PadicFieldElem[a]

coordinates(Qp::PadicField, a::PadicFieldElem) = PadicFieldElem[_coerce(Qp, a)]

function coordinates(a::QadicFieldElem)
  res = Vector{PadicFieldElem}(undef, degree(parent(a)))
  for i = 0:length(res)-1
    res[i+1] = coeff(a, i)
  end
  return res
end

function coordinates(Qp::PadicField, a::QadicFieldElem)
  res = Vector{PadicFieldElem}(undef, degree(parent(a)))
  for i = 0:length(res)-1
    res[i + 1] = _coerce(Qp, coeff(a, i))
  end
  return res
end

absolute_coordinates(a::Union{PadicFieldElem, QadicFieldElem}) = coordinates(a)

absolute_coordinates(Qp::PadicField, a::Union{PadicFieldElem, QadicFieldElem}) = coordinates(Qp, a)

function absolute_coordinates(a::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  K = parent(a)
  v = Vector{PadicFieldElem}(undef, absolute_degree(K))
  va = coordinates(a)
  ind = 1
  for i = 1:length(va)
    vi = absolute_coordinates(va[i])
    for j = 1:length(vi)
      v[ind] = vi[j]
      ind += 1
    end
  end
  return v
end

function absolute_coordinates(Qp::PadicField, a::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  K = parent(a)
  v = Vector{PadicFieldElem}(undef, absolute_degree(K))
  va = coordinates(a)
  ind = 1
  for i = 1:length(va)
    vi = absolute_coordinates(Qp, va[i])
    for j = 1:length(vi)
      v[ind] = vi[j]
      ind += 1
    end
  end
  return v
end

function inv_absolute_coordinates(K::PadicField, C::Vector{PadicFieldElem}; start::Int = 0)
  return C[start+1]
end

function inv_absolute_coordinates(K::QadicField, C::Vector{PadicFieldElem}; start::Int = 0)
  a = K()
  pr = minimum(precision, C[start+1:start+degree(K)])
  setprecision!(a, pr)
  for i=0:degree(K)-1
    setcoeff!(a, i, C[start+i+1])
  end
  return a
end

function inv_absolute_coordinates(K::LocalField, C::Vector{PadicFieldElem}; start::Int = 0)
  a = K()
  k = base_field(K)
  deg_k = absolute_degree(k)
  for i=0:degree(K)-1
    setcoeff!(a.data, i, inv_absolute_coordinates(k, C, start = start))
    start += deg_k
  end
  normalise(a.data, degree(K))
  setprecision!(a, compute_precision(K, a.data))
  return a
end

################################################################################
#
#  Zero/One
#
################################################################################

iszero(a::LocalFieldElem) = iszero(a.data)

#in ramified fields the generator is the uniformizer and has valuation 1
# precision is measured in powers of a uniformizer, but the uniformizer
# is represented as x.
#the precision of the coefficient of x comes in multiples of e
#hence pi in precision 1 which should be 0 (valuation >= precision)
#fails as x has coefficient 1 in precision 1 which is non zero
function iszero(a::LocalFieldElem{S, EisensteinLocalField}) where S
  f = a.data
  iszero(f) && return true
  e = ramification_index(parent(a))
  p = precision(a)
  for i=0:degree(f)
    c = coeff(f, i)
    if !iszero(c) && valuation(c)*e + i < p
      return false
    end
  end
  return true
end

isone(a::LocalFieldElem) = isone(data(a))
function isone(a::LocalFieldElem{S, EisensteinLocalField}) where S
  a1 = a - one(parent(a), precision = precision(a))
  return iszero(a1)
end

is_unit(a::LocalFieldElem) = !iszero(a)

function O(K::LocalField, prec::T) where T <: IntegerUnion
  d, r = divrem(prec, ramification_index(K))
  if !iszero(r)
    r += 1
  end
  return K(O(base_field(K), d))
end

function zero(K::LocalField; precision=precision(K))
  a = zero(parent(defining_polynomial(K)))
  return setprecision!(K(a), precision)
end

(K::LocalField)(; precision=precision(K)) = zero(K, precision = precision)

function one(K::LocalField; precision=precision(K))
  a = one(parent(defining_polynomial(K)))
  return setprecision!(K(a), precision)
end

function zero!(a::LocalFieldElem; precision=precision(parent(a)))
  zero!(a.data)
  a.data = setprecision!(a.data, precision)
  return a
end

function Base.:(==)(a::LocalFieldElem, b::LocalFieldElem)
  for i = 0:max(degree(a.data), degree(b.data))
    if coeff(a, i) != coeff(b, i)
      return false
    end
  end
  return true
end

function Base.:(==)(a::LocalFieldElem{S, EisensteinLocalField}, b::LocalFieldElem{S, EisensteinLocalField}) where {S}
  e = ramification_index(parent(a))
  p = min(precision(a), precision(b))
  for i = 0:max(degree(a.data), degree(b.data))
    ca = coeff(a, i)
    cb = coeff(b, i)
    if ca != cb && valuation(ca-cb) * e + i < p
      return false
    end
  end
  return true
end


################################################################################
#
#  Coercion
#
################################################################################

function (K::LocalField{S, T})(a::Integer; precision=precision(K)) where {S <: FieldElem, T <: LocalFieldParameter}
  el =  K(parent(defining_polynomial(K))(a))
  return setprecision!(el, precision)
end

function (K::LocalField{S, T})(a::Union{ZZRingElem, QQFieldElem}; precision=precision(K)) where {S <: FieldElem, T <: LocalFieldParameter}
  el =  K(parent(defining_polynomial(K))(a))
  return setprecision!(el, precision)
end

function (K::LocalField{S, T})(a::U) where {U <: Union{PadicFieldElem, QadicFieldElem}, S <: FieldElem, T <: LocalFieldParameter}
  return K(parent(defining_polynomial(K))(a))
end

function (K::LocalField{S, T})(a::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  return a
end

function (K::LocalField{S, T})(a::LocalFieldElem{U, V}) where {S <: FieldElem, U <: FieldElem, T <: LocalFieldParameter, V <: LocalFieldParameter}
  if parent(a) === K
    return a
  elseif base_field(K) === parent(a)
    kt = parent(defining_polynomial(K))
    return K(kt(a.data))
  else
    return K(base_field(K)(a))
  end
end

function (K::LocalField{S, T})(p::Generic.Poly{S}) where {S <: FieldElem, T <: LocalFieldParameter}
  if degree(p) >= degree(K)
    p = mod(p, defining_polynomial(K, max(10, precision(p))))
  end
  return LocalFieldElem{S, T}(K, p, compute_precision(K, p))
end

function (Rx::Generic.PolyRing{S})(a::LocalFieldElem{S, T}) where {S, T}
  @assert base_ring(Rx) == base_field(parent(a))
  return a.data
end

################################################################################
#
#  Valuation
#
################################################################################

@doc raw"""
    valuation(a::LocalFieldElem) -> QQFieldElem

The valuation of $a$, normalized so that $v(p) = 1$. Scale by the
`absolute_ramification_index` to get a surjection onto ZZ.
"""
function valuation(a::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  return valuation(norm(a))//degree(parent(a))
end

function valuation(a::LocalFieldElem{S, UnramifiedLocalField}) where S <: FieldElem
  return QQ(_valuation_integral(a), absolute_ramification_index(base_field(parent(a))))
end

function valuation(a::LocalFieldElem{S, EisensteinLocalField}) where S <: FieldElem
  return QQ(_valuation_integral(a), absolute_ramification_index(parent(a)))
end

_valuation_integral(a::Union{PadicFieldElem, QadicFieldElem}) = valuation(a)

function _valuation_integral(a::LocalFieldElem)
  return numerator(absolute_ramification_index(parent(a))*valuation(a))
end

function _valuation_integral(a::LocalFieldElem{S, UnramifiedLocalField}) where S <: FieldElem
  if iszero(a)
    error("Input element is zero")
  end
  K = parent(a)
  i = 0
  c = coeff(a, i)
  while iszero(c)
    i += 1
    c = coeff(a, i)
  end
  v = _valuation_integral(c)
  for j in i + 1:degree(K)
    c = coeff(a, j)
    if iszero(c)
      continue
    end
    vc = _valuation_integral(c)
    if vc < v
      v = vc
    end
  end
  return v
end

function _valuation_integral(a::LocalFieldElem{S, EisensteinLocalField}) where S <: FieldElem
  if iszero(a)
    error("Input element is zero")
  end
  K = parent(a)
  e = absolute_ramification_index(K)
  i = 0
  c = coeff(a, i)
  while iszero(c)
    i += 1
    i > degree(parent(a)) && error("interesting element")
    c = coeff(a, i)
  end
  v = e*_valuation_integral(c) + i
  for j = i + 1:degree(K)
    c = coeff(a, j)
    if iszero(c)
      continue
    end
    vnew = e*_valuation_integral(c) + j
    if vnew < v
      v = vnew
    end
  end
  return v
end

################################################################################
#
#  Representation matrix
#
################################################################################

function elem_to_mat_row!(M::MatElem, i::Int, a::LocalFieldElem)
  K = parent(a)
  @assert ncols(M) == degree(K)
  for j = 1:degree(K)
    M[i, j] = coeff(a, j-1)
  end
  return nothing
end

function representation_matrix(a::LocalFieldElem)
  K = parent(a)
  g = gen(K)
  el = a
  M = zero_matrix(base_field(K), degree(K), degree(K))
  elem_to_mat_row!(M, 1, a)
  for i = 1:degree(K)-1
    el *= g
    elem_to_mat_row!(M, i+1, el)
  end
  return M
end


################################################################################
#
#  Norm
#
################################################################################

function norm(a::LocalFieldElem)
  K = parent(a)
  return AbstractAlgebra.det_df(representation_matrix(a))
  #the resultant is not quite stable (yet), it is not using the
  #fun factor stuff...
  res = setprecision(base_ring(a.data), precision(a.data)) do
    resultant(defining_polynomial(K, precision(a.data)), a.data)
  end
  return res
end

function absolute_norm(a::LocalFieldElem)
  return absolute_norm(norm(a))
end

function absolute_norm(a::PadicFieldElem)
  return a
end

function absolute_norm(a::QadicFieldElem)
  return norm(a)
end

function norm(a::LocalFieldElem, F::LocalField)
  K = parent(a)
  while absolute_degree(parent(a)) > absolute_degree(F)
    a = norm(a)
  end
  if K == F
    return a::elem_type(F)
  end
  error("wrong target in norm")
end

function norm(a::LocalFieldElem, F::PadicField)
  return absolute_norm(a)
end

################################################################################
#
#  Trace
#
################################################################################

function tr(a::LocalFieldElem)
  K = parent(a)
  n = precision(a)
  tb = assure_traces(K, n)
  res = base_field(K)()
  res = setprecision!(res, n)
  for i = 0:degree(K)-1
    res += tb[i+1]*coeff(a, i)
  end
  return res
end

function absolute_tr(a::LocalFieldElem)
  return absolute_tr(tr(a))
end

function absolute_tr(a::PadicFieldElem)
  return a
end

function absolute_tr(a::QadicFieldElem)
  return tr(a)
end

function tr(a::LocalFieldElem, F::LocalField)
  K = parent(a)
  while absolute_degree(parent(a)) > absolute_degree(F)
    a = trace(a)
  end
  if parent(a) != F
    error("wrong field given")
  end
  return a::elem_type(F)
end

function tr(a::LocalFieldElem, F::PadicField)
  return absolute_tr(a)
end

function tr(a::LocalFieldElem{QadicFieldElem}, F::QadicField)
  return tr(a)
end
################################################################################
#
#  Minpoly
#
################################################################################

function minpoly(Kx::PolyRing, a::T)  where T <: Union{LocalFieldElem, QadicFieldElem}
  return squarefree_part(norm(gen(Kx)-a))
end

function minpoly(a::Union{LocalFieldElem, QadicFieldElem})
  return minpoly(polynomial_ring(parent(a), "t", cached = false)[1], a)
end

function absolute_minpoly(a::LocalFieldElem)
  f = minpoly(a)
  return _absolute_minpoly(f)
end

function _absolute_minpoly(p::Generic.Poly{T}) where T <: Union{QadicFieldElem, LocalFieldElem}
  return _absolute_minpoly(squarefree_part(norm(p)))
end

function _absolute_minpoly(p::Generic.Poly{PadicFieldElem})
  return squarefree_part(p)
end

function absolute_minpoly(a::PadicFieldElem, parent = polynomial_ring(parent(a), "x"))
  return gen(parent)-a
end

function absolute_minpoly(a::QadicFieldElem)
  return minpoly(a)
end

################################################################################
#
#  Basic operations
#
################################################################################

function Base.:-(a::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  return LocalFieldElem{S, T}(parent(a), -a.data, precision(a))
end

function Base.:+(a::LocalFieldElem{S, T}, b::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  check_parent(a, b)
  K = parent(a)
  c = setprecision(base_ring(a.data), _precision_base(K)) do
    a.data + b.data
  end
  return LocalFieldElem{S, T}(parent(a), c, min(precision(a), precision(b)))
end

function Base.:-(a::LocalFieldElem{S, T}, b::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  check_parent(a, b)
  K = parent(a)
  c = setprecision(base_ring(a.data), _precision_base(K)) do
    a.data - b.data
  end
  return LocalFieldElem{S, T}(parent(a), c, min(precision(a), precision(b)))
end

function Base.:*(a::LocalFieldElem{S, T}, b::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  check_parent(a, b)
  c = parent(a)()
  return mul!(c, a, b)
end

function Base.:(//)(a::LocalFieldElem{S, T}, b::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  check_parent(a, b)
  ib = inv(b)
  return a*ib
end

function Base.:(//)(a::LocalFieldElem{S, T}, b::Union{PadicFieldElem, QadicFieldElem}) where {S <: FieldElem, T <: LocalFieldParameter}
  ib = inv(b)
  return a*ib
end

function divexact(a::LocalFieldElem{S, T}, b::LocalFieldElem{S, T}; check::Bool = true) where {S <: FieldElem, T <: LocalFieldParameter}
  return a//b
end

function add!(c::LocalFieldElem{S, T}, a::LocalFieldElem{S, T}, b::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  check_parent(a, b)
  c.parent = a.parent
  c.data = a.data + b.data
  c.precision = min(a.precision, b.precision)
  return c
end

function sub!(c::LocalFieldElem{S, T}, a::LocalFieldElem{S, T}, b::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  check_parent(a, b)
  c.parent = a.parent
  c.data = a.data - b.data
  c.precision = min(a.precision, b.precision)
  return c
end

function mul!(c::LocalFieldElem{S, T}, a::LocalFieldElem{S, T}, b::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  check_parent(a, b)
  K = parent(a)
  e = ramification_index(K)
  va = (iszero(a) ? 0 : Int(_valuation_integral(a)))
  vb = (iszero(b) ? 0 : Int(_valuation_integral(b)))
  pr = min(precision(a) + vb, precision(b) + va)
  c.data = mul!(c.data, data(a), data(b))
  # from this point on, a, b might have changed (if c === a or c === b)
  c.data = mod(c.data, defining_polynomial(K, max(precision(data(c)), _precision_base(K))))
  c.precision = min(compute_precision(K, data(c)), pr)
  return c
end

function uniformizer(L::Union{PadicField, QadicField}, v::Int; prec::Int = 20)  #precision????
  return setprecision(L, prec) do
    uniformizer(L)^v
  end
end

function uniformizer(L::LocalField, v::Int; prec::Int = 20)  #precision????
  if v > 0
    return setprecision(L, prec) do
      uniformizer(L)^v
    end
  end

  if !isa(L, LocalField{<:Any, EisensteinLocalField})
    return L(uniformizer(base_field(L), v, prec = prec))
  end

  #possibly compute the pi^v only for v mod e the complicated way, and scale
  #by prime number afterwards
  #also: find out abs and rel prec....
  e = absolute_ramification_index(L)
  pr = ceil(Int, (prec-v)/e)+2
  f = defining_polynomial(L, pr)
  local pi_inv
  setprecision(L, pr*e) do
    g = parent(f)([coeff(f, i) for i=1:degree(f)])
    pi_inv = g(uniformizer(L))
    pi_inv *= -inv(coeff(f, 0))
    @assert valuation(pi_inv) == - valuation(uniformizer(L))
    @assert precision(pi_inv) >= prec - 1
  end
  return pi_inv^-v
end

function inv(a::LocalFieldElem)
  K = parent(a)
  v = Int(_valuation_integral(a))
  if v == 0
    p = invmod(a.data, defining_polynomial(K, precision(a.data)))
    return K(p)
  end
  pi_v = uniformizer(parent(a), -v, prec = precision(a)-v)
  aa = a* pi_v
  p = invmod(aa.data, defining_polynomial(K, precision(aa.data)))
  return (K(p)*pi_v)::typeof(a)
end

Base.:(^)(a::LocalFieldElem, n::UInt) = a^Int(n)

function Base.:(^)(a::LocalFieldElem, n::Int)
  K = parent(a)
  if iszero(a)
    return zero(K)
  end

  if iszero(n)
    return one(K)
  end

  if n < 0 && iszero(a)
    error("Element is not invertible")
  end
  v = valuation(n, prime(K))
  prec = precision(data(a)) + v
  if v > 0
    b = setprecision(data(a), prec)
  else
    b = data(a)
  end
  b = setprecision(base_ring(b), prec) do
    powermod(b, n, defining_polynomial(K, prec))
  end
  return K(b)
end

################################################################################
#
#  Exponential
#
################################################################################

function _underlying_base_field(K::LocalField)
  return _underlying_base_field(base_field(K))
end

function _underlying_base_field(K::T) where T <: Union{PadicField, QadicField}
  return K
end

@doc raw"""
    exp(a::LocalFieldElem) -> LocalFieldElem

Computes the $p$-adic exponential of $a$.
"""
function exp(a::LocalFieldElem)
  K = parent(a)
  p = prime(K)
  if valuation(a) <= QQFieldElem(1, p-1)
    error("Exponential not defined!")
  end
  Qp = _underlying_base_field(K)
  N_orig = precision(a)
  N = N_orig + clog(ZZRingElem(N_orig), p)
  a = setprecision(a, N)
  oN = precision(parent(a))
  setprecision!(parent(a), max(oN, N))
  res = one(K, precision = N)
  el = one(K)
  den = one(Qp, precision = N)
  #precision is suboptimal, its truncated badly, thus losing it
  max_i = QQFieldElem(N)//(valuation(a) - QQFieldElem(1, p-1)) + 1
  bound = Int(floor(ZZRingElem, max_i))
  for i = 1:bound
    el *= a//i
    res += el
  end
  setprecision!(res, N_orig)
  setprecision!(parent(a), oN)
  return res
end

################################################################################
#
#   Logarithm
#
################################################################################

@doc raw"""
    log(a::LocalFieldElem) -> LocalFieldElem

Computes the $p$-adic logarithm of $a$, defined via the series on the 1-units and
extended so that $log(p) = 0$.
"""
function log(a::LocalFieldElem)
  K = parent(a)
  va = valuation(a)
  if isone(a)
    return zero(K)
  end
  if iszero(va) && valuation(a-1) > 0
    return _log_one_units(a)
  end
  e = absolute_ramification_index(K)
  f = absolute_inertia_degree(K)
  p = prime(K)
  pf1 = p^f - 1
  pi = uniformizer(K)
  y = a*pi^(-Int(numerator(va*e)))
  #Now, y has valuation 0
  z = y^pf1
  #Now, z is a 1-unit
  logy = _log_one_units(z)//pf1
  eps = ((pi^e)//p)
  #Same trick to make eps is now a 1-unit.
  if !isone(eps) && iszero(valuation(eps-1))
    logeps = divexact(_log_one_units(eps^pf1), pf1)
  else
    logeps = _log_one_units(eps)
  end
  return logy + va*logeps
end

function _log_one_units(a::LocalFieldElem)
  K = parent(a)
  if isone(a)
    return zero(K, precision = precision(a))
  end
  #TODO: computing log(a^p^l)//p^l might accelerate the
  #computation. Find the optimal l.
  #Here is an attempt, but it is not theoretical.
  #It is based on the fact that the powering requires log p^l multiplication and
  #that the number of terms of the series we need to compute is approximately precision(a)/v_pi(a).
  p = prime(K)
  el = deepcopy(a)
  d = ZZRingElem(1)
  v = _valuation_integral(a - one(K, precision = precision(a)))
  N = precision(el)
  num = a
  den = ZZRingElem(1)
  candidate = div(N, v)
  Nv = candidate
  while Nv != 1
    d *= p
    el = el^p
    N = precision(el)
    el1 = el - one(K, precision = N)

    if iszero(el1)
      num = el
      den = d
      break
    end

    Nv = div(N, _valuation_integral(el1))
    attempt = clog(d, 2) + Nv
    attempt > candidate && break

    num = el
    den = d
  end
  r = _log_one_units_fast(num)
  r = divexact(r, den)
  return r
end

function divexact(a::LocalFieldElem, b::Union{Integer, ZZRingElem}; check::Bool=true)
  K = parent(a)
  p = prime(K)
  e = absolute_ramification_index(K)
  v = valuation(b, p)
  iszero(a) && return setprecision(a, precision(a) - v*e)
  Qp = absolute_base_field(K)
  old = precision(Qp)
  setprecision!(Qp, e*precision(a)+ Int(_valuation_integral(a)) + v)
  bb = inv(Qp(b))
  setprecision!(Qp, old)
  return a*bb
end

function _log_one_units_fast(a::LocalFieldElem)
  K = parent(a)
  fl, b = setprecision(K, precision(a)) do
    if isone(a) || iszero(a - 1)
      return true, zero(K)
    end
    false, a - 1
  end
  fl && return b
  #= Plan:
    log(1+b) = log(a) = sum (-b)^i/i
    up to precision pr(a)
    val(b^i / i) = i val(b) - val(i) and val(i) <= flog(i, p)
    as a function in i, this is increasing past the min at i=val(a)
    thus we need at least pr/val(b) many summands (since up to then
    val(b^i / i) <= val(b^i) = i val(b) <= thus non-zero
    For i sth. val(i) == 0, this is sharp.
    For i = mult. of p, we need more terms, the largest possibility
    i = p^r gets val(b^i / i) = p^r val(b) - r
    again, this as a min and is growing otherwise.

    Careful: valuation is extending from Q and might be fractional
             precision is in pi, not p
  =#
  vb = valuation(b)
  p = prime(K)
  N = precision(a)
  res = zero(K)
  e = absolute_ramification_index(K)
  res = setprecision!(res, N + e*flog(ZZRingElem(N), p))
  bound1 = div(N, numerator(vb*e)) #num(vb*e) = val(b) above

  l = 1
  left = p*vb*e  #val(b^p)
  right = N + e  #powering will increase prec by e
  #need p^i*val(b) - i >= pr, so p^i *val(b) >= pr + i is what we test
  while left < right
    left *= p
    right += e
    l += 1
  end
  bound2 = p^l #definitely an upper bound on terms
  el = one(K)
  el = setprecision!(el, N) #necc. if prec(K) < prec(a)
  #prec here means rel. prec. Each mult. by el of valuation vb above
  #will increase the abs. prec. The division by i will then reduce the abs. prec
  # (and the rel prec), but the abs prec will be larger than the abs prec in el.
  #
  b = a - el
  #sum (-b)^i/i for 1st step: crude estimate without val(den)
  for i = 1:bound1
    el *= b
    to_add = divexact(el, i)
    if isodd(i)
      res += to_add
    else
      res -= to_add
    end
  end
  leftlim = bound1 + p - mod(ZZRingElem(bound1), p)
  #smallest expo (i) > bound so far
  if leftlim <= bound2
    el *= b^(leftlim-bound1)
    if isodd(leftlim)
      res += divexact(el, leftlim)
    else
      res -= divexact(el, leftlim)
    end
    inc = b^p
    for i = leftlim+p:p:bound2
      el *= inc
      if isodd(i)
        res += divexact(el, i)
      else
        res -= divexact(el, i)
      end
    end
  end
  return res
end


################################################################################
#
#  Promote rules
#
################################################################################

AbstractAlgebra.promote_rule(::Type{S}, ::Type{ZZRingElem}) where S <: LocalFieldElem = S

AbstractAlgebra.promote_rule(::Type{S}, ::Type{QQFieldElem}) where S <: LocalFieldElem = S


AbstractAlgebra.promote_rule(::Type{S}, ::Type{T}) where {S <: LocalFieldElem, T <: Integer} = S

AbstractAlgebra.promote_rule(::Type{LocalFieldElem{S, T}}, ::Type{PadicFieldElem}) where {S <: FieldElem, T <: LocalFieldParameter} = LocalFieldElem{S, T}

AbstractAlgebra.promote_rule(::Type{LocalFieldElem{S, T}}, ::Type{QadicFieldElem}) where {S <: FieldElem, T <: LocalFieldParameter} = LocalFieldElem{S, T}

#AbstractAlgebra.promote_rule(::Type{PadicFieldElem}, ::Type{LocalFieldElem{S, T}}) where {S <: FieldElem, T <: LocalFieldParameter} = LocalFieldElem{S, T}
#
#AbstractAlgebra.promote_rule(::Type{QadicFieldElem}, ::Type{LocalFieldElem{S, T}}) where {S <: FieldElem, T <: LocalFieldParameter} = LocalFieldElem{S, T}

function AbstractAlgebra.promote_rule(::Type{LocalFieldElem{T, S}}, ::Type{U}) where {S, T, U <: LocalFieldElem}
  # We have to also capture the promote_rule(::T, ::T) case here
  if LocalFieldElem{T, S} === U || T === U
    return LocalFieldElem{T, S}
  end
  if AbstractAlgebra.promote_rule(T, U) === T
    return LocalFieldElem{T, S}
  end
  return Union{}
end

#=
function AbstractAlgebra.promote_rule(::Type{LocalFieldElem{S, T}}, ::Type{PadicFieldElem}) where {S <: LocalFieldElem,  T <: LocalFieldParameter}
  if S === AbstractAlgebra.promote_rule(S, PadicFieldElem)
    return LocalFieldElem{S, T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{LocalFieldElem{S, T}}, ::Type{QadicFieldElem}) where {S <: LocalFieldElem, T <: LocalFieldParameter}
  if S === AbstractAlgebra.promote_rule(S, QadicFieldElem)
    return LocalFieldElem{S, T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{PadicFieldElem}, ::Type{LocalFieldElem{S, T}}) where {S <: LocalFieldElem,  T <: LocalFieldParameter}
  if S === AbstractAlgebra.promote_rule(S, PadicFieldElem)
    return LocalFieldElem{S, T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{QadicFieldElem}, ::Type{LocalFieldElem{S, T}}) where {S <: LocalFieldElem, T <: LocalFieldParameter}
  if S === AbstractAlgebra.promote_rule(S, QadicFieldElem)
    return LocalFieldElem{S, T}
  else
    return Union{}
  end
end
=#

function AbstractAlgebra.promote_rule(::Type{LocalFieldElem{S, T}}, ::Type{LocalFieldElem{U, V}}) where {S <: LocalFieldElem, T <: LocalFieldParameter, U <: LocalFieldElem, V <: LocalFieldParameter}
  if S === U && T === V
    return LocalFieldElem{S, T}
  end
  R = AbstractAlgebra.promote_rule(S, LocalFieldElem{U, V})
  if R === S
    return LocalFieldElem{S, T}
  end
  R = AbstractAlgebra.promote_rule(U, LocalFieldElem{S, T})
  if R === U
    return LocalFieldElem{U, V}
  else
    return Union{}
  end
end

################################################################################
#
#  Expansion
#
################################################################################

# Construct a laurent series over the residue field
function expansion(x::NonArchLocalFieldElem, pi = uniformizer(parent(x)))
  prec = precision(x)
  K = parent(x)
  F, KtoF = residue_field(K)
  Rt, t = laurent_series_ring(F, prec, :x)
  v = _valuation_integral(x)
  y = divexact(x, pi^v)
  coeffs = elem_type(F)[]
  res = zero(Rt)
  # the laurent_series_ring constructor is unusable. We do it the inefficient way:
  for k in 1:precision(y)
    c = KtoF(y)
    res += c * t^k
    y = divexact(y - KtoF\c, pi)
  end
  return res * t^(v - 1)
end
