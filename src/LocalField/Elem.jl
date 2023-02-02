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

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(x::LocalFieldElem{S, T}, dict::IdDict) where {S, T}
  return LocalFieldElem{S, T}(parent(x), Base.deepcopy_internal(x.data, dict), precision(x))
end

################################################################################
#
#  Precision
#
################################################################################

function _generator_valuation(K::LocalField{S, T}) where {S <: Union{padic, qadic}, T <: LocalFieldParameter}
  f = defining_polynomial(K)
  return fmpq(valuation(coeff(f, 0)), degree(f))
end

function _generator_valuation(K::LocalField)
  f = defining_polynomial(K)
  return divexact(valuation(coeff(f, 0)), degree(K))
end

function compute_precision(K::LocalField, a::Generic.Poly)
  v = numerator(_generator_valuation(K)*ramification_index(K))
  prec = precision(coeff(a, 0))*ramification_index(K)
  for i = 1:degree(a)
    c = coeff(a, i)
    prec = min(prec, precision(c)*ramification_index(K)+Int(numerator(ceil(i*v))))
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

function setprecision!(a::padic, n::Int)
  return setprecision(a, n)
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

parent_type(a::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter} = LocalField{S, T}
parent_type(::Type{LocalFieldElem{S, T}}) where {S <: FieldElem, T <: LocalFieldParameter} = LocalField{S, T}

################################################################################
#
#   Coefficients
#
################################################################################

coeff(a::LocalFieldElem, i::Int) = coeff(a.data, i)
setcoeff!(a::LocalFieldElem, i::Int) = setcoeff!(a.data, i)

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

coordinates(a::padic) = padic[a]

function coordinates(a::qadic)
  res = Vector{padic}(undef, degree(parent(a)))
  for i = 0:length(res)-1
    res[i+1] = coeff(a, i)
  end
  return res
end

absolute_coordinates(a::Union{padic, qadic}) = coordinates(a)

function absolute_coordinates(a::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  K = parent(a)
  v = Vector{padic}(undef, absolute_degree(K))
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


################################################################################
#
#  Zero/One
#
################################################################################

iszero(a::LocalFieldElem) = iszero(a.data)
isone(a::LocalFieldElem) = isone(a.data)
is_unit(a::LocalFieldElem) = !iszero(a)

function O(K::LocalField, prec::T) where T <: IntegerUnion
  d, r = divrem(prec, ramification_index(K))
  if !iszero(r)
    r += 1
  end
  return K(O(base_field(K), d))
end

function zero(K::LocalField)
  a = zero(parent(defining_polynomial(K)))
  return setprecision(K(a), precision(K))
end

(K::LocalField)() = zero(K)

function one(K::LocalField)
  a = one(parent(defining_polynomial(K)))
  return setprecision(K(a), precision(K))
end

function zero!(a::LocalFieldElem)
  K = parent(a)
  zero!(a.data)
  a.data = setprecision(a.data, precision(K))
  return a
end

function Base.:(==)(a::LocalFieldElem{S, T}, b::LocalFieldElem{S, T}) where {S, T}
  for i = 0:max(degree(a.data), degree(b.data))
    if coeff(a, i) != coeff(b, i)
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

function (K::LocalField{S, T})(a::Integer) where {S <: FieldElem, T <: LocalFieldParameter}
  el =  K(parent(defining_polynomial(K))(a))
  return setprecision!(el, precision(K))
end

function (K::LocalField{S, T})(a::Union{fmpz, fmpq}) where {S <: FieldElem, T <: LocalFieldParameter}
  el =  K(parent(defining_polynomial(K))(a))
  return setprecision!(el, precision(K))
end

function (K::LocalField{S, T})(a::U) where {U <: Union{padic, qadic}, S <: FieldElem, T <: LocalFieldParameter}
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

@doc Markdown.doc"""
    valuation(a::LocalFieldElem) -> fmpq

The valuation of $a$, normalized so that $v(p) = 1$.
"""
function valuation(a::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  return valuation(norm(a))//degree(parent(a))
end

function valuation(a::LocalFieldElem{S, EisensteinLocalField}) where S <: FieldElem
  if iszero(a)
    error("Input element is zero")
  end
  K = parent(a)
  e = absolute_ramification_index(K)
  i = 0
  c = coeff(a, i)
  while iszero(c)
    i += 1
    i > degree(parent(a)) && error("intersting element")
    c = coeff(a, i)
  end
  vc = valuation(c)
  v = vc + fmpq(i, e)
  for j = i+1:degree(K)
    c = coeff(a, j)
    if iszero(c)
      continue
    end
    vc = valuation(c)
    vnew = vc + fmpq(j, e)
    if vnew < v
      v = vnew
    end
  end
  return v
end

function valuation(a::LocalFieldElem{S, UnramifiedLocalField}) where S <: FieldElem
  if iszero(a)
    error("Input element is zero")
  end
  K = parent(a)
  e = absolute_ramification_index(K)
  i = 0
  c = coeff(a, i)
  while iszero(c)
    i += 1
    c = coeff(a, i)
  end
  v = valuation(c)
  for j = i+1:degree(K)
    c = coeff(a, j)
    if iszero(c)
      continue
    end
    vc = valuation(c)
    if vc < v
      v = vc
    end
  end
  return v
end

function check_parent(a::LocalFieldElem{S, T}, b::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  #=
  if parent(a) !== parent(b)
    @show parent(a)
    @show parent(b)
    error("Wrong parents!")
  end
  =#
  return nothing
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
  return det(representation_matrix(a))
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

function absolute_norm(a::padic)
  return a
end

function absolute_norm(a::qadic)
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

function norm(a::LocalFieldElem, F::FlintPadicField)
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

function absolute_tr(a::padic)
  return a
end

function absolute_tr(a::qadic)
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

function tr(a::LocalFieldElem, F::FlintPadicField)
  return absolute_tr(a)
end

function tr(a::LocalFieldElem{qadic}, F::FlintQadicField)
  return tr(a)
end
################################################################################
#
#  Minpoly
#
################################################################################

function minpoly(a::T, Kx::PolyRing = PolynomialRing(parent(a), "t", cached = false)[1]) where T <: Union{LocalFieldElem, qadic}
  return squarefree_part(norm(gen(Kx)-a))
end

function absolute_minpoly(a::LocalFieldElem)
  f = minpoly(a)
  return _absolute_minpoly(f)
end

function _absolute_minpoly(p::Generic.Poly{T}) where T <: Union{qadic, LocalFieldElem}
  return _absolute_minpoly(squarefree_part(norm(p)))
end

function _absolute_minpoly(p::Generic.Poly{padic})
  return squarefree_part(p)
end

function absolute_minpoly(a::padic, parent = PolynomialRing(parent(a), "x"))
  return gen(parent)-a
end

function absolute_minpoly(a::qadic)
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
  c = setprecision(base_ring(a.data), ceil(Int, precision(K)/ramification_index(K))) do
     a.data + b.data
  end
  return LocalFieldElem{S, T}(parent(a), c, min(precision(a), precision(b)))
end

function Base.:-(a::LocalFieldElem{S, T}, b::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  check_parent(a, b)
  K = parent(a)
  c = setprecision(base_ring(a.data), ceil(Int, precision(K)/ramification_index(K))) do
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
  n = max(precision(a.data), precision(b.data))
  pol = setprecision(base_ring(a.data), n) do
    mod(a.data*ib.data, defining_polynomial(parent(a), n))
  end
  res =  LocalFieldElem{S, T}(parent(a), pol, compute_precision(parent(a), pol))
  return res
end

function Base.:(//)(a::LocalFieldElem{S, T}, b::Union{padic, qadic}) where {S <: FieldElem, T <: LocalFieldParameter}
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

function addeq!(c::LocalFieldElem{S, T}, a::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  check_parent(a, c)
  c.data = add!(c.data, c.data, a.data)
  c.precision = min(a.precision, c.precision)
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
  K = c.parent = a.parent
  c.data = mul!(c.data, a.data, b.data)
  c.data = mod(c.data, defining_polynomial(parent(a), max(precision(c.data), ceil(Int, precision(K)/ramification_index(K)))))
  c.precision = compute_precision(a.parent, c.data)
  return c
end

function uniformizer(L::LocalField, v::Int; prec::Int = 20)  #precision????
  if v > 0
    return uniformizer(L)^v
  end
  if inertia_degree(L) == degree(L)
    return L(uniformizer(base_field(L))^v)
  end
  #possibly compute the pi^v only for v mod e the complicated way, and scale
  #by prime number afterwards
  #also: find out abs and rel prec....
  e = absolute_ramification_index(L)
  pr = ceil(Int, prec/e-2*v)
  f = defining_polynomial(L, pr)
  local pi_inv
  setprecision(L, pr*e) do
    g = parent(f)([coeff(f, i) for i=1:degree(f)])
    pi_inv = -g(uniformizer(L))*inv(coeff(f, 0))
    @assert valuation(pi_inv) == - valuation(uniformizer(L))
    @assert precision(pi_inv) >= prec - 1
  end  
  return pi_inv^-v
end

function inv(a::LocalFieldElem)
  K = parent(a)
  e =  absolute_ramification_index(parent(a))
  v =  Int(e*valuation(a))
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
  e = absolute_ramification_index(parent(a))
  v = valuation(n, prime(parent(a)))
  if v > 0
    b = setprecision(a.data, precision(a.data)+v)
  else
    b = a.data
  end
  b = setprecision(base_ring(b), precision(b)) do
    powermod(b, n, defining_polynomial(K, precision(b)))
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

@doc Markdown.doc"""
    log(a::LocalFieldElem) -> LocalFieldElem

Computes the $p$-adic exponential of $a$.
"""
function exp(a::LocalFieldElem)
  K = parent(a)
  p = prime(K)
  if valuation(a) <= fmpq(1, p-1)
    error("Exponential not defined!")
  end
  Qp = _underlying_base_field(K)
  N_orig = precision(a)
  N = N_orig + clog(fmpz(N_orig), p) 
  a = setprecision(a, N)
  oN = precision(parent(a))
  setprecision!(parent(a), max(oN, N))
  res = one(K)
  res = setprecision(res, N)
  el = one(K)
  res = res
  den = setprecision!(one(Qp), N)
  #precision is suboptimal, its truncated badly, thus loosing it
  max_i = fmpq(N)//(valuation(a) - fmpq(1, p-1)) + 1
  bound = Int(floor(fmpz, max_i))
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

@doc Markdown.doc"""
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
  pi = uniformizer(K)
  y = a*pi^(-Int(numerator(va*e)))
  #Now, y has valuation 0
  z = y^(p^f-1)
  #Now, z is a 1-unit
  logy = _log_one_units(z)//(p^f-1)
  eps = ((pi^e)//p)
  #Same trick to make eps is now a 1-unit.
  if !isone(eps) && iszero(valuation(eps-1))
    logeps = divexact(_log_one_units(eps^(p^f-1)), p^f-1)
  else
    logeps = _log_one_units(eps)
  end
  return logy + va*logeps
end


function _log_one_units(a::LocalFieldElem)
  K = parent(a)
  if isone(a)
    return setprecision!(zero(K), precision(a))
  end
  #TODO: computing log(a^p^l)//p^l might accelerate the
  #computation. Find the optimal l.
  #Here is an attempt, but it is not theoretical.
  #It is based on the fact that the powering requires log p^l multiplication and
  #that the number of terms of the series we need to compute is approximately precision(a)/v_pi(a).
  p = prime(K)
  el = deepcopy(a)
  d = fmpz(1)
  e = absolute_ramification_index(K)
  v = numerator(e*valuation(a-1))
  N = precision(el)
  num = a
  den = fmpz(1)
  candidate = div(N, v)
  #XXX: currently broke!
  # the precision is not increasing...
  while true
    d *= p
    el = el^p
    N = precision(el)
    if isone(el) || iszero(el - 1)
      num = el
      den = d
      break
    end
    attempt = clog(d, 2) + div(N, numerator(e*valuation(el-1)))
    if attempt > candidate
      break
    else
      num = el
      den = d
    end
  end
  r = _log_one_units_fast(num)
  r = divexact(r, den)
  return r
end

function divexact(a::LocalFieldElem, b::Union{Integer, fmpz})
  iszero(a) && return a
  p = prime(parent(a))
  v = valuation(b, p)
  Qp = prime_field(parent(a))
  old = precision(Qp)
  e = absolute_ramification_index(parent(a))
  setprecision!(Qp, e*precision(a)+round(Int, e*valuation(a)) + v)
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
  vb = valuation(b)
  p = prime(K)
  N = precision(a)
  res = zero(K)
  e = absolute_ramification_index(K)
  res = setprecision!(res, N + e*flog(fmpz(N), p))
  bound1 = div(N, numerator(vb*e))

  l = 1
  left = p*vb*e
  right = N + e
  while left < right
    left *= p
    right += e
    l += 1
  end
  bound2 = p^l
  el = one(K)
  el = setprecision!(el, N+l)
  b = setprecision(a, N+l) - el
  for i = 1:bound1
    el *= b
    to_add = divexact(el, i)
    if isodd(i)
      res += to_add
    else
      res -= to_add
    end
  end
  leftlim = bound1 + p - mod(fmpz(bound1), p)
  if leftlim < bound2
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

AbstractAlgebra.promote_rule(::Type{S}, ::Type{fmpz}) where S <: LocalFieldElem = S

AbstractAlgebra.promote_rule(::Type{S}, ::Type{fmpq}) where S <: LocalFieldElem = S


AbstractAlgebra.promote_rule(::Type{S}, ::Type{T}) where {S <: LocalFieldElem, T <: Integer} = S

AbstractAlgebra.promote_rule(::Type{LocalFieldElem{S, T}}, ::Type{padic}) where {S <: FieldElem, T <: LocalFieldParameter} = LocalFieldElem{S, T}

AbstractAlgebra.promote_rule(::Type{LocalFieldElem{S, T}}, ::Type{qadic}) where {S <: FieldElem, T <: LocalFieldParameter} = LocalFieldElem{S, T}

#AbstractAlgebra.promote_rule(::Type{padic}, ::Type{LocalFieldElem{S, T}}) where {S <: FieldElem, T <: LocalFieldParameter} = LocalFieldElem{S, T}
#
#AbstractAlgebra.promote_rule(::Type{qadic}, ::Type{LocalFieldElem{S, T}}) where {S <: FieldElem, T <: LocalFieldParameter} = LocalFieldElem{S, T}

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
function AbstractAlgebra.promote_rule(::Type{LocalFieldElem{S, T}}, ::Type{padic}) where {S <: LocalFieldElem,  T <: LocalFieldParameter}
  if S === AbstractAlgebra.promote_rule(S, padic)
    return LocalFieldElem{S, T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{LocalFieldElem{S, T}}, ::Type{qadic}) where {S <: LocalFieldElem, T <: LocalFieldParameter}
  if S === AbstractAlgebra.promote_rule(S, qadic)
    return LocalFieldElem{S, T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{padic}, ::Type{LocalFieldElem{S, T}}) where {S <: LocalFieldElem,  T <: LocalFieldParameter}
  if S === AbstractAlgebra.promote_rule(S, padic)
    return LocalFieldElem{S, T}
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{qadic}, ::Type{LocalFieldElem{S, T}}) where {S <: LocalFieldElem, T <: LocalFieldParameter}
  if S === AbstractAlgebra.promote_rule(S, qadic)
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
