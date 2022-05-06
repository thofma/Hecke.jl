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
    p = mod(p, defining_polynomial(K))
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
  global last_a = a
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
  return resultant(a.data, defining_polynomial(K))
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
  if K === F
    return norm(a)::elem_type(F)
  else
    return norm(norm(a), F)::elem_type(F)
  end
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
  assure_traces(K)
  res = base_field(K)()
  for i = 0:degree(K)-1
    res += K.traces_basis[i+1]*coeff(a, i)
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
  if K === F
    return tr(a)::elem_type(F)
  else
    return tr(tr(a), F)::elem_type(F)
  end
end

function tr(a::LocalFieldElem, F::FlintPadicField)
  return absolute_tr(a)
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
  return LocalFieldElem{S, T}(parent(a), a.data+b.data, min(precision(a), precision(b)))
end

function Base.:-(a::LocalFieldElem{S, T}, b::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  check_parent(a, b)
  return LocalFieldElem{S, T}(parent(a), a.data-b.data, min(precision(a), precision(b)))
end

function Base.:*(a::LocalFieldElem{S, T}, b::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  check_parent(a, b)
  pol = mod(a.data*b.data, defining_polynomial(parent(a)))
  res =  LocalFieldElem{S, T}(parent(a), pol, compute_precision(parent(a), pol))
  return res
end

function Base.:(//)(a::LocalFieldElem{S, T}, b::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  check_parent(a, b)
  ib = inv(b)
  pol = mod(a.data*ib.data, defining_polynomial(parent(a)))
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
  c.parent = a.parent
  c.data = mul!(c.data, a.data, b.data)
  c.data = mod(c.data, defining_polynomial(parent(a)))
  c.precision = compute_precision(a.parent, c.data)
  return c
end

function inv(a::LocalFieldElem)
  K = parent(a)
  p = invmod(a.data, defining_polynomial(K))
  return K(p)
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

  return K(powermod(a.data, n, defining_polynomial(K)))
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
  N = precision(a)
  res = one(K)
  res = setprecision(res, N)
  el = one(K)
  res = res
  den = setprecision!(one(Qp), N)
  max_i = fmpq(N)//(valuation(a) - fmpq(1, p-1)) + 1
  bound = Int(floor(fmpz, max_i))
  for i = 1:bound
    el *= a//i
    res += el
  end
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
    logeps = _log_one_units(eps^(p^f-1))//(p^f-1)
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
  el = a
  d = fmpz(1)
  e = absolute_ramification_index(K)
  v = numerator(e*valuation(a-1))
  N = precision(el)
  num = a
  den = fmpz(1)
  candidate = div(N, v)
  while true
    d *= p
    el = el^p
    N = precision(el)
    if isone(el)
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
  return _log_one_units_fast(num)//den
end

function _log_one_units_fast(a::LocalFieldElem)
  K = parent(a)
  if isone(a)
    return setprecision!(zero(K), precision(a))
  end
  b = a-1
  vb = valuation(b)
  p = prime(K)
  N = precision(a)
  res = zero(K)
  res = setprecision!(res, N)
  e = absolute_ramification_index(K)
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
  for i = 1:bound1
    el *= b
    to_add = el//i
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
      res += el//leftlim
    else
      res -= el//leftlim
    end
    inc = b^p
    for i = leftlim+p:p:bound2
      el *= inc
      if isodd(i)
        res += el//i
      else
        res -= el//i
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

AbstractAlgebra.promote_rule(::Type{fmpz}, ::Type{S}) where S <: LocalFieldElem = S

AbstractAlgebra.promote_rule(::Type{S}, ::Type{fmpq}) where S <: LocalFieldElem = S

AbstractAlgebra.promote_rule(::Type{fmpq}, ::Type{S}) where S <: LocalFieldElem = S

AbstractAlgebra.promote_rule(::Type{T}, ::Type{S}) where {S <: LocalFieldElem, T <: Integer} = S

AbstractAlgebra.promote_rule(::Type{S}, ::Type{T}) where {S <: LocalFieldElem, T <: Integer} = S

AbstractAlgebra.promote_rule(::Type{LocalFieldElem{S, T}}, ::Type{padic}) where {S <: FieldElem, T <: LocalFieldParameter} = LocalFieldElem{S, T}

AbstractAlgebra.promote_rule(::Type{LocalFieldElem{S, T}}, ::Type{qadic}) where {S <: FieldElem, T <: LocalFieldParameter} = LocalFieldElem{S, T}

AbstractAlgebra.promote_rule(::Type{padic}, ::Type{LocalFieldElem{S, T}}) where {S <: FieldElem, T <: LocalFieldParameter} = LocalFieldElem{S, T}

AbstractAlgebra.promote_rule(::Type{qadic}, ::Type{LocalFieldElem{S, T}}) where {S <: FieldElem, T <: LocalFieldParameter} = LocalFieldElem{S, T}

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
