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
#  Precision
#
################################################################################

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
  for i = 0:degree(a.data)
    setcoeff!(a.data, i, setprecision!(coeff(a, i), n))
  end
  return a
end

function setprecision!(a::Generic.Poly{T}, n::Int) where T <: LocalFieldElem
  for i = 1:length(a.coeffs)
    a.coeffs[i] = setprecision!(a.coeffs[i], n)
  end
  return a
end

################################################################################
#
#  Parent
#
################################################################################

parent(a::LocalFieldElem) =  a.parent

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

iszero(a::LocalFieldElem) = iszero(a.data)
isone(a::LocalFieldElem) = isone(a.data)
isunit(a::LocalFieldElem) = !iszero(a)

function zero(K::LocalField) 
  a = zero(parent(defining_polynomial(K)))
  return setprecision(K(a), precision(a))
end

function one(K::LocalField)
  a = one(parent(defining_polynomial(K)))
  return setprecision(K(a), precision(K))
end

################################################################################
#
#  Coercion
#
################################################################################

function (K::LocalField{S, T})(a::Int) where {S <: FieldElem, T <: LocalFieldParameter} 
  el =  K(parent(defining_polynomial(K))(a))
  return setprecision!(el, precision(K))
end

function (K::LocalField{S, T})(a::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter} 
  return a
end

function (K::LocalField{S, T})(a::LocalFieldElem{U, V}) where {S <: FieldElem, U <: FieldElem, T <: LocalFieldParameter, V <: LocalFieldParameter} 
  @show parent(a)
  @show K
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
  return LocalFieldElem{S, T}(K, p, precision(p))
end

################################################################################
#
#  Valuation
#
################################################################################

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
    vnew = vc + fmpq(j, n)
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
#  Basic operations
#
################################################################################

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
  res =  LocalFieldElem{S, T}(parent(a), pol, precision(pol))
  return res
end

function Base.:/(a::LocalFieldElem{S, T}, b::LocalFieldElem{S, T}) where {S <: FieldElem, T <: LocalFieldParameter}
  check_parent(a, b)
  ib = inv(b)
  pol = mod(a.data*ib.data, defining_polynomial(parent(a)))
  res =  LocalFieldElem{S, T}(parent(a), pol, precision(pol))
  return res
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
  c.parent = a.parent
  c.data = mul!(c.data, a.data, b.data)
  c.data = mod(c.data, defining_polynomial(parent(a)))
  c.precision = precision(c.data)
  return c
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
#  Promote rules
#
################################################################################

AbstractAlgebra.promote_rule(::Type{S}, ::Type{fmpz}) where S <: LocalFieldElem = S

AbstractAlgebra.promote_rule(::Type{fmpz}, ::Type{S}) where S <: LocalFieldElem = S

AbstractAlgebra.promote_rule(::Type{S}, ::Type{fmpq}) where S <: LocalFieldElem = S

AbstractAlgebra.promote_rule(::Type{fmpq}, ::Type{S}) where S <: LocalFieldElem = S

AbstractAlgebra.promote_rule(::Type{T}, ::Type{S}) where {S <: LocalFieldElem, T <: Integer} = S

AbstractAlgebra.promote_rule(::Type{S}, ::Type{T}) where {S <: LocalFieldElem, T <: Integer} = S

AbstractAlgebra.promote_rule(::Type{LocalFieldElem{padic, T}}, ::Type{padic}) where T <: LocalFieldParameter = LocalFieldElem{padic, T}

AbstractAlgebra.promote_rule(::Type{LocalFieldElem{qadic, T}}, ::Type{qadic}) where T <: LocalFieldParameter = LocalFieldElem{qadic, T}

AbstractAlgebra.promote_rule(::Type{padic}, ::Type{LocalFieldElem{padic, T}}) where T <: LocalFieldParameter = LocalFieldElem{padic, T}

AbstractAlgebra.promote_rule(::Type{qadic}, ::Type{LocalFieldElem{qadic, T}}) where T <: LocalFieldParameter = LocalFieldElem{qadic, T}


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