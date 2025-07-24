################################################################################
#
#  Parent
#
################################################################################

_is_sparse(a::AbstractCentralSimpleAlgebraElem) = _is_sparse(parent(a))

_is_dense(a::AbstractCentralSimpleAlgebraElem) = _is_dense(parent(a))

function AbstractAlgebra.promote_rule(U::Type{<:AbstractCentralSimpleAlgebraElem{T}}, ::Type{S}) where {T,S}
  if AbstractAlgebra.promote_rule(T, S) === T
    return U
  else
    return Union{}
  end
end

function AbstractAlgebra.promote_rule(::Type{S}, ::Type{S}) where {T,S<:AbstractCentralSimpleAlgebraElem{T}}
  return S
end

parent_type(::Type{CentralSimpleAlgebraElem{T,S}}) where {T,S} = S


parent(a::AbstractCentralSimpleAlgebraElem) = a.parent

function (K::AbsSimpleNumField)(a::AbstractCentralSimpleAlgebraElem{AbsSimpleNumFieldElem})
  @assert K == base_ring(parent(a))
  @assert has_one(parent(a))
  o = one(parent(a))

  if iszero(a)
    return zero(K)
  end

  i = findfirst(!iszero, o.coeffs)

  fl, c = divides(a.coeffs[i], o.coeffs[i])

  if fl
    if c * o == a
      return c
    end
  end

  error("Not an element of the base field")
end

function (K::QQField)(a::AbstractCentralSimpleAlgebraElem{QQFieldElem})
  @assert K == base_ring(parent(a))
  @assert has_one(parent(a))
  o = one(parent(a))

  if iszero(a)
    return zero(K)
  end

  i = findfirst(!iszero, o.coeffs)

  fl, c = divides(a.coeffs[i], o.coeffs[i])

  if fl
    if c * o == a
      return c
    end
  end

  error("Not an element of the base field")
end

################################################################################
#
#  Special elements
#
################################################################################

zero(A::AbstractCentralSimpleAlgebra) = A()::elem_type(A)

function one(A::AbstractCentralSimpleAlgebra)
  if _is_dense(A)
    return A(deepcopy(A.one)) # deepcopy needed by mul!
  else
    return A(deepcopy(A.sparse_one)::sparse_row_type(base_ring(A)))
  end
end

################################################################################
#
#  Unary operations
#
################################################################################

function -(a::AbstractCentralSimpleAlgebraElem{T}) where {T}
  if _is_sparse(a)
    return parent(a)(-a.coeffs_sparse)
  else
    v = T[-coefficients(a, copy=false)[i] for i = 1:dim(parent(a))]
    return parent(a)(v)
  end
end

################################################################################
#
#  Binary operations
#
################################################################################

function +(a::AbstractCentralSimpleAlgebraElem{T}, b::AbstractCentralSimpleAlgebraElem{T}) where {T}
  parent(a) != parent(b) && error("Parents don't match.")
  if !_is_sparse(a)
    v = Vector{T}(undef, dim(parent(a)))
    for i = 1:dim(parent(a))
      v[i] = coefficients(a, copy=false)[i] + coefficients(b, copy=false)[i]
    end
    return parent(a)(v)
  else
    vv = a.coeffs_sparse + b.coeffs_sparse
    return parent(a)(vv)
  end
end

function -(a::AbstractCentralSimpleAlgebraElem{T}, b::AbstractCentralSimpleAlgebraElem{T}) where {T}
  parent(a) != parent(b) && error("Parents don't match.")
  if _is_sparse(a)
    return parent(a)(a.coeffs_sparse - b.coeffs_sparse)
  else
    v = Vector{T}(undef, dim(parent(a)))
    for i = 1:dim(parent(a))
      v[i] = coefficients(a, copy=false)[i] - coefficients(b, copy=false)[i]
    end
    return parent(a)(v)
  end
end

function *(a::CentralSimpleAlgebraElem{T}, b::CentralSimpleAlgebraElem{T}) where {T}
  parent(a) != parent(b) && error("Parents don't match.")

  ca = coefficients(a, copy=false)
  cb = coefficients(b, copy=false)

  A = parent(a)
  n = dim(A)
  c = A()
  t = base_ring(A)()
  mt = multiplication_table(A, copy=false)

  for i = 1:n
    cai = ca[i]
    if iszero(cai)
      continue
    end
    for j = 1:n
      t = mul!(t, cai, cb[j])
      if iszero(t)
        continue
      end
      for k = 1:n
        c.coeffs[k] = addmul!(c.coeffs[k], mt[i, j, k], t)
      end
    end
  end
  return c
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function zero!(a::CentralSimpleAlgebraElem)
  for i = 1:length(coefficients(a, copy=false))
    a.coeffs[i] = zero!(coefficients(a, copy=false)[i])
  end
  return a
end

function add!(c::AbstractCentralSimpleAlgebraElem{T}, a::AbstractCentralSimpleAlgebraElem{T}, b::AbstractCentralSimpleAlgebraElem{T}) where {T}
  parent(a) != parent(b) && error("Parents don't match.")
  parent(c) != parent(b) && error("Parents don't match.")
  A = parent(a)
  d = dim(A)

  if c === a || c === b
    d = A()
    d = add!(d, a, b)
    return d
  end

  for i = 1:d
    c.coeffs[i] = add!(coefficients(c, copy=false)[i], coefficients(a, copy=false)[i], coefficients(b, copy=false)[i])
  end

  return c
end

function mul!(c::AbstractCentralSimpleAlgebraElem{T}, a::AbstractCentralSimpleAlgebraElem{T}, b::T) where {T}
  parent(a) != parent(c) && error("Parents don't match.")

  if c === a
    d = parent(a)()
    d = mul!(d, a, b)
    return d
  end

  for i = 1:dim(parent(a))
    c.coeffs[i] = mul!(coefficients(c, copy=false)[i], coefficients(a, copy=false)[i], b)
  end
  return c
end

mul!(c::AbstractCentralSimpleAlgebraElem{T}, a::T, b::AbstractCentralSimpleAlgebraElem{T}) where {T} = mul!(c, b, a)

function mul!(c::AbstractCentralSimpleAlgebraElem{T}, a::AbstractCentralSimpleAlgebraElem{T}, b::Union{Int,ZZRingElem}) where {T}
  parent(a) != parent(c) && error("Parents don't match.")

  if c === a
    d = parent(a)()
    d = mul!(d, a, b)
    return d
  end

  ccoeffs = coefficients(c, copy=false)

  bfmpq = QQFieldElem(b, 1)
  for i = 1:dim(parent(a))
    ccoeffs[i] = mul!(ccoeffs[i], coefficients(a, copy=false)[i], bfmpq)
  end

  if c isa MatAlgebraElem
    c.matrix = mul!(c.matrix, a.matrix, b)
  end
  return c
end


mul!(c::AbstractCentralSimpleAlgebraElem{T}, a::Union{Int,ZZRingElem}, b::AbstractCentralSimpleAlgebraElem{T}) where {T} = mul!(c, b, a)

function mul!(c::CentralSimpleAlgebraElem{T}, a::CentralSimpleAlgebraElem{T}, b::CentralSimpleAlgebraElem{T}) where {T}
  A = parent(a)
  n = dim(A)
  t = base_ring(A)()
  s = base_ring(A)()

  if c === a || c === b
    z = parent(a)()
    mul!(z, a, b)
    return z
  end

  ccoeff = coefficients(c, copy=false)
  acoeff = coefficients(a, copy=false)
  bcoeff = coefficients(b, copy=false)
  mt = multiplication_table(A, copy=false)

  for k in 1:n
    c.coeffs[k] = zero!(ccoeff[k])
  end

  for i = 1:n
    ai = acoeff[i]
    if iszero(ai)
      continue
    end
    for j = 1:n
      t = mul!(t, ai, bcoeff[j])
      if iszero(t)
        continue
      end
      for k = 1:n
        s = mul!(s, mt[i, j, k], t)
        c.coeffs[k] = add!(ccoeff[k], ccoeff[k], s)
        #c.coeffs[k] += A.mult_table[i, j, k]*t
      end
    end
  end
  #@assert c == a * b
  return c
end

################################################################################
#
#  Division
#
################################################################################

#TODO: make sure this is sensible.

function is_divisible_right(a::AbstractCentralSimpleAlgebraElem, b::AbstractCentralSimpleAlgebraElem)
  return is_divisible(a, b, :right)[1]
end

function is_divisible_left(a::AbstractCentralSimpleAlgebraElem, b::AbstractCentralSimpleAlgebraElem)
  return is_divisible(a, b, :left)[1]
end

# Tries to compute a/b if action is :right and b\a if action is :left
@doc raw"""
    is_divisible(a::AbstractCentralSimpleAlgebraElem, b::AbstractCentralSimpleAlgebraElem, action::Symbol)
      -> Bool, AbstractCentralSimpleAlgebraElem

Returns `true` and an element $c$ such that $a = c \cdot b$ (if
`action == :right`) respectively $a = b \cdot c$ (if `action == :left`) if
such an element exists and `false` and $0$ otherwise.
"""
function is_divisible(a::AbstractCentralSimpleAlgebraElem, b::AbstractCentralSimpleAlgebraElem, action::Symbol)
  parent(a) != parent(b) && error("Parents don't match.")
  # a/b = c <=> a = c*b, so we need to solve the system v_a = v_c*M_b for v_c

  A = parent(a)
  M = transpose(representation_matrix(b, action))
  va = matrix(base_ring(A), dim(A), 1, coefficients(a))
  # a could be a zero divisor, so there will not be a unique solution
  Ma = hcat(M, va)
  r = rref!(Ma)

  if r == 0 || all(iszero, [Ma[r, i] for i = 1:dim(A)])
    return false, A()
  end

  vc = _solve_ut(sub(Ma, 1:r, 1:dim(A)), sub(Ma, 1:r, (dim(A)+1):(dim(A)+1)))
  return true, A([vc[i, 1] for i = 1:dim(A)])
end

# Computes a/b if action is :right and b\a if action is :left (and if this is possible)
function divexact(a::AbstractCentralSimpleAlgebraElem, b::AbstractCentralSimpleAlgebraElem, action::Symbol=:left; check::Bool=true)
  t, c = is_divisible(a, b, action)
  if !t
    error("Division not possible")
  end
  return c
end

@doc raw"""
    divexact_right(a::AbstractCentralSimpleAlgebraElem, b::AbstractCentralSimpleAlgebraElem) -> AbstractAssociativeAlgebraElem

Returns an element $c$ such that $a = c \cdot b$.
"""
divexact_right(a::AbstractCentralSimpleAlgebraElem, b::AbstractCentralSimpleAlgebraElem; check::Bool=true) = divexact(a, b, :right; check=check)

@doc raw"""
    divexact_left(a::AbstractCentralSimpleAlgebraElem, b::AbstractCentralSimpleAlgebraElem) -> AbstractAssociativeAlgebraElem

Returns an element $c$ such that $a = b \cdot c$.
"""
divexact_left(a::AbstractCentralSimpleAlgebraElem, b::AbstractCentralSimpleAlgebraElem; check::Bool=true) = divexact(a, b, :left; check=check)

################################################################################
#
#  Ad hoc operations
#
################################################################################

function *(a::AbstractCentralSimpleAlgebraElem{S}, b::S) where {S<:RingElem}
  if !_is_sparse(a)
    return typeof(a)(parent(a), coefficients(a, copy=false) .* Ref(b))
  else
    return typeof(a)(parent(a), a.coeffs_sparse * b)
  end
end

*(b::S, a::AbstractCentralSimpleAlgebraElem{S}) where {S<:RingElem} = a * b

*(a::AbstractCentralSimpleAlgebraElem{T}, b::Integer) where {T<:RingElem} = a * base_ring(parent(a))(b)

*(b::Integer, a::AbstractCentralSimpleAlgebraElem{T}) where {T<:RingElem} = a * b

dot(a::AbstractCentralSimpleAlgebraElem{T}, b::T) where {T<:RingElem} = a * b

dot(b::T, a::AbstractCentralSimpleAlgebraElem{T}) where {T<:RingElem} = b * a

dot(a::AbstractCentralSimpleAlgebraElem{T}, b::Integer) where {T<:RingElem} = a * b

dot(b::Integer, a::AbstractCentralSimpleAlgebraElem{T}) where {T<:RingElem} = b * a

dot(a::AbstractCentralSimpleAlgebraElem{T}, b::ZZRingElem) where {T<:RingElem} = a * b

dot(b::ZZRingElem, a::AbstractCentralSimpleAlgebraElem{T}) where {T<:RingElem} = b * a

function dot(c::Vector{T}, V::Vector{CentralSimpleAlgebraElem{T,StructureConstantAlgebra{T}}}) where {T<:EuclideanRingResidueFieldElem{S}} where {S<:Union{Int,ZZRingElem}}
  @assert length(c) == length(V)
  A = parent(V[1])
  res = zero(A)
  aux = zero(A)
  for i = 1:length(c)
    aux = mul!(aux, V[i], c[i])
    res = add!(res, res, aux)
  end
  return res
end

function dot(c::Vector{fpFieldElem}, V::Vector{CentralSimpleAlgebraElem{fpFieldElem,StructureConstantAlgebra{fpFieldElem}}})
  @assert length(c) == length(V)
  A = parent(V[1])
  res = zero(A)
  aux = zero(A)
  for i = 1:length(c)
    aux = mul!(aux, V[i], c[i])
    res = add!(res, res, aux)
  end
  return res
end

################################################################################
#
#  Inverse
#
################################################################################

@doc raw"""
    is_invertible(a::AbstractCentralSimpleAlgebraElem) -> Bool, AbstractCentralSimpleAlgebraElem

Returns `true` and $a^{-1}$ if $a$ is a unit and `false` and $0$ otherwise.
"""
is_invertible(a::AbstractCentralSimpleAlgebraElem) = is_divisible(one(parent(a)), a, :right)

@doc raw"""
    inv(a::AbstractCentralSimpleAlgebraElem) -> AbstractCentralSimpleAlgebraElem

Assuming $a$ is a unit this function returns $a^{-1}$.
"""
function inv(a::AbstractCentralSimpleAlgebraElem)
  t, b = is_invertible(a)
  if !t
    error("Element is not invertible")
  end
  return b
end

################################################################################
#
#  Exponentiation
#
################################################################################

#TODO: Seemingly there is a bit limit on the size of the exponent (needs to be <128 bits, why is that?)

function ^(a::AbstractCentralSimpleAlgebraElem, b::Int)
  if b == 0
    return one(parent(a))
  elseif b == 1
    return deepcopy(a)
  else
    if b < 0
      a = inv(a)
      b = -b
    end
    bit = ~((~UInt(0)) >> 1)
    while (UInt(bit) & b) == 0
      bit >>= 1
    end
    z = deepcopy(a)
    bit >>= 1
    while bit != 0
      z = mul!(z, z, z)
      if (UInt(bit) & b) != 0
        z = mul!(z, z, a)
      end
      bit >>= 1
    end
    return z
  end
end

function ^(a::AbstractCentralSimpleAlgebraElem, b::ZZRingElem)
  if fits(Int, b)
    return a^Int(b)
  end

  if iszero(b)
    return one(parent(a))
  end

  if isone(b)
    return deepcopy(a)
  end

  if b < 0
    a = inv(a)
    b = -b
  end

  if mod(b, 2) == 0
    c = a^(div(b, 2))
    return c * c
  elseif mod(b, 2) == 1
    return a^(b - 1) * a
  else
    error("This should not happen")
  end
end

################################################################################
#
#  Parent object overloading
#
################################################################################

function (A::QuaternionAlgebra{T})() where {T}
  return CentralSimpleAlgebraElem{T,QuaternionAlgebra{T}}(A)
end

function _create_element_from_vector(A::AbstractCentralSimpleAlgebra{T}, c::Vector; copy::Bool=true) where {T}
  length(c) != dim(A) && error("Dimensions don't match.")
  if eltype(c) === T
    _c = c
  else
    _c = convert(Vector{T}, map(base_ring(A), c))::Vector{T}
  end
  if copy
    return CentralSimpleAlgebraElem{T,typeof(A)}(A, deepcopy(_c))
  else
    return CentralSimpleAlgebraElem{T,typeof(A)}(A, _c)
  end
end

function (A::QuaternionAlgebra{T})(c::Vector; copy::Bool=true) where {T}
  return _create_element_from_vector(A, c; copy)
end

function Base.getindex(A::AbstractCentralSimpleAlgebra{T}, i::Int) where {T}
  (i < 1 || i > dim(A)) && error("Index must be in range $(1:dim(A))")
  return basis(A)[i]
end

# Generic.Mat needs it
function (A::AbstractCentralSimpleAlgebra)(a::CentralSimpleAlgebraElem)
  @assert parent(a) == A "Wrong parent"
  return a
end

function (A::AbstractCentralSimpleAlgebra)(a::Union{Integer,ZZRingElem,Rational{<:Integer}})
  return A(base_ring(A)(a))
end

(A::AbstractCentralSimpleAlgebra{T})(x::T) where {T<:RingElem} = x * one(A)

(A::AbstractCentralSimpleAlgebra{T})(x::T) where {T<:CentralSimpleAlgebraElem} = x * one(A)

# resolve ambiguity
(A::AbstractCentralSimpleAlgebra{ZZRingElem})(x::ZZRingElem) = x * one(A)


################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::AbstractCentralSimpleAlgebraElem)
  if get(io, :compact, false)
    print(io, coefficients(a, copy=false))
  else
    if _is_sparse(a)
      sum = Expr(:call, :+)
      if !iszero(a)
        for (i, ci) in a.coeffs_sparse
          push!(sum.args,
            Expr(:call, :*, AbstractAlgebra.expressify(ci, context=io),
              AbstractAlgebra.expressify(parent(a).base_to_group[i], context=IOContext(io, :compact => true))))
        end
      end
      print(io, AbstractAlgebra.expr_to_string(AbstractAlgebra.canonicalize(sum)))
    else
      ve = Expr(:vect)
      for ci in coefficients(a, copy=false)
        push!(ve.args, AbstractAlgebra.expressify(ci, context=io))
      end
      print(io, AbstractAlgebra.expr_to_string(AbstractAlgebra.canonicalize(ve)))
    end
  end
end

# TODO: Expressify?

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(a::AbstractCentralSimpleAlgebraElem{T}, dict::IdDict) where {T}
  b = parent(a)()
  for x in fieldnames(typeof(a))
    if x != :parent && isdefined(a, x)
      setfield!(b, x, Base.deepcopy_internal(getfield(a, x), dict))
    end
  end
  return b
end

Base.copy(a::AbstractCentralSimpleAlgebraElem) = deepcopy(a)

################################################################################
#
#  Hashing
#
################################################################################

function Base.hash(a::AbstractCentralSimpleAlgebraElem{T}, h::UInt) where {T}
  return Base.hash(coefficients(a, copy=false), h)
end

################################################################################
#
#  Equality
#
################################################################################

function ==(a::AbstractCentralSimpleAlgebraElem{T}, b::AbstractCentralSimpleAlgebraElem{T}) where {T}
  parent(a) != parent(b) && return false
  if !_is_sparse(a)
    return coefficients(a, copy=false) == coefficients(b, copy=false)
  else
    return a.coeffs_sparse == b.coeffs_sparse
  end
end

################################################################################
#
#  isone/iszero
#
################################################################################

isone(a::AbstractCentralSimpleAlgebraElem) = a == one(parent(a))

function iszero(a::AbstractCentralSimpleAlgebraElem)
  if _is_sparse(a)
    return length(a.coeffs_sparse) == 0
  end
  return all(i -> iszero(i), coefficients(a, copy=false))
end

################################################################################
#
#  Field access
#
################################################################################

@doc raw"""
    coefficients(a::AbsAlgAbsElem; copy::Bool = true) -> Vector{RingElem}

Returns the coefficients of $a$ in the basis of `algebra(a)`.
"""
function coefficients(a::AbstractCentralSimpleAlgebraElem; copy::Bool=true)
  if copy
    return deepcopy(a.coeffs)
  end
  return a.coeffs
end

