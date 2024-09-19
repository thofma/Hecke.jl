################################################################################
#
#  Parent
#
################################################################################

function AbstractAlgebra.promote_rule(U::Type{<:AbstractAssociativeAlgebraElem{T}}, ::Type{S}) where {T, S}
  if AbstractAlgebra.promote_rule(T, S) === T
    return U
  else
    return Union{}
  end
end

parent_type(::Type{AssociativeAlgebraElem{T, S}}) where {T, S} = S

parent_type(::Type{GroupAlgebraElem{T, S}}) where {T, S} = S

parent(a::AbstractAssociativeAlgebraElem) = a.parent

function (K::AbsSimpleNumField)(a::AbstractAssociativeAlgebraElem{AbsSimpleNumFieldElem})
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

function (K::QQField)(a::AbstractAssociativeAlgebraElem{QQFieldElem})
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
#  elem_in_algebra
#
################################################################################

# This is may look weird but is really useful.
function _elem_in_algebra(a::AbstractAssociativeAlgebraElem; copy::Bool = true)
  if copy
    return deepcopy(a)
  else
    return a
  end
end

################################################################################
#
#  Special elements
#
################################################################################

zero(A::AbstractAssociativeAlgebra) = A()::elem_type(A)

function one(A::AbstractAssociativeAlgebra)
  if !has_one(A)
    error("Algebra does not have a one")
  end
  return A(deepcopy(A.one)) # deepcopy needed by mul!
end

################################################################################
#
#  Is integral
#
################################################################################

@doc raw"""
    is_integral(a::AbstractAssociativeAlgebraElem) -> Bool

Returns `true` if $a$ is integral and `false` otherwise.
"""
function is_integral(a::AbstractAssociativeAlgebraElem)
  f = minpoly(a)
  for i = 0:(degree(f) - 1)
    if !is_integral(coeff(f, i))
      return false
    end
  end
  return true
end

################################################################################
#
#  Idempotent
#
################################################################################

function is_idempotent(a::AbstractAssociativeAlgebraElem)
  return a^2 == a
end

function is_central(a::AbstractAssociativeAlgebraElem)
  return all(a * b == b * a for b in basis(parent(a)))
end

function is_central_idempotent(a::AbstractAssociativeAlgebraElem)
  return is_idempotent(a) && is_central(a)
end

################################################################################
#
#  Unary operations
#
################################################################################

function -(a::AbstractAssociativeAlgebraElem{T}) where {T}
  v = T[ -coefficients(a, copy = false)[i] for i = 1:dim(parent(a)) ]
  return parent(a)(v)
end

################################################################################
#
#  Binary operations
#
################################################################################

function +(a::AbstractAssociativeAlgebraElem{T}, b::AbstractAssociativeAlgebraElem{T}) where {T}
  parent(a) != parent(b) && error("Parents don't match.")
  v = Vector{T}(undef, dim(parent(a)))
  for i = 1:dim(parent(a))
    v[i] = coefficients(a, copy = false)[i] + coefficients(b, copy = false)[i]
  end
  return parent(a)(v)
end

function -(a::AbstractAssociativeAlgebraElem{T}, b::AbstractAssociativeAlgebraElem{T}) where {T}
  parent(a) != parent(b) && error("Parents don't match.")
  v = Vector{T}(undef, dim(parent(a)))
  for i = 1:dim(parent(a))
    v[i] = coefficients(a, copy = false)[i] - coefficients(b, copy = false)[i]
  end
  return parent(a)(v)
end

function *(a::AssociativeAlgebraElem{T}, b::AssociativeAlgebraElem{T}) where {T}
  parent(a) != parent(b) && error("Parents don't match.")

  ca = coefficients(a, copy = false)
  cb = coefficients(b, copy = false)

  A = parent(a)
  n = dim(A)
  c = A()
  t = base_ring(A)()
  mt = multiplication_table(A, copy = false)

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

function *(a::GroupAlgebraElem{T, S}, b::GroupAlgebraElem{T, S}) where {T, S}
  parent(a) != parent(b) && error("Parents don't match.")
  A = parent(a)
  d = dim(A)
  v = Vector{T}(undef, d)
  for i in 1:d
    v[i] = zero(base_ring(A))
  end
  t = zero(base_ring(A))
  mt = multiplication_table(A, copy = false)
  acoeff = coefficients(a, copy = false)
  bcoeff = coefficients(b, copy = false)
  for i in 1:d
    if iszero(acoeff[i])
      continue
    end
    for j in 1:d
      k = mt[i, j]
      v[k] = addmul!(v[k], acoeff[i], bcoeff[j], t)
    end
  end
  return A(v)
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function zero!(a::GroupAlgebraElem)
  for i = 1:length(coefficients(a, copy = false))
    a.coeffs[i] = zero!(coefficients(a, copy = false)[i])
  end
  return a
end

function zero!(a::AssociativeAlgebraElem)
  for i = 1:length(coefficients(a, copy = false))
    a.coeffs[i] = zero!(coefficients(a, copy = false)[i])
  end
  return a
end

function add!(c::AbstractAssociativeAlgebraElem{T}, a::AbstractAssociativeAlgebraElem{T}, b::AbstractAssociativeAlgebraElem{T}) where {T}
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
    c.coeffs[i] = add!(coefficients(c, copy = false)[i], coefficients(a, copy = false)[i], coefficients(b, copy = false)[i])
  end

  return c
end

function mul!(c::AbstractAssociativeAlgebraElem{T}, a::AbstractAssociativeAlgebraElem{T}, b::T) where {T}
  parent(a) != parent(c) && error("Parents don't match.")

  if c === a
    d = parent(a)()
    d = mul!(d, a, b)
    return d
  end

  for i = 1:dim(parent(a))
    c.coeffs[i] = mul!(coefficients(c, copy = false)[i], coefficients(a, copy = false)[i], b)
  end
  return c
end

mul!(c::AbstractAssociativeAlgebraElem{T}, a::T, b::AbstractAssociativeAlgebraElem{T}) where {T} = mul!(c, b, a)

function mul!(c::AbstractAssociativeAlgebraElem{T}, a::AbstractAssociativeAlgebraElem{T}, b::Union{ Int, ZZRingElem }) where {T}
  parent(a) != parent(c) && error("Parents don't match.")

  if c === a
    d = parent(a)()
    d = mul!(d, a, b)
    return d
  end

  ccoeffs = coefficients(c, copy = false)

  bfmpq = QQFieldElem(b, 1)
  for i = 1:dim(parent(a))
    ccoeffs[i] = mul!(ccoeffs[i], coefficients(a, copy = false)[i], bfmpq)
  end

  if c isa MatAlgebraElem
    c.matrix = mul!(c.matrix, a.matrix, b)
  end
  return c
end

mul!(c::AbstractAssociativeAlgebraElem{T}, a::Union{ Int, ZZRingElem }, b::AbstractAssociativeAlgebraElem{T}) where {T} = mul!(c, b, a)

function mul!(c::GroupAlgebraElem{T, S}, a::GroupAlgebraElem{T, S}, b::GroupAlgebraElem{T, S}) where {T, S}
  parent(a) != parent(b) && error("Parents don't match.")
  A = parent(a)
  d = dim(A)

  if c === a || c === b
    z = parent(a)()
    z = mul!(z, a, b)
    return z
  end

  v = coefficients(c, copy = false)

  for i in 1:d
    v[i] = zero!(v[i])
  end

  mA = multiplication_table(A, copy = false)
  ca = coefficients(a, copy = false)
  cb = coefficients(b, copy = false)

  for i in 1:d
    for j in 1:d
      k = mA[i, j]
      _v = v[k]
      if _ismutabletype(T)
        _v = addmul!(_v, ca[i], cb[j])
      else
        v[k] = addmul!(_v, ca[i], cb[j])
      end
    end
  end

  return c
end

if VERSION <= v"1.7"
  _ismutabletype(::Type{T}) where {T} = T.mutable
else
  _ismutabletype(::Type{T}) where {T} = ismutabletype(T)
end

function mul!(c::AssociativeAlgebraElem{T}, a::AssociativeAlgebraElem{T}, b::AssociativeAlgebraElem{T}) where {T}
  A = parent(a)
  n = dim(A)
  t = base_ring(A)()
  s = base_ring(A)()

  if c === a || c === b
    z = parent(a)()
    mul!(z, a, b)
    return z
  end

  ccoeff = coefficients(c, copy = false)
  acoeff = coefficients(a, copy = false)
  bcoeff = coefficients(b, copy = false)
  mt = multiplication_table(A, copy = false)

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

# Tries to compute a/b if action is :right and b\a if action is :left
@doc raw"""
    is_divisible(a::AbstractAssociativeAlgebraElem, b::AbstractAssociativeAlgebraElem, action::Symbol)
      -> Bool, AbstractAssociativeAlgebraElem

Returns `true` and an element $c$ such that $a = c \cdot b$ (if
`action == :right`) respectively $a = b \cdot c$ (if `action == :left`) if
such an element exists and `false` and $0$ otherwise.
"""
function is_divisible(a::AbstractAssociativeAlgebraElem, b::AbstractAssociativeAlgebraElem, action::Symbol)
  parent(a) != parent(b) && error("Parents don't match.")
  # a/b = c <=> a = c*b, so we need to solve the system v_a = v_c*M_b for v_c

  A = parent(a)
  M = transpose(representation_matrix(b, action))
  va = matrix(base_ring(A), dim(A), 1, coefficients(a))
  # a could be a zero divisor, so there will not be a unique solution
  Ma = hcat(M, va)
  r = rref!(Ma)

  if all(iszero, [ Ma[r, i] for i = 1:dim(A) ])
    return false, A()
  end

  vc = _solve_ut(sub(Ma, 1:r, 1:dim(A)), sub(Ma, 1:r, (dim(A) + 1):(dim(A) + 1)))
  return true, A([ vc[i, 1] for i = 1:dim(A) ])
end

# Computes a/b if action is :right and b\a if action is :left (and if this is possible)
function divexact(a::AbstractAssociativeAlgebraElem, b::AbstractAssociativeAlgebraElem, action::Symbol = :left; check::Bool=true)
  t, c = is_divisible(a, b, action)
  if !t
    error("Division not possible")
  end
  return c
end

@doc raw"""
    divexact_right(a::AbstractAssociativeAlgebraElem, b::AbstractAssociativeAlgebraElem) -> AbstractAssociativeAlgebraElem

Returns an element $c$ such that $a = c \cdot b$.
"""
divexact_right(a::AbstractAssociativeAlgebraElem, b::AbstractAssociativeAlgebraElem; check::Bool=true) = divexact(a, b, :right; check=check)

@doc raw"""
    divexact_left(a::AbstractAssociativeAlgebraElem, b::AbstractAssociativeAlgebraElem) -> AbstractAssociativeAlgebraElem

Returns an element $c$ such that $a = b \cdot c$.
"""
divexact_left(a::AbstractAssociativeAlgebraElem, b::AbstractAssociativeAlgebraElem; check::Bool=true) = divexact(a, b, :left; check=check)

################################################################################
#
#  Ad hoc operations
#
################################################################################

function *(a::AbstractAssociativeAlgebraElem{S}, b::S) where {S <: RingElem}
  return typeof(a)(parent(a), coefficients(a, copy = false).* Ref(b))
end

*(b::S, a::AbstractAssociativeAlgebraElem{S}) where {S <: RingElem} = a*b

*(a::AbstractAssociativeAlgebraElem{T}, b::Integer) where {T <: RingElem} = a*base_ring(parent(a))(b)

*(b::Integer, a::AbstractAssociativeAlgebraElem{T}) where {T <: RingElem} = a*b

dot(a::AbstractAssociativeAlgebraElem{T}, b::T) where {T <: RingElem} = a*b

dot(b::T, a::AbstractAssociativeAlgebraElem{T}) where {T <: RingElem} = b*a

dot(a::AbstractAssociativeAlgebraElem{T}, b::Integer) where {T <: RingElem} = a*b

dot(b::Integer, a::AbstractAssociativeAlgebraElem{T}) where {T <: RingElem} = b*a

dot(a::AbstractAssociativeAlgebraElem{T}, b::ZZRingElem) where {T <: RingElem} = a*b

dot(b::ZZRingElem, a::AbstractAssociativeAlgebraElem{T}) where {T <: RingElem} = b*a

function dot(c::Vector{T}, V::Vector{AssociativeAlgebraElem{T, StructureConstantAlgebra{T}}}) where T <: EuclideanRingResidueFieldElem{S} where S <: Union{Int, ZZRingElem}
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

function dot(c::Vector{fpFieldElem}, V::Vector{AssociativeAlgebraElem{fpFieldElem, StructureConstantAlgebra{fpFieldElem}}})
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
    is_invertible(a::AbstractAssociativeAlgebraElem) -> Bool, AbstractAssociativeAlgebraElem

Returns `true` and $a^{-1}$ if $a$ is a unit and `false` and $0$ otherwise.
"""
is_invertible(a::AbstractAssociativeAlgebraElem) = is_divisible(one(parent(a)), a, :right)

@doc raw"""
    inv(a::AbstractAssociativeAlgebraElem) -> AbstractAssociativeAlgebraElem

Assuming $a$ is a unit this function returns $a^{-1}$.
"""
function inv(a::AbstractAssociativeAlgebraElem)
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

function ^(a::AbstractAssociativeAlgebraElem, b::Int)
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

function ^(a::AbstractAssociativeAlgebraElem, b::ZZRingElem)
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
    return c*c
  elseif mod(b, 2) == 1
    return a^(b - 1)*a
  else
    error("This should not happen")
  end
end

################################################################################
#
#  Parent object overloading
#
################################################################################

function (A::StructureConstantAlgebra{T})() where {T}
  if iszero(A)
    return A(T[])
  end
  return AssociativeAlgebraElem{T, StructureConstantAlgebra{T}}(A)
end

function (A::QuaternionAlgebra{T})() where {T}
  return AssociativeAlgebraElem{T, StructureConstantAlgebra{T}}(A)
end

(A::GroupAlgebra{T, S, R})() where {T, S, R} = GroupAlgebraElem{T, typeof(A)}(A)

function (A::StructureConstantAlgebra{T})(c::Vector; copy::Bool = true) where {T}
  length(c) != dim(A) && error("Dimensions don't match.")
  if eltype(c) === T
    _c = c
  else
    _c = convert(Vector{T}, map(base_ring(A), c))::Vector{T}
  end
  if copy
    return AssociativeAlgebraElem{T, StructureConstantAlgebra{T}}(A, deepcopy(_c))
  else
    return AssociativeAlgebraElem{T, StructureConstantAlgebra{T}}(A, _c)
  end
end

function (A::QuaternionAlgebra{T})(c::Vector{T}; copy::Bool = true) where {T}
  length(c) != dim(A) && error("Dimensions don't match.")
  return AssociativeAlgebraElem{T, QuaternionAlgebra{T}}(A, copy ? deepcopy(c) : c)
end

function Base.getindex(A::AbstractAssociativeAlgebra{T}, i::Int) where {T}
  (i < 1 || i > dim(A)) && error("Index must be in range $(1:dim(A))")
  return basis(A)[i]
end

#function (A::GroupAlgebra{T, S, R})(c::Vector{T}) where {T, S, R}
#  length(c) != dim(A) && error("Dimensions don't match.")
#  return GroupAlgebraElem{T, typeof(A)}(A, deepcopy(c))
#end

function (A::GroupAlgebra{T, S, R})(c::R) where {T, S, R}
  return GroupAlgebraElem{T, typeof(A)}(A, deepcopy(c))
end

# Generic.Mat needs it
function (A::AbstractAssociativeAlgebra)(a::AssociativeAlgebraElem)
  @assert parent(a) == A "Wrong parent"
  return a
end

function (A::GroupAlgebra)(a::GroupAlgebraElem)
  @assert parent(a) == A "Wrong parent"
  return a
end

# For polynomial substitution
for T in subtypes(AbstractAssociativeAlgebra)
  @eval begin
    function (A::$T)(a::Union{Integer, ZZRingElem, Rational{<: Integer}})
      return A(base_ring(A)(a))
    end

    #function (A::$T{S})(a::S) where {S <: RingElem}
    #  return a*one(A)
    #end
  end
end

(A::AbstractAssociativeAlgebra{T})(x::T) where {T <: RingElem} = x * one(A)

(A::AbstractAssociativeAlgebra{T})(x::T) where {T <: AssociativeAlgebraElem} = x * one(A)

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::AbstractAssociativeAlgebraElem)
  if get(io, :compact, false)
    print(io, coefficients(a, copy = false))
  else
    print(io, "Element of ")
    print(io, parent(a))
    print(io, " with coefficients ")
    print(io, coefficients(a, copy = false))
  end
end

# TODO: Expressify?

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(a::AbstractAssociativeAlgebraElem{T}, dict::IdDict) where {T}
  b = parent(a)()
  for x in fieldnames(typeof(a))
    if x != :parent && isdefined(a, x)
      setfield!(b, x, Base.deepcopy_internal(getfield(a, x), dict))
    end
  end
  return b
end

Base.copy(a::AbstractAssociativeAlgebraElem) = deepcopy(a)

################################################################################
#
#  Hashing
#
################################################################################

function Base.hash(a::AbstractAssociativeAlgebraElem{T}, h::UInt) where {T}
  return Base.hash(coefficients(a, copy = false), h)
end

################################################################################
#
#  Equality
#
################################################################################

function ==(a::AbstractAssociativeAlgebraElem{T}, b::AbstractAssociativeAlgebraElem{T}) where {T}
  parent(a) != parent(b) && return false
  return coefficients(a, copy = false) == coefficients(b, copy = false)
end

################################################################################
#
#  Minpoly / (reduced) charpoly
#
################################################################################

@doc raw"""
    minpoly(a::AbstractAssociativeAlgebraElem) -> PolyRingElem

Returns the minimal polynomial of $a$ as a polynomial over
`base_ring(algebra(a))`.
"""
function Generic.minpoly(a::AbstractAssociativeAlgebraElem)
  M = representation_matrix(a)
  R = polynomial_ring(base_ring(parent(a)), "x", cached=false)[1]
  return minpoly(R, a)
end

function Generic.minpoly(R::PolyRing, a::AbstractAssociativeAlgebraElem)
  M = representation_matrix(a)
  return minpoly(R, M)
end

@doc raw"""
    charpoly(a::AbstractAssociativeAlgebraElem) -> PolyRingElem

Returns the characteristic polynomial of $a$ as a polynomial over
`base_ring(algebra(a))`.
"""
function charpoly(a::AbstractAssociativeAlgebraElem)
  M = representation_matrix(a)
  R = polynomial_ring(base_ring(parent(a)), "x", cached = false)[1]
  return charpoly(R, M)
end

function _reduced_charpoly_simple(a::AbstractAssociativeAlgebraElem, R::PolyRing)
  A = parent(a)
  @assert is_simple(A)

  M = representation_matrix(a)
  f = charpoly(R, M)
  sf_fac = factor_squarefree(f)

  d = dimension_of_center(A)
  n = divexact(dim(A), d)
  m = isqrt(n)
  @assert m^2 == n

  g = one(R)
  for (h, e) in sf_fac
    q, r = divrem(e, m)
    @assert iszero(r)
    g = mul!(g, g, h^q)
  end

  u = unit(sf_fac)
  if !isone(u)
    fl, uu = is_power(coeff(u, 0), m)
    @assert fl
    g = uu * g
  end

  return g
end

@doc raw"""
    reduced_charpoly(a::AbstractAssociativeAlgebraElem) -> PolyRingElem

Returns the reduced characteristic polynomial of $a$ as a polynomial over
`base_ring(algebra(a))`.
"""
function reduced_charpoly(a::AbstractAssociativeAlgebraElem)
  A = parent(a)
  R = polynomial_ring(base_ring(A), "x", cached = false)[1]
  W = decompose(A)
  f = one(R)
  for (B, BtoA) in W
    f *= _reduced_charpoly_simple(BtoA\a, R)
  end
  return f
end

################################################################################
#
#  Representation matrix
#
################################################################################

function elem_to_mat_row!(M::MatElem{T}, i::Int, a::AbstractAssociativeAlgebraElem{T}) where T
  ca = coefficients(a, copy = false)
  for c = 1:ncols(M)
    if M isa QQMatrix
      M[i, c] = ca[c]
    else
      M[i, c] = deepcopy(ca[c])
    end
  end
  return nothing
end

function elem_from_mat_row(A::AbstractAssociativeAlgebra{T}, M::MatElem{T}, i::Int) where T
  a = A()
  for c = 1:ncols(M)
    a.coeffs[c] = deepcopy(M[i, c])
  end
  return a
end

function elem_to_mat_row!(x::ZZMatrix, i::Int, d::ZZRingElem, a::AbstractAssociativeAlgebraElem{QQFieldElem})
  z = zero_matrix(FlintQQ, 1, ncols(x))
  elem_to_mat_row!(z, 1, a)
  z_q = FakeFmpqMat(z)

  for j in 1:ncols(x)
    x[i, j] = z_q.num[1, j]
  end

  ccall((:fmpz_set, libflint), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}), d, z_q.den)
  return nothing
end

function elem_from_mat_row(A::AbstractAssociativeAlgebra{QQFieldElem}, M::ZZMatrix, i::Int, d::ZZRingElem = ZZRingElem(1))
  a = A()
  for j in 1:ncols(M)
    a.coeffs[j] = QQFieldElem(M[i, j], d)
  end
  return a
end

@doc raw"""
    representation_matrix(a::AbstractAssociativeAlgebraElem, action::Symbol = :left) -> MatElem

Returns a matrix over `base_ring(algebra(a))` representing multiplication with
$a$ with respect to the basis of `algebra(a)`.
The multiplication is from the left if `action == :left` and from the right if
`action == :right`.
"""
function representation_matrix(a::GroupAlgebraElem, action::Symbol=:left)
  A = parent(a)
  acoeff = coefficients(a, copy = false)
  mt = multiplication_table(A, copy = false)
  M = zero_matrix(base_ring(A), dim(A), dim(A))
  if action == :left
    for i = 1:dim(A)
      for j = 1:dim(A)
        _set_to_copy!(M, i, mt[j, i], acoeff[j]) # M[i, mt[j, i]] = deepcopy(acoeff[j])
      end
    end
  elseif action == :right
    for i = 1:dim(A)
      for j = 1:dim(A)
        _set_to_copy!(M, i, mt[i, j], acoeff[j]) # M[i, mt[i, j] = deepcopy(acoeff[j])
      end
    end
  else
    error("Not yet implemented")
  end
  return M
end

_set_to_copy!(M::QQMatrix, i, j, c) = M[i, j] = c

_set_to_copy!(M, i, j, c) = M[i, j] = deepcopy(c)

function _addmul!(M::MatrixElem, i, j, b, c, temp = nothing)
  return M[i, j] = addmul!(M[i, j], b, c)
end

function _addmul!(M::QQMatrix, i, j, a::QQFieldElem, b::QQFieldElem, temp = nothing)
  GC.@preserve M begin
    c = mat_entry_ptr(M, i, j)
    ccall((:fmpq_addmul, libflint), Nothing, (Ptr{QQFieldElem}, Ref{QQFieldElem}, Ref{QQFieldElem}), c, a, b)
  end
end

function _addmul!(M::FqMatrix, i, j, a::FqFieldElem, b::FqFieldElem, temp = base_ring(M)())
  GC.@preserve M begin
    c = Nemo.fq_default_mat_entry_ptr(M, i, j)
    mul!(temp, a, b)
    ccall((:fq_default_add, libflint), Nothing, (Ptr{FqFieldElem}, Ptr{FqFieldElem}, Ref{FqFieldElem}, Ref{FqField}), c, c, temp, base_ring(M))
  end
end

function representation_matrix!(a::Union{AssociativeAlgebraElem, MatAlgebraElem}, M::MatElem, action::Symbol = :left)
  A = parent(a)
  acoeff = coefficients(a, copy = false)
  mt = multiplication_table(A, copy = false)
  if base_ring(A) isa QQField
    temp = nothing
  else
    temp = base_ring(A)()
  end
  GC.@preserve M begin
    if action == :left
      for i = 1:dim(A)
        if iszero(acoeff[i])
          continue
        end
        for j = 1:dim(A)
          for k = 1:dim(A)
            _addmul!(M, j, k, acoeff[i], mt[i, j, k], temp)
            #M[j, k] += acoeff[i] * mt[i, j, k]
          end
        end
      end
    elseif action == :right
      for i = 1:dim(A)
        if iszero(coefficients(a, copy = false)[i])
          continue
        end
        for j = 1:dim(A)
          for k = 1:dim(A)
            _addmul!(M, j, k, acoeff[i], mt[j, i, k]) # M[j, k] += acoeff[i] * mt[j, i, k]
          end
        end
      end
    else
      error("Not yet implemented")
    end
  end
  return M
end

function representation_matrix(a::Union{ AssociativeAlgebraElem, MatAlgebraElem }, action::Symbol = :left)
  A = parent(a)
  M = zero_matrix(base_ring(A), dim(A), dim(A))
  representation_matrix!(a, M, action)
  return M
end

################################################################################
#
#  isone/iszero
#
################################################################################

isone(a::AbstractAssociativeAlgebraElem) = a == one(parent(a))

function iszero(a::AbstractAssociativeAlgebraElem)
  return all(i -> iszero(i), coefficients(a, copy = false))
end

################################################################################
#
#  (Reduced) trace
#
################################################################################

#function tr(x::AbstractAssociativeAlgebraElem)
#  return tr(representation_matrix(x))
#end

@doc raw"""
    tr(x::AbstractAssociativeAlgebraElem{T}) where T -> T

Returns the trace of $x$.
"""
function tr(x::AbstractAssociativeAlgebraElem{T}) where T
  A=parent(x)
  _assure_trace_basis(A)
  tr=zero(base_ring(A))
  for i=1:dim(A)
    tr = add!(tr, tr, coefficients(x, copy = false)[i]*A.trace_basis_elem[i])
  end
  return tr
end

#function _tr(x::AssociativeAlgebraElem{T}) where {T}
#  return trace(representation_matrix(x))
#end

@doc raw"""
    trred(x::AbstractAssociativeAlgebraElem{T}) where T -> T

Returns the reduced trace of $x$.
"""
function trred(a::AbstractAssociativeAlgebraElem)
  A = parent(a)
  if is_simple_known(A) && A.is_simple == 1
    d = dimension_of_center(A)
    n = divexact(dim(A), d)
    m = isqrt(n)
    @assert m^2 == n
    return divexact(tr(a), m)
  else
    W = decompose(A)
    t = zero(base_ring(A))
    for (B, BtoA) in W
      t = t + trred(BtoA\(a))
    end
    return t
  end
end

################################################################################
#
#  (Reduced) norm
#
################################################################################

@doc raw"""
    norm(x::AbstractAssociativeAlgebraElem{T}) where T -> T

Returns the norm of $x$.
"""
function norm(a::AbstractAssociativeAlgebraElem{QQFieldElem})
  return abs(det(representation_matrix(a)))
end

function norm(a::AbstractAssociativeAlgebraElem)
  return det(representation_matrix(a))
end

@doc raw"""
    normred(x::AbstractAssociativeAlgebraElem{T}) where T -> T

Returns the reduced norm of $x$.
"""
function normred(a::AbstractAssociativeAlgebraElem{T}) where {T}
  f = reduced_charpoly(a)
  n = degree(f)
  if iseven(n)
    return coeff(f, 0)
  else
    return -coeff(f, 0)
  end
end

function _normred_over_center_simple(a::AbstractAssociativeAlgebraElem, ZtoA::AbsAlgAssMor)
  A = parent(a)
  Z = domain(ZtoA)
  fields = as_number_fields(Z)
  @assert length(fields) == 1
  K, ZtoK = fields[1]
  B, BtoA = _as_algebra_over_center(A)
  @assert base_ring(B) === K
  n = normred(BtoA\(a))
  return ZtoK\(n)
end

# Computes the norm of algebra(a) considered as an algebra over its centre.
# ZtoA should be center(algebra(a))[2]
function normred_over_center(a::AbstractAssociativeAlgebraElem, ZtoA::AbsAlgAssMor)
  A = parent(a)
  Adec = decompose(A)
  n = zero(domain(ZtoA))
  for (B, BtoA) in Adec
    _, ZtoB = center(B)
    n1 = _normred_over_center_simple(BtoA\a, ZtoB)
    t, n2 = has_preimage_with_preimage(ZtoA, BtoA(ZtoB(n1)))
    n += n2
  end
  return n
end

function normred(x::FacElem{S, T}) where { S <: AbstractAssociativeAlgebraElem, T <: AbstractAssociativeAlgebra }
  K = base_ring(base_ring(parent(x)))
  @assert is_commutative(K) # so, it doesn't matter in which order we compute the norms
  n = one(K)
  for (b, e) in x.fac
    n *= normred(b)^e
  end
  return n
end

################################################################################
#
#  Gram matrix of reduced trace
#
################################################################################

@doc raw"""
    trred_matrix(A::Vector{ <: AssociativeAlgebraElem}) -> MatElem

Returns a matrix $M$ such that $M_{ij} = \mathrm{tr}(A_i \cdot A_j)$ where
$\mathrm{tr}$ is the reduced trace.
"""
function trred_matrix(A::Vector{<: AbstractAssociativeAlgebraElem})
  n = length(A)
  n == 0 && error("Array must be non-empty")
  K = base_ring(parent(A[1]))
  M = zero_matrix(K, n, n)
  for i in 1:n
    for j in 1:n
      M[i, j] = trred(A[i] * A[j])
    end
  end
  return M
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
function coefficients(a::AbstractAssociativeAlgebraElem; copy::Bool = true)
  if copy
    return deepcopy(a.coeffs)
  end
  return a.coeffs
end

################################################################################
#
#  Denominator
#
################################################################################

function denominator(x::AbstractAssociativeAlgebraElem)
  return lcm([ denominator(y) for y in coefficients(x, copy = false) ])
end
