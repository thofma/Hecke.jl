################################################################################
#
#  Parent
#
################################################################################

parent_type(::Type{AlgAssElem{T, S}}) where {T, S} = S

parent_type(::Type{AlgGrpElem{T, S}}) where {T, S} = S

parent(a::AbsAlgAssElem) = a.parent

################################################################################
#
#  Special elements
#
################################################################################

zero(A::AbsAlgAss) = A()

function one(A::AbsAlgAss)
  if !has_one(A)
    error("Algebra does not have a one")
  end
  return A(deepcopy(A.one)) # deepcopy needed by mul!
end

################################################################################
#
#  Unary operations
#
################################################################################

function -(a::AbsAlgAssElem{T}) where {T}
  coeffs = T[ -a.coeffs[i] for i = 1:dim(parent(a)) ]
  return parent(a)(coeffs)
end

################################################################################
#
#  Binary operations
#
################################################################################

function +(a::AbsAlgAssElem{T}, b::AbsAlgAssElem{T}) where {T}
  parent(a) != parent(b) && error("Parents don't match.")
  coeffs = Array{T, 1}(undef, dim(parent(a)))
  for i = 1:dim(parent(a))
    coeffs[i] = a.coeffs[i] + b.coeffs[i]
  end
  return parent(a)(coeffs)
end

function -(a::AbsAlgAssElem{T}, b::AbsAlgAssElem{T}) where {T}
  parent(a) != parent(b) && error("Parents don't match.")
  coeffs = Array{T, 1}(undef, dim(parent(a)))
  for i = 1:dim(parent(a))
    coeffs[i] = a.coeffs[i] - b.coeffs[i]
  end
  return parent(a)(coeffs)
end

function *(a::AlgAssElem{T}, b::AlgAssElem{T}) where {T}
  parent(a) != parent(b) && error("Parents don't match.")

  A = parent(a)
  n = dim(A)
  c = A()
  t = base_ring(A)()
  for i = 1:n
    if iszero(a.coeffs[i])
      continue
    end
    for j = 1:n
      t = a.coeffs[i]*b.coeffs[j]
      if iszero(t)
        continue
      end
      for k = 1:n
        c.coeffs[k] += A.mult_table[i, j, k]*t
      end
    end
  end
  return c
end

function *(a::AlgGrpElem{T, S}, b::AlgGrpElem{T, S}) where {T, S}
  parent(a) != parent(b) && error("Parents don't match.")
  A = parent(a)
  d = dim(A)
  coeffs = Vector{T}(undef, d)
  for i in 1:d
    coeffs[i] = zero(base_ring(A))
  end
  for i in 1:d
    for j in 1:d
      coeffs[A.mult_table[i, j]] += a.coeffs[i] * b.coeffs[j]
    end
  end
  return A(coeffs)
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function zero!(a::AlgGrpElem)
  for i = 1:length(a.coeffs)
    a.coeffs[i] = zero!(a.coeffs[i])
  end
  return a
end

function zero!(a::AlgAssElem)
  for i = 1:length(a.coeffs)
    a.coeffs[i] = zero!(a.coeffs[i])
  end
  return a
end

function add!(c::AbsAlgAssElem{T}, a::AbsAlgAssElem{T}, b::AbsAlgAssElem{T}) where {T}
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
    c.coeffs[i] = add!(c.coeffs[i], a.coeffs[i], b.coeffs[i])
  end

  return c
end

function mul!(c::AbsAlgAssElem{T}, a::AbsAlgAssElem{T}, b::T) where {T}
  parent(a) != parent(c) && error("Parents don't match.")

  if c === a
    d = parent(a)()
    d = mul!(d, a, b)
    return d
  end

  for i = 1:dim(parent(a))
    c.coeffs[i] = mul!(c.coeffs[i], a.coeffs[i], b)
  end
  return c
end

mul!(c::AbsAlgAssElem{T}, a::T, b::AbsAlgAssElem{T}) where {T} = mul!(c, b, a)

function mul!(c::AbsAlgAssElem{T}, a::AbsAlgAssElem{T}, b::fmpz) where {T}
  parent(a) != parent(c) && error("Parents don't match.")

  if c === a
    d = parent(a)()
    d = mul!(d, a, b)
    return d
  end

  bfmpq = fmpq(b, 1)
  for i = 1:dim(parent(a))
    c.coeffs[i] = mul!(c.coeffs[i], a.coeffs[i], bfmpq)
  end
  return c
end

mul!(c::AbsAlgAssElem{T}, a::fmpz, b::AbsAlgAssElem{T}) where {T} = mul!(c, b, a)

function mul!(c::AlgGrpElem{T, S}, a::AlgGrpElem{T, S}, b::AlgGrpElem{T, S}) where {T, S}
  parent(a) != parent(b) && error("Parents don't match.")
  A = parent(a)
  d = dim(A)

  if c === a || c === b
    z = parent(a)()
    mul!(z, a, b)
    return z
  end

  coeffs = c.coeffs

  for i in 1:d
    coeffs[i] = zero(base_ring(A))
  end

  for i in 1:d
    for j in 1:d
      coeffs[A.mult_table[i, j]] += a.coeffs[i] * b.coeffs[j]
    end
  end

  return c
end

function mul!(c::AlgAssElem{T}, a::AlgAssElem{T}, b::AlgAssElem{T}) where {T}
  A = parent(a)
  n = dim(A)
  t = base_ring(A)()
  s = base_ring(A)()

  if c === a || c === b
    z = parent(a)()
    mul!(z, a, b)
    return z
  end

  for k in 1:n
    c.coeffs[k] = zero!(c.coeffs[k])
  end

  for i = 1:n
    if iszero(a.coeffs[i])
      continue
    end
    for j = 1:n
      t = a.coeffs[i]*b.coeffs[j]
      if iszero(t)
        continue
      end
      for k = 1:n
        s = mul!(s, A.mult_table[i, j, k], t)
        c.coeffs[k] = add!(c.coeffs[k], c.coeffs[k], s)
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

# Computes a/b if action is :right and b\a if action is :left (and if this is possible)
function divexact(a::AbsAlgAssElem, b::AbsAlgAssElem, action::Symbol)
  parent(a) != parent(b) && error("Parents don't match.")
  # a/b = c <=> a = c*b, so we need to solve the system v_a = v_c*M_b for v_c

  A = parent(a)
  M = transpose(representation_matrix(b, action))
  va = matrix(base_ring(A), dim(A), 1, coeffs(a))
  # a could be a zero divisor, so there will not be a unique solution
  Ma = hcat(M, va)
  r = rref!(Ma)
  @assert !all(iszero, [ Ma[r, i] for i = 1:dim(A) ]) "Division not possible"
  vc = solve_ut(sub(Ma, 1:r, 1:dim(A)), sub(Ma, 1:r, (dim(A) + 1):(dim(A) + 1)))

  return A([ vc[i, 1] for i = 1:dim(A) ])
end

divexact_right(a::AbsAlgAssElem, b::AbsAlgAssElem) = divexact(a, b, :right)

divexact_left(a::AbsAlgAssElem, b::AbsAlgAssElem) = divexact(a, b, :left)

################################################################################
#
#  Ad hoc operations
#
################################################################################

function *(a::AbsAlgAssElem{S}, b::T) where {T <: RingElem, S <: RingElem}
  return typeof(a)(parent(a), a.coeffs.* Ref(b))
end

*(b::T, a::AbsAlgAssElem{S}) where {T <: RingElem,  S <: RingElem } = a*b

*(a::AbsAlgAssElem{T}, b::Integer) where {T} = a*base_ring(parent(a))(b)

*(b::Integer, a::AbsAlgAssElem{T}) where {T} = a*b

dot(a::AbsAlgAssElem{T}, b::T) where {T} = a*b

dot(b::T, a::AbsAlgAssElem{T}) where {T} = b*a

dot(a::AbsAlgAssElem{T}, b::Integer) where {T} = a*b

dot(b::Integer, a::AbsAlgAssElem{T}) where {T} = b*a

dot(a::AbsAlgAssElem{T}, b::fmpz) where {T} = a*b

dot(b::fmpz, a::AbsAlgAssElem{T}) where {T} = b*a

################################################################################
#
#  Inverse
#
################################################################################

function inv(a::AbsAlgAssElem)
  return divexact_right(one(parent(a)), a)
end

################################################################################
#
#  Exponentiation
#
################################################################################

function ^(a::AbsAlgAssElem, b::Int)
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

function ^(a::AbsAlgAssElem, b::fmpz)
  if nbits(b) < 64
    return a^Int(b)
  end
  if b < 0
    a = inv(a)
    b = -b
  elseif b == 0
    return one(parent(a))
  elseif b == 1
    return deepcopy(a)
  elseif mod(b, 2) == 0
    c = a^(div(b, 2))
    return c*c
  elseif mod(b, 2) == 1
    return a^(b - 1)*a
  end
end

################################################################################
#
#  Parent object overloading
#
################################################################################

(A::AlgAss{T})() where {T} = AlgAssElem{T, AlgAss{T}}(A)

(A::AlgGrp{T, S, R})() where {T, S, R} = AlgGrpElem{T, typeof(A)}(A)

function (A::AlgAss{T})(c::Array{T, 1}) where {T}
  length(c) != dim(A) && error("Dimensions don't match.")
  return AlgAssElem{T, AlgAss{T}}(A, c)
end

function Base.getindex(A::AbsAlgAss{T}, i::Int) where {T}
  (i < 1 || i > dim(A)) && error("Index must be in range $(1:dim(A))")
  basis(A)[i]
end

#function (A::AlgGrp{T, S, R})(c::Array{T, 1}) where {T, S, R}
#  length(c) != dim(A) && error("Dimensions don't match.")
#  return AlgGrpElem{T, typeof(A)}(A, c)
#end

function (A::AlgGrp{T, S, R})(c::R) where {T, S, R}
  return AlgGrpElem{T, typeof(A)}(A, c)
end

# Generic.Mat needs it
function (A::AlgAss)(a::AlgAssElem)
  @assert parent(a) == A "Wrong parent"
  return a
end

function (A::AlgGrp)(a::AlgGrpElem)
  @assert parent(a) == A "Wrong parent"
  return a
end

# For polynomial substitution
function (A::AlgAss)(a::Int)
  return a*one(A)
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::AbsAlgAssElem)
  print(io, "Element of ")
  print(io, parent(a))
  print(io, " with coefficients ")
  print(io, a.coeffs)
end

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(a::AbsAlgAssElem{T}, dict::IdDict) where {T}
  b = parent(a)()
  for x in fieldnames(typeof(a))
    if x != :parent && isdefined(a, x)
      setfield!(b, x, Base.deepcopy_internal(getfield(a, x), dict))
    end
  end
  return b
end

################################################################################
#
#  Equality
#
################################################################################

function ==(a::AbsAlgAssElem{T}, b::AbsAlgAssElem{T}) where {T}
  parent(a) != parent(b) && return false
  return a.coeffs == b.coeffs
end

################################################################################
#
#  Minpoly
#
################################################################################

function Generic.minpoly(a::AbsAlgAssElem)
  M = representation_matrix(a)
  R = PolynomialRing(base_ring(parent(a)), "x", cached=false)[1]
  return minpoly(R, M)
end

################################################################################
#
#  Trace
#
################################################################################

#function tr(x::AbsAlgAssElem)
#  return tr(representation_matrix(x))
#end

function tr(x::AbsAlgAssElem{T}) where T
  A=parent(x)
  _assure_trace_basis(A)
  tr=zero(base_ring(A))
  for i=1:dim(A)
    tr = add!(tr, tr, x.coeffs[i]*A.trace_basis_elem[i])
  end
  return tr
end

#function _tr(x::AlgAssElem{T}) where {T}
#  return trace(representation_matrix(x))
#end

################################################################################
#
#  Representation matrix
#
################################################################################

function elem_to_mat_row!(M::MatElem{T}, i::Int, a::AbsAlgAssElem{T}) where T
  for c = 1:ncols(M)
    M[i, c] = deepcopy(a.coeffs[c])
  end
  return nothing
end

function elem_from_mat_row(A::AbsAlgAss{T}, M::MatElem{T}, i::Int) where T
  a = A()
  for c = 1:ncols(M)
    a.coeffs[c] = deepcopy(M[i, c])
  end
  return a
end

function elem_from_mat_row(A::AbsAlgAss, M::fmpz_mat, i::Int, d::fmpz=fmpz(1))
  a = A()
  for j in 1:ncols(M)
    a.coeffs[j] = fmpq(M[i, j], d)
  end
  return a
end

function representation_matrix(a::AlgGrpElem, action::Symbol=:left)
  A = parent(a)
  M = zero_matrix(base_ring(A), dim(A), dim(A))
  if action==:left
    for i = 1:dim(A)
      for j = 1:dim(A)
        M[i, A.mult_table[j, i]] = a.coeffs[j]
      end
    end
  elseif action==:right
    for i = 1:dim(A)
      for j = 1:dim(A)
        M[i, A.mult_table[i, j]] = a.coeffs[j]
      end
    end
  else
    error("Not yet implemented")
  end
  return M
end

function representation_matrix(a::AlgAssElem, action::Symbol=:left)
  A = parent(a)
  M = zero_matrix(base_ring(A), dim(A), dim(A))
  if action==:left
    for i = 1:dim(A)
      if iszero(a.coeffs[i])
        continue
      end
      for j = 1:dim(A)
        for k = 1:dim(A)
          M[j, k] += a.coeffs[i]*A.mult_table[i, j, k]
        end
      end
    end
  elseif action==:right
    for i = 1:dim(A)
      if iszero(a.coeffs[i])
        continue
      end
      for j = 1:dim(A)
        for k = 1:dim(A)
          M[j, k] += a.coeffs[i]*A.mult_table[j, i, k]
        end
      end
    end
  else
    error("Not yet implemented")
  end
  return M
end

################################################################################
#
#  isone/iszero
#
################################################################################

isone(a::AbsAlgAssElem) = a == one(parent(a))

function iszero(a::AbsAlgAssElem)
  return all(i -> iszero(i), a.coeffs)
end

################################################################################
#
#  (Reduced) trace
#
################################################################################

function trred(a::AbsAlgAssElem)
  A = parent(a)
  if issimple_known(A) && A.issimple == 1
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
#  Characteristic polynomial
#
################################################################################


################################################################################
#
#  Field access
#
################################################################################

function coeffs(a::AbsAlgAssElem, copy::Bool = true)
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

function denominator(x::AbsAlgAssElem)
  return lcm([ denominator(y) for y in coeffs(x, false) ])
end
