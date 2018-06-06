################################################################################
#
#  Parent
#
################################################################################

parent(a::AlgAssElem) = a.parent

################################################################################
#
#  Special elements
#
################################################################################

zero(A::AlgAss) = A()

one(A::AlgAss) = A(A.one)

################################################################################
#
#  Unary operations
#
################################################################################

function -(a::AlgAssElem{T}) where {T}
  coeffs = [ -a.coeffs[i] for i = 1:dim(parent(a)) ]
  return AlgAssElem{T}(parent(a), coeffs)
end

################################################################################
#
#  Binary operations
#
################################################################################

function +(a::AlgAssElem{T}, b::AlgAssElem{T}) where {T}
  parent(a) != parent(b) && error("Parents don't match.")
  coeffs = Array{T, 1}(dim(parent(a)))
  for i = 1:dim(parent(a))
    coeffs[i] = a.coeffs[i] + b.coeffs[i]
  end
  return AlgAssElem{T}(parent(a), coeffs)
end

function -(a::AlgAssElem{T}, b::AlgAssElem{T}) where {T}
  parent(a) != parent(b) && error("Parents don't match.")
  coeffs = Array{T, 1}(dim(parent(a)))
  for i = 1:dim(parent(a))
    coeffs[i] = a.coeffs[i] - b.coeffs[i]
  end
  return AlgAssElem{T}(parent(a), coeffs)
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
#  Ad hoc operations
#
################################################################################

function *(a::AlgAssElem{T}, b::T) where { T <: RingElem }
  return AlgAssElem{T}(parent(a), a.coeffs.*b)
end

*(b::T, a::AlgAssElem{T}) where { T <: RingElem } = a*b

*(a::AlgAssElem{T}, b::Union{Integer, fmpz}) where {T} = a*base_ring(parent(a))(b)

*(b::Union{Integer, fmpz}, a::AlgAssElem{T}) where {T} = a*b

dot(a::AlgAssElem{T}, b::T) where {T} = a*b

dot(b::T, a::AlgAssElem{T}) where {T} = b*a

dot(a::AlgAssElem{T}, b::Union{Integer, fmpz}) where {T} = a*b

dot(b::Union{Integer, fmpz}, a::AlgAssElem{T}) where {T} = b*a

################################################################################
#
#  Exponentiation
#
################################################################################

function ^(a::AlgAssElem, b::Int)
  if b == 0
    return one(parent(a))
  elseif b == 1
    return deepcopy(a)
  else
    if b < 0
      error("Not implemented yet")
      #a = inv(a)
      #b = -b
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

function ^(a::AlgAssElem, b::fmpz)
  if nbits(b) < 64
    return a^Int(b)
  end
  if b < 0
    error("Not implemented yet")
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

(A::AlgAss{T})() where {T} = AlgAssElem{T}(A)

function (A::AlgAss{T})(c::Array{T, 1}) where {T}
  length(c) != dim(A) && error("Dimensions don't match.")
  return AlgAssElem{T}(A, c)
end

function Base.getindex(A::AlgAss{T}, i::Int) where {T}
  (i < 1 || i > dim(A)) && error("Index must be in range $(1:dim(A))")
  n = dim(A)
  v = Vector{T}(n)
  for j in 1:n
    v[j] = zero(base_ring(A))
  end
  v[i] = one(base_ring(A))
  return A(v)
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::AlgAssElem)
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

function Base.deepcopy_internal(a::AlgAssElem{T}, dict::ObjectIdDict) where {T}
  b = parent(a)()
  for x in fieldnames(a)
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

function ==(a::AlgAssElem{T}, b::AlgAssElem{T}) where {T}
  parent(a) != parent(b) && return false
  return a.coeffs == b.coeffs
end

################################################################################
#
#  Minpoly
#
################################################################################

function Generic.minpoly(a::AlgAssElem)
  M = representation_matrix(a)
  R = PolynomialRing(base_ring(parent(a)), "x", cached=false)[1]
  return minpoly(R, M)
end

################################################################################
#
#  Trace
#
################################################################################

function trace(x::AlgAssElem{T}) where T
  A=parent(x)
  _assure_trace_basis(A)
  tr=zero(base_ring(A))
  for i=1:dim(A)
    add!(tr, tr, x.coeffs[i]*A.trace_basis_elem[i]) 
  end
  return tr 
end

################################################################################
#
#  Representation matrix
#
################################################################################

function elem_to_mat_row!(M::MatElem{T}, i::Int, a::AlgAssElem{T}) where T
  for c = 1:cols(M)
    M[i, c] = deepcopy(a.coeffs[c])
  end
  return nothing
end

function elem_from_mat_row(A::AlgAss{T}, M::MatElem{T}, i::Int) where T
  a = A()
  for c = 1:cols(M)
    a.coeffs[c] = deepcopy(M[i, c])
  end
  return a
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

isone(a::AlgAssElem) = a == one(parent(a))

iszero(a::AlgAssElem) = all(i -> i == 0, a.coeffs)
