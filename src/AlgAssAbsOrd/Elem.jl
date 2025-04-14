parent_type(::Type{AlgAssAbsOrdElem{S, T}}) where {S, T} = S

@inline parent(x::AlgAssAbsOrdElem) = x.parent

Base.hash(x::AlgAssAbsOrdElem, h::UInt) = hash(elem_in_algebra(x, copy = false), h)

################################################################################
#
#  Parent object overloading
#
################################################################################

(O::AlgAssAbsOrd)(a::AbstractAssociativeAlgebraElem, check::Bool = true) = begin
  if check
    (x, y) = _check_elem_in_order(a, O)
    !x && error("Algebra element not in the order")
    return AlgAssAbsOrdElem{typeof(O), typeof(a)}(O, deepcopy(a), y)
  else
    return AlgAssAbsOrdElem{typeof(O), typeof(a)}(O, deepcopy(a))
  end
end

(O::AlgAssAbsOrd)(a::AbstractAssociativeAlgebraElem, arr::Vector, check::Bool = false) = begin
  if check
    (x, y) = _check_elem_in_order(a, O)
    (!x || arr != y) && error("Algebra element not in the order")
    return AlgAssAbsOrdElem{typeof(O), typeof(a)}(O, deepcopy(a), y)
  else
    return AlgAssAbsOrdElem{typeof(O), typeof(a)}(O, deepcopy(a), deepcopy(arr))
  end
end

(O::AlgAssAbsOrd{S, T})(arr::Vector{ZZRingElem}) where {S, T} = begin
  M = basis_matrix(O, copy = false)
  N = matrix(ZZ, 1, degree(O), arr)
  NM = N*M
  x = elem_from_mat_row(algebra(O), NM, 1)
  return AlgAssAbsOrdElem{typeof(O), typeof(x)}(O, x, deepcopy(arr))
end

(O::AlgAssAbsOrd{S, T})(a::AlgAssAbsOrdElem, check::Bool = true) where {S, T} = begin
  b = elem_in_algebra(a) # already a copy
  if check
    (x, y) = _check_elem_in_order(b, O)
    !x && error("Algebra element not in the order")
    return AlgAssAbsOrdElem{typeof(O), typeof(b)}(O, b, y)
  else
    return AlgAssAbsOrdElem{typeof(O), typeof(b)}(O, b)
  end
end

(O::AlgAssAbsOrd)(a::T, check::Bool = true) where T = O(algebra(O)(a), check)

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(a::AlgAssAbsOrdElem, dict::IdDict)
  b = parent(a)()
  b.elem_in_algebra = Base.deepcopy_internal(a.elem_in_algebra, dict)
  if a.has_coord
    b.has_coord = true
    b.coordinates = Base.deepcopy_internal(a.coordinates, dict)
  end
  return b
end

################################################################################
#
#  Special elements
#
################################################################################

(O::AlgAssAbsOrd{S, T})() where {S, T} = elem_type(O)(O)

one(O::AlgAssAbsOrd) = O(one(algebra(O)))

zero(O::AlgAssAbsOrd) = O(algebra(O)())

################################################################################
#
#  Element in algebra
#
################################################################################

@doc raw"""
    elem_in_algebra(x::AlgAssAbsOrdElem; copy::Bool = true) -> AbstractAssociativeAlgebraElem
    elem_in_algebra(x::AlgAssRelOrdElem; copy::Bool = true) -> AbstractAssociativeAlgebraElem

Returns $x$ as an element of the algebra containing it.
"""
function elem_in_algebra(x::AlgAssRelOrdElem{S, T, U}; copy::Bool = true) where {S, T, U}
  if copy
    return deepcopy(x.elem_in_algebra)::elem_type(U)
  else
    return x.elem_in_algebra::elem_type(U)
  end
end

function elem_in_algebra(x::AlgAssAbsOrdElem{S, T}; copy::Bool = true) where {S, T}
  if copy
    return deepcopy(x.elem_in_algebra)
  else
    return x.elem_in_algebra
  end
end

_elem_in_algebra(x::Union{ AlgAssAbsOrdElem, AlgAssRelOrdElem }; copy::Bool = true) = elem_in_algebra(x, copy = copy)

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_coord(x::Union{ AlgAssAbsOrdElem, AlgAssRelOrdElem })
  if x.has_coord
    return nothing
  end

  a, b = _check_elem_in_order(elem_in_algebra(x, copy = false), parent(x))
  !a && error("Not a valid order element")
  x.coordinates = b
  x.has_coord = true
  return nothing
end

################################################################################
#
#  Coordinates
#
################################################################################

@doc raw"""
    coordinates(x::AlgAssAbsOrdElem; copy::Bool = true) -> Vector{ZZRingElem}
    coordinates(x::AlgAssRelOrdElem; copy::Bool = true) -> Vector{NumFieldElem}

Returns the coordinates of $x$ in the basis of `parent(x)`.
"""
function coordinates(x::Union{ AlgAssAbsOrdElem, AlgAssRelOrdElem }; copy::Bool = true)
  assure_has_coord(x)
  if copy
    return deepcopy(x.coordinates)::Vector{elem_type(base_ring(parent(x)))}
  else
    return x.coordinates::Vector{elem_type(base_ring(parent(x)))}
  end
end

function coordinates(x::AlgAssRelOrdElem; copy::Bool = true)
  assure_has_coord(x)
  if copy
    return deepcopy(x.coordinates)
  else
    return x.coordinates
  end
end

################################################################################
#
#  Unary operations
#
################################################################################

function -(x::Union{ AlgAssAbsOrdElem, AlgAssRelOrdElem })
  return parent(x)(-elem_in_algebra(x, copy = false))
end

###############################################################################
#
#  Binary operations
#
###############################################################################

function *(x::T, y::T) where { T <: Union{ AlgAssAbsOrdElem, AlgAssRelOrdElem } }
  check_parent(x, y)
  return parent(x)(elem_in_algebra(x, copy = false)*elem_in_algebra(y, copy = false))
end

function +(x::T, y::T) where { T <: Union{ AlgAssAbsOrdElem, AlgAssRelOrdElem } }
  check_parent(x, y)
  z = parent(x)(elem_in_algebra(x, copy = false) + elem_in_algebra(y, copy = false))
  if x.has_coord && y.has_coord
    z.coordinates = [ x.coordinates[i] + y.coordinates[i] for i = 1:degree(parent(x)) ]
    z.has_coord = true
  end
  return z
end

function -(x::T, y::T) where { T <: Union{ AlgAssAbsOrdElem, AlgAssRelOrdElem } }
  check_parent(x, y)
  z = parent(x)(elem_in_algebra(x, copy = false) - elem_in_algebra(y, copy = false))
  if x.has_coord && y.has_coord
    z.coordinates = [ x.coordinates[i] - y.coordinates[i] for i = 1:degree(parent(x)) ]
    z.has_coord = true
  end
  return z
end

function *(n::IntegerUnion, x::AlgAssAbsOrdElem)
  #O=x.parent
  O = parent(x)
  y = O(n * elem_in_algebra(x, copy = false))
  if x.has_coord
    y.coordinates = n .* coordinates(x, copy = false)
    y.has_coord = true
  end
  return y
end

*(x::AlgAssAbsOrdElem, n::IntegerUnion) = n*x

# Computes a/b if action is :right and b\a if action is :left (and if this is possible)
function divexact(a::T, b::T, action::Symbol, check::Bool = true) where { T <: Union{ AlgAssAbsOrdElem, AlgAssRelOrdElem } }
  check_parent(a, b)
  O = parent(a)
  c = divexact(elem_in_algebra(a, copy = false), elem_in_algebra(b, copy = false), action)
  if check
    (x, y) = _check_elem_in_order(c, O)
    !x && error("Quotient not an element of the order")
    return typeof(a)(O, c, y) # Avoid unnecessary copies
  end
  return typeof(a)(O, c)
end

@doc raw"""
    divexact_right(a::AlgAssAbsOrdElem, b::AlgAssAbsOrdElem; check::Bool = true)
    divexact_right(a::AlgAssRelOrdElem, b::AlgAssRelOrdElem; check::Bool = true)
      -> AlgAssRelOrdElem

Returns an element $c \in O$ such that $a = c \cdot b$ where $O$ is the order
containing $a$.
If `check` is `false`, it is not checked whether $c$ is an element of $O$.
"""
divexact_right(a::T, b::T; check::Bool = true) where { T <: Union{ AlgAssAbsOrdElem, AlgAssRelOrdElem } } = divexact(a, b, :right, check)

@doc raw"""
    divexact_left(a::AlgAssAbsOrdElem, b::AlgAssAbsOrdElem; check::Bool = true)
    divexact_left(a::AlgAssRelOrdElem, b::AlgAssRelOrdElem; check::Bool = true)
      -> AlgAssRelOrdElem

Returns an element $c \in O$ such that $a = b \cdot c$ where $O$ is the order
containing $a$.
If `check` is `false`, it is not checked whether $c$ is an element of $O$.
"""
divexact_left(a::T, b::T; check::Bool = true) where { T <: Union{ AlgAssAbsOrdElem, AlgAssRelOrdElem } } = divexact(a, b, :left, check)

################################################################################
#
#  Conversion from matrix
#
################################################################################

function elem_from_mat_row(O::AlgAssAbsOrd, M::ZZMatrix, i::Int)
  return O(ZZRingElem[ M[i, j] for j = 1:degree(O) ])
end

function elem_to_mat_row!(M::ZZMatrix, i::Int, a::AlgAssAbsOrdElem)
  for c = 1:ncols(M)
    M[i, c] = deepcopy(coordinates(a; copy = false))[c]
  end
  return nothing
end

################################################################################
#
#  Exponentiation
#
################################################################################

@doc raw"""
    ^(x::AlgAssAbsOrdElem, y::Union{ Int, ZZRingElem }) -> AlgAssAbsOrdElem
    ^(x::AlgAssRelOrdElem, y::Union{ Int, ZZRingElem }) -> AlgAssRelOrdElem

Returns $x^y$.
"""
function ^(x::Union{ AlgAssAbsOrdElem, AlgAssRelOrdElem }, y::ZZRingElem)
  z = parent(x)()
  z.elem_in_algebra = elem_in_algebra(x, copy = false)^y
  return z
end

function ^(x::Union{ AlgAssAbsOrdElem, AlgAssRelOrdElem }, y::Integer)
  z = parent(x)()
  z.elem_in_algebra = elem_in_algebra(x, copy = false)^y
  return z
end

################################################################################
#
#  Equality
#
################################################################################

@doc raw"""
    ==(a::AlgAssAbsOrdElem, b::AlgAssAbsOrdElem) -> Bool
    ==(a::AlgAssRelOrdElem, b::AlgAssRelOrdElem) -> Bool

Returns `true` if $a$ and $b$ are equal and `false` otherwise.
"""
function ==(a::T, b::T) where { T <: Union{ AlgAssAbsOrdElem, AlgAssRelOrdElem } }
  if parent(a) !== parent(b)
    return false
  end
  return elem_in_algebra(a, copy = false) == elem_in_algebra(b, copy = false)
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function add!(z::T, x::T, y::T) where { T <: Union{ AlgAssAbsOrdElem, AlgAssRelOrdElem } }
  z.elem_in_algebra = add!(elem_in_algebra(z, copy = false), elem_in_algebra(x, copy = false), elem_in_algebra(y, copy = false))
  z.has_coord = false
  return z
end

function mul!(z::T, x::T, y::T) where { T <: Union{ AlgAssAbsOrdElem, AlgAssRelOrdElem } }
  z.elem_in_algebra = mul!(elem_in_algebra(z, copy = false), elem_in_algebra(x, copy = false), elem_in_algebra(y, copy = false))
  z.has_coord = false
  return z
end

function mul!(z::AlgAssAbsOrdElem, x::Union{ Int, ZZRingElem }, y::AlgAssAbsOrdElem)
  z.elem_in_algebra = mul!(elem_in_algebra(z, copy = false), x, elem_in_algebra(y, copy = false))
  if isassigned(z.coordinates, 1) && y.has_coord
    x = ZZRingElem(x)
    coy = coordinates(y, copy = false)
    for i = 1:degree(parent(y))
      z.coordinates[i] = mul!(z.coordinates[i], x, coy[i])
    end
  end
  return z
end

mul!(z::AlgAssAbsOrdElem, y::AlgAssAbsOrdElem, x::Union{ Int, ZZRingElem }) = mul!(z, x, y)

function addmul!(a::AlgAssAbsOrdElem, b::ZZRingElem, c::AlgAssAbsOrdElem, d = parent(a)())
  mul!(d, b, c)
  return add!(a, a, d)
end

function addmul!(a::AbsNumFieldOrderElem, b::ZZRingElem, c::AbsNumFieldOrderElem, d = parent(a)())
  mul!(d, b, c)
  return add!(a, a, d)
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::AlgAssAbsOrdElem)
  print(io, a.elem_in_algebra)
end

################################################################################
#
#  Representation matrices
#
################################################################################

@doc raw"""
    representation_matrix(x::AlgAssAbsOrdElem, action::Symbol = :left) -> ZZMatrix

Returns a matrix representing multiplication with $x$ with respect to the basis
of `order(x)`.
The multiplication is from the left if `action == :left` and from the right if
`action == :right`.
"""
function representation_matrix(x::AlgAssAbsOrdElem, action::Symbol = :left)

  O = parent(x)
  M = basis_matrix(O, copy = false)
  M1 = basis_matrix_inverse(O, copy = false)

  B = representation_matrix(elem_in_algebra(x, copy = false), action)
  B = mul!(B, M, B)
  B = mul!(B, B, M1)

  @assert is_one(denominator(B))
  return numerator(B)
end

function representation_matrix_mod(x::AlgAssAbsOrdElem, d::ZZRingElem, action::Symbol = :left)
  O = parent(x)
  M = basis_matrix(O, copy = false)
  M1 = basis_matrix_inverse(O, copy = false)

  A = representation_matrix(elem_in_algebra(x, copy = false), action)
  d2 = denominator(M) * denominator(M1) * denominator(A)
  d2c, d2nc = ppio(d2, d)
  d1 = d * d2c
  A1 = numerator(A)
  mod!(A1, d1)
  S1 = mod(numerator(M), d1)
  mul!(A1, S1, A1)
  S2 = mod(numerator(M1), d1)
  mul!(A1, A1, S2)
  mod!(A1, d1)
  divexact!(A1, A1, d2c)
  inver = invmod(d2nc, d1)
  mul!(A1, A1, inver)
  mod!(A1, d)
  return A1
end

################################################################################
#
#  Trace
#
################################################################################

@doc raw"""
    tr(x::AlgAssAbsOrdElem) -> ZZRingElem

Returns the trace of $x$.
"""
function tr(x::AlgAssAbsOrdElem)
  return ZZ(tr(x.elem_in_algebra))
end

@doc raw"""
    trred(x::AlgAssAbsOrdElem) -> ZZRingElem

Returns the reduced trace of $x$.
"""
function trred(x::AlgAssAbsOrdElem)
  return ZZ(trred(x.elem_in_algebra))
end

################################################################################
#
#  Modular exponentiation and division
#
################################################################################

function powermod(a::AlgAssAbsOrdElem, i::Union{ZZRingElem, Int}, m::AlgAssAbsOrdIdl)
  if i < 0
    b, a = is_divisible_mod_ideal(one(parent(a)), a, m)
    @assert b "Element is not invertible modulo the ideal"
    return powermod(a, -i, m)
  end

  if i == 0
    return one(parent(a))
  end

  if i == 1
    b = mod(a, m)
    return b
  end

  if mod(i, 2) == 0
    j = div(i, 2)
    b = powermod(a, j, m)
    b = b^2
    b = mod(b, m)
    return b
  end

  b = mod(a*powermod(a, i - 1, m), m)
  return b
end

# This is mostly is_divisible in AbsSimpleNumFieldOrder/residue_ring.jl
function is_divisible_mod_ideal(x::AlgAssAbsOrdElem, y::AlgAssAbsOrdElem, a::AlgAssAbsOrdIdl)

  iszero(y) && error("Dividing by zero")

  if iszero(x)
    return true, zero(parent(x))
  end

  O = parent(x)
  d = degree(O)
  V = zero_matrix(ZZ, 2*d + 1, 2*d + 1)
  V[1, 1] = ZZRingElem(1)

  for i = 1:d
    V[1, 1 + i] = coordinates(x, copy = false)[i]
  end

  A = representation_matrix(y)
  B = integral_basis_matrix_wrt(a, O, copy = false)

  _copy_matrix_into_matrix(V, 2, 2, A)
  _copy_matrix_into_matrix(V, 2 + d, 2, B)

  for i = 1:d
    V[1 + i, d + 1 + i] = 1
  end

  V = hnf(V)

  for i = 2:(d + 1)
    if !iszero(V[1, i])
      return false, O()
    end
  end

  z = -O([ V[1, i] for i = (d + 2):(2*d + 1) ])
  return true, z
end

################################################################################
#
#  isone/iszero
#
################################################################################

iszero(a::AlgAssAbsOrdElem) = iszero(elem_in_algebra(a, copy = false))

isone(a::AlgAssAbsOrdElem) = isone(elem_in_algebra(a, copy = false))
