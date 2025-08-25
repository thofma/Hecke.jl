parent_type(::Type{AssociativeAlgebraOrderElem{S, T}}) where {S, T} = S

@inline parent(x::AssociativeAlgebraOrderElem) = x.parent

Base.hash(x::AssociativeAlgebraOrderElem, h::UInt) = hash(elem_in_algebra(x, copy = false), h)

################################################################################
#
#  Parent object overloading
#
################################################################################

(O::AssociativeAlgebraOrderElem)(a::AbstractAssociativeAlgebraElem, check::Bool = true) = begin
  if check
    (x, y) = _check_elem_in_order(a, O)
    !x && error("Algebra element not in the order")
    return AssociativeAlgebraOrderElem{typeof(O), typeof(a)}(O, deepcopy(a), y)
  else
    return AssociativeAlgebraOrderElem{typeof(O), typeof(a)}(O, deepcopy(a))
  end
end

(O::AssociativeAlgebraOrderElem)(a::AbstractAssociativeAlgebraElem, arr::Vector, check::Bool = false) = begin
  if check
    (x, y) = _check_elem_in_order(a, O)
    (!x || arr != y) && error("Algebra element not in the order")
    return AssociativeAlgebraOrderElem{typeof(O), typeof(a)}(O, deepcopy(a), y)
  else
    return AssociativeAlgebraOrderElem{typeof(O), typeof(a)}(O, deepcopy(a), deepcopy(arr))
  end
end

(O::AssociativeAlgebraOrderElem{S, T})(arr::Vector{ZZRingElem}) where {S, T} = begin
  M = basis_matrix(O, copy = false)
  N = matrix(ZZ, 1, degree(O), arr)
  NM = N*M
  x = elem_from_mat_row(algebra(O), NM, 1)
  return AssociativeAlgebraOrderElem{typeof(O), typeof(x)}(O, x, deepcopy(arr))
end

(O::AssociativeAlgebraOrderElem{S, T})(a::AssociativeAlgebraOrderElem, check::Bool = true) where {S, T} = begin
  b = elem_in_algebra(a) # already a copy
  if check
    (x, y) = _check_elem_in_order(b, O)
    !x && error("Algebra element not in the order")
    return AssociativeAlgebraOrderElem{typeof(O), typeof(b)}(O, b, y)
  else
    return AssociativeAlgebraOrderElem{typeof(O), typeof(b)}(O, b)
  end
end

(O::AssociativeAlgebraOrderElem)(a::T, check::Bool = true) where T = O(algebra(O)(a), check)

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(a::AssociativeAlgebraOrderElem, dict::IdDict)
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

(O::AssociativeAlgebraOrderElem{S, T})() where {S, T} = elem_type(O)(O)

one(O::AssociativeAlgebraOrderElem) = O(one(algebra(O)))

zero(O::AssociativeAlgebraOrderElem) = O(algebra(O)())

################################################################################
#
#  Element in algebra
#
################################################################################

#@doc raw"""
#    elem_in_algebra(x::AssociativeAlgebraOrderElem; copy::Bool = true) -> AbstractAssociativeAlgebraElem
#    elem_in_algebra(x::AlgAssRelOrdElem; copy::Bool = true) -> AbstractAssociativeAlgebraElem
#
#Returns $x$ as an element of the algebra containing it.
#"""
#function elem_in_algebra(x::AlgAssRelOrdElem{S, T, U}; copy::Bool = true) where {S, T, U}
#  if copy
#    return deepcopy(x.elem_in_algebra)::elem_type(U)
#  else
#    return x.elem_in_algebra::elem_type(U)
#  end
#end

function elem_in_algebra(x::AssociativeAlgebraOrderElem{S, T}; copy::Bool = true) where {S, T}
  if copy
    return deepcopy(x.elem_in_algebra)
  else
    return x.elem_in_algebra
  end
end

_elem_in_algebra(x::Union{ AssociativeAlgebraOrderElem, AlgAssRelOrdElem }; copy::Bool = true) = elem_in_algebra(x, copy = copy)

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_coord(x::Union{ AssociativeAlgebraOrderElem, AlgAssRelOrdElem })
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
    coordinates(x::AssociativeAlgebraOrderElem; copy::Bool = true) -> Vector{ZZRingElem}
    coordinates(x::AlgAssRelOrdElem; copy::Bool = true) -> Vector{NumFieldElem}

Returns the coordinates of $x$ in the basis of `parent(x)`.
"""
function coordinates(x::AssociativeAlgebraOrderElem; copy::Bool = true)
  assure_has_coord(x)
  if copy
    return deepcopy(x.coordinates)::Vector{elem_type(base_ring(parent(x)))}
  else
    return x.coordinates::Vector{elem_type(base_ring(parent(x)))}
  end
end

################################################################################
#
#  Unary operations
#
################################################################################

function -(x::Union{ AssociativeAlgebraOrderElem, AlgAssRelOrdElem })
  return parent(x)(-elem_in_algebra(x, copy = false), false)
end

###############################################################################
#
#  Binary operations
#
###############################################################################

function *(x::T, y::T) where { T <: Union{ AssociativeAlgebraOrderElem, AlgAssRelOrdElem } }
  check_parent(x, y)
  return parent(x)(elem_in_algebra(x, copy = false)*elem_in_algebra(y, copy = false), false)
end

function +(x::T, y::T) where { T <: Union{ AssociativeAlgebraOrderElem, AlgAssRelOrdElem } }
  check_parent(x, y)
  z = parent(x)(elem_in_algebra(x, copy = false) + elem_in_algebra(y, copy = false), false)
  if x.has_coord && y.has_coord
    z.coordinates = [ x.coordinates[i] + y.coordinates[i] for i = 1:degree(parent(x)) ]
    z.has_coord = true
  end
  return z
end

function -(x::T, y::T) where { T <: Union{ AssociativeAlgebraOrderElem, AlgAssRelOrdElem } }
  check_parent(x, y)
  z = parent(x)(elem_in_algebra(x, copy = false) - elem_in_algebra(y, copy = false), false)
  if x.has_coord && y.has_coord
    z.coordinates = [ x.coordinates[i] - y.coordinates[i] for i = 1:degree(parent(x)) ]
    z.has_coord = true
  end
  return z
end

function *(n::IntegerUnion, x::AssociativeAlgebraOrderElem)
  #O=x.parent
  O = parent(x)
  y = O(n * elem_in_algebra(x, copy = false), false)
  if x.has_coord
    y.coordinates = n .* coordinates(x, copy = false)
    y.has_coord = true
  end
  return y
end

*(x::AssociativeAlgebraOrderElem, n::IntegerUnion) = n*x

# Computes a/b if action is :right and b\a if action is :left (and if this is possible)
function divexact(a::T, b::T, action::Symbol, check::Bool = true) where { T <: Union{ AssociativeAlgebraOrderElem, AlgAssRelOrdElem } }
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
    divexact_right(a::AssociativeAlgebraOrderElem, b::AssociativeAlgebraOrderElem; check::Bool = true)
    divexact_right(a::AlgAssRelOrdElem, b::AlgAssRelOrdElem; check::Bool = true)
      -> AlgAssRelOrdElem

Returns an element $c \in O$ such that $a = c \cdot b$ where $O$ is the order
containing $a$.
If `check` is `false`, it is not checked whether $c$ is an element of $O$.
"""
divexact_right(a::T, b::T; check::Bool = true) where { T <: Union{ AssociativeAlgebraOrderElem, AlgAssRelOrdElem } } = divexact(a, b, :right, check)

@doc raw"""
    divexact_left(a::AssociativeAlgebraOrderElem, b::AssociativeAlgebraOrderElem; check::Bool = true)
    divexact_left(a::AlgAssRelOrdElem, b::AlgAssRelOrdElem; check::Bool = true)
      -> AlgAssRelOrdElem

Returns an element $c \in O$ such that $a = b \cdot c$ where $O$ is the order
containing $a$.
If `check` is `false`, it is not checked whether $c$ is an element of $O$.
"""
divexact_left(a::T, b::T; check::Bool = true) where { T <: Union{ AssociativeAlgebraOrderElem, AlgAssRelOrdElem } } = divexact(a, b, :left, check)

################################################################################
#
#  Conversion from matrix
#
################################################################################

function elem_from_mat_row(O::AssociativeAlgebraOrderElem, M::ZZMatrix, i::Int)
  return O(ZZRingElem[ M[i, j] for j = 1:degree(O) ])
end

function elem_to_mat_row!(M::ZZMatrix, i::Int, a::AssociativeAlgebraOrderElem)
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
    ^(x::AssociativeAlgebraOrderElem, y::Union{ Int, ZZRingElem }) -> AssociativeAlgebraOrderElem
    ^(x::AlgAssRelOrdElem, y::Union{ Int, ZZRingElem }) -> AlgAssRelOrdElem

Returns $x^y$.
"""
function ^(x::Union{ AssociativeAlgebraOrderElem, AlgAssRelOrdElem }, y::ZZRingElem)
  z = parent(x)()
  z.elem_in_algebra = elem_in_algebra(x, copy = false)^y
  return z
end

function ^(x::Union{ AssociativeAlgebraOrderElem, AlgAssRelOrdElem }, y::Integer)
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
    ==(a::AssociativeAlgebraOrderElem, b::AssociativeAlgebraOrderElem) -> Bool
    ==(a::AlgAssRelOrdElem, b::AlgAssRelOrdElem) -> Bool

Returns `true` if $a$ and $b$ are equal and `false` otherwise.
"""
function ==(a::T, b::T) where { T <: Union{ AssociativeAlgebraOrderElem, AlgAssRelOrdElem } }
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

function add!(z::T, x::T, y::T) where { T <: Union{ AssociativeAlgebraOrderElem, AlgAssRelOrdElem } }
  z.elem_in_algebra = add!(elem_in_algebra(z, copy = false), elem_in_algebra(x, copy = false), elem_in_algebra(y, copy = false))
  z.has_coord = false
  return z
end

function mul!(z::T, x::T, y::T) where { T <: Union{ AssociativeAlgebraOrderElem, AlgAssRelOrdElem } }
  z.elem_in_algebra = mul!(elem_in_algebra(z, copy = false), elem_in_algebra(x, copy = false), elem_in_algebra(y, copy = false))
  z.has_coord = false
  return z
end

function mul!(z::AssociativeAlgebraOrderElem, x::Union{ Int, ZZRingElem }, y::AssociativeAlgebraOrderElem)
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

mul!(z::AssociativeAlgebraOrderElem, y::AssociativeAlgebraOrderElem, x::Union{ Int, ZZRingElem }) = mul!(z, x, y)

function addmul!(a::AssociativeAlgebraOrderElem, b::ZZRingElem, c::AssociativeAlgebraOrderElem, d = parent(a)())
  mul!(d, b, c)
  return add!(a, a, d)
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::AssociativeAlgebraOrderElem)
  print(io, a.elem_in_algebra)
end

################################################################################
#
#  Representation matrices
#
################################################################################

@doc raw"""
    representation_matrix(x::AssociativeAlgebraOrderElem, action::Symbol = :left) -> ZZMatrix

Returns a matrix representing multiplication with $x$ with respect to the basis
of `order(x)`.
The multiplication is from the left if `action == :left` and from the right if
`action == :right`.
"""
function representation_matrix(x::AssociativeAlgebraOrderElem, action::Symbol = :left)

  O = parent(x)
  M = basis_matrix(O, copy = false)
  M1 = basis_matrix_inverse(O, copy = false)

  B = representation_matrix(elem_in_algebra(x, copy = false), action)
  B = mul!(B, M, B)
  B = mul!(B, B, M1)

  @assert is_one(denominator(B))
  return numerator(B)
end

function representation_matrix_mod(x::AssociativeAlgebraOrderElem, d::ZZRingElem, action::Symbol = :left)
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
    tr(x::AssociativeAlgebraOrderElem) -> ZZRingElem

Returns the trace of $x$.
"""
function tr(x::AssociativeAlgebraOrderElem)
  return ZZ(tr(x.elem_in_algebra))
end

@doc raw"""
    trred(x::AssociativeAlgebraOrderElem) -> ZZRingElem

Returns the reduced trace of $x$.
"""
function trred(x::AssociativeAlgebraOrderElem)
  return ZZ(trred(x.elem_in_algebra))
end

################################################################################
#
#  Modular exponentiation and division
#
################################################################################

function powermod(a::AssociativeAlgebraOrderElem, i::Union{ZZRingElem, Int}, m::AssociativeAlgebraLattice)
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
function is_divisible_mod_ideal(x::AssociativeAlgebraOrderElem, y::AssociativeAlgebraOrderElem, a::AssociativeAlgebraLattice)

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

iszero(a::AssociativeAlgebraOrderElem) = iszero(elem_in_algebra(a, copy = false))

isone(a::AssociativeAlgebraOrderElem) = isone(elem_in_algebra(a, copy = false))
