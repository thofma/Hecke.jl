parent_type(::Type{AssociativeAlgebraOrderElem{S, T}}) where {S, T} = S

is_exact_type(::Type{<:AssociativeAlgebraOrderElem}) = true

is_domain_type(::Type{<:AssociativeAlgebraOrderElem}) = false

@inline parent(x::AssociativeAlgebraOrderElem) = x.parent

Base.hash(x::AssociativeAlgebraOrderElem, h::UInt) = hash(elem_in_algebra(x, copy = false), h)

################################################################################
#
#  Parent object overloading
#
################################################################################

function (O::AssociativeAlgebraOrder)(a::AbstractAssociativeAlgebraElem; check::Bool = true)
  if check
    (x, y) = _check_elem_in_order(a, O)
    !x && error("Algebra element not in the order")
    z = AssociativeAlgebraOrderElem(O)
    z.elem_in_algebra = deepcopy(a)
    z.elem_in_module = _element_from_coordinates_and_ambient_coordinates(_underlying_module(O), y, coefficients(a; copy = false); check = false)
  else
    z = AssociativeAlgebraOrderElem(O)
    z.elem_in_algebra  = deepcopy(a)
  end
  return z
end

function (O::AssociativeAlgebraOrder)(arr::Vector)
  return O(_element_from_coordinates(_underlying_module(O), arr))
end

function (O::AssociativeAlgebraOrder)(m::EmbeddedModuleElem; check::Bool = true)
  @assert parent(m) === _underlying_module(O)
  z = AssociativeAlgebraOrderElem(O)
  z.elem_in_module = m
  return z
end

#(O::AssociativeAlgebraOrder)(a::AbstractAssociativeAlgebraElem, arr::Vector; check::Bool = false) = begin
#  if check
#    (x, y) = _check_elem_in_order(a, O)
#    (!x || arr != y) && error("Algebra element not in the order")
#    return AssociativeAlgebraOrderElem(O, deepcopy(a), y)
#  else
#    return AssociativeAlgebraOrderElem(O, deepcopy(a), deepcopy(arr))
#  end
#end

#(O::AssociativeAlgebraOrder{S, T})(arr::Vector{ZZRingElem}) where {S, T} = begin
#  M = basis_matrix(O, copy = false)
#  N = matrix(ZZ, 1, degree(O), arr)
#  NM = N*M
#  x = elem_from_mat_row(algebra(O), NM, 1)
#  return AssociativeAlgebraOrderElem(O, x, deepcopy(arr))
#end
#
#(O::AssociativeAlgebraOrder{S, T})(a::AssociativeAlgebraOrderElem; check::Bool = true) where {S, T} = begin
#  b = elem_in_algebra(a) # already a copy
#  if check
#    (x, y) = _check_elem_in_order(b, O)
#    !x && error("Algebra element not in the order")
#    return AssociativeAlgebraOrderElem(O, b, y)
#  else
#    return AssociativeAlgebraOrderElem(O, b)
#  end
#end
#
#(O::AssociativeAlgebraOrder)(a::T; check::Bool = true) where T = O(algebra(O)(a); check)

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

(O::AssociativeAlgebraOrder{S, T})() where {S, T} = zero(O)

one(O::AssociativeAlgebraOrder) = O(one(algebra(O)); check = false)

zero(O::AssociativeAlgebraOrder) = O(zero(algebra(O)); check = false)

is_unit(a::AssociativeAlgebraOrderElem) = !is_zero(a) && (inv(elem_in_algebra(a; copy = false)) in parent(a))

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
  if !isdefined(x, :elem_in_algebra)
    x.elem_in_algebra = algebra(parent(x))(ambient_coordinates(elem_in_module(x)))
  end
  if copy
    return deepcopy(x.elem_in_algebra)
  else
    return x.elem_in_algebra
  end
end

_elem_in_algebra(x::AssociativeAlgebraOrderElem; copy::Bool = true) = elem_in_algebra(x, copy = copy)

function elem_in_module(x::AssociativeAlgebraOrderElem)
  O = parent(x)
  if isdefined(x, :elem_in_module)
    return x.elem_in_module::elem_type(_underlying_module(O))
  end
  @assert isdefined(x, :elem_in_algebra)
  m = _element_from_ambient_coordinates(_underlying_module(O), coefficients(elem_in_algebra(x); copy = false))
  x.elem_in_module = m
  return m
end

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_coord(x::AssociativeAlgebraOrderElem)
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
  return coordinates(elem_in_module(x); copy)
end

################################################################################
#
#  Unary operations
#
################################################################################

function -(x::AssociativeAlgebraOrderElem)
  return parent(x)(-elem_in_algebra(x, copy = false); check = false)
end

###############################################################################
#
#  Binary operations
#
###############################################################################

function *(x::AssociativeAlgebraOrderElem, y::AssociativeAlgebraOrderElem)
  check_parent(x, y)
  return parent(x)(elem_in_algebra(x, copy = false) * elem_in_algebra(y, copy = false); check = false)
end

function +(x::AssociativeAlgebraOrderElem, y::AssociativeAlgebraOrderElem)
  check_parent(x, y)
  z = parent(x)(elem_in_algebra(x, copy = false) + elem_in_algebra(y, copy = false); check = false)
  if x.has_coord && y.has_coord
    z.coordinates = [x.coordinates[i] + y.coordinates[i] for i in 1:degree(parent(x))]
    z.has_coord = true
  end
  return z
end

function -(x::AssociativeAlgebraOrderElem, y::AssociativeAlgebraOrderElem)
  check_parent(x, y)
  z = parent(x)(elem_in_algebra(x, copy = false) - elem_in_algebra(y, copy = false); check = false)
  if x.has_coord && y.has_coord
    z.coordinates = [ x.coordinates[i] - y.coordinates[i] for i = 1:degree(parent(x)) ]
    z.has_coord = true
  end
  return z
end

function *(n::IntegerUnion, x::AssociativeAlgebraOrderElem)
  #O=x.parent
  O = parent(x)
  y = O(n * elem_in_algebra(x, copy = false); check = false)
  if x.has_coord
    y.coordinates = n .* coordinates(x, copy = false)
    y.has_coord = true
  end
  return y
end

*(x::AssociativeAlgebraOrderElem, n::IntegerUnion) = n*x

# Computes a/b if action is :right and b\a if action is :left (and if this is possible)
function divexact(a::AssociativeAlgebraOrderElem, b::AssociativeAlgebraOrderElem, action::Symbol, check::Bool = true)
  check_parent(a, b)
  O = parent(a)
  c = divexact(elem_in_algebra(a, copy = false), elem_in_algebra(b, copy = false), action)
  if check
    (x, y) = _check_elem_in_order(c, O)
    !x && error("Quotient not an element of the order")
    return AssociativeAlgebraOrderElem(O, c, y) # Avoid unnecessary copies
  end
  return O(c; check = false)
end

@doc raw"""
    divexact_right(a::AssociativeAlgebraOrderElem, b::AssociativeAlgebraOrderElem; check::Bool = true)
    divexact_right(a::AlgAssRelOrdElem, b::AlgAssRelOrdElem; check::Bool = true)
      -> AlgAssRelOrdElem

Returns an element $c \in O$ such that $a = c \cdot b$ where $O$ is the order
containing $a$.
If `check` is `false`, it is not checked whether $c$ is an element of $O$.
"""
divexact_right(a::AssociativeAlgebraOrderElem, b::AssociativeAlgebraOrderElem; check::Bool = true) = divexact(a, b, :right, check)

@doc raw"""
    divexact_left(a::AssociativeAlgebraOrderElem, b::AssociativeAlgebraOrderElem; check::Bool = true)
    divexact_left(a::AlgAssRelOrdElem, b::AlgAssRelOrdElem; check::Bool = true)
      -> AlgAssRelOrdElem

Returns an element $c \in O$ such that $a = b \cdot c$ where $O$ is the order
containing $a$.
If `check` is `false`, it is not checked whether $c$ is an element of $O$.
"""
divexact_left(a::AssociativeAlgebraOrderElem, b::AssociativeAlgebraOrderElem; check::Bool = true) = divexact(a, b, :left, check)

################################################################################
#
#  Conversion from matrix
#
################################################################################

function elem_from_mat_row(O::AssociativeAlgebraOrderElem, M::ZZMatrix, i::Int)
  return O(M[i, :])
end

function elem_to_mat_row!(M::ZZMatrix, i::Int, a::AssociativeAlgebraOrderElem)
  for c = 1:ncols(M)
    M[i, c] = coordinates(a; copy = false)[c]
  end
  return nothing
end

################################################################################
#
#  Exponentiation
#
################################################################################

function ^(x::AssociativeAlgebraOrderElem, y::IntegerUnion)
  prent(z)(elem_in_algebra(x, copy = false)^y; check = false)
end

################################################################################
#
#  Equality
#
################################################################################

function ==(a::AssociativeAlgebraOrderElem, b::AssociativeAlgebraOrderElem)
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

function add!(z::AssociativeAlgebraOrderElem, x::AssociativeAlgebraOrderElem, y::AssociativeAlgebraOrderElem)
  z.elem_in_algebra = add!(elem_in_algebra(z, copy = false), elem_in_algebra(x, copy = false), elem_in_algebra(y, copy = false))
  z.has_coord = false
  return z
end

function mul!(z::AssociativeAlgebraOrderElem, x::AssociativeAlgebraOrderElem, y::AssociativeAlgebraOrderElem)
  z.elem_in_algebra = mul!(elem_in_algebra(z, copy = false), elem_in_algebra(x, copy = false), elem_in_algebra(y, copy = false))
  z.has_coord = false
  return z
end

function mul!(z::AssociativeAlgebraOrderElem, x::IntegerUnion, y::AssociativeAlgebraOrderElem)
  z.elem_in_algebra = mul!(elem_in_algebra(z, copy = false), x, elem_in_algebra(y, copy = false))
  if isdefined(z, :coordinates) && y.has_coord
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
  print(io, elem_in_algebra(a)) # TODO: adjust to use coordinates if available
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
  return _preimage(rationalmap(_module(O)), B)
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

###############################################################################
#
#  Norm and trace
#
###############################################################################

function norm(a::AssociativeAlgebraOrderElem)
  n = norm(elem_in_algebra(a; copy = false))
  return _preimage(fraction_map(_module(parent(a))), n)
end

function trace(a::AssociativeAlgebraOrderElem)
  n = trace(elem_in_algebra(a; copy = false))
  return _preimage(fraction_map(_module(parent(a))), n)
end

function trred(a::AssociativeAlgebraOrderElem)
  n = ttred(elem_in_algebra(a; copy = false))
  return _preimage(fraction_map(_module(parent(a))), n)
end

###############################################################################
#
#   Conformance test element generation
#
###############################################################################

function ConformanceTests.generate_element(O::AssociativeAlgebraOrder)
  B = basis(O)
  return sum(rand(-10:10) * B[i] for i in 1:degree(O))
end
