parent_type(::Type{AlgAssAbsOrdElem{S, T}}) where {S, T} = AlgAssAbsOrd{S, T}

parent_type(::AlgAssAbsOrdElem{S, T}) where {S, T} = AlgAssAbsOrd{S, T}

@inline parent(x::AlgAssAbsOrdElem) = x.parent

################################################################################
#
#  Parent check
#
################################################################################

function check_parent(x::AlgAssAbsOrdElem{S, T}, y::AlgAssAbsOrdElem{S, T}) where {S, T}
  return parent(x) === parent(y)
end

################################################################################
#
#  Parent object overloading
#
################################################################################

(O::AlgAssAbsOrd{S, T})(a::T, check::Bool = true) where {S, T} = begin
  if check
    (x, y) = _check_elem_in_order(a, O)
    !x && error("Algebra element not in the order")
    return AlgAssAbsOrdElem{S, T}(O, deepcopy(a), y)
  else
    return AlgAssAbsOrdElem{S, T}(O, deepcopy(a))
  end
end

(O::AlgAssAbsOrd{S, T})(a::T, arr::Vector{fmpz}, check::Bool = false) where {S, T} = begin
  if check
    (x, y) = _check_elem_in_order(a, O)
    (!x || arr != y) && error("Algebra element not in the order")
    return AlgAssAbsOrdElem{S, T}(O, deepcopy(a), y)
  else
    return AlgAssAbsOrdElem{S, T}(O, deepcopy(a), deepcopy(arr))
  end
end

(O::AlgAssAbsOrd{S, T})(arr::Vector{fmpz}) where {S, T} = begin
  return AlgAssAbsOrdElem{S, T}(O, deepcopy(arr))
end

(O::AlgAssAbsOrd{S, T})(a::AlgAssAbsOrdElem{S, T}, check::Bool = true) where {S, T} =begin
  b = elem_in_algebra(a) # already a copy
  if check
    (x, y) = _check_elem_in_order(b, O)
    !x && error("Algebra element not in the order")
    return AlgAssAbsOrdElem{S, T}(O, b, y)
  else
    return AlgAssAbsOrdElem{S, T}(O, b)
  end
end

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(a::AlgAssAbsOrdElem, dict::IdDict)
  b = parent(a)()
  b.elem_in_algebra = Base.deepcopy_internal(a.elem_in_algebra, dict)
  if isdefined(a, :elem_in_basis)
    b.elem_in_basis = Base.deepcopy_internal(a.elem_in_basis, dict)
  end
  return b
end

################################################################################
#
#  Special elements
#
################################################################################

(O::AlgAssAbsOrd{S, T})() where {S, T} = AlgAssAbsOrdElem{S, T}(O)

one(O::AlgAssAbsOrd) = O(one(algebra(O)))

zero(O::AlgAssAbsOrd) = O(algebra(O)())

################################################################################
#
#  Element in algebra
#
################################################################################

function elem_in_algebra(x::AlgAssAbsOrdElem, copy::Type{Val{T}} = Val{true}) where T
  if copy == Val{true}
    return deepcopy(x.elem_in_algebra)
  else
    return x.elem_in_algebra
  end
end

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_coord(x::AlgAssAbsOrdElem)
  if x.has_coord
    return nothing
  end
  a, b = _check_elem_in_order(elem_in_algebra(x, Val{false}), parent(x))
  !a && error("Not a valid order element")
  x.elem_in_basis = b
  return nothing
end

function assure_elem_in_algebra(x::AlgAssAbsOrdElem)
  if !isdefined(x, :elem_in_algebra)
    O = parent(x)
    x.elem_in_algebra = dot(O.basis_alg, x.elem_in_basis)
  end
  return nothing
end

################################################################################
#
#  Coordinates
#
################################################################################

function elem_in_basis(x::AlgAssAbsOrdElem, copy::Type{Val{T}} = Val{true}) where T
  assure_has_coord(x)
  if copy == Val{true}
    return deepcopy(x.elem_in_basis)
  else
    return x.elem_in_basis
  end
end

################################################################################
#
#  Unary operations
#
################################################################################

function -(x::AlgAssAbsOrdElem)
  return parent(x)(-elem_in_algebra(x, Val{false}))
end

###############################################################################
#
#  Binary operations
#
###############################################################################

function *(x::AlgAssAbsOrdElem, y::AlgAssAbsOrdElem)
  !check_parent(x, y) && error("Wrong parents")
  return parent(x)(elem_in_algebra(x, Val{false})*elem_in_algebra(y, Val{false}))
end

function +(x::AlgAssAbsOrdElem, y::AlgAssAbsOrdElem)
  !check_parent(x, y) && error("Wrong parents")
  z = parent(x)(elem_in_algebra(x, Val{false}) + elem_in_algebra(y, Val{false}))
  if x.has_coord && y.has_coord
    z.elem_in_basis = [ x.elem_in_basis[i] + y.elem_in_basis[i] for i = 1:degree(parent(x)) ]
    z.has_coord = true
  end
  return z
end

function -(x::AlgAssAbsOrdElem, y::AlgAssAbsOrdElem)
  !check_parent(x, y) && error("Wrong parents")
  z = parent(x)(elem_in_algebra(x, Val{false}) - elem_in_algebra(y, Val{false}))
  if x.has_coord && y.has_coord
    z.elem_in_basis = [ x.elem_in_basis[i] - y.elem_in_basis[i] for i = 1:degree(parent(x)) ]
    z.has_coord = true
  end
  return z
end

function *(n::Union{Integer, fmpz}, x::AlgAssAbsOrdElem)
  O=x.parent
  y=Array{fmpz,1}(undef, O.dim)
  z=elem_in_basis(x, Val{false})
  for i=1:O.dim
    y[i] = z[i] * n
  end
  return O(y)
end

# Computes a/b if action is :right and b\a if action is :left (and if this is possible)
function divexact(a::AlgAssAbsOrdElem, b::AlgAssAbsOrdElem, action::Symbol, check::Bool = true)
  !check_parent(a, b) && error("Wrong parents")
  O = parent(a)
  c = divexact(elem_in_algebra(a, Val{false}), elem_in_algebra(b, Val{false}), action)
  if check
    (x, y) = _check_elem_in_order(c, O)
    !x && error("Quotient not an element of the order")
    return typeof(a)(O, c, y) # Avoid unneccessary copies
  end
  return typeof(a)(O, c)
end

divexact_right(a::AlgAssAbsOrdElem, b::AlgAssAbsOrdElem, check::Bool = true) = divexact(a, b, :right, check)

divexact_left(a::AlgAssAbsOrdElem, b::AlgAssAbsOrdElem, check::Bool = true) = divexact(a, b, :left, check)

################################################################################
#
#  Conversion from matrix
#
################################################################################

function elem_from_mat_row(O::AlgAssAbsOrd, M::fmpz_mat, i::Int)
  return O(fmpz[ deepcopy(M[i, j]) for j = 1:degree(O) ])
end

function elem_to_mat_row!(M::fmpz_mat, i::Int, a::AlgAssAbsOrdElem)
  for c = 1:ncols(M)
    M[i, c] = elem_in_basis(a)[c]
  end
  return nothing
end

################################################################################
#
#  Exponentiation
#
################################################################################

function ^(x::AlgAssAbsOrdElem, y::Union{fmpz, Int})
  z = parent(x)()
  z.elem_in_algebra = elem_in_algebra(x, Val{false})^y
  return z
end

################################################################################
#
#  Equality
#
################################################################################

function ==(a::AlgAssAbsOrdElem, b::AlgAssAbsOrdElem)
  if parent(a) != parent(b)
    return false
  end
  return elem_in_algebra(a, Val{false}) == elem_in_algebra(b, Val{false})
end

################################################################################
#
#  Unsafe operations
#
################################################################################

function mul!(z::AlgAssAbsOrdElem, x::AlgAssAbsOrdElem, y::AlgAssAbsOrdElem)
  z.elem_in_algebra = mul!(elem_in_algebra(z, Val{false}), elem_in_algebra(x, Val{false}), elem_in_algebra(y, Val{false}))
  z.has_coord = false
  return z
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

function representation_matrix(x::AlgAssAbsOrdElem)

  O = parent(x)
  M = O.basis_mat
  if isdefined(O, :basis_mat_inv)
    M1 = O.basis_mat_inv
  else
    M1 = inv(O.basis_mat)
    O.basis_mat_inv = M1
  end
  assure_elem_in_algebra(x)
  B = FakeFmpqMat(representation_matrix(x.elem_in_algebra))
  mul!(B, M, B)
  mul!(B, B, M1)

  @assert B.den==1
  return B.num
end

################################################################################
#
#  Trace
#
################################################################################

function tr(x::AlgAssAbsOrdElem)
  return FlintZZ(tr(x.elem_in_algebra))
end

function trred(x::AlgAssAbsOrdElem)
  return FlintZZ(trred(x.elem_in_algebra))
end

################################################################################
#
#  Modular exponentiation and division
#
################################################################################

function powermod(a::AlgAssAbsOrdElem, i::Union{fmpz, Int}, m::AlgAssAbsOrdIdl)
  if i < 0
    b, a = isdivisible_mod_ideal(one(parent(a)), a, m)
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

# This is mostly isdivisible in NfOrd/ResidueRing.jl
function isdivisible_mod_ideal(x::AlgAssAbsOrdElem, y::AlgAssAbsOrdElem, a::AlgAssAbsOrdIdl)

  iszero(y) && error("Dividing by zero")

  if iszero(x)
    return true, zero(parent(x))
  end

  O = parent(x)
  d = degree(O)
  V = zero_matrix(FlintZZ, 2*d + 1, 2*d + 1)
  V[1, 1] = fmpz(1)

  for i = 1:d
    V[1, 1 + i] = elem_in_basis(x, Val{false})[i]
  end

  A = representation_matrix(y)
  B = basis_mat(a, Val{false})

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

iszero(a::AlgAssAbsOrdElem) = iszero(elem_in_algebra(a, Val{false}))

isone(a::AlgAssAbsOrdElem) = isone(elem_in_algebra(a, Val{false}))
