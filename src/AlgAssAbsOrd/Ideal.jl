export isinvertible, contract

@doc Markdown.doc"""
    order(I::AlgAssAbsOrdIdl) -> AlgAssAbsOrd

> Returns the order containing $I$.
"""
@inline order(I::AlgAssAbsOrdIdl) = I.order

iszero(I::AlgAssAbsOrdIdl) = (I.iszero == 1)
isone(I::AlgAssAbsOrdIdl) = isone(abs(det(basis_matrix(I, copy = false))))

function Base.one(S::AlgAssAbsOrdIdlSet)
  O = order(S)
  M = identity_matrix(FlintZZ, degree(O))
  return ideal(O, M, :twosided, true)
end

function one(I::AlgAssAbsOrdIdl)
  return ideal(order(I), one(order(I)))
end

function Base.copy(I::AlgAssAbsOrdIdl)
  return I
end

###############################################################################
#
#  String I/O
#
###############################################################################

function show(io::IO, a::AlgAssAbsOrdIdl)
  print(io, "Ideal of ")
  show(IOContext(io, :compact => true), order(a))
  println(io, " with basis matrix")
  print(io, a.basis_matrix)
end

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(a::AlgAssAbsOrdIdl, dict::IdDict)
  b = typeof(a)(order(a))
  for i in fieldnames(typeof(a))
    if isdefined(a, i)
      if i != :order
        setfield!(b, i, Base.deepcopy_internal(getfield(a, i), dict))
      end
    end
  end
  return b
end

################################################################################
#
#  Ideal Set
#
################################################################################

function show(io::IO, a::AlgAssAbsOrdIdlSet)
  print(io, "Set of ideals of $(order(a))\n")
end

order(a::AlgAssAbsOrdIdlSet) = a.order

parent(I::AlgAssAbsOrdIdl) = AlgAssAbsOrdIdlSet(order(I))

function IdealSet(O::AlgAssAbsOrd)
   return AlgAssAbsOrdIdlSet(O)
end

elem_type(::Type{AlgAssAbsOrdIdlSet{S, T}}) where {S, T} = AlgAssAbsOrdIdl{S, T}

elem_type(::AlgAssAbsOrdIdlSet{S, T}) where {S, T} = AlgAssAbsOrdIdl{S, T}

parent_type(::Type{AlgAssAbsOrdIdl{S, T}}) where {S, T} = AlgAssAbsOrdIdlSet{S, T}

################################################################################
#
#  "Assure" functions for fields
#
################################################################################

function assure_has_basis(a::AlgAssAbsOrdIdl{S, T}) where {S, T}
  if isdefined(a, :basis)
    return nothing
  end

  O = order(a)
  a.basis = Vector{AlgAssAbsOrdElem{S, T}}(undef, degree(O))
  for i = 1:degree(O)
    a.basis[i] = elem_from_mat_row(O, basis_matrix(a, copy = false), i)
  end
  return nothing
end

function assure_has_basis_mat_inv(a::AlgAssAbsOrdIdl)
  if isdefined(a, :basis_mat_inv)
    return nothing
  else
    a.basis_mat_inv = FakeFmpqMat(pseudo_inv(basis_matrix(a, copy = false)))
    return nothing
  end
end

################################################################################
#
#  Basis (matrices)
#
################################################################################

@doc Markdown.doc"""
    basis(a::AlgAssAbsOrdIdl; copy::Bool = true) -> Vector{AlgAssAbsOrdElem}

> Returns the basis of $a$.
"""
function basis(a::AlgAssAbsOrdIdl; copy::Bool = true)
  assure_has_basis(a)
  if copy
    return deepcopy(a.basis)
  else
    return a.basis
  end
end

@doc Markdown.doc"""
    basis_matrix(a::AlgAssAbsOrdIdl; copy::Bool = true) -> fmpz_mat

> Returns the basis matrix of $a$ with respect to the basis of the order.
"""
function basis_matrix(a::AlgAssAbsOrdIdl; copy::Bool = true)
  if copy
    return deepcopy(a.basis_matrix)
  else
    return a.basis_matrix
  end
end

@doc Markdown.doc"""
    basis_mat_inv(a::AlgAssAbsOrdIdl; copy::Bool = true) -> FakeFmpqMat

> Returns the inverse of the basis matrix of $a$.
"""
function basis_mat_inv(a::AlgAssAbsOrdIdl; copy::Bool = true)
  assure_has_basis_mat_inv(a)
  if copy
    return deepcopy(a.basis_mat_inv)
  else
    return a.basis_mat_inv
  end
end

function det_of_basis_matrix(a::AlgAssAbsOrdIdl)
  d = fmpz(1)
  M = basis_matrix(a, copy = false)
  for i = 1:nrows(M)
    d = mul!(d, d, M[i, i])
  end
  return d
end

################################################################################
#
#  Arithmetic
#
################################################################################

@doc Markdown.doc"""
    +(a::AlgAssAbsOrdIdl, b::AlgAssAbsOrdIdl) -> AlgAssAbsOrdIdl

> Returns $a + b$.
"""
function +(a::AlgAssAbsOrdIdl{S, T}, b::AlgAssAbsOrdIdl{S, T}) where {S, T}
  if iszero(a)
    return deepcopy(b)
  elseif iszero(b)
    return deepcopy(a)
  end

  d = degree(order(a))
  M = vcat(basis_matrix(a), basis_matrix(b))
  deta = det_of_basis_matrix(a)
  detb = det_of_basis_matrix(b)
  M = hnf_modular_eldiv!(M, gcd(deta, detb), :lowerleft)
  M = sub(M, (d + 1):2*d, 1:d)
  return ideal(order(a), M, :nothing, true)
end

@doc Markdown.doc"""
    *(a::AlgAssAbsOrdIdl, b::AlgAssAbsOrdIdl) -> AlgAssAbsOrdIdl

> Returns $a \cdot b$.
"""
function *(a::AlgAssAbsOrdIdl{S, T}, b::AlgAssAbsOrdIdl{S, T}) where {S, T}
  if iszero(a)
    return deepcopy(a)
  elseif iszero(b)
    return deepcopy(b)
  end

  d = degree(order(a))
  ba = basis(a, copy = false)
  bb = basis(b, copy = false)
  d2 = d^2

  M = zero_matrix(FlintZZ, d2, d)
  t = one(order(a))
  for i = 1:d
    for j = 1:d
      t = mul!(t, ba[i], bb[j])
      for k = 1:d
        M[(i - 1)*d + j, k] = coordinates(t; copy = false)[k]
      end
    end
  end

  deta = det_of_basis_matrix(a)
  detb = det_of_basis_matrix(b)
  M = hnf_modular_eldiv!(M, deta*detb, :lowerleft)
  M = sub(M, (d2 - d + 1):d2, 1:d)
  return ideal(order(a), M, :nothing, true)
end

@doc Markdown.doc"""
    ^(a::AlgAssAbsOrdIdl, e::Int) -> AlgAssAbsOrdIdl
    ^(a::AlgAssAbsOrdIdl, e::fmpz) -> AlgAssAbsOrdIdl

> Returns $a^e$.
"""
^(A::AlgAssAbsOrdIdl, e::Int) = Base.power_by_squaring(A, e)
^(A::AlgAssAbsOrdIdl, e::fmpz) = Base.power_by_squaring(A, BigInt(e))

@doc Markdown.doc"""
    intersect(a::AlgAssAbsOrdIdl, b::AlgAssAbsOrdIdl) -> AlgAssAbsOrdIdl

> Returns $a \cap b$.
"""
function intersect(a::AlgAssAbsOrdIdl{S, T}, b::AlgAssAbsOrdIdl{S, T}) where {S, T}
  d = degree(order(a))
  H = vcat(basis_matrix(a), basis_matrix(b))
  K = left_kernel(H)[2]
  return ideal(order(a), _hnf(view(K, 1:d, 1:d)*basis_matrix(a, copy = false), :lowerleft), :nothing, true)
end

################################################################################
#
#  Ad hoc multiplication
#
################################################################################

*(x::Union{ Int, fmpz }, a::AlgAssAbsOrdIdl) = ideal(order(a), x*basis_matrix(a, copy = false), :nothing, true)
*(a::AlgAssAbsOrdIdl, x::Union{ Int, fmpz }) = ideal(order(a), basis_matrix(a, copy = false)*x, :nothing, true)

function *(x::AlgAssAbsOrdElem, a::AlgAssAbsOrdIdl)
  @assert parent(x) === order(a)
  @assert isleft_ideal(a)
  O = order(a)
  return ideal(O, x)*a
end

function *(a::AlgAssAbsOrdIdl, x::AlgAssAbsOrdElem)
  @assert parent(x) === order(a)
  @assert isright_ideal(a)
  O = order(a)
  return a*ideal(O, x)
end

################################################################################
#
#  Division
#
################################################################################

function divexact(a::AlgAssAbsOrdIdl, x::fmpz)
  O = order(a)
  M = FakeFmpqMat(basis_matrix(a, copy = false), deepcopy(x))
  if M.den != 1
    error("Ideal not divisible by x")
  end
  return ideal(O, M.num)
end

################################################################################
#
#  Construction
#
################################################################################

# Assumes that B_I[i] == elem_from_mat_row(O, M, i)
function defines_ideal(O::Union{ NfAbsOrd, AlgAssAbsOrd }, M::fmpz_mat, B_I::Vector{ <: Union{ NfAbsOrdElem, AlgAssAbsOrdElem } })
  if nrows(M) != degree(O) || ncols(M) != degree(O)
    return false, FakeFmpqMat()
  end
  local Minv
  try
    Minv = FakeFmpqMat(pseudo_inv(M))
  catch
    return false, FakeFmpqMat()
  end
  n = degree(O)
  B_O = basis(O, copy = false)

  N = zero_matrix(FlintZZ, n, n)
  t = O()
  for i = 1:n
    for j = 1:n
      t = mul!(t, B_O[i], B_I[j])
      for k = 1:n
        N[j, k] = deepcopy(coordinates(t, copy = false)[k])
      end
    end
    if !isone((N*Minv).den)
      return false, Minv
    end
    if iscommutative(O)
      continue
    end
    for j = 1:n
      t = mul!(t, B_I[i], B_O[j])
      for k = 1:n
        N[j, k] = deepcopy(coordinates(t, copy = false)[k])
      end
    end
    if !isone((N*Minv).den)
      return false, Minv
    end
  end
  return true, Minv
end

function defines_ideal(O::Union{ NfAbsOrd, AlgAssAbsOrd }, M::fmpz_mat)
  if nrows(M) != degree(O) || ncols(M) != degree(O)
    return false, FakeFmpqMat(M), elem_type(O)[]
  end
  B_I = Vector{elem_type(O)}(undef, degree(O))
  for i = 1:degree(O)
    B_I[i] = elem_from_mat_row(O, M, i)
  end
  b, Minv = defines_ideal(O, M, B_I)
  return b, Minv, B_I
end

function defines_ideal(O::Union{ NfAbsOrd, AlgAssAbsOrd }, B_I::Vector{ <: Union{ NfAbsOrdElem, AlgAssAbsOrdElem } })
  if length(B_I) != degree(O)
    return false, zero_matrix(O, degree(O), degree(O)), FakeFmpqMat()
  end
  M = zero_matrix(FlintZZ, degree(O), degree(O))
  for i = 1:degree(O)
    for j = 1:degree(O)
      M[i, j] = deepcopy(coordinates(B_I[i], copy = false)[j])
    end
  end
  b, Minv = defines_ideal(O, M, B_I)
  return b, M, Minv
end

@doc Markdown.doc"""
    ideal(O::AlgAssAbsOrd, M::fmpz_mat, side::Symbol = :nothing,
          M_in_hnf::Bool = false)
      -> AlgAssAbsOrdIdl

> Returns the ideal of $O$ with basis matrix $M$.
> If the ideal is known to be a right/left/twosided ideal of $O$, `side` may be
> set to `:right`/`:left`/`:twosided` respectively.
> If `M_in_hnf == true` it is assumed that $M$ is already in lower left HNF.
"""
function ideal(O::AlgAssAbsOrd{S, T}, M::fmpz_mat, side::Symbol = :nothing, M_in_hnf::Bool = false) where {S, T}
  !M_in_hnf ? M = _hnf(M, :lowerleft) : nothing
  a = AlgAssAbsOrdIdl{S, T}(O, M)
  _set_sidedness(a, side)
  return a
end

@doc Markdown.doc"""
    ideal(O::AlgAssAbsOrd, x::AlgAssAbsOrdElem) -> AlgAssAbsOrdIdl

> Returns the twosided principal ideal of $O$ generated by $x$.
"""
function ideal(O::AlgAssAbsOrd{S, T}, x::AlgAssAbsOrdElem{S, T}) where {S, T}
  @assert parent(x) == O

  if iscommutative(O)
    a = ideal(O, x, :left)
    a.isright = 1
    return a
  end

  t1 = O()
  t2 = O()
  M = zero_matrix(FlintZZ, degree(O)^2, degree(O))
  b = basis(O, copy = false)
  for i = 1:degree(O)
    t1 = mul!(t1, b[i], x)
    ii = (i - 1)*degree(O)
    for j = 1:degree(O)
      t2 = mul!(t2, t1, b[j])
      elem_to_mat_row!(M, ii + j, t2)
    end
  end
  M = sub(_hnf(M, :lowerleft), nrows(M) - degree(O) + 1:nrows(M), 1:ncols(M))

  return ideal(O, M, :twosided, true)
end

@doc Markdown.doc"""
    ideal(O::AlgAssAbsOrd, x::AlgAssAbsOrdElem, action::Symbol) -> AlgAssAbsOrdIdl

> Returns the ideal $x \cdot O$, if `action == :left`, and $O \cdot x$, if
> `action == :right`.
"""
function ideal(O::AlgAssAbsOrd{S, T}, x::AlgAssAbsOrdElem{S, T}, action::Symbol) where {S, T}
  @assert parent(x) == O
  M = representation_matrix(x, action)
  a = ideal(O, M)
  if iszero(x)
    a.iszero = 1
  end

  if action == :left
    a.isright = 1
  elseif action == :right
    a.isleft = 1
  end

  return a
end

@doc Markdown.doc"""
    *(O::AlgAssAbsOrd, x::AlgAssAbsOrdElem) -> AlgAssAbsOrdIdl
    *(O::AlgAssAbsOrd, x::Int) -> AlgAssAbsOrdIdl
    *(O::AlgAssAbsOrd, x::fmpz) -> AlgAssAbsOrdIdl
    *(x::AlgAssAbsOrdElem, O::AlgAssAbsOrd) -> AlgAssAbsOrdIdl
    *(x::Int, O::AlgAssAbsOrd) -> AlgAssAbsOrdIdl
    *(x::fmpz, O::AlgAssAbsOrd) -> AlgAssAbsOrdIdl

> Returns the ideal $O \cdot x$ or $x \cdot O$ respectively.
"""
*(O::AlgAssAbsOrd{S, T}, x::AlgAssAbsOrdElem{S, T}) where {S, T} = ideal(O, x, :right)
*(x::AlgAssAbsOrdElem{S, T}, O::AlgAssAbsOrd{S, T}) where {S, T} = ideal(O, x, :left)

*(O::AlgAssAbsOrd, x::Union{ Int, fmpz }) = O*O(x)
*(x::Union{ Int, fmpz }, O::AlgAssAbsOrd) = O(x)*O

@doc Markdown.doc"""
    ideal_from_z_gens(O::AlgAssAbsOrd, b::Vector{ <: AlgAssAbsOrdElem},
                      side::Symbol = :nothing)
      -> AlgAssAbsOrdIdl

> Returns the ideal of $O$ generated by the elements of `b` as a lattice over
> $\mathbb Z$.
"""
function ideal_from_z_gens(O::AlgAssAbsOrd, b::Vector{T}, side::Symbol = :nothing) where { T <: AlgAssAbsOrdElem }
  d = degree(O)
  @assert length(b) >= d

  M = zero_matrix(FlintZZ, length(b), d)
  for i = 1:length(b)
    elem_to_mat_row!(M, i, b[i])
  end
  M = _hnf(M, :lowerleft)
  if d < length(b)
    M = sub(M, (length(b) - d + 1):length(b), 1:d)
  end
  return ideal(O, M, side, true)
end

################################################################################
#
#  Extend/contract
#
################################################################################

@doc Markdown.doc"""
    extend(a::AlgAssAbsOrdIdl, O::AlgAssAbsOrd) -> AlgAssAbsOrdIdl

> Returns $O \cdot a \cdot O$.
> It is assumed that the order of $a$ is contained in $O$.
"""
function extend(A::AlgAssAbsOrdIdl, O::AlgAssAbsOrd, action::Symbol = :twosided)
  # Assumes order(A) \subseteq O

  d = degree(O)
  X = map(O, basis(A, copy = false))
  Y = basis(O, copy = false)
  if action == :left || action == :twosided
    M = zero_matrix(FlintZZ, d^2, d)
    t = O()
    for i = 1:d
      ii = (i - 1)*d
      for j = 1:d
        t = Y[i]*X[j]
        elem_to_mat_row!(M, ii + j, t)
      end
    end
    M = sub(_hnf(M, :lowerleft), nrows(M) - d + 1: nrows(M), 1:d)
    if action == :left
      return ideal(O, M, :left, true)
    end
    for i = 1:d
      X[i] = elem_from_mat_row(O, M, i)
    end
  end
  if action == :right || action == :twosided
    M = zero_matrix(FlintZZ, d^2, d)
    t = O()
    for i = 1:d
      ii = (i - 1)*d
      for j = 1:d
        t = X[i]*Y[j]
        elem_to_mat_row!(M, ii + j, t)
      end
    end
    M = sub(_hnf(M, :lowerleft), nrows(M) - d + 1: nrows(M), 1:d)
    return ideal(O, M, action, true)
  end
  error("action should be :left, :right or :twosided")
end

@doc Markdown.doc"""
    *(a::AlgAssAbsOrdIdl, O::AlgAssAbsOrd) -> AlgAssAbsOrdIdl
    *(O::AlgAssAbsOrd, a::AlgAssAbsOrdIdl) -> AlgAssAbsOrdIdl

> Returns $a \cdot O$ or $O \cdot a$ respectively.
> It is assumed that the order of $a$ is contained in $O$.
"""
*(A::AlgAssAbsOrdIdl, O::AlgAssAbsOrd) = extend(A, O, :right)
*(O::AlgAssAbsOrd, A::AlgAssAbsOrdIdl) = extend(A, O, :left)

@doc Markdown.doc"""
    contract(a::AlgAssAbsOrdIdl, O::AlgAssAbsOrd) -> AlgAssAbsOrdIdl
    intersect(a::AlgAssAbsOrdIdl, O::AlgAssAbsOrd) -> AlgAssAbsOrdIdl
    intersect(O::AlgAssAbsOrd, a::AlgAssAbsOrdIdl) -> AlgAssAbsOrdIdl

> Returns $a \cap O$.
> It is assumed that the order of $a$ contains $O$.
"""
function contract(A::AlgAssAbsOrdIdl, O::AlgAssAbsOrd)
  # Assumes O \subseteq order(A)

  d = degree(O)
  M = basis_matrix(O, copy = false)*basis_mat_inv(order(A), copy = false)
  @assert M.den == 1
  H = vcat(basis_matrix(A), M.num)
  K = left_kernel(H)[2]
  M = sub(K, 1:d, 1:d)*basis_matrix(A, copy = false)
  M = M*basis_matrix(order(A), copy = false)*basis_mat_inv(O, copy = false)
  @assert M.den == 1
  M = _hnf(M.num, :lowerleft)
  return ideal(O, M, :nothing, true)
end

intersect(O::AlgAssAbsOrd, A::AlgAssAbsOrdIdl) = contract(A, O)
intersect(A::AlgAssAbsOrdIdl, O::AlgAssAbsOrd) = contract(A, O)

################################################################################
#
#  Move ideals to another algebra
#
################################################################################

# Let m: A -> B be an injection and I an ideal in B. Then this computes the
# ideal O_A\cap I, where O_A is the maximal order of A.
# OB is assumed to be a maximal order of B containing order(I).
function _as_ideal_of_smaller_algebra(m::AbsAlgAssMor, I::AlgAssAbsOrdIdl, OB::AlgAssAbsOrd)
  A = domain(m)
  B = codomain(m)
  @assert dim(A) <= dim(B)
  @assert algebra(order(I)) === B
  OA = maximal_order(A)
  IB = extend(I, OB)
  # Transport OA to B
  M = zero_matrix(FlintZZ, dim(B), dim(B))
  for i = 1:dim(A)
    t = OB(m(elem_in_algebra(basis(OA, copy = false)[i])))
    elem_to_mat_row!(M, i, t)
  end
  # Compute the intersection of M and IB
  H = vcat(M, basis_matrix(IB))
  K = left_kernel(H)[2]
  N = view(K, 1:dim(B), 1:dim(B))*M
  # Map the basis to A
  basis_in_A = Vector{elem_type(OA)}(undef, dim(B))
  for i = 1:dim(B)
    t = elem_from_mat_row(OB, N, i)
    b, s = haspreimage(m, elem_in_algebra(t, copy = false))
    @assert b
    basis_in_A[i] = OA(s)
  end
  J = ideal_from_z_gens(OA, basis_in_A)
  return J
end

# Let m: A -> B be an injection and O an order in B. Then this computes the
# order O_A\cap O, where O_A is the maximal order of A.
# OB is assumed to be a maximal order of B containing O.
function _as_order_of_smaller_algebra(m::AbsAlgAssMor, O::AlgAssAbsOrd, OB::AlgAssAbsOrd)
  A = domain(m)
  B = codomain(m)
  @assert dim(A) <= dim(B)
  @assert algebra(O) == B
  OA = maximal_order(A)
  # Transport OA to B
  M = zero_matrix(FlintZZ, dim(B), dim(B))
  for i = 1:dim(A)
    t = OB(m(elem_in_algebra(basis(OA, copy = false)[i])))
    elem_to_mat_row!(M, i, t)
  end
  # Compute the intersection of M and O (in OB)
  N = basis_matrix(O, copy = false)*basis_mat_inv(OB, copy = false)
  @assert N.den == 1
  H = vcat(M, N.num)
  K = left_kernel(H)[2]
  N = sub(K, 1:dim(B), 1:dim(B))*M
  # Map the basis to A
  basis_in_A = Vector{elem_type(A)}(undef, dim(B))
  for i = 1:dim(B)
    t = elem_from_mat_row(OB, N, i)
    b, s = haspreimage(m, elem_in_algebra(t, copy = false))
    @assert b
    basis_in_A[i] = s
  end
  M = zero_matrix(base_ring(A), length(basis_in_A), dim(A))
  for i = 1:length(basis_in_A)
    elem_to_mat_row!(M, i, basis_in_A[i])
  end
  M = FakeFmpqMat(M)
  MM = sub(hnf!(M, :lowerleft), (dim(B) - dim(A) + 1):dim(B), 1:dim(A))
  OO = Order(A, MM)
  return OO
end

# Let m: A -> B be an injection, I an ideal in A and O an order of B. Then this
# computes I*O.
# WE ASSUME THAT m(A) LIES IN THE CENTRE OF B!
function _as_ideal_of_larger_algebra(m::AbsAlgAssMor, I::AlgAssAbsOrdIdl, O::AlgAssAbsOrd)
  A = domain(m)
  B = codomain(m)
  @assert dim(A) <= dim(B)
  @assert algebra(order(I)) == A
  @assert algebra(O) == B

  M = zero_matrix(FlintZZ, dim(A)*dim(B), dim(B))
  X = Vector{elem_type(O)}(undef, dim(A))
  for i = 1:dim(A)
    t = elem_in_algebra(basis(I, copy = false)[i])
    X[i] = O(m(t))
  end
  for i = 1:dim(A)
    for j = 1:dim(B)
      t = X[i]*basis(O, copy = false)[j]
      elem_to_mat_row!(M, (i - 1)*dim(B) + j, t)
    end
  end
  M = sub(_hnf(M, :lowerleft), dim(B)*(dim(A) - 1) + 1:dim(A)*dim(B), 1:dim(B))
  return ideal(O, M, :nothing, true)
end

################################################################################
#
#  Inclusion of elements in ideals
#
################################################################################

@doc Markdown.doc"""
    in(x::AlgAssAbsOrdElem, a::AlgAssAbsOrdIdl) -> Bool

> Returns `true` if the order element $x$ is in $a$ and `false` otherwise.
"""
function in(x::AlgAssAbsOrdElem, I::AlgAssAbsOrdIdl)
  el = coordinates(x)
  y = matrix(FlintZZ, 1, length(el), el)
  M1, d = pseudo_inv(basis_matrix(I, copy = false))
  if FakeFmpqMat(y*M1, d).den == 1
    return true
  else
    return false
  end
end

################################################################################
#
#  Equality
#
################################################################################

@doc Markdown.doc"""
    ==(a::AlgAssAbsOrdIdl, b::AlgAssAbsOrdIdl) -> Bool

> Returns `true` if $a$ and $b$ are equal and `false` otherwise.
"""
function ==(A::AlgAssAbsOrdIdl, B::AlgAssAbsOrdIdl)
  order(A) !== order(B) && return false
  return basis_matrix(A, copy = false) == basis_matrix(B, copy = false)
end

################################################################################
#
#  Hashing
#
################################################################################

function Base.hash(A::AlgAssAbsOrdIdl, h::UInt)
  return Base.hash(basis_matrix(A, copy = false), h)
end

################################################################################
#
#  Idempotents
#
################################################################################

@doc Markdown.doc"""
    idempotents(a::AlgAssAbsOrdIdl, b::AlgAssAbsOrdIdl)
      -> AlgAssAbsOrdElem, AlgAssAbsOrdElem

> Given coprime ideals $a$ and $b$, this function returns elements $x \in a$
> and $y \in b$ such that $x + y = 1$.
"""
function idempotents(a::AlgAssAbsOrdIdl, b::AlgAssAbsOrdIdl)

  !(order(a) === order(b)) && error("Parent mismatch")
  O = order(a)
  d = degree(O)

  V = zero_matrix(FlintZZ, 1 + 2*degree(O), 1 + 2*degree(O))
  V[1, 1] = 1
  u = coordinates(one(O))
  for i = 1:d
    V[1, i + 1] = u[i]
  end

  _copy_matrix_into_matrix(V, 2, 2, basis_matrix(a, copy = false))
  _copy_matrix_into_matrix(V, 2 + d, 2, basis_matrix(b, copy = false))
  for i = 2:d + 1
    V[i, d + i] = 1
  end

  H = hnf!(V)
  for i = 2:d + 1
    if H[1, i] != 0
      error("Ideals are not coprime")
    end
  end

  t = O()
  z = basis(a, copy = false)[1]*H[1, d + 2]
  for i = 2:d
    t = mul!(t, basis(a, copy = false)[i], H[1, d + 1 + i])
    z = add!(z, z, t)
  end

  @assert -z in a
  @assert one(O) + z in b
  return -z, one(O) + z
end

################################################################################
#
#  From algebra to number field
#
################################################################################

function _as_ideal_of_number_field(I::AlgAssAbsOrdIdl, m::AbsAlgAssToNfAbsMor)
  @assert algebra(order(I)) == domain(m)
  K = codomain(m)
  OK = maximal_order(K)

  b = Vector{elem_type(OK)}()
  for i = 1:dim(domain(m))
    push!(b, OK(m(elem_in_algebra(basis(I, copy = false)[i]))))
  end
  return ideal_from_z_gens(OK, b)
end

function _as_ideal_of_number_field(I::FacElem{<: AlgAssAbsOrdIdl, <: AlgAssAbsOrdIdlSet}, m::AbsAlgAssToNfAbsMor)
  @assert algebra(order(base_ring(parent(I)))) == domain(m)
  K = codomain(m)
  OK = maximal_order(K)

  if isempty(I)
    return FacElemMon(IdealSet(OK))()
  end

  bases = Vector{ideal_type(OK)}()
  exps = Vector{fmpz}()
  for (b, e) in I
    push!(bases, _as_ideal_of_number_field(b, m))
    push!(exps, e)
  end
  return FacElem(bases, exps)
end

function _as_ideal_of_algebra(I::NfAbsOrdIdl, i::Int, O::AlgAssAbsOrd, one_ideals::Vector{Vector{T}}) where { T <: AlgAssAbsOrdElem }
  A = algebra(O)
  fields_and_maps = as_number_fields(A)
  b = Vector{elem_type(O)}()
  for j = 1:length(fields_and_maps)
    K, AtoK = fields_and_maps[j]
    if j == i
      @assert nf(order(I)) == K
      append!(b, [ O(AtoK\K(bb)) for bb in basis(I, copy = false) ])
    else
      append!(b, one_ideals[j])
    end
  end
  return ideal_from_z_gens(O, b)
end

function _as_ideal_of_algebra(I::FacElem{NfOrdIdl, NfOrdIdlSet}, i::Int, O::AlgAssAbsOrd, one_ideals::Vector{Vector{T}}) where { T <: AlgAssAbsOrdElem }
  if isempty(I)
    return FacElemMon(IdealSet(O))()
  end

  base = Vector{ideal_type(O)}()
  exp = Vector{fmpz}()
  for (b, e) in I
    push!(base, _as_ideal_of_algebra(b, i, O, one_ideals))
    push!(exp, e)
  end
  return FacElem(base, exp)
end

# Returns an array of bases of the ideals O_i(1)*O_i lifted to O, where O_i
# are the maximal orders of the number fields in the decomposition of
# algebra(O).
function _lift_one_ideals(O::AlgAssAbsOrd)
  A = algebra(O)
  fields_and_maps = as_number_fields(A)

  one_ideals = Vector{Vector{elem_type(O)}}()
  for i = 1:length(fields_and_maps)
    K, AtoK = fields_and_maps[i]
    OK = maximal_order(K)
    a = OK(1)*OK
    b = Vector{elem_type(O)}()
    for i = 1:degree(K)
      push!(b, O(AtoK\K(basis(a, copy = false)[i])))
    end
    push!(one_ideals, b)
  end
  return one_ideals
end

################################################################################
#
#  Factorization
#
################################################################################

@doc Markdown.doc"""
    factor(I::AlgAssAbsOrdIdl) -> Dict{AlgAssAbsOrdIdl, Int}

> Returns the prime ideal factorization of $I$ as a dictionary.
"""
function factor(I::AlgAssAbsOrdIdl)
  O = order(I)
  A = algebra(O)
  fields_and_maps = as_number_fields(A)

  one_ideals = _lift_one_ideals(O)

  fac = Dict{ideal_type(O), Int}()
  for i = 1:length(fields_and_maps)
    K, AtoK = fields_and_maps[i]
    J = _as_ideal_of_number_field(I, AtoK)
    fac2 = factor(J)
    for (p, e) in fac2
      P = _as_ideal_of_algebra(p, i, O, one_ideals)
      fac[P] = e
    end
  end
  return fac
end

################################################################################
#
#  Inverse
#
################################################################################

# If I is not coprime to the conductor of O in the maximal order, then this might
# not be an inverse.
function inv(a::AlgAssAbsOrdIdl)
  @assert !iszero(a)
  O = order(a)
  return colon(ideal(O, one(O)), a)
end

# Mostly the same as colon in NfOrd/Ideal/Ideal.jl
function colon(a::AlgAssAbsOrdIdl{S, T}, b::AlgAssAbsOrdIdl{S, T}) where {S, T}
  O = order(a)
  n = degree(O)
  B = basis(b)

  bmatinv = basis_mat_inv(a, copy = false)

  n = representation_matrix(B[1])*bmatinv
  m = numerator(n)
  d = denominator(n)
  for i in 2:length(B)
    n = representation_matrix(B[i])*bmatinv
    mm = n.num
    dd = n.den
    l = lcm(dd, d)
    if l == d && l == dd
      m = hcat(m, mm)
    elseif l == d
      m = hcat(m, div(d, dd)*mm)
    elseif l == dd
      m = hcat(div(dd, d)*m, mm)
      d = dd
    else
      m = hcat(m*div(l, d), mm*div(l, dd))
      d = l
    end
  end
  m = hnf(transpose(m))
  # n is upper right HNF
  m = transpose(sub(m, 1:degree(O), 1:degree(O)))
  b = inv(FakeFmpqMat(m, d))
  return fractional_ideal_type(O)(O, ideal(O, b.num), b.den)
end

function isinvertible(a::AlgAssAbsOrdIdl)
  if iszero(a)
    return false, a
  end

  bmata = basis_matrix(a, copy = false)

  if any(iszero(bmata[i, i]) for i in 1:degree(order(a)))
    return false, a
  end

  if order(a).ismaximal == 1
    return true, inv(a)
  end

  b = inv(a)
  c = a*b
  return isone(c), b
end

################################################################################
#
#  Normal ideals
#
################################################################################

@doc Markdown.doc"""
    isnormal(a::AlgAssAbsOrdIdl) -> Bool

> Returns `true` if $a$ is a normal ideal and `false` otherwise.
"""
isnormal(a::AlgAssAbsOrdIdl) = ismaximal(left_order(a))

################################################################################
#
#  Locally free basis
#
################################################################################

@doc Markdown.doc"""
    locally_free_basis(a::AlgAssAbsOrdIdl, p::Union{ Int, fmpz }) -> AlgAssAbsOrdElem

> Returns an element $x$ of the order $O$ of $a$ such that $a_p = O_p x$
> where $p$ is a prime of `base_ring(O)`.
> See also `islocally_free`.
"""
function locally_free_basis(I::AlgAssAbsOrdIdl, p::Union{ Int, fmpz })
  b, x = islocally_free(I, p)
  if !b
    error("The ideal is not locally free at the prime")
  end
  return x
end

# See Bley, Wilson "Computations in relative algebraic K-groups", section 4.2
@doc Markdown.doc"""
    islocally_free(a::AlgAssAbsOrdIdl, p::Union{ Int, fmpz })
      -> Bool, AlgAssAbsOrdElem

> Returns a tuple `(true, x)` with an element $x$ of the order $O$ of $a$ such
> that $a_p = O_p x$ if $a$ is locally free at $p$, and `(false, 0)` otherwise.
> $p$ is a prime of `base_ring(O)`.
> See also `locally_free_basis`.
"""
function islocally_free(I::AlgAssAbsOrdIdl, p::Union{ Int, fmpz })
  O = order(I)
  OpO, toOpO = AlgAss(O, p*O, p)
  J = radical(OpO)
  OJ, toOJ = quo(OpO, J)
  decOJ = decompose(OJ)

  pI = p*I
  IpI, toIpI = AlgAss(I, p*I, p)
  gensJ = Vector{elem_type(IpI)}()
  for b in basis(J, copy = false)
    bb = toOpO\b
    for c in basis(I, copy = false)
      push!(gensJ, toIpI(bb*c))
    end
  end
  JinIpI = ideal_from_gens(IpI, gensJ)
  IJ, toIJ = quo(IpI, JinIpI)

  a = O()
  for i = 1:length(decOJ)
    A, AtoOJ = decOJ[i]
    B, AtoB, BtoA = _as_algebra_over_center(A)
    C, BtoC = _as_matrix_algebra(B)
    e = toOpO\(toOJ\(AtoOJ(BtoA(BtoC\C[1]))))
    basiseIJ = Vector{elem_type(IJ)}()
    for b in basis(I, copy = false)
      bb = toIJ(toIpI(e*b))
      if !iszero(bb)
        push!(basiseIJ, bb)
      end
    end

    # Construct an Fq-basis for e*IJ where Fq \cong centre(A)
    Z, ZtoA = center(A)
    basisZ = [ toOpO\(toOJ\(AtoOJ(ZtoA(Z[i])))) for i = 1:dim(Z) ]

    basiseIJoverZ = Vector{elem_type(O)}()
    M = zero_matrix(base_ring(IJ), dim(Z), dim(IJ))
    MM = zero_matrix(base_ring(IJ), 0, dim(IJ))
    r = 0
    for i = 1:length(basiseIJ)
      b = toIpI\(toIJ\basiseIJ[i])

      for j = 1:dim(Z)
        bb = toIJ(toIpI(basisZ[j]*b))
        elem_to_mat_row!(M, j, bb)
      end

      N = vcat(MM, M)
      s = rank(N)
      if s > r
        push!(basiseIJoverZ, b)
        MM = N
        r = s
      end
      if r == length(basiseIJ)
        break
      end
    end

    if length(basiseIJoverZ) != degree(C)
      # I is not locally free
      return false, O()
    end

    for i = 1:length(basiseIJoverZ)
      a += mod(toOpO\(toOJ\(AtoOJ(BtoA(BtoC\C[i]))))*basiseIJoverZ[i], pI)
    end
  end

  return true, mod(a, pI)
end

################################################################################
#
#  Ring of multipliers, left and right order
#
################################################################################

@doc Markdown.doc"""
    ring_of_multipliers(I::AlgAssAbsOrdIdl) -> AlgAssAbsOrd

> Given an ideal $I$, it returns the ring $(I : I)$.
"""
function ring_of_multipliers(I::AlgAssAbsOrdIdl, p::fmpz=fmpz(1), action::Symbol = :left)
  O = order(I)
  @hassert :AlgAssOrd 1 Hecke.check_associativity(algebra(O))
  @hassert :AlgAssOrd 1 Hecke.check_distributivity(algebra(O))
  @hassert :AlgAssOrd 1 defines_ideal(O, basis_matrix(I, copy = false))[1]
  bmatinv = basis_mat_inv(I, copy = false)
  if isdefined(I, :gens) && length(I.gens) < degree(O)
    B = I.gens
  else
    B = basis(I, copy = false)
  end
  m = zero_matrix(FlintZZ, degree(O)*length(B), degree(O))
  for i = 1:length(B)
    M = representation_matrix(B[i], action)
    mul!(M, M, bmatinv.num)
    if bmatinv.den == 1
      for s = 1:degree(O)
        for t = 1:degree(O)
          m[t + (i - 1)*degree(O), s] = M[s, t]
        end
      end
    else
      for s = 1:degree(O)
        for t = 1:degree(O)
          @hassert :AlgAssOrd 1 divisible(M[s, t], bmatinv.den)
          m[t + (i - 1)*degree(O), s] = divexact(M[s, t], bmatinv.den)
        end
      end
    end
  end
  #In the case of the p-radical, it is important to do this modulo p
  if p == 1
    m = hnf(m)
  else
    hnf_modular_eldiv!(m, p)
  end
  s = prod(m[i,i] for i=1:ncols(m))
  if s==1
    return O
  end
  # n is upper right HNF
  n = transpose(view(m, 1:degree(O), 1:degree(O)))
  b = FakeFmpqMat(pseudo_inv(n))
  mul!(b, b, basis_matrix(O, copy = false))
  @hassert :AlgAssOrd 1 defines_order(algebra(O), b)[1]
  O1 = Order(algebra(O), b)
  O1.disc = divexact(discriminant(O), s^2)
  return O1
end

@doc Markdown.doc"""
    left_order(a::AlgAssAbsOrdIdl) -> AlgAssAbsOrd

> Returns the order $\{ x \in A \mid xa \subseteq a\}$, where $A$ is the algebra
> containing $a$.
"""
left_order(a::AlgAssAbsOrdIdl) = ring_of_multipliers(a, fmpz(1), :right)

@doc Markdown.doc"""
    right_order(a::AlgAssAbsOrdIdl) -> AlgAssAbsOrd

> Returns the order $\{ x \in A \mid ax \subseteq a\}$, where $A$ is the algebra
> containing $a$.
"""
right_order(a::AlgAssAbsOrdIdl) = ring_of_multipliers(a, fmpz(1), :left)

################################################################################
#
#  p-radical
#
################################################################################

function pradical_meataxe(O::AlgAssAbsOrd, p::Int)
  
  A1, OtoA1  = quo(O, p*O, p)
  #@show dim(A1)
  @vtime :AlgAssOrd 1 lg = Hecke.gens(A1)
  #@show length(lg)
  lM = dense_matrix_type(base_ring(A1))[transpose(representation_matrix(lg[i])) for i=1:length(lg)]
  M = ModAlgAss(lM)
  ls = minimal_submodules(M)
  l = sum(nrows(x) for x in ls)
  M1 = zero_matrix(base_ring(A1), l, degree(O))
  i=1
  for x in ls
    for j=1:nrows(x)
      for k=1:degree(O)
        M1[i,k] = x[j,k]
      end
      i+=1
    end
  end
  r = rref!(M1)
  if r == degree(O)
    J = ideal(O, scalar_matrix(FlintZZ, degree(O), p))
    J.gens = elem_type(O)[O(p*one(O.algebra))]
    return J
  end
  M1 = view(M1, 1:r, 1:degree(O))
  dM = transpose(nullspace(M1)[2])
  gens=Vector{elem_type(O)}(undef, nrows(dM)+1)
  m = zero_matrix(FlintZZ, degree(O), degree(O))
  for i=1:nrows(dM)
    for j=1:ncols(dM)
      m[i,j] = lift(dM[i,j])
    end
    gens[i]= elem_from_mat_row(O,m,i)
  end
  hnf_modular_eldiv!(m, fmpz(p))
  gens[nrows(dM)+1]=O(p*one(algebra(O)))
  J=ideal(O,m)
  J.gens=gens
  return J

end

@doc Markdown.doc"""
    pradical(O::AlgAssAbsOrd, p::Int) -> AlgAssAbsOrdIdl

> Given an order $O$ and a prime $p$, it returns the radical of the ideal generated by $p$.
"""
function pradical(O::AlgAssAbsOrd, p::Int)

  #See the paper from Ronyai, Structure of finite algebra
  l = clog(fmpz(degree(O)),p)
  if l > 1
    return pradical_meataxe(O,p)
  end
  n = root(degree(O),2)
  F = GF(p, cached=false)

  #First step: kernel of the trace matrix mod p 

  I = change_base_ring(n*trred_matrix(O), F)
  k, B = nullspace(I)
  # The columns of B give the coordinates of the elements in the order.
  if k==0
    J= ideal(O, scalar_matrix(FlintZZ, degree(O), p))
    J.gens = AlgAssAbsOrdElem[O(p*one(algebra(O)))]
    return J
  end
  if l==1
    #In this case, we can output I: it is the standard p-trace method.
    M=zero_matrix(FlintZZ, degree(O), degree(O))
    for i=1:ncols(B)
      for j=1:degree(O)
        M[i,j]=lift(B[j,i])
      end
    end
    M1 = hnf_modular_eldiv!(M, fmpz(p))
    res = ideal(O, view(M1,1:degree(O),1:degree(O)))
    B1 = lift(B')
    res.gens = Vector{elem_type(O)}(undef, k+1)
    for i=1:k
      res.gens[i] = elem_from_mat_row(O, B1, i)
    end
    res.gens[k+1] = O(p*one(algebra(O)))
    @hassert :AlgAssOrd 1 check_pradical(res,p)
    return res
  end

  Ide = transpose(lift(B))
  #Now, iterate: we need to find the kernel of tr((xy)^(p^i))/p^i mod p
  #on the subspace generated by I
  #Hard to believe, but this is linear on I!!!!
  for i = 1:l
    N = zero_matrix(F, degree(O), nrows(Ide))
    a = algebra(O)()
    for t = 1:nrows(Ide)
      elm = elem_from_mat_row(O,Ide,t)
      for s = 1:degree(O)
        mul!(a, elem_in_algebra(elm, copy = false), O.basis_alg[s])
        bbb = (a^(p^i))
        trel = tr(bbb)
        el = divexact(numerator(trel),p^i)
        N[s,t] = F(el)
      end
    end
    k, B2 = nullspace(N)
    if k == 0
      J = ideal(O, scalar_matrix(FlintZZ, degree(O), p))
      J.gens = AlgAssAbsOrdElem[O(p*one(algebra(O)))]
      return J
    end
    Ide = lift(transpose(B2))*Ide
  end
  gens = Vector{AlgAssAbsOrdElem}(undef, nrows(Ide)+1)
  for i in 1:nrows(Ide)
    gens[i] = elem_from_mat_row(O, Ide, i)
  end
  gens[nrows(Ide)+1]= O(p*one(algebra(O)))
  #Now, I have to give a basis for the ideal.
  m=zero_matrix(FlintZZ, degree(O), degree(O))
  for i=1:nrows(Ide)
    for j=1:ncols(Ide)
      m[i,j]=Ide[i,j]
    end
  end
  hnf_modular_eldiv!(m, fmpz(p))
  res = ideal(O, m)
  res.gens=gens
  @hassert :AlgAssOrd 1 check_pradical(res,p)
  return res

end

################################################################################
#
#  Some tests
#
################################################################################

function check_pradical(I::AlgAssAbsOrdIdl, p::Int)
  
  O= order(I)
  for i=1:degree(O)
    x=elem_from_mat_row(O,basis_matrix(I, copy = false), i)
    for j=1:degree(O)
      @assert divisible(numerator(tr(elem_in_algebra(x; copy = false)*O.basis_alg[j])), p)
    end
  end
  #=
  if p==2
    for i=1:O.dim
      x=elem_from_mat_row(O,I.basis_matrix, i)
      for j=1:O.dim
        for k=1:clog(fmpz(O.dim), p)
          @assert divisible(numerator(tr((x.elem_in_algebra*O.basis_alg[j])^(p^k))), p^(k+1))
        end
      end
    end
  end
  =#
  return true
end

################################################################################
#
#  Primes lying over a prime
#
################################################################################

# Returns the twosided maximal ideals of O containing I, where p*O \subseteq I.
# If strict_containment == true and I is already prime, we return an empty array.
function _maximal_ideals(O::AlgAssAbsOrd, I::AlgAssAbsOrdIdl, p::Union{Int, fmpz}; strict_containment::Bool = false)

  A1, OtoA1 = quo(O, I, p)
  @vtime :AlgAssOrd 1 lg = gens(A1)
  lM = dense_matrix_type(base_ring(A1))[representation_matrix(lg[i]) for i=1:length(lg)]
  append!(lM, dense_matrix_type(base_ring(A1))[representation_matrix(lg[i], :right) for i=1:length(lg)])
  M = ModAlgAss(lM)
  ls = maximal_submodules(M)
  if strict_containment && isone(length(ls)) && iszero(nrows(ls[1]))
    ls = typeof(ls)[]
  end
  poneO = O(p*one(algebra(O)))
  return ( _from_submodules_to_ideals(M, O, I, x, fmpz(p), poneO, A1, OtoA1) for x in ls )

end

function _from_submodules_to_ideals(M::ModAlgAss, O::AlgAssAbsOrd, I::AlgAssAbsOrdIdl, x::Union{Zmodn_mat, Generic.Mat{Generic.ResF{fmpz}}}, p::fmpz, poneO::AlgAssAbsOrdElem, A1::AlgAss, OtoA1::AbsOrdToAlgAssMor)
  @hassert :AlgAssOrd 1 begin r = rref(x)[1]; closure(x, M.action) == sub(rref(x)[2], 1:r, 1:ncols(x)) end
  m = zero_matrix(FlintZZ, nrows(x)+degree(O) , degree(O))
  gens = Vector{AlgAssAbsOrdElem}(undef, nrows(x))
  for i = 1:nrows(x)
    el = OtoA1\(elem_from_mat_row(A1, x, i))
    for j = 1:degree(O)
      m[i,j] = coordinates(el, copy = false)[j]
    end
    gens[i] = elem_from_mat_row(O, m, i)
  end
  for i=nrows(x)+1:nrows(m)
    for j=1:degree(O)
      m[i,j] = basis_matrix(I, copy = false)[i-nrows(x), j]
    end
  end
  hnf_modular_eldiv!(m, fmpz(p))
  J = ideal(O, view(m, 1:degree(O), 1:degree(O)))
  if isdefined(I, :gens)
    append!(gens, I.gens)
    J.gens = gens
  else
    append!(gens, basis(I, copy = false))
  end
  return J

end

@doc Markdown.doc"""
    prime_ideals_over(O::AlgAssAbsOrd, p::Union{ Int, fmpz })
      -> Vector{AlgAssAbsOrdIdl}

> Returns all prime ideal of $O$ lying over the prime number $p$.
"""
function prime_ideals_over(O::AlgAssAbsOrd, p::Union{ Int, fmpz })
  @vtime :AlgAssOrd 1 max_id = collect(_maximal_ideals(O, p*O, Int(p)))
  return max_id
end

@doc Markdown.doc"""
    prime_ideals_over(O::AlgAssAbsOrd, P::AlgAssAbsOrdIdl) -> Vector{AlgAssAbsOrdIdl}

> Given a prime ideal $P$ in an order contained in $O$, this function returns
> the prime ideals of $O$ lying over $P$.
"""
function prime_ideals_over(O::AlgAssAbsOrd, P::AlgAssAbsOrdIdl)
  O1 = order(P)
  if O1 == O
    return ideal_type(O)[P]
  end
  M = maximal_order(O)
  lp = prime_ideals_over(M, minimum(P))
  p_critical_primes = Vector{ideal_type(O)}()
  for Q in lp
    c = contract(Q, O1)
    if c == P
      c1 = contract(Q, O)
      if !(c1 in p_critical_primes)
        push!(p_critical_primes, c1)
      end
    end
  end
  return p_critical_primes
end

################################################################################
#
#  Minimum
#
################################################################################

function minimum(P::AlgAssAbsOrdIdl)
  N = norm(P, copy = false)
  f, p = ispower(N)
  @assert isprime(p)
  return p
end

################################################################################
#
#  Norm
#
################################################################################

function assure_has_norm(a::AlgAssAbsOrdIdl)
  if isdefined(a, :norm)
    return nothing
  end

  a.norm = abs(det(basis_matrix(a, copy = false)))
  return nothing
end

@doc Markdown.doc"""
    norm(a::AlgAssAbsordIdl; copy::Bool = true) -> fmpz

> Returns the norm of $a$.
"""
function norm(a::AlgAssAbsOrdIdl; copy::Bool = true)
  assure_has_norm(a)
  if copy
    return deepcopy(a.norm)
  else
    return a.norm
  end
end

function assure_has_normred(a::AlgAssAbsOrdIdl)
  if isdefined(a, :normred)
    return nothing
  end

  A = algebra(order(a))
  m = isqrt(dim(A))
  @assert m^2 == dim(A)
  N = norm(a, copy = false)
  b, n = ispower(N, m)
  @assert b "Cannot compute reduced norm. Maybe the algebra is not simple and central?"
  a.normred = n
  return nothing
end

@doc Markdown.doc"""
    normred(a::AlgAssAbsOrdIdl; copy::Bool = true) -> fmpz

> Returns the reduced norm of $a$.
> It is assumed that the algebra containing $a$ is simple and central.
"""
function normred(a::AlgAssAbsOrdIdl; copy::Bool = true)
  @assert dimension_of_center(algebra(order(a))) == 1
  @assert algebra(order(a)).issimple == 1
  assure_has_normred(a)
  if copy
    return deepcopy(a.normred)
  else
    return a.normred
  end
end
