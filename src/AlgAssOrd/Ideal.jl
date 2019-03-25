export isinvertible

@inline order(I::AlgAssAbsOrdIdl) = I.order

iszero(I::AlgAssAbsOrdIdl) = (I.iszero == 1)
isone(I::AlgAssAbsOrdIdl) = isone(abs(det(basis_mat(I, copy = false))))

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
  print(io, a.basis_mat)
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
#  Basis (matrices)
#
################################################################################

function assure_has_basis(a::AlgAssAbsOrdIdl{S, T}) where {S, T}
  if isdefined(a, :basis)
    return nothing
  end

  O = order(a)
  a.basis = Vector{AlgAssAbsOrdElem{S, T}}(undef, degree(O))
  for i = 1:degree(O)
    a.basis[i] = elem_from_mat_row(O, basis_mat(a, copy = false), i)
  end
  return nothing
end

function assure_has_basis_mat_inv(a::AlgAssAbsOrdIdl)
  if isdefined(a, :basis_mat_inv)
    return nothing
  else
    a.basis_mat_inv = FakeFmpqMat(pseudo_inv(basis_mat(a, copy = false)))
    return nothing
  end
end

function basis(a::AlgAssAbsOrdIdl; copy::Bool = true)
  assure_has_basis(a)
  if copy
    return deepcopy(a.basis)
  else
    return a.basis
  end
end

function basis_mat(a::AlgAssAbsOrdIdl; copy::Bool = true)
  if copy
    return deepcopy(a.basis_mat)
  else
    return a.basis_mat
  end
end

function basis_mat_inv(a::AlgAssAbsOrdIdl; copy::Bool = true)
  assure_has_basis_mat_inv(a)
  if copy
    return deepcopy(a.basis_mat_inv)
  else
    return a.basis_mat_inv
  end
end

################################################################################
#
#  Arithmetic
#
################################################################################

function +(a::AlgAssAbsOrdIdl{S, T}, b::AlgAssAbsOrdIdl{S, T}) where {S, T}
  if iszero(a)
    return deepcopy(b)
  elseif iszero(b)
    return deepcopy(a)
  end

  d = degree(order(a))
  M = vcat(basis_mat(a), basis_mat(b))
  M = view(_hnf(M, :lowerleft), (d + 1):2*d, 1:d)
  return ideal(order(a), M, :nothing, true)
end

function *(a::AlgAssAbsOrdIdl{S, T}, b::AlgAssAbsOrdIdl{S, T}) where {S, T}
  if iszero(a)
    return deepcopy(a)
  elseif iszero(b)
    return deepcopy(b)
  end

  if !isright_ideal(a)
    error("First argument is not a right ideal")
  end
  if !isleft_ideal(b)
    error("Second argument is not a left ideal")
  end

  d = degree(order(a))
  ba = basis(a, copy = false)
  bb = basis(b, copy = false)
  M = zero_matrix(FlintZZ, d^2, d)
  for i = 1:d
    for j = 1:d
      t = ba[i]*bb[j]
      for k = 1:d
        M[(i - 1)*d + j, k] = elem_in_basis(t)[k]
      end
    end
  end
  M = view(_hnf(M, :lowerleft), (d^2 - d + 1):d^2, 1:d)
  return ideal(order(a), M, :nothing, true)
end

^(A::AlgAssAbsOrdIdl, e::Int) = Base.power_by_squaring(A, e)
^(A::AlgAssAbsOrdIdl, e::fmpz) = Base.power_by_squaring(A, BigInt(e))

function intersect(a::AlgAssAbsOrdIdl{S, T}, b::AlgAssAbsOrdIdl{S, T}) where {S, T}
  d = degree(order(a))
  H = vcat(basis_mat(a), basis_mat(b))
  K = left_kernel(H)[2]
  return ideal(order(a), _hnf(view(K, 1:d, 1:d)*basis_mat(a, copy = false), :lowerleft), :nothing, true)
end

################################################################################
#
#  Ad hoc multiplication
#
################################################################################

*(x::fmpz, a::AlgAssAbsOrdIdl) = ideal(order(a), x*basis_mat(a, copy = false), :nothing, true)
*(a::AlgAssAbsOrdIdl, x::fmpz) = ideal(order(a), basis_mat(a, copy = false)*x, :nothing, true)

function *(x::AlgAssAbsOrdElem, a::AlgAssAbsOrdIdl)
  @assert parent(x) == order(a)
  @assert isleft_ideal(a)
  O = order(a)
  return ideal(O, x)*a
end

function *(a::AlgAssAbsOrdIdl, x::AlgAssAbsOrdElem)
  @assert parent(x) == order(a)
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
  M = FakeFmpqMat(basis_mat(a, copy = false), deepcopy(x))
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

function ideal(O::AlgAssAbsOrd{S, T}, M::fmpz_mat, side::Symbol = :nothing, M_in_hnf::Bool = false) where {S, T}
  !M_in_hnf ? M = _hnf(M, :lowerleft) : nothing
  a = AlgAssAbsOrdIdl{S, T}(O, M)
  _set_sidedness(a, side)
  return a
end

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

*(O::AlgAssAbsOrd{S, T}, x::AlgAssAbsOrdElem{S, T}) where {S, T} = ideal(O, x, :left)
*(x::AlgAssAbsOrdElem{S, T}, O::AlgAssAbsOrd{S, T}) where {S, T} = ideal(O, x, :right)

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
        #for k = 1:d
        #  M[(i - 1)*d + j, k] = elem_in_basis(t, copy = false)[k]
        #end
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
        #for k = 1:d
        #  M[(i - 1)*d + j, k] = elem_in_basis(t, copy = false)[k]
        #end
      end
    end
    M = sub(_hnf(M, :lowerleft), nrows(M) - d + 1: nrows(M), 1:d)
    return ideal(O, M, action, true)
  end
  error("action should be :left, :right or :twosided")
end

*(A::AlgAssAbsOrdIdl, O::AlgAssAbsOrd) = extend(A, O, :right)
*(O::AlgAssAbsOrd, A::AlgAssAbsOrdIdl) = extend(A, O, :left)

function contract(A::AlgAssAbsOrdIdl, O::AlgAssAbsOrd)
  # Assumes O \subseteq order(A)

  d = degree(O)
  M = basis_mat(O, copy = false)*basis_mat_inv(order(A), copy = false)
  @assert M.den == 1
  H = vcat(basis_mat(A), M.num)
  K = left_kernel(H)[2]
  M = sub(K, 1:d, 1:d)*basis_mat(A, copy = false)
  M = M*basis_mat(order(A), copy = false)*basis_mat_inv(O, copy = false)
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
function _as_ideal_of_smaller_algebra(m::AbsAlgAssMor, I::AlgAssAbsOrdIdl)
  A = domain(m)
  B = codomain(m)
  @assert dim(A) <= dim(B)
  @assert algebra(order(I)) == B
  OA = maximal_order(A)
  OB = maximal_order(B)
  IB = extend(I, OB)
  # Transport OA to B
  M = zero_matrix(FlintZZ, dim(B), dim(B))
  for i = 1:dim(A)
    t = OB(m(elem_in_algebra(basis(OA, copy = false)[i])))
    elem_to_mat_row!(M, i, t)
  end
  # Compute the intersection of M and IB
  H = vcat(M, basis_mat(IB))
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
function _as_order_of_smaller_algebra(m::AbsAlgAssMor, O::AlgAssAbsOrd)
  A = domain(m)
  B = codomain(m)
  @assert dim(A) <= dim(B)
  @assert algebra(O) == B
  OA = maximal_order(A)
  OB = maximal_order(B)
  # Transport OA to B
  M = zero_matrix(FlintZZ, dim(B), dim(B))
  for i = 1:dim(A)
    t = OB(m(elem_in_algebra(basis(OA, copy = false)[i])))
    elem_to_mat_row!(M, i, t)
  end
  # Compute the intersection of M and O (in OB)
  N = basis_mat(O, copy = false)*basis_mat_inv(OB, copy = false)
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

function in(x::AlgAssAbsOrdElem, I::AlgAssAbsOrdIdl)
  el = elem_in_basis(x)
  y = matrix(FlintZZ, 1, length(el), el)
  M1, d =pseudo_inv(I.basis_mat)
  if FakeFmpqMat(y*M1, d).den==1
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

function ==(A::AlgAssAbsOrdIdl, B::AlgAssAbsOrdIdl)
  order(A) != order(B) && return false
  return basis_mat(A, copy = false) == basis_mat(B, copy = false)
end

################################################################################
#
#  Hashing
#
################################################################################

function Base.hash(A::AlgAssAbsOrdIdl, h::UInt)
  return Base.hash(basis_mat(A, copy = false), h)
end

################################################################################
#
#  Idempotents
#
################################################################################

# Algorithm 1.3.2 in Cohen "Advanced Topics in Computational Number Theory"
function idempotents(a::AlgAssAbsOrdIdl, b::AlgAssAbsOrdIdl)
  !(order(a) === order(b)) && error("Parent mismatch")
  O = order(a)
  d = degree(O)
  A = basis_mat(a, copy = false)
  B = basis_mat(b, copy = false)

  C = vcat(A, B)
  H, U = hnf_with_transform(C)

  if H != vcat(identity_matrix(FlintZZ, d), zero_matrix(FlintZZ, d, d))
    error("Ideals are not coprime")
  end

  X = sub(U, 1:1, 1:d)
  XA = X*A
  x = O([ XA[1, i] for i = 1:d ])
  @assert x in a
  y = one(O) - x
  @assert y in b
  return x, y
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

  n = FakeFmpqMat(representation_matrix(B[1]), FlintZZ(1))*bmatinv
  m = numerator(n)
  d = denominator(n)
  for i in 2:length(B)
    n = FakeFmpqMat(representation_matrix(B[i]), FlintZZ(1))*bmatinv
    l = lcm(denominator(n), d)
    if l == d
      m = hcat(m, n.num)
    else
      m = hcat(m*div(l, d), n.num*div(l, denominator(n)))
      d = l
    end
  end
  m = hnf(transpose(m))
  # n is upper right HNF
  m = transpose(sub(m, 1:degree(O), 1:degree(O)))
  b, l = pseudo_inv(m)
  return frac_ideal_type(O)(O, ideal(O, b), l)
end

function isinvertible(a::AlgAssAbsOrdIdl)
  if iszero(a)
    return false, a
  end

  bmata = basis_mat(a, copy = false)

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
