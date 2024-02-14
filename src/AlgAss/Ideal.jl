@doc raw"""
    algebra(a::AbsAlgAssIdl) -> AbstractAssociativeAlgebra

Returns the algebra containing $a$.
"""
algebra(a::AbsAlgAssIdl) = a.algebra

iszero(a::AbsAlgAssIdl) = (a.iszero == 1)

###############################################################################
#
#  String I/O
#
###############################################################################

function show(io::IO, a::AbsAlgAssIdl)
  print(io, "Ideal of ")
  print(io, algebra(a))
  println(io, " with basis matrix")
  print(io, basis_matrix(a, copy = false))
end

################################################################################
#
#  Deepcopy
#
################################################################################

function Base.deepcopy_internal(a::AbsAlgAssIdl, dict::IdDict)
  b = typeof(a)(algebra(a))
  for i in fieldnames(typeof(a))
    if isdefined(a, i)
      if i != :algebra
        setfield!(b, i, Base.deepcopy_internal(getfield(a, i), dict))
      end
    end
  end
  return b
end

################################################################################
#
#  Basis (matrices)
#
################################################################################

function assure_has_basis(a::AbsAlgAssIdl)
  if isdefined(a, :basis)
    return nothing
  end

  A = algebra(a)
  M = basis_matrix(a, copy = false)
  a.basis = Vector{elem_type(A)}(undef, nrows(M))
  for i = 1:nrows(M)
    a.basis[i] = elem_from_mat_row(A, M, i)
  end
  return nothing
end

@doc raw"""
    basis(a::AbsAlgAssIdl; copy::Bool = true) -> Vector{AbstractAssociativeAlgebraElem}

Returns the basis of $a$.
"""
function basis(a::AbsAlgAssIdl; copy::Bool = true)
  assure_has_basis(a)
  if copy
    return deepcopy(a.basis)
  else
    return a.basis
  end
end

@doc raw"""
    basis_matrix(a::AbsAlgAssIdl; copy::Bool = true) -> MatElem

Returns the basis matrix of $a$ with respect to the basis of the algebra.
"""
function basis_matrix(a::AbsAlgAssIdl; copy::Bool = true)
  if copy
    return deepcopy(a.basis_matrix)
  else
    return a.basis_matrix
  end
end

################################################################################
#
#  Inclusion of elements in ideals
#
################################################################################

@doc raw"""
    in(x::AbstractAssociativeAlgebraElem, a::AbsAlgAssIdl) -> Bool

Returns `true` if $x$ is an element of $a$ and `false` otherwise.
"""
function in(x::T, a::AbsAlgAssIdl{S, T, U}) where {S, T, U}
  A = algebra(a)
  M = matrix(base_ring(A), 1, dim(A), coefficients(x, copy = false))
  return rank(vcat(basis_matrix(a, copy = false), M)) == nrows(basis_matrix(a, copy = false)) # so far we assume nrows(basis_matrix) == rank(basis_matrix)
end

################################################################################
#
#  Test right/left
#
################################################################################

function _test_ideal_sidedness(a::AbsAlgAssIdl, side::Symbol)
  A = algebra(a)
  ba = basis(a, copy = false)
  t = A()
  for i = 1:dim(A)
    for j = 1:length(ba)
      if side == :left
        t = mul!(t, A[i], ba[j])
      elseif side == :right
        t = mul!(t, ba[j], A[i])
      else
        error("side must be either :left or :right")
      end
      if !(t in a)
        return false
      end
    end
  end
  return true
end

@doc raw"""
    is_right_ideal(a::AbsAlgAssIdl) -> Bool
    is_right_ideal(a::AlgAssAbsOrdIdl) -> Bool
    is_right_ideal(a::AlgAssRelOrdIdl) -> Bool

Returns `true` if $a$ is a right ideal and `false` otherwise.
"""
function is_right_ideal(a::Union{ AbsAlgAssIdl, AlgAssAbsOrdIdl, AlgAssRelOrdIdl })
  if a.isright == 1
    return true
  elseif a.isright == 2
    return false
  end

  if _test_ideal_sidedness(a, :right)
    a.isright = 1
    return true
  end

  a.isright = 2
  return false
end

@doc raw"""
    is_left_ideal(a::AbsAlgAssIdl) -> Bool
    is_left_ideal(a::AlgAssAbsOrdIdl) -> Bool
    is_left_ideal(a::AlgAssRelOrdIdl) -> Bool

Returns `true` if $a$ is a left ideal and `false` otherwise.
"""
function is_left_ideal(a::Union{ AbsAlgAssIdl, AlgAssAbsOrdIdl, AlgAssRelOrdIdl })
  if a.isleft == 1
    return true
  elseif a.isleft == 2
    return false
  end

  if _test_ideal_sidedness(a, :left)
    a.isleft = 1
    return true
  end

  a.isleft = 2
  return false
end

################################################################################
#
#  Arithmetic
#
################################################################################

@doc raw"""
    +(a::AbsAlgAssIdl, b::AbsAlgAssIdl) -> AbsAlgAssIdl

Returns $a + b$.
"""
function +(a::AbsAlgAssIdl{S, T, U}, b::AbsAlgAssIdl{S, T, U}) where {S, T, U}
  if iszero(a)
    return deepcopy(b)
  elseif iszero(b)
    return deepcopy(a)
  end

  M = vcat(basis_matrix(a), basis_matrix(b))
  r = rref!(M)
  if r != nrows(M)
    M = sub(M, 1:r, 1:ncols(M))
  end
  return ideal(algebra(a), M; M_in_rref=true)
end

@doc raw"""
    *(a::AbsAlgAssIdl, b::AbsAlgAssIdl) -> AbsAlgAssIdl

Returns $a \cdot b$.
"""
function *(a::AbsAlgAssIdl{S, T, U}, b::AbsAlgAssIdl{S, T, U}) where {S, T, U}
  if iszero(a)
    return deepcopy(a)
  elseif iszero(b)
    return deepcopy(b)
  end

  A = algebra(a)
  ba = basis(a, copy = false)
  bb = basis(b, copy = false)
  M = zero_matrix(base_ring(A), length(ba)*length(bb), dim(A))
  for i = 1:length(ba)
    ii = (i - 1)*length(bb)
    for j = 1:length(bb)
      elem_to_mat_row!(M, ii + j, ba[i]*bb[j])
    end
  end
  return ideal(algebra(a), M)
end

@doc raw"""
    ^(a::AbsAlgAssIdl, e::Union{ Int, ZZRingElem }) -> AbsAlgAssIdl

Returns $a^e$.
"""
^(A::AbsAlgAssIdl, e::Int) = Base.power_by_squaring(A, e)
^(A::AbsAlgAssIdl, e::ZZRingElem) = Base.power_by_squaring(A, BigInt(e))

function one(a::AbsAlgAssIdl)
  A = algebra(a)
  return ideal(A, identity_matrix(base_ring(A), dim(A)); side=:twosided, M_in_rref=true)
end

function Base.copy(a::AbsAlgAssIdl)
  return a
end

function *(x::AbstractAssociativeAlgebraElem, a::AbsAlgAssIdl)
  @assert is_left_ideal(a) "Not a left ideal"
  if iszero(a)
    return deepcopy(a)
  end

  basis_a = basis(a, copy = false)
  return ideal_from_gens(algebra(a), [ x*basis_a[i] for i = 1:length(basis_a) ])
end

function *(a::AbsAlgAssIdl, x::AbstractAssociativeAlgebraElem)
  @assert is_right_ideal(a) "Not a right ideal"
  if iszero(a)
    return deepcopy(a)
  end

  basis_a = basis(a, copy = false)
  return ideal_from_gens(algebra(a), [ basis_a[i]*x for i = 1:length(basis_a) ])
end
################################################################################
#
#  Equality
#
################################################################################

@doc raw"""
    ==(a::AbsAlgAssIdl, b::AbsAlgAssIdl) -> Bool

Returns `true` if $a$ and $b$ are equal and `false` otherwise.
"""
function ==(a::AbsAlgAssIdl, b::AbsAlgAssIdl)
  algebra(a) != algebra(b) && return false
  return basis_matrix(a, copy = false) == basis_matrix(b, copy = false)
end

################################################################################
#
#  Construction
#
################################################################################

@doc raw"""
    ideal_from_gens(A::AbstractAssociativeAlgebra, b::Vector{ <: AbstractAssociativeAlgebraElem},
                    side::Symbol = :nothing)
      -> AbsAlgAssIdl

Returns the ideal of $A$ generated by the elements of `b` as a subspace of $A$.
"""
function ideal_from_gens(A::AbstractAssociativeAlgebra, b::Vector{T}, side::Symbol = :nothing) where { T <: AbstractAssociativeAlgebraElem }
  if length(b) == 0
    M = zero_matrix(base_ring(A), 0, dim(A))
    return ideal(A, M; side, M_in_rref=true)
  end

  @assert parent(b[1]) == A

  M = zero_matrix(base_ring(A), length(b), dim(A))
  for i = 1:length(b)
    elem_to_mat_row!(M, i, b[i])
  end
  return ideal(A, M; side)
end

@doc raw"""
    ideal(A::AbstractAssociativeAlgebra, x::AbstractAssociativeAlgebraElem) -> AbsAlgAssIdl

Returns the twosided principal ideal of $A$ generated by $x$.
"""
function ideal(A::AbstractAssociativeAlgebra, x::AbstractAssociativeAlgebraElem)
  t1 = A()
  t2 = A()
  M = zero_matrix(base_ring(A), dim(A)^2, dim(A))
  for i = 1:dim(A)
    t1 = mul!(t1, A[i], x)
    ii = (i - 1)*dim(A)
    for j = 1:dim(A)
      t2 = mul!(t2, t1, A[j])
      elem_to_mat_row!(M, ii + j, t2)
    end
  end

  return ideal(A, M; side=:twosided)
end

@doc raw"""
    ideal(A::AbstractAssociativeAlgebra, x::AbstractAssociativeAlgebraElem, action::Symbol) -> AbsAlgAssIdl

Returns the ideal $x \cdot A$ if `action == :left`, and $A \cdot x$ if
`action == :right`.
"""
function ideal(A::AbstractAssociativeAlgebra, x::AbstractAssociativeAlgebraElem, action::Symbol)
  M = representation_matrix(x, action)
  a = ideal(A, M)

  if action == :left
    a.isright = 1
  elseif action == :right
    a.isleft = 1
  end

  return a
end

@doc raw"""
    *(A::AbstractAssociativeAlgebra, x::AbstractAssociativeAlgebraElem) -> AbsAlgAssIdl
    *(x::AbstractAssociativeAlgebraElem, A::AbstractAssociativeAlgebra) -> AbsAlgAssIdl

Returns the ideal $A \cdot x$ or $x \cdot A$ respectively.
"""
*(A::AbstractAssociativeAlgebra, x::AbstractAssociativeAlgebraElem) = ideal(A, x, :right)
*(x::AbstractAssociativeAlgebraElem, A::AbstractAssociativeAlgebra) = ideal(A, x, :left)

@doc raw"""
    ideal(A::AbstractAssociativeAlgebra, M::MatElem; side::Symbol = :nothing, M_in_rref::Bool = false)
      -> AbsAlgAssIdl

Returns the ideal of $A$ with basis matrix $M$.
If the ideal is known to be a right/left/twosided ideal of $A$, `side` may be
set to `:right`/`:left`/`:twosided` respectively.
If `M_in_rref == true`, it is assumed that $M$ is already in row reduced echelon
form.
"""
function ideal(A::AbstractAssociativeAlgebra, M::MatElem; side::Symbol = :nothing, M_in_rref::Bool = false)
  @assert base_ring(M) == base_ring(A)
  @assert ncols(M) == dim(A)
  if !M_in_rref
    r, N = rref(M)
    if r == 0
      a = AbsAlgAssIdl{typeof(A), typeof(M)}(A, zero_matrix(base_ring(A), 0, dim(A)))
      a.iszero = 1
      return a
    end
    if r != nrows(N)
      M = sub(N, 1:r, 1:ncols(N))
    else
      M = N
    end
  end
  if M_in_rref && nrows(M) == 0
    a = AbsAlgAssIdl{typeof(A), typeof(M)}(A, M)
    a.iszero = 1
    return a
  end

  a = AbsAlgAssIdl{typeof(A), typeof(M)}(A, M)
  _set_sidedness(a, side)
  a.iszero = 2
  return a
end

# Helper function to set the side-flags
# side can be :right, :left or :twosided
function _set_sidedness(a::Union{ AbsAlgAssIdl, AlgAssAbsOrdIdl, AlgAssRelOrdIdl }, side::Symbol)
  if side == :right
    a.isleft = 0
    a.isright = 1
  elseif side == :left
    a.isleft = 1
    a.isright = 0
  elseif side == :twosided
    a.isleft = 1
    a.isright = 1
  else
    a.isleft = 0
    a.isright = 0
  end
  return nothing
end

################################################################################
#
#  Quotient rings
#
################################################################################

@doc raw"""
    quo(A::AbstractAssociativeAlgebra, a::AbsAlgAssIdl) -> AbstractAssociativeAlgebra, AbsAlgAssMor

Returns the quotient algebra $A/a$ and the projection map $A \to A/a$.
"""
function quo(A::S, a::AbsAlgAssIdl{S, T, U}) where { S, T, U }
  @assert A == algebra(a)
  K = base_ring(A)

  # First compute the vector space quotient
  Ma = basis_matrix(a, copy = false)
  M = hcat(deepcopy(transpose(Ma)), identity_matrix(K, dim(A)))
  r = rref!(M)
  pivot_cols = Vector{Int}()
  j = 1
  for i = 1:ncols(M)
    if !iszero(M[j, i])
      if i > nrows(Ma)
        push!(pivot_cols, i - nrows(Ma))
      end
      j += 1
      if j > nrows(M)
        break
      end
    end
  end

  # We now have the basis (basis of the quotient, basis of the ideal)
  n = dim(A) - nrows(Ma)
  M = vcat(zero_matrix(K, n, dim(A)), Ma)
  oneK = K(1)
  zeroK = K()
  for i = 1:n
    M[i, pivot_cols[i]] = oneK
  end
  iM = inv(M)

  N = sub(M, 1:n, 1:dim(A))
  NN = sub(iM, 1:dim(A), 1:n)

  # Lift a basis of the quotient to A
  quotient_basis = Vector{elem_type(A)}(undef, n)
  b = zero_matrix(K, 1, n)
  for i = 1:n
    b[1, i] = oneK
    bN = b*N
    quotient_basis[i] = A([ bN[1, i] for i = 1:dim(A) ])
    b[1, i] = zeroK
  end

  # Build the multiplication table
  t = A()
  s = zero_matrix(K, 1, dim(A))
  mult_table = Array{elem_type(K), 3}(undef, n, n, n)
  for i = 1:n
    for j = 1:n
      t = mul!(t, quotient_basis[i], quotient_basis[j])
      elem_to_mat_row!(s, 1, t)
      sNN = s*NN
      mult_table[i, j, :] = [ sNN[1, k] for k = 1:n ]
    end
  end

  B = StructureConstantAlgebra(K, mult_table)
  AtoB = hom(A, B, NN, N)
  return B, AtoB
end

# Assumes b \subseteq a
@doc raw"""
    quo(a::AbsAlgAssIdl, b::AbsAlgAssIdl) -> AbstractAssociativeAlgebra, AbsAlgAssMor

Given ideals $b \subseteq a$, this function returns the quotient algebra $a/b$
and the projection map $a \to a/b$.
"""
function quo(a::AbsAlgAssIdl{S, T, U}, b::AbsAlgAssIdl{S, T, U}) where { S, T, U }
  @assert algebra(a) == algebra(b)
  A = algebra(a)
  K = base_ring(A)

  # First compute the vector space quotient
  Ma = basis_matrix(a, copy = false)
  Mb = basis_matrix(b, copy = false)
  M = hcat(deepcopy(transpose(Mb)), deepcopy(transpose(Ma)))
  r = rref!(M)
  pivot_cols = Vector{Int}()
  j = 1
  for i = 1:ncols(M)
    if !iszero(M[j, i])
      if i > nrows(Mb)
        push!(pivot_cols, i - nrows(Mb))
      end
      j += 1
      if j > nrows(M)
        break
      end
    end
  end

  # Build the basis matrix for the quotient
  n = nrows(Ma) - nrows(Mb)
  M = zero_matrix(K, n, dim(A))
  for i = 1:n
    for j = 1:dim(A)
      M[i, j] = deepcopy(Ma[pivot_cols[i], j])
    end
  end

  # Lift a basis of the quotient to A
  quotient_basis = Vector{elem_type(A)}(undef, n)
  b = zero_matrix(K, 1, n)
  for i = 1:n
    b[1, i] = one(K)
    bM = b*M
    quotient_basis[i] = A([ bM[1, j] for j in 1:dim(A) ])
    b[1, i] = zero(K)
  end

  # Another basis matrix for a: basis of the quotient + basis of b
  N = vcat(M, Mb)

  # Build the multiplication table
  t = A()
  s = zero_matrix(K, 1, dim(A))
  mult_table = Array{elem_type(K), 3}(undef, n, n, n)
  for i = 1:n
    for j = 1:n
      t = mul!(t, quotient_basis[i], quotient_basis[j])
      elem_to_mat_row!(s, 1, t)
      y = solve(N, s, side = :left)
      mult_table[i, j, :] = [ y[1, k] for k = 1:n ]
    end
  end

  B = StructureConstantAlgebra(K, mult_table)

  AtoB = AbsAlgAssMor{typeof(A), typeof(B), typeof(M)}(A, B)

  function _image(x::AbstractAssociativeAlgebraElem)
    t, y = can_solve_with_solution(N, matrix(K, 1, dim(A), coefficients(x, copy = false)), side = :left)
    if t
      return B([ y[1, i] for i in 1:dim(B) ])
    else
      error("Element is not in the domain")
    end
  end

  function _preimage(x::AbstractAssociativeAlgebraElem)
    t = zero_matrix(K, 1, dim(B))
    for i = 1:dim(B)
      t[1, i] = x.coeffs[i]
    end
    tt = t*M
    return A([ tt[1, i] for i in 1:dim(A) ])
  end

  AtoB.header.image = _image
  AtoB.header.preimage = _preimage
  return B, AtoB
end

################################################################################
#
#  Random elements
#
################################################################################

# TODO: implement for ::Type{AbsAlgAssIdl}
Random.gentype(a::AbsAlgAssIdl) = elem_type(algebra(a))

function rand(rng::AbstractRNG, a_sp::Random.SamplerTrivial{<:AbsAlgAssIdl})
  a = a_sp[]
  A = algebra(a)
  x = A()
  for b in basis(a, copy = false)
    x += rand(rng, base_ring(A))*b
  end
  return x
end

function rand(a::AbsAlgAssIdl, rng::AbstractUnitRange{Int})
  A = algebra(a)
  x = A()
  for b in basis(a, copy = false)
    x += rand(base_ring(A), rng)*b
  end
  return x
end

################################################################################
#
#  Reduction of element modulo ideal
#
################################################################################

function mod(x::AbstractAssociativeAlgebraElem, a::AbsAlgAssIdl)
  if iszero(a)
    return deepcopy(x)
  end

  c = coefficients(x)
  M = basis_matrix(a, copy = false) # Assumed to be in upper right rref
  k = 1
  for i = 1:nrows(M)
    while iszero(M[i, k])
      k += 1
    end
    if iszero(c[k])
      continue
    end

    t = divexact(c[k], M[i, k])
    for j = k:dim(algebra(a))
      c[j] = c[j] - t*M[i, j]
    end
  end
  return algebra(a)(c)
end

################################################################################
#
#  Principal generators (in full matrix algebras)
#
################################################################################

function left_principal_generator(a::AbsAlgAssIdl{S, T, U}) where { S <: MatAlgebra, T, U }
  @assert is_left_ideal(a) "Not a left ideal"
  A = algebra(a)
  if dim(A) != degree(A)^2*dim_of_coefficient_ring(A)
    error("Only implemented for full matrix algebras")
  end

  if is_canonical(A)
    e11 = A[1]
  else
    t = zero_matrix(coefficient_ring(A), degree(A), degree(A))
    t[1, 1] = one(coefficient_ring(A))
    e11 = A(t)
    t[1, 1] = zero(coefficient_ring(A))
  end
  ea = e11*a

  x = A()
  for i = 1:length(basis(ea, copy = false))
    if is_canonical(A)
      ei1 = A[i]
    else
      t[i, 1] = one(coefficient_ring(A))
      ei1 = A(t)
      t[i, 1] = zero(coefficient_ring(A))
    end
    x += ei1*basis(ea, copy = false)[i]
  end
  return x
end

function right_principal_generator(a::AbsAlgAssIdl{S, T, U}) where { S <: MatAlgebra, T, U }
  @assert is_right_ideal(a) "Not a right ideal"
  A = algebra(a)
  if dim(A) != degree(A)^2*dim_of_coefficient_ring(A)
    error("Only implemented for full matrix algebras")
  end

  if is_canonical(A)
    e11 = A[1]
  else
    t = zero_matrix(coefficient_ring(A), degree(A), degree(A))
    t[1, 1] = one(coefficient_ring(A))
    e11 = A(t)
    t[1, 1] = zero(coefficient_ring(A))
  end
  ae = a*e11

  x = A()
  for i = 1:length(basis(ae, copy = false))
    if is_canonical(A)
      e1i = A[(i - 1)*degree(A) + 1]
    else
      t[1, i] = one(coefficient_ring(A))
      e1i = A(t)
      t[1, i] = zero(coefficient_ring(A))
    end
    x += basis(ae, copy = false)[i]*e1i
  end
  return x
end
