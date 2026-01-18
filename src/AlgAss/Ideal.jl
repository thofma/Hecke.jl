@doc raw"""
    algebra(a::AbsAlgAssIdl) -> AbstractAssociativeAlgebra

Returns the algebra containing $a$.
"""
algebra(a::AbsAlgAssIdl) = a.algebra

iszero(a::AbsAlgAssIdl) = (a.iszero == 1)

@doc raw"""
    dim(a::AbsAlgAssIdl) -> Int

Return the vector space dimension an ideal.
"""
dim(a::AbsAlgAssIdl) = nrows(basis_matrix(a, copy = false))

ideal_type(::Type{S}) where {S <: AbstractAssociativeAlgebra} = AbsAlgAssIdl{S}

###############################################################################
#
#  String I/O
#
###############################################################################

function show(io::IO, A::AbsAlgAssIdl)
  if is_terse(io)
    print(io, "Ideal")
  else
    io = pretty(io)
    print(io, "Ideal of dimension ", dim(A), " in ")
    print(terse(io), Lowercase(), algebra(A))
  end
end

function show(io::IO, mime::MIME"text/plain", a::AbsAlgAssIdl)
  println(io, "Ideal")
  io = pretty(io)
  println(io, Indent(), "of dimension ", dim(a))
  println(io, "in ", Lowercase(), algebra(a))
  println(io, "with basis matrix")
  print(io, Indent())
  show(io, MIME"text/plain"(), basis_matrix(a, copy = false))
  print(io, Dedent())
  print(io, Dedent())
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
    return Base.copy(a.basis)::Vector{elem_type(algebra(a))}
  else
    return a.basis::Vector{elem_type(algebra(a))}
  end
end

@doc raw"""
    basis_matrix(a::AbsAlgAssIdl; copy::Bool = true) -> MatElem

Returns the basis matrix of $a$ with respect to the basis of the algebra.
"""
function basis_matrix(a::AbsAlgAssIdl; copy::Bool = true)
  if copy
    return deepcopy(a.basis_matrix)::dense_matrix_type(base_ring_type(algebra(a)))
  else
    return a.basis_matrix::dense_matrix_type(base_ring_type(algebra(a)))
  end
end

function basis_matrix_solve_context(a::AbsAlgAssIdl)
  if isdefined(a, :basis_matrix_solve_ctx)
    return a.basis_matrix_solve_ctx::Solve.solve_context_type(base_ring(algebra(a)))
  else
    c = Solve.solve_init(basis_matrix(a, copy = false))
    a.basis_matrix_solve_ctx = c
    return c
  end
end

################################################################################
#
#  Inclusion of elements in ideals
#
################################################################################

function in(x, a::AbsAlgAssIdl)
  c = basis_matrix_solve_context(a)
  return can_solve(c, coefficients(x, copy = false); side = :left)
end

function is_subset(a::AbsAlgAssIdl, b::AbsAlgAssIdl)
  return all(in(b), basis(a, copy = false))
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
  for i in 1:dim(A)
    for j in 1:length(ba)
      if side === :left || side === :twosided
        t = mul!(t, A[i], ba[j])
        if !(t in a)
          return false
        end
      elseif side === :right || side === :twosided
        t = mul!(t, ba[j], A[i])
        if !(t in a)
          return false
        end
      else
        error("side must be either :left or :right")
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

function +(a::AbsAlgAssIdl{S}, b::AbsAlgAssIdl{S}) where {S}
  @req algebra(a) === algebra(b) "Ideals must have same algebra"

  if is_zero(a)
    return b
  elseif is_zero(b)
    return a
  end

  M = vcat(basis_matrix(a), basis_matrix(b))
  r = rref!(M)
  if r != nrows(M)
    M = sub(M, 1:r, 1:ncols(M))
  end
  return _ideal_from_matrix(algebra(a), M; M_in_rref=true)
end

function *(a::AbsAlgAssIdl{S}, b::AbsAlgAssIdl{S}) where {S}
  @req algebra(a) === algebra(b) "Ideals must have same algebra"
  if iszero(a)
    return a
  elseif iszero(b)
    return b
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
  return _ideal_from_matrix(algebra(a), M)
end

^(A::AbsAlgAssIdl, e::Int) = Base.power_by_squaring(A, e)
^(A::AbsAlgAssIdl, e::ZZRingElem) = Base.power_by_squaring(A, BigInt(e))

function one(a::AbsAlgAssIdl)
  A = algebra(a)
  return _ideal_from_matrix(A, identity_matrix(base_ring(A), dim(A)); side=:twosided, M_in_rref=true)
end

function Base.copy(a::AbsAlgAssIdl)
  return a
end

function *(x::AbstractAssociativeAlgebraElem, a::AbsAlgAssIdl)
  @assert is_left_ideal(a) "Not a left ideal"
  if iszero(a)
    return a
  end

  basis_a = basis(a, copy = false)
  return _ideal_from_kgens(algebra(a), [ x*basis_a[i] for i = 1:length(basis_a) ])
end

function *(a::AbsAlgAssIdl, x::AbstractAssociativeAlgebraElem)
  @assert is_right_ideal(a) "Not a right ideal"
  if iszero(a)
    return deepcopy(a)
  end

  basis_a = basis(a, copy = false)
  return _ideal_from_kgens(algebra(a), [ basis_a[i]*x for i = 1:length(basis_a) ])
end

################################################################################
#
#  Equality
#
################################################################################

function ==(a::AbsAlgAssIdl, b::AbsAlgAssIdl)
  algebra(a) !== algebra(b) && return false
  return basis_matrix(a, copy = false) == basis_matrix(b, copy = false)
end

function Base.hash(a::AbsAlgAssIdl, h::UInt)
  h = hash(algebra(a), h)
  h = hash(basis_matrix(a, copy = false), h)
  return h
end

################################################################################
#
#  Construction
#
################################################################################

# side is necessary
function ideal(A::AbstractAssociativeAlgebra, b::Vector; side::Symbol)
  @req side in (:left, :right, :twosided) "Side must be :left, :right or :twosided"
  if length(b) == 0
    M = zero_matrix(base_ring(A), 0, dim(A))
    return _ideal_from_matrix(A, M; side, M_in_rref=true)
  end
  B = basis(A)

  kgens = elem_type(A)[]
  for i in 1:length(b)
    for j in 1:dim(A)
      el = b[i]
      if side == :left || side == :twosided
        Bel = B[j] * el
        if side == :twosided
          for k in 1:dim(A)
            push!(kgens, Bel * B[k])
          end
        else
          push!(kgens, Bel)
        end
      end
      if side == :right
        push!(kgens, el * B[j])
      end
    end
  end
  return _ideal_from_kgens(A, kgens; side = side)
end

function _ideal_from_kgens(A::AbstractAssociativeAlgebra, b::Vector{<:AbstractAssociativeAlgebraElem}; side = nothing)
  if length(b) == 0
    M = zero_matrix(base_ring(A), 0, dim(A))
    return _ideal_from_matrix(A, M; side, M_in_rref=true)
  end

  @assert parent(b[1]) == A

  M = zero_matrix(base_ring(A), length(b), dim(A))
  for i = 1:length(b)
    elem_to_mat_row!(M, i, b[i])
  end
  return _ideal_from_matrix(A, M; side)
end

left_ideal(A::AbstractAssociativeAlgebra, x...; kw...) = ideal(A, x...; side = :left, kw...)

right_ideal(A::AbstractAssociativeAlgebra, x...; kw...) = ideal(A, x...; side = :right, kw...)

twosided_ideal(A::AbstractAssociativeAlgebra, x...; kw...) = ideal(A, x...; side = :twosided, kw...)

*(A::AbstractAssociativeAlgebra, x::NCRingElement) = left_ideal(A, x)

*(x::NCRingElement, A::AbstractAssociativeAlgebra) = right_ideal(A, x)

@doc raw"""
    _ideal_from_matrix(A::AbstractAssociativeAlgebra, M::MatElem; side::Symbol = :nothing, M_in_rref::Bool = false)
      -> AbsAlgAssIdl

Returns the ideal of $A$ with basis matrix $M$.
If the ideal is known to be a right/left/twosided ideal of $A$, `side` may be
set to `:right`/`:left`/`:twosided` respectively.
If `M_in_rref == true`, it is assumed that $M$ is already in row reduced echelon
form.
"""
function _ideal_from_matrix(A::AbstractAssociativeAlgebra, M::MatElem; side = nothing, M_in_rref::Bool = false)
  @assert base_ring(M) == base_ring(A)
  @assert ncols(M) == dim(A)
  if !M_in_rref
    r, N = rref(M)
    if r == 0
      a = AbsAlgAssIdl{typeof(A)}(A, zero_matrix(base_ring(A), 0, dim(A)))
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
    a = AbsAlgAssIdl{typeof(A)}(A, M)
    a.iszero = 1
    return a
  end

  a = AbsAlgAssIdl{typeof(A)}(A, M)
  _set_sidedness(a, side)
  a.iszero = 2
  return a
end

# Helper function to set the side-flags
# side can be :right, :left or :twosided
function _set_sidedness(a::Union{ AbsAlgAssIdl, AlgAssAbsOrdIdl, AlgAssRelOrdIdl }, side)
  if side == :right
    a.isleft = 0
    a.isright = 1
  elseif side == :left
    a.isleft = 1
    a.isright = 0
  elseif side == :twosided
    a.isleft = 1
    a.isright = 1
  elseif side === nothing || side === :nothing
    a.isleft = 0
    a.isright = 0
  else
    error("Not a valid side")
  end
  return nothing
end

################################################################################
#
#  Quotient rings
#
################################################################################

@doc raw"""
    quo(A::AbstractAssociativeAlgebra, a::AbsAlgAssIdl)
                                    -> AbstractAssociativeAlgebra, AbsAlgAssMor

Return the quotient algebra $A/a$ and the projection map $A \to A/a$.
"""
function quo(A::S, a::AbsAlgAssIdl{S}) where {S}
  @req A === algebra(a) "Ideal not in the algebra"
  K = base_ring(A)
  d = dim(A)

  # First compute the vector space quotient
  Ma = basis_matrix(a, copy = false)
  M = hcat(transpose(Ma), identity_matrix(K, d))
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
  n = d - nrows(Ma)
  M = vcat(zero_matrix(K, n, d), Ma)
  oneK = one(K)
  zeroK = zero(K)
  for i = 1:n
    M[i, pivot_cols[i]] = oneK
  end
  iM = inv(M)

  N = sub(M, 1:n, 1:d)
  NN = sub(iM, 1:d, 1:n)

  # Lift a basis of the quotient to A
  quotient_basis = Vector{elem_type(A)}(undef, n)
  b = zeros_array(K, n)
  for i = 1:n
    b[i] = oneK
    bN = b*N
    quotient_basis[i] = A(bN; copy = true)
    b[i] = zeroK
  end

  # Build the multiplication table
  t = A()
  s = zeros_array(K, d)
  mult_table = Array{elem_type(K), 3}(undef, n, n, n)
  for i in 1:n
    for j in 1:n
      t = mul!(t, quotient_basis[i], quotient_basis[j])
      sNN = coefficients(t, copy = false) * NN
      mult_table[i, j, :] = sNN
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
function quo(a::AbsAlgAssIdl{S}, b::AbsAlgAssIdl{S}) where {S}
  @req algebra(a) === algebra(b) "Ideals must have same algebra"
  @req is_subset(b, a) "Second ideal must be a subsets of the first ideal"
  @req _test_ideal_sidedness(b, :twosided) "Second ideal must be two-sided"

  A = algebra(a)
  d = dim(A)
  K = base_ring(A)

  # First compute the vector space quotient
  Ma = basis_matrix(a, copy = false)
  Mb = basis_matrix(b, copy = false)
  M = hcat(transpose(Mb), transpose(Ma))
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
  M = zero_matrix(K, n, d)
  for i = 1:n
    for j = 1:d
      M[i, j] = deepcopy(Ma[pivot_cols[i], j])
    end
  end

  # Lift a basis of the quotient to A
  quotient_basis = Vector{elem_type(A)}(undef, n)
  b = zeros_array(K, n)
  for i = 1:n
    b[i] = one(K)
    bM = b*M
    quotient_basis[i] = A(bM; copy = true)
    b[i] = zero(K)
  end

  # Another basis matrix for a: basis of the quotient + basis of b
  N = vcat(M, Mb)

  # Build the multiplication table
  t = A()
  mult_table = Array{elem_type(K), 3}(undef, n, n, n)
  Nctx = solve_init(N)
  for i = 1:n
    for j = 1:n
      t = mul!(t, quotient_basis[i], quotient_basis[j])
      y = solve(Nctx, coefficients(t, copy = false), side = :left)
      mult_table[i, j, :] = view(y, 1:n)
    end
  end

  B = StructureConstantAlgebra(K, mult_table)

  AtoB = AbsAlgAssMor{typeof(A), typeof(B), typeof(M)}(A, B)

  function _image(x::AbstractAssociativeAlgebraElem)
    t, y = can_solve_with_solution(Nctx, coefficients(x, copy = false), side = :left)
    if t
      return B(y[1:dim(B)]; copy = false)
    else
      error("Element is not in the domain")
    end
  end

  function _preimage(x::AbstractAssociativeAlgebraElem)
    tt = coefficients(x, copy = false) * M
    return A(tt; copy = false)
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
#Random.gentype(a::AbsAlgAssIdl) = elem_type(algebra(a))

function RandomExtensions.maketype(I::AbsAlgAssIdl, _)
  return elem_type(algebra(I))
end

function RandomExtensions.make(I::AbsAlgAssIdl, vs...)
  R = base_ring(algebra(I))
  if length(vs) == 1 && elem_type(R) == Random.gentype(vs[1])
    RandomExtensions.Make(I, vs[1]) # forward to default Make constructor
  else
    RandomExtensions.Make(I, make(R, vs...))
  end
end

function rand(rng::AbstractRNG, a_sp::Random.SamplerTrivial{<:Make2{<:NCRingElem, <:AbsAlgAssIdl}})
  a, v = a_sp[][1:end]
  A = algebra(a)
  x = A()
  for b in basis(a, copy = false)
    x = add!(x, rand(rng, v)*b)
  end
  return x
end

rand(rng::AbstractRNG, a::AbsAlgAssIdl, v...) = rand(rng, make(a, v...))

rand(a::AbsAlgAssIdl, v...) = rand(Random.GLOBAL_RNG, a, v...)

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

function left_principal_generator(a::AbsAlgAssIdl{S}) where {S <: MatAlgebra}
  @req is_left_ideal(a) "Not a left ideal"
  A = algebra(a)
  if dim(A) != _matdeg(A)^2*dim_of_coefficient_ring(A)
    error("Only implemented for full matrix algebras")
  end

  if is_canonical(A)
    e11 = A[1]
  else
    t = zero_matrix(coefficient_ring(A), _matdeg(A), _matdeg(A))
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

function right_principal_generator(a::AbsAlgAssIdl{S}) where {S <: MatAlgebra}
  @assert is_right_ideal(a) "Not a right ideal"
  A = algebra(a)
  if dim(A) != _matdeg(A)^2*dim_of_coefficient_ring(A)
    error("Only implemented for full matrix algebras")
  end

  if is_canonical(A)
    e11 = A[1]
  else
    t = zero_matrix(coefficient_ring(A), _matdeg(A), _matdeg(A))
    t[1, 1] = one(coefficient_ring(A))
    e11 = A(t)
    t[1, 1] = zero(coefficient_ring(A))
  end
  ae = a*e11

  x = A()
  for i = 1:length(basis(ae, copy = false))
    if is_canonical(A)
      e1i = A[(i - 1)*_matdeg(A) + 1]
    else
      t[1, i] = one(coefficient_ring(A))
      e1i = A(t)
      t[1, i] = zero(coefficient_ring(A))
    end
    x += basis(ae, copy = false)[i]*e1i
  end
  return x
end

################################################################################
#
#  Maximal ideals of matrix algebras
#
################################################################################

# These are standard results, see for example "Left ideals of matrix rings and
# error-correcting codes":
# Left (right) ideals correspond to subspaces and
# this bijection is dimension presevering. Hence maximal ideals are the same
# as maximal subspaces, with a basis matrix being a generator of the ideal.
# Now turn this into a basis.

@doc raw"""
    maximal_ideal(A::MatAlgebra{FinFieldElem}; side)

Given a full matrix algebra over a finite field, return a maximal right (if
`side == :right`) or left (if `side == :left`) ideal of $A$.
"""
function maximal_ideal(A::MatAlgebra{<:FinFieldElem, <:Any}; side::Symbol)
  n = _matdeg(A)
  F = base_ring(A)
  @req dim(A) == _matdeg(A)^2 "Must be a full matrix algebra"
  n = _matdeg(A)

  M = identity_matrix(F, n)
  M[n, n] = zero(F)
  return ideal(A, M; side = side)
end

@doc raw"""
    maximal_ideal(A::MatAlgebra{FinFieldElem}; side)

Given a full matrix algebra over a finite field, return all maximal right (if
`side == :right`) or left (if `side == :left`) ideals of $A$.
"""
function maximal_ideals(A::MatAlgebra{<:FinFieldElem, <:Any}; side::Symbol)
  # must be full matrix algebra
  n = _matdeg(A)
  F = base_ring(A)
  @req dim(A) == _matdeg(A)^2 "Must be a full matrix algebra"
  res = AbsAlgAssIdl{typeof(A)}[]
  if side == :left
    zrow = zeros_array(F, n)
    t = zero_matrix(F, n, n)
    for M in maximal_subspaces(F, n)
      bas = elem_type(A)[]
      for i in 1:n
        for j in 1:n-1
          # i-th row of t should be j-th row of M
          t[i, :] = M[j, :]
          push!(bas, A(t))
        end
        t[i, :] = zrow
      end
      push!(res, _ideal_from_kgens(A, bas; side = side))
    end
    q = order(F)
    @assert length(res) == divexact(q^n - 1, q - 1)
    return res
  else
    @req side == :right "Side (:$(side)) must be :left or :right."
    zcol = zeros_array(F, n)
    t = zero_matrix(F, n, n)
    for M in maximal_subspaces(F, n)
      bas = elem_type(A)[]
      for j in 1:n
        for i in 1:n-1
          # i-th row of t should be j-th row of M
          t[:, j] = M[i, :]
          push!(bas, A(t))
        end
        t[:, j] = zcol
      end
      push!(res, _ideal_from_kgens(A, bas; side = side))
    end
    q = order(F)
    @assert length(res) == divexact(q^n - 1, q - 1)
    return res
  end
end

################################################################################
#
#  Prime ideals
#
################################################################################

# We could in fact first factor out the Jacobson (= Brown--McCoy since f.d.
# k-algebra) radical and then determine the maximal submodules.
function prime_ideals(A::AbstractAssociativeAlgebra)
  if !is_finite(base_ring(A))
    throw(NotImplemented)
  end
  @vtime :AlgAssOrd 1 lg = gens(A)
  l = length(lg)
  K = base_ring(A)
  lM = dense_matrix_type(K)[ representation_matrix(lg[i]) for i = 1:l]
  append!(lM, dense_matrix_type(K)[ representation_matrix(lg[i], :right) for i = 1:l])
  M = Amodule(lM)
  ls = maximal_submodules(M)
  return ideal_type(A)[_ideal_from_matrix(A, B; side = :twosided) for B in ls]
end
