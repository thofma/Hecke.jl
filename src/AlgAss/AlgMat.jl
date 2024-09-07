################################################################################
#
#  Basic field access
#
################################################################################

degree(A::MatAlgebra) = A.degree

dim(A::MatAlgebra) = A.dim

base_ring(A::MatAlgebra{T, S}) where {T, S} = A.base_ring::parent_type(T)

base_ring_type(::Type{MatAlgebra{T, S}}) where {T, S} = parent_type(T)

coefficient_ring(A::MatAlgebra{T, S}) where {T, S} = A.coefficient_ring::base_ring_type(S)

basis(A::MatAlgebra) = A.basis::Vector{elem_type(A)}

has_one(A::MatAlgebra) = true

elem_type(::Type{MatAlgebra{T, S}}) where { T, S } = MatAlgebraElem{T, S}

order_type(::MatAlgebra{QQFieldElem, S}) where { S } = AlgAssAbsOrd{MatAlgebra{QQFieldElem, S}, elem_type(MatAlgebra{QQFieldElem, S})}
order_type(::Type{MatAlgebra{QQFieldElem, S}}) where { S } = AlgAssAbsOrd{MatAlgebra{QQFieldElem, S}, elem_type(MatAlgebra{QQFieldElem, S})}

order_type(::MatAlgebra{T, S}) where { T <: NumFieldElem, S } = AlgAssRelOrd{T, fractional_ideal_type(order_type(parent_type(T))), MatAlgebra{T, S}}
order_type(::Type{MatAlgebra{T, S}}) where { T <: NumFieldElem, S } = AlgAssRelOrd{T, fractional_ideal_type(order_type(parent_type(T))), MatAlgebra{T, S}}

matrix_algebra_type(K::Field) = matrix_algebra_type(typeof(K))

matrix_algebra_type(::Type{T}) where {T <: Field} = MatAlgebra{elem_type(T), dense_matrix_type(elem_type(T))}

# Returns the dimension d of the coefficient_ring of A, so that dim(A) is up to degree(A)^2 * d.
function dim_of_coefficient_ring(A::MatAlgebra)
  if base_ring(A) == coefficient_ring(A)
    return 1
  end
  @assert _base_ring(coefficient_ring(A)) == base_ring(A)
  return dim(coefficient_ring(A))
end

################################################################################
#
#  Commutativity
#
################################################################################

is_commutative_known(A::MatAlgebra) = (A.is_commutative != 0)

@doc raw"""
    is_commutative(A::MatAlgebra) -> Bool

Returns `true` if $A$ is a commutative ring and `false` otherwise.
"""
function is_commutative(A::MatAlgebra)
  if is_commutative_known(A)
    return A.is_commutative == 1
  end
  dcr = dim_of_coefficient_ring(A)
  if degree(A) == 1
    if base_ring(A) isa Field || is_commutative(base_ring(A))
      A.is_commutative = 1
      return true
    end
    A.is_commutative = 2
    return false
  end
  if dim(A) == degree(A)^2*dcr
    A.is_commutative = 2
    return false
  end

  mt = multiplication_table(A, copy = false)
  for i = 1:dim(A)
    for j = i + 1:dim(A)
      if mt[i, j, :] != mt[j, i, :]
        A.is_commutative = 2
        return false
      end
    end
  end
  A.is_commutative = 1
  return true
end

################################################################################
#
#  Basis matrix
#
################################################################################

function assure_has_basis_matrix(A::MatAlgebra)
  if isdefined(A, :basis_matrix)
    return nothing
  end

  d2 = degree(A)^2
  if coefficient_ring(A) == base_ring(A)
    M = zero_matrix(base_ring(A), dim(A), d2)
    for i = 1:dim(A)
      N = matrix(A[i])
      @assert length(N) == d2
      for (j, n) in enumerate(N)
        M[i, j] = n
      end
    end
    A.basis_matrix = M
  else
    dcr = dim_of_coefficient_ring(A)
    M = zero_matrix(base_ring(A), dim(A), d2*dcr)
    for i = 1:dim(A)
      N = matrix(A[i])
      for (j, n) in enumerate(N)
        jj = (j - 1)*dcr
        for k = 1:dcr
          M[i, jj + k] = coefficients(n, copy = false)[k]
        end
      end
    end
    A.basis_matrix = M
  end
  return nothing
end

function basis_matrix(A::MatAlgebra{S, T}; copy::Bool = true) where {S, T}
  assure_has_basis_matrix(A)
  if copy
    return deepcopy(A.basis_matrix)::dense_matrix_type(S)
  else
    return A.basis_matrix::dense_matrix_type(S)
  end
end

function assure_has_basis_matrix_rref(A::MatAlgebra)
  if isdefined(A, :basis_matrix_rref)
    return nothing
  end
  s, R, U = _rref_with_trans(basis_matrix(A, copy = false))
  pivots = _get_pivots_ut(R)
  A.basis_matrix_rref = (R, U, pivots)
  return nothing
end

function basis_matrix_rref(A::MatAlgebra{S, T}) where {S, T}
  assure_has_basis_matrix_rref(A)
  return A.basis_matrix_rref::Tuple{dense_matrix_type(S), dense_matrix_type(S), Vector{Int}}
end

function assure_has_basis_matrix_solve_context(A::MatAlgebra)
  if isdefined(A, :basis_matrix_solve_ctx)
    return nothing
  end
  A.basis_matrix_solve_ctx = solve_init(basis_matrix(A))
  return nothing
end

function basis_matrix_solve_context(A::MatAlgebra{S, T}) where {S, T}
  assure_has_basis_matrix_solve_context(A)
  return A.basis_matrix_solve_ctx
end

################################################################################
#
#  Multiplication Table
#
################################################################################

function assure_has_multiplication_table(A::MatAlgebra{T, S}) where { T, S }
  if isdefined(A, :mult_table)
    return nothing
  end

  d = dim(A)
  de = degree(A)
  mt = Array{T, 3}(undef, d, d, d)
  K = base_ring(A)

  if is_canonical(A) # this is M_n(K)
    cartesiantolinear = LinearIndices((de, de))
    lineartocartesian = CartesianIndices((de, de))
    for i in 1:d
      itup = lineartocartesian[i]
      for j in 1:d
        jtup = lineartocartesian[j]
        k = 0
        if itup[2] == jtup[1]
          k = cartesiantolinear[itup[1], jtup[2]]
        end
        for l in 1:d
          if l == k
            mt[i, j, l] = one(K)
          else
            mt[i, j, l] = zero(K)
          end
        end
      end
    end
    A.mult_table = mt
    return nothing
  end

  B = basis(A)
  for i in 1:d
    for j in 1:d
      mt[i, j, :] = coefficients(B[i] * B[j], copy = false)
    end
  end
  A.mult_table = mt
  return nothing
end

@doc raw"""
    multiplication_table(A::MatAlgebra; copy::Bool = true) -> Array{RingElem, 3}

Given an algebra $A$ this function returns the multiplication table of $A$:
If the function returns $M$ and the basis of $A$ is $e_1,\dots, e_n$ then
it holds $e_i \cdot e_j = \sum_k M[i, j, k] \cdot e_k$.
"""
function multiplication_table(A::MatAlgebra; copy::Bool = true)
  assure_has_multiplication_table(A)
  if copy
    return deepcopy(A.mult_table)
  else
    return A.mult_table
  end
end

denominator_of_structure_constant_table(A::MatAlgebra) =
    denominator_of_multiplication_table(A)

function denominator_of_multiplication_table(A::MatAlgebra)
  get_attribute!(A, :denominator_of_multiplication_table) do
    den = one(ZZ)
    mt = multiplication_table(A)
    d = degree(A)
    for i in 1:d
      for j in 1:d
        for k in 1:d
          den = lcm!(den, den, denominator(mt[i, j, k]))
        end
      end
    end
    return den
  end::ZZRingElem
end

################################################################################
#
#  Construction
#
################################################################################

@doc raw"""
    matrix_algebra(R::Ring, n::Int) -> MatAlgebra

Returns $\mathrm{Mat}_n(R)$.
"""
function matrix_algebra(R::Ring, n::Int)
  A = MatAlgebra{elem_type(R), dense_matrix_type(elem_type(R))}(R)
  n2 = n^2
  A.dim = n2
  A.degree = n
  B = Vector{elem_type(A)}(undef, n2)
  for i = 1:n
    ni = n*(i - 1)
    for j = 1:n
      M = zero_matrix(R, n, n)
      M[j, i] = one(R)
      B[ni + j] = A(M, check = false)
    end
  end
  A.basis = B
  A.one = identity_matrix(R, n)
  A.canonical_basis = 1
  A.is_simple = 1
  A.issemisimple = 1
  return A
end

# Constructs Mat_n(S) as an R-algebra
@doc raw"""
    matrix_algebra(R::Ring, S::NCRing, n::Int) -> MatAlgebra

Returns $\mathrm{Mat}_n(S)$ as an $R$-algebra.
It is assumed that $S$ is an $R$-algebra.
"""
function matrix_algebra(R::Ring, S::NCRing, n::Int)
  A = MatAlgebra{elem_type(R), dense_matrix_type(elem_type(S))}(R, S)
  n2 = n^2
  A.dim = n2*dim(S)
  A.degree = n
  B = Vector{elem_type(A)}(undef, dim(A))
  for k = 1:dim(S)
    n2k = n2*(k - 1)
    for i = 1:n
      ni = n2k + n*(i - 1)
      for j = 1:n
        M = zero_matrix(S, n, n)
        M[j, i] = S[k]
        B[ni + j] = A(M, check = false)
      end
    end
  end
  A.basis = B
  A.one = identity_matrix(S, n)
  A.canonical_basis = 2
  return A
end

@doc raw"""
    matrix_algebra(R::Ring, gens::Vector{<: MatElem}; isbasis::Bool = false)
      -> MatAlgebra

Returns the matrix algebra over $R$ generated by the matrices in `gens`.
If `isbasis` is `true`, it is assumed that the given matrices are an $R$-basis
of this algebra, i. e. that the spanned $R$-module is closed under
multiplication.
"""
function matrix_algebra(R::Ring, gens::Vector{<:MatElem}; isbasis::Bool = false)
  @assert length(gens) > 0
  A = MatAlgebra{elem_type(R), dense_matrix_type(elem_type(R))}(R)
  A.degree = nrows(gens[1])
  A.one = identity_matrix(R, degree(A))
  if isbasis
    A.dim = length(gens)
    bas = Vector{elem_type(A)}(undef, dim(A))
    for i = 1:dim(A)
      bas[i] = A(gens[i]; check = false)
    end
    A.basis = bas
    return A
  end
  A.gens = map(x -> A(x, check = false), gens)

  d = degree(A)
  d2 = degree(A)^2
  span = deepcopy(gens)
  push!(span, identity_matrix(R, d))
  M = zero_matrix(R, max(d2, length(span)), d2) # the maximal possible dimension is d^2
  pivot_rows = zeros(Int, d2)
  new_elements = Set{Int}()
  cur_rank = 0
  for i = 1:length(span)
    cur_rank == d2 ? break : nothing
    new_elt = _add_row_to_rref!(M, reshape(collect(span[i]), :), pivot_rows, cur_rank + 1)
    if new_elt
      push!(new_elements, i)
      cur_rank += 1
    end
  end

  # Build all possible products
  while !isempty(new_elements)
    cur_rank == d2 ? break : nothing
    i = pop!(new_elements)
    b = span[i]

    n = length(span)
    for r = 1:n
      s = b*span[r]
      for l = 1:n
        t = span[l]*s
        new_elt = _add_row_to_rref!(M, reshape(collect(t), :), pivot_rows, cur_rank + 1)
        if !new_elt
          continue
        end
        push!(span, t)
        cur_rank += 1
        push!(new_elements, length(span))
        cur_rank == d2 ? break : nothing
      end
      cur_rank == d2 ? break : nothing
    end
  end

  A.dim = cur_rank
  A.basis_matrix = sub(M, 1:cur_rank, 1:d2)
  bas = Vector{elem_type(A)}(undef, dim(A))
  for i = 1:dim(A)
    N = zero_matrix(R, degree(A), degree(A))
    for j = 1:d
      jd = (j - 1)*d
      for k = 1:d
        N[k, j] = basis_matrix(A, copy = false)[i, jd + k]
      end
    end
    bas[i] = A(N)
  end
  A.basis = bas

  return A
end

@doc raw"""
    matrix_algebra(R::Ring, S::NCRing, gens::Vector{<: MatElem};
                   isbasis::Bool = false)
      -> MatAlgebra

Returns the matrix algebra over $S$ generated by the matrices in `gens` as
an algebra with base ring $R$.
It is assumed $S$ is an algebra over $R$.
If `isbasis` is `true`, it is assumed that the given matrices are an $R$-basis
of this algebra, i. e. that the spanned $R$-module is closed under
multiplication.
"""
function matrix_algebra(R::Ring, S::NCRing, gens::Vector{<:MatElem}; isbasis::Bool = false)
  @assert length(gens) > 0
  A = MatAlgebra{elem_type(R), dense_matrix_type(elem_type(S))}(R, S)
  A.degree = nrows(gens[1])
  A.one = identity_matrix(S, degree(A))
  if isbasis
    A.dim = length(gens)
    bas = Vector{elem_type(A)}(undef, dim(A))
    for i = 1:dim(A)
      bas[i] = A(gens[i])
    end
    A.basis = bas

    return A
  end

  d = degree(A)
  d2 = degree(A)^2
  span = deepcopy(gens)
  push!(span, identity_matrix(S, d))
  dcr = dim(S)
  max_dim = d2*dcr
  M = zero_matrix(R, max(length(gens), max_dim), max_dim)
  pivot_rows = zeros(Int, max_dim)
  new_elements = Set{Int}()
  cur_rank = 0
  v = Vector{elem_type(R)}(undef, max_dim)
  for i = 1:length(span)
    cur_rank == max_dim ? break : nothing
    @assert length(span[i]) == d2
    for (j, s) in enumerate(span[i])
      jj = (j - 1)*dcr
      for k = 1:dcr
        v[jj + k] = coefficients(s, copy = false)[k]
      end
    end
    new_elt = _add_row_to_rref!(M, deepcopy(v), pivot_rows, cur_rank + 1)
    if new_elt
      push!(new_elements, i)
      cur_rank += 1
    end
  end

  # Build all possible products
  while !isempty(new_elements)
    cur_rank == max_dim ? break : nothing
    i = pop!(new_elements)
    b = span[i]

    n = length(span)
    for r = 1:n
      s = b*span[r]
      for l = 1:n
        t = span[l]*s
        @assert length(t) == d2
        for (j, s) in enumerate(t)
          jj = (j - 1)*dcr
          for k = 1:dcr
            v[jj + k] = coefficients(s, copy = false)[k]
          end
        end
        new_elt = _add_row_to_rref!(M, deepcopy(v), pivot_rows, cur_rank + 1)
        if !new_elt
          continue
        end
        push!(span, t)
        cur_rank += 1
        push!(new_elements, length(span))
        cur_rank == max_dim ? break : nothing
      end
      cur_rank == max_dim ? break : nothing
    end
  end

  A.dim = cur_rank
  A.basis_matrix = sub(M, 1:cur_rank, 1:max_dim)
  bas = Vector{elem_type(A)}(undef, dim(A))
  for i = 1:dim(A)
    N = zero_matrix(S, degree(A), degree(A))
    for j = 1:d
      jd = (j - 1)*d
      for k = 1:d
        jkd = (jd + k - 1)*dcr
        t = Vector{elem_type(_base_ring(S))}(undef, dcr)
        for l = 1:dcr
          t[l] = basis_matrix(A, copy = false)[i, jkd + l]
        end
        N[k, j] = S(t)
      end
    end
    bas[i] = A(N)
  end
  A.basis = bas

  return A
end

###############################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, A::MatAlgebra)
  print(io, "Matrix algebra of dimension ", dim(A), " over ", base_ring(A))
end

################################################################################
#
#  Deepcopy
#
################################################################################

function deepcopy_internal(A::MatAlgebra{T, S}, dict::IdDict) where { T, S }
  B = MatAlgebra{T, S}(base_ring(A))
  for x in fieldnames(typeof(A))
    if x != :base_ring x != :coefficient_ring && isdefined(A, x)
      setfield!(B, x, deepcopy_internal(getfield(A, x), dict))
    end
  end
  B.base_ring = A.base_ring
  B.coefficient_ring = A.coefficient_ring
  return B
end

################################################################################
#
#  Inclusion of matrices
#
################################################################################

function _matrix_in_algebra(M::S, A::MatAlgebra{T, S}) where {T, S<:MatElem}
  @assert size(M) == (degree(A), degree(A))
  _, U, pivots = basis_matrix_rref(A)
  # U * basis_matrix(A)[:, pivots] == R[:, pivots] == I, thus
  # U = inv(basis_matrix(A)[:, pivots]). So, for t = M[pivots],
  # summing (t*U)[i]*basis(A)[i] gives back M, for all M in the basis and hence for all M.
  # Note: Unless `isbasis=true` was given in the constructor, basis(A) is already in rref, and U == I.

  if coefficient_ring(A) == base_ring(A)
    ind = CartesianIndices(axes(M))
    t = [M[I] for I in ind[pivots]] # = M[ind[pivots]] if it were supported
  else
    ind = CartesianIndices((dim_of_coefficient_ring(A), axes(M)...))
    t = [coefficients(M[I[2], I[3]]; copy=false)[I[1]] for I in ind[pivots]]
  end
  return t*U
end

function _check_matrix_in_algebra(M::S, A::MatAlgebra{T, S}, ::Val{short} = Val(false)) where {S, T, short}
  if nrows(M) != degree(A) || ncols(M) != degree(A)
    if short
      return false
    end
    return false, zeros(base_ring(A), dim(A))
  end

  d2 = degree(A)^2
  #B = basis_matrix(A, copy = false)
  if coefficient_ring(A) == base_ring(A)
    #tt = zero_matrix(base_ring(A), 1, d2)
    t = Vector{elem_type(base_ring(A))}(undef, d2)
    @assert length(M) == d2
    for (i, m) in enumerate(M)
      t[i] = m
      #tt[1, i] = m
    end
  else
    dcr = dim_of_coefficient_ring(A)
    #tt = zero_matrix(base_ring(A), 1, d2*dcr)
    t = Vector{elem_type(base_ring(A))}(undef, d2 * dcr)
    @assert length(M) == d2
    for (i, m) in enumerate(M)
      ii = (i - 1)*dcr
      for j = 1:dcr
        t[ii + j] = coefficients(m, copy = false)[j]
        #tt[1, ii + j] = coefficients(m, copy = false)[j]
      end
    end
  end
  C = basis_matrix_solve_context(A)
  b, N = can_solve_with_solution(C, t, side = :left)
  if short
    return b
  end
  s = N #[N[1, i] for i in 1:length(N)]
  return b, s
end

################################################################################
#
#  Center
#
################################################################################

function center(A::MatAlgebra{T, S}) where {T, S}
  if isdefined(A, :center)
    return A.center::Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(A))}
  end

  # Unlike for StructureConstantAlgebra, we should cache the centre even if A is commutative
  # since it is of a different type, so A !== center(A)[1].
  # Otherwise center(A)[1] !== center(A)[1] which is really annoying.
  B, mB = StructureConstantAlgebra(A)
  C, mC = center(B)
  mD = compose_and_squash(mB, mC)
  A.center = C, mD

  if isdefined(A, :decomposition)
    idems = elem_type(C)[has_preimage_with_preimage(mC, StoA(one(SS)))[2] for (SS, StoA) in A.decomposition]
    set_attribute!(C, :central_idempotents, idems)
  end

  return C, mD
end

################################################################################
#
#  Conversion to StructureConstantAlgebra
#
################################################################################

function StructureConstantAlgebra(A::MatAlgebra{T, S}) where {T, S}
  K = base_ring(A)
  B = StructureConstantAlgebra(K, multiplication_table(A), coefficients(one(A)))
  B.is_simple = A.is_simple
  B.issemisimple = A.issemisimple
  AtoB = hom(A, B, identity_matrix(K, dim(A)), identity_matrix(K, dim(A)))
  if isdefined(A, :center)
    Z, ZtoA = center(A)
    B.center = (Z, compose_and_squash(AtoB, ZtoA))
  end
  if isdefined(A, :decomposition)
    dec = Tuple{StructureConstantAlgebra{T}, morphism_type(StructureConstantAlgebra{T}, typeof(B))}[]
    for (C, CtoA) in A.decomposition
      CtoB = compose_and_squash(AtoB, CtoA)
      push!(dec, (C, CtoB))
    end
    B.decomposition = dec
  end
  if isdefined(A, :maps_to_numberfields)
    fields_and_maps = Tuple{AbsSimpleNumField, AbsAlgAssToNfAbsMor{typeof(B), elem_type(B)}}[]
    for (K, AtoK) in A.maps_to_numberfields
      BtoK = AbsAlgAssToNfAbsMor(B, K, AtoK.mat, AtoK.imat)
      push!(fields_and_maps, (K, BtoK))
    end
    B.maps_to_numberfields = fields_and_maps
  end
  return B, hom(B, A, identity_matrix(K, dim(A)), identity_matrix(K, dim(A)))
end

################################################################################
#
#  Canonical basis
#
################################################################################

# Checks whether A[(j - 1)*n + i] == E_ij, where E_ij = (e_kl)_kl with e_kl = 1 if i =k and j = l and e_kl = 0 otherwise.
function is_canonical(A::MatAlgebra)
  if A.canonical_basis != 0
    return A.canonical_basis == 1
  end

  if coefficient_ring(A) != base_ring(A)
    A.canonical_basis = 2
    return false
  end

  n = degree(A)
  if dim(A) != n^2
    A.canonical_basis = 2
    return false
  end

  for j = 1:n
    nj = (j - 1)*n
    for i = 1:n
      m = matrix(A[nj + i], copy = false)
      for k = 1:n
        for l = 1:n
          if k == i && l == j
            if !isone(m[k, l])
              A.canonical_basis = 2
              return false
            end
          else
            if !iszero(m[k, l])
              A.canonical_basis = 2
              return false
            end
          end
        end
      end
    end
  end

  A.canonical_basis = 1
  return true
end

################################################################################
#
#  Opposite algebra
#
################################################################################

@attr Tuple{typeof(A), morphism_type(typeof(A), typeof(A))} function opposite_algebra(A::MatAlgebra)
  BA = basis(A)
  d = dim(A)
  K = coefficient_ring(A)
  BAt = [transpose(matrix(a, copy = false)) for a in BA]
  Aop = matrix_algebra(coefficient_ring(A), BAt, isbasis = true)
  return Aop, hom(A, Aop, identity_matrix(K, d), identity_matrix(K, d))
end
