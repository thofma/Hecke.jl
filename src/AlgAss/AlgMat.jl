export matrix_algebra

################################################################################
#
#  Basic field access
#
################################################################################

degree(A::AlgMat) = A.degree

dim(A::AlgMat) = A.dim

base_ring(A::AlgMat{T, S}) where {T, S} = A.base_ring::parent_type(T)

coefficient_ring(A::AlgMat) = A.coefficient_ring

basis(A::AlgMat) = A.basis

has_one(A::AlgMat) = true

elem_type(A::AlgMat{T, S}) where { T, S } = AlgMatElem{T, AlgMat{T, S}, S}

elem_type(::Type{AlgMat{T, S}}) where { T, S } = AlgMatElem{T, AlgMat{T, S}, S}

order_type(::AlgMat{fmpq, S}) where { S } = AlgAssAbsOrd{AlgMat{fmpq, S}, elem_type(AlgMat{fmpq, S})}
order_type(::Type{AlgMat{fmpq, S}}) where { S } = AlgAssAbsOrd{AlgMat{fmpq, S}, elem_type(AlgMat{fmpq, S})}

order_type(::AlgMat{T, S}) where { T <: NumFieldElem, S } = AlgAssRelOrd{T, fractional_ideal_type(order_type(parent_type(T))), AlgMat{T, S}}
order_type(::Type{AlgMat{T, S}}) where { T <: NumFieldElem, S } = AlgAssRelOrd{T, fractional_ideal_type(order_type(parent_type(T))), AlgMat{T, S}}

matrix_algebra_type(K::Field) = matrix_algebra_type(typeof(K))

matrix_algebra_type(::Type{T}) where {T <: Field} = AlgMat{elem_type(T), dense_matrix_type(elem_type(T))}

# Returns the dimension d of the coefficient_ring of A, so that dim(A) = degree(A)^2 + d.
function dim_of_coefficient_ring(A::AlgMat)
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

iscommutative_known(A::AlgMat) = (A.iscommutative != 0)

@doc Markdown.doc"""
    iscommutative(A::AlgMat) -> Bool

Returns `true` if $A$ is a commutative ring and `false` otherwise.
"""
function iscommutative(A::AlgMat)
  if iscommutative_known(A)
    return A.iscommutative == 1
  end
  dcr = dim_of_coefficient_ring(A)
  if dim(A) == degree(A)^2*dcr
    A.iscommutative = 2
    return false
  end

  mt = multiplication_table(A, copy = false)
  for i = 1:dim(A)
    for j = i + 1:dim(A)
      if mt[i, j, :] != mt[j, i, :]
        A.iscommutative = 2
        return false
      end
    end
  end
  A.iscommutative = 1
  return true
end

################################################################################
#
#  Basis matrix
#
################################################################################

function assure_has_basis_matrix(A::AlgMat)
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

function basis_matrix(A::AlgMat{S, T}; copy::Bool = true) where {S, T}
  assure_has_basis_matrix(A)
  if copy
    return deepcopy(A.basis_matrix)::dense_matrix_type(S)
  else
    return A.basis_matrix::dense_matrix_type(S)
  end
end

function assure_has_basis_matrix_rref(A::AlgMat)
  if isdefined(A, :basis_matrix_rref)
    return nothing
  end
  s, R, U = _rref_with_trans(basis_matrix(A, copy = false))
  pivots = _get_pivots_ut(R)
  A.basis_matrix_rref = (R, U, pivots)
  return nothing
end

function basis_matrix_rref(A::AlgMat{S, T}) where {S, T}
  assure_has_basis_matrix_rref(A)
  return A.basis_matrix_rref::Tuple{dense_matrix_type(S), dense_matrix_type(S), Vector{Int}}
end

function assure_has_basis_matrix_transpose_rref(A::AlgMat)
  if isdefined(A, :basis_matrix_transpose_rref)
    return nothing
  end
  s, R, U = _rref_with_trans(transpose(basis_matrix(A, copy = false)))
  pivots = _get_pivots_ut(R)
  A.basis_matrix_transpose_rref = (R, U, pivots)
  return nothing
end

function basis_matrix_transpose_rref(A::AlgMat{S, T}) where {S, T}
  assure_has_basis_matrix_transpose_rref(A)
  return A.basis_matrix_transpose_rref::Tuple{dense_matrix_type(S), dense_matrix_type(S), Vector{Int}}
end

################################################################################
#
#  Multiplication Table
#
################################################################################

function assure_has_multiplication_table(A::AlgMat{T, S}) where { T, S }
  if isdefined(A, :mult_table)
    return nothing
  end

  B = basis(A)
  d = dim(A)
  mt = Array{T, 3}(undef, d, d, d)
  for i in 1:d
    for j in 1:d
      mt[i, j, :] = coefficients(B[i]*B[j], copy = false)
    end
  end
  A.mult_table = mt
  return nothing
end

@doc Markdown.doc"""
    multiplication_table(A::AlgMat; copy::Bool = true) -> Array{RingElem, 3}

Given an algebra $A$ this function returns the multiplication table of $A$:
If the function returns $M$ and the basis of $A$ is $e_1,\dots, e_n$ then
it holds $e_i \cdot e_j = \sum_k M[i, j, k] \cdot e_k$.
"""
function multiplication_table(A::AlgMat; copy::Bool = true)
  assure_has_multiplication_table(A)
  if copy
    return deepcopy(A.mult_table)
  else
    return A.mult_table
  end
end

################################################################################
#
#  Construction
#
################################################################################

@doc Markdown.doc"""
    matrix_algebra(R::Ring, n::Int) -> AlgMat

Returns $\mathrm{Mat}_n(R)$.
"""
function matrix_algebra(R::Ring, n::Int)
  A = AlgMat{elem_type(R), dense_matrix_type(elem_type(R))}(R)
  n2 = n^2
  A.dim = n2
  A.degree = n
  B = Vector{elem_type(A)}(undef, n2)
  for i = 1:n
    ni = n*(i - 1)
    for j = 1:n
      M = zero_matrix(R, n, n)
      M[j, i] = one(R)
      B[ni + j] = A(M)
    end
  end
  A.basis = B
  A.one = identity_matrix(R, n)
  A.canonical_basis = 1
  A.issimple = 1
  A.issemisimple = 1
  return A
end

# Constructs Mat_n(S) as an R-algebra
@doc Markdown.doc"""
    matrix_algebra(R::Ring, S::Ring, n::Int) -> AlgMat

Returns $\mathrm{Mat}_n(S)$ as an $R$-algebra.
It is assumed that $S$ is an $R$-algebra.
"""
function matrix_algebra(R::Ring, S::Ring, n::Int)
  A = AlgMat{elem_type(R), dense_matrix_type(elem_type(S))}(R, S)
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
        B[ni + j] = A(M)
      end
    end
  end
  A.basis = B
  A.one = identity_matrix(S, n)
  A.canonical_basis = 2
  return A
end

@doc Markdown.doc"""
    matrix_algebra(R::Ring, gens::Vector{<: MatElem}; isbasis::Bool = false)
      -> AlgMat

Returns the matrix algebra over $R$ generated by the matrices in `gens`.
If `isbasis` is `true`, it is assumed that the given matrices are an $R$-basis
of this algebra, i. e. that the spanned $R$-module is closed under
multiplication.
"""
function matrix_algebra(R::Ring, gens::Vector{<:MatElem}; isbasis::Bool = false)
  @assert length(gens) > 0
  A = AlgMat{elem_type(R), dense_matrix_type(elem_type(R))}(R)
  A.degree = nrows(gens[1])
  A.one = identity_matrix(R, degree(A))
  if isbasis
    A.dim = length(gens)
    bas = Vector{elem_type(A)}(undef, dim(A))
    for i = 1:dim(A)
      bas[i] = A(gens[i])
    end
    A.basis = bas
    return A
  end
  A.gens = A.(gens)

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

@doc Markdown.doc"""
    matrix_algebra(R::Ring, S::Ring, gens::Vector{<: MatElem};
                   isbasis::Bool = false)
      -> AlgMat

Returns the matrix algebra over $S$ generated by the matrices in `gens` as
an algebra with base ring $R$.
It is assumed $S$ is an algebra over $R$.
If `isbasis` is `true`, it is assumed that the given matrices are an $R$-basis
of this algebra, i. e. that the spanned $R$-module is closed under
multiplication.
"""
function matrix_algebra(R::AbstractAlgebra.NCRing, S::AbstractAlgebra.NCRing, gens::Vector{<:MatElem}; isbasis::Bool = false)
  @assert length(gens) > 0
  A = AlgMat{elem_type(R), dense_matrix_type(elem_type(S))}(R, S)
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

function show(io::IO, A::AlgMat)
  print(io, "Matrix algebra of dimension ", dim(A), " over ", base_ring(A))
end

################################################################################
#
#  Deepcopy
#
################################################################################

function deepcopy_internal(A::AlgMat{T, S}, dict::IdDict) where { T, S }
  B = AlgMat{T, S}(base_ring(A))
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

function _check_matrix_in_algebra(M::S, A::AlgMat{T, S}, short::Type{Val{U}} = Val{false}) where {S, T, U}
  if nrows(M) != degree(A) || ncols(M) != degree(A)
    if short == Val{true}
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
  R, UU, piv = basis_matrix_transpose_rref(A)
  #@show B, tt
  #@show UU
  #@show UU * B == R
  b, N = can_solve_given_rref(R, UU, piv, t)
  #b, N = can_solve_with_solution(B, tt, side = :left)
  #@assert b == bb && NN == [N[1, i] for i in 1:length(N)]
  if short == Val{true}
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

@doc Markdown.doc"""
    center(A::AlgMat) -> AlgAss, AbsAlgAssMor

Returns the center $C$ of $A$ and the inclusion $C \to A$.
"""
function center(A::AlgMat{T, S}) where {T, S}
  if isdefined(A, :center)
    return A.center::Tuple{AlgAss{T}, morphism_type(AlgAss{T}, typeof(A))}
  end

  # Unlike for AlgAss, we should cache the centre even if A is commutative
  # since it is of a different type, so A !== center(A)[1].
  # Otherwise center(A)[1] !== center(A)[1] which is really annoying.
  B, mB = AlgAss(A)
  C, mC = center(B)
  mD = compose_and_squash(mB, mC)
  A.center = C, mD
  return C, mD
end

################################################################################
#
#  Conversion to AlgAss
#
################################################################################

function AlgAss(A::AlgMat{T, S}) where {T, S}
  K = base_ring(A)
  B = AlgAss(K, multiplication_table(A))
  B.issimple = A.issimple
  B.issemisimple = A.issemisimple
  AtoB = hom(A, B, identity_matrix(K, dim(A)), identity_matrix(K, dim(A)))
  if isdefined(A, :center)
    Z, ZtoA = center(A)
    B.center = (Z, compose_and_squash(AtoB, ZtoA))
  end
  if isdefined(A, :decomposition)
    dec = Tuple{AlgAss{T}, morphism_type(AlgAss{T}, typeof(B))}[]
    for (C, CtoA) in A.decomposition
      CtoB = compose_and_squash(AtoB, CtoA)
      push!(dec, (C, CtoB))
    end
    B.decomposition = dec
  end
  if isdefined(A, :maps_to_numberfields)
    fields_and_maps = Tuple{AnticNumberField, AbsAlgAssToNfAbsMor{typeof(B), elem_type(B)}}[]
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
function iscanonical(A::AlgMat)
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

function opposite_algebra(A::AlgMat)
  B, BtoA = AlgAss(A)
  O, BtoO = opposite_algebra(B)
  return O, compose_and_squash(BtoO, inv(BtoA))
end

