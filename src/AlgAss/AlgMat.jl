export matrix_algebra

################################################################################
#
#  Basic field access
#
################################################################################

degree(A::AlgMat) = A.degree

dim(A::AlgMat) = A.dim

base_ring(A::AlgMat) = A.base_ring

coefficient_ring(A::AlgMat) = A.coefficient_ring

basis(A::AlgMat) = A.basis

has_one(A::AlgMat) = true

elem_type(A::AlgMat{T, S}) where { T, S } = AlgMatElem{T, AlgMat{T, S}, S}

elem_type(::Type{AlgMat{T, S}}) where { T, S } = AlgMatElem{T, AlgMat{T, S}, S}

################################################################################
#
#  Basis matrix
#
################################################################################

function assure_has_basis_mat(A::AlgMat)
  if isdefined(A, :basis_mat)
    return nothing
  end

  d2 = degree(A)^2
  if coefficient_ring(A) == base_ring(A)
    M = zero_matrix(base_ring(A), dim(A), d2)
    for i = 1:dim(A)
      N = matrix(A[i])
      for j = 1:d2
        M[i, j] = N[j]
      end
    end
    A.basis_mat = M
  else
    dcr = dim(coefficient_ring(A))
    M = zero_matrix(base_ring(A), dim(A), d2*dcr)
    for i = 1:dim(A)
      N = matrix(A[i])
      for j = 1:d2
        jj = (j - 1)*dcr
        for k = 1:dcr
          M[i, jj + k] = coeffs(N[j], copy = false)[k]
        end
      end
    end
    A.basis_mat = M
  end
  return nothing
end

function basis_mat(A::AlgMat; copy::Bool = true)
  assure_has_basis_mat(A)
  if copy
    return deepcopy(A.basis_mat)
  else
    return A.basis_mat
  end
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
      mt[i, j, :] = coeffs(B[i]*B[j], copy = false)
    end
  end
  A.mult_table = mt
  return nothing
end

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
  return A
end

# Constructs Mat_n(S) as an R-algebra
function matrix_algebra(R::Ring, S::AbsAlgAss, n::Int)
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
  return A
end

function matrix_algebra(R::Ring, gens::Vector{<:MatElem}; check::Bool = true, isbasis::Bool = false)
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
  else
    d = degree(A)
    d2 = degree(A)^2
    span = deepcopy(gens)
    push!(span, identity_matrix(R, d))
    M = zero_matrix(R, max(d2, length(span)), d2) # the maximal possible dimension will is d^2
    pivot_rows = zeros(Int, d2)
    new_elements = Set{Int}()
    cur_rank = 0
    for i = 1:length(span)
      cur_rank == d2 ? break : nothing
      new_elt = _add_row_to_rref!(M, [ span[i][j] for j = 1:d2 ], pivot_rows, cur_rank + 1)
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
          new_elt = _add_row_to_rref!(M, [ t[j] for j = 1:d2 ], pivot_rows, cur_rank + 1)
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
    A.basis_mat = sub(M, 1:cur_rank, 1:d2)
    bas = Vector{elem_type(A)}(undef, dim(A))
    for i = 1:dim(A)
      N = zero_matrix(R, degree(A), degree(A))
      for j = 1:d
        jd = (j - 1)*d
        for k = 1:d
          N[k, j] = basis_mat(A, copy = false)[i, jd + k]
        end
      end
      bas[i] = A(N)
    end
    A.basis = bas
    check = false
  end

  if check
    for i = 1:dim(A)
      for j = 1:dim(A)
        t = basis(A)[i]*basis(A)[j]
        b = _check_matrix_in_algebra(matrix(t), A, Val{true})
        if !b
          error("The elements do not define an algebra")
        end
      end
    end
  end

  return A
end

function matrix_algebra(R::Ring, S::AbsAlgAss, gens::Vector{<:MatElem}; check::Bool = true, isbasis::Bool = false)
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
  else
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
      for j = 1:d2
        jj = (j - 1)*dcr
        for k = 1:dcr
          v[jj + k] = coeffs(span[i][j], copy = false)[k]
        end
      end
      new_elt = _add_row_to_rref!(M, v, pivot_rows, cur_rank + 1)
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
          for j = 1:d2
            jj = (j - 1)*dcr
            for k = 1:dcr
              v[jj + k] = coeffs(t[j], copy = false)[k]
            end
          end
          new_elt = _add_row_to_rref!(M, v, pivot_rows, cur_rank + 1)
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
    A.basis_mat = sub(M, 1:cur_rank, 1:max_dim)
    bas = Vector{elem_type(A)}(undef, dim(A))
    for i = 1:dim(A)
      N = zero_matrix(S, degree(A), degree(A))
      for j = 1:d
        jd = (j - 1)*d
        for k = 1:d
          jkd = (jd + k - 1)*dcr
          t = Vector{elem_type(base_ring(S))}(undef, dcr)
          for l = 1:dcr
            t[l] = basis_mat(A, copy = false)[i, jkd + l]
          end
          N[k, j] = S(t)
        end
      end
      bas[i] = A(N)
    end
    A.basis = bas
    check = false
  end

  if check
    for i = 1:dim(A)
      for j = 1:dim(A)
        t = basis(A)[i]*basis(A)[j]
        b = _check_matrix_in_algebra(matrix(t), A, Val{true})
        if !b
          error("The elements do not define an algebra")
        end
      end
    end
  end

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
#  Equality
#
################################################################################

# So far we don't have a canonical basis
==(A::AlgMat, B::AlgMat) = A === B

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
  B = basis_mat(A, copy = false)
  if coefficient_ring(A) == base_ring(A)
    t = zero_matrix(base_ring(A), 1, d2)
    for i = 1:d2
      t[1, i] = M[i]
    end
  else
    dcr = dim(coefficient_ring(A))
    t = zero_matrix(base_ring(A), 1, d2*dcr)
    for i = 1:d2
      ii = (i - 1)*dcr
      for j = 1:dcr
        t[1, ii + j] = coeffs(M[i], copy = false)[j]
      end
    end
  end
  b, N = can_solve(B, t, side = :left)
  if short == Val{true}
    return b
  end
  s = elem_type(base_ring(A))[ N[1, i] for i = 1:dim(A) ]
  return b, s
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
  return B, hom(B, A, identity_matrix(K, dim(A)), identity_matrix(K, dim(A)))
end
