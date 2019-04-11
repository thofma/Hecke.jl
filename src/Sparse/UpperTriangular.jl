# this is the old upper triangular code

################################################################################
#
#  One echelonization step w/o transformations
#
################################################################################

# Perform one step in the echelonization, that is, find a pivot and clear
# elements below.
# sr = starting row
function _one_step(A::SMat{T}, sr = 1) where T
  nr, trafo = _one_step_with_transform(A, sr)
  return nr
end

function _one_step_with_transform(A::SMat{T}, sr = 1) where T
  trafos = SparseTrafoElem[]
  i = sr
  @assert i > 0
  all_r = Int[]
  min = A.c

  while i <= length(A.rows)
    # if we encounter zero row, push it to the end
    if iszero(A.rows[i])
      deleteat!(A.rows, i)
      push!(A.rows, sparse_row(base_ring(A)))
      push!(trafos, sparse_trafo_move_row(T, i, nrows(A)))
      i += 1
      continue
    end
    @assert length(A.rows[i].pos)>0
    @assert A.rows[i].pos[1] >= sr
    if A.rows[i].pos[1] < min
      min = A.rows[i].pos[1]
      all_r = Int[i]
    elseif A.rows[i].pos[1] == min
      push!(all_r, i)
    end
    i += 1
  end

  if length(all_r) == 0
    return A.r+1, trafos
  end

  #sorting
  sort!(all_r, lt = (a,b) -> (length(A.rows[a].pos) < length(A.rows[b].pos)))
  # we need to have rows[all_r[1]] == sr, so that the new pivot will be in
  # row sr

  if !(sr in all_r)
    push!(trafos, sparse_trafo_swap(T, sr, all_r[1]))
    q = A.rows[sr]
    A.rows[sr] = A.rows[all_r[1]]
    A.rows[all_r[1]] = q
    all_r[1] = sr
  else
    p = something(findfirst(isequal(sr), all_r), 0)
    if p > 1
      push!(trafos, sparse_trafo_swap(T, sr, all_r[1]))

      q = A.rows[sr]
      A.rows[sr] = A.rows[all_r[1]]
      A.rows[all_r[1]] = q

      all_r[p] = all_r[1]
      all_r[1] = sr
    end
  end

  if length(all_r) == 1
    return sr + 1, trafos
  end

  for j = 2:length(all_r)
    x = A.rows[sr].values[1]
    y = A.rows[all_r[j]].values[1]
    t = echelonize_basecase!(x, y, sr, all_r[j], A)
    push!(trafos, t)
  end

  sort!(all_r)

  for j = length(all_r):-1:2
    if length(A.rows[all_r[j]].pos) == 0
      deleteat!(A.rows, all_r[j])
      push!(A.rows, sparse_row(base_ring(A)))
      push!(trafos, sparse_trafo_move_row(T, all_r[j]), nrows(A))
o   end
  end
  return sr + 1, trafos
end

################################################################################
#
#  Echelonization via dense matrix
#
################################################################################

# The echelonization_via_dense must not remove zero rows automatically
function echelonize_via_dense(h::SMat{nmod})
  R = parent(h.rows[1].values[1])
  # turn into dense structure
  hdense = nmod_mat(h)
  # echelonize
  # I need to the following trick since we do not have the transformation
  rref!(hdense)
  # put back into sparse matrix over R (!= base_ring h)
  return sparse_matrix(hdense)
end

function echelonize_via_dense_with_transform(h::SMat{fmpz})
  hdense = matrix(h)
  # echelonize
  hdense, U = hnf_with_transform(hdense)
  # put back into sparse matrix
  h = sparse_matrix(hdense)
  return h, U
end

function echelonize_via_dense(h::SMat{fmpz})
  hdense = matrix(h)
  # echelonize
  hdense = hnf(hdense)
  # put back into sparse matrix
  h = sparse_matrix(hdense)
  return h
end

################################################################################
#
#  Base case of echelonization
#
################################################################################

# Given two rows i, j with entries x, y (x != 0) in the same column, this
# function must produce a zero at entry y.

function echelonize_basecase!(x::T, y::T, i::Int, j::Int, A::Hecke.SMat{T}) where T
  c = -divexact(y, x)
  add_scaled_row!(A, i, j, c)
  return sparse_trafo_addscaled(i, j, c)
end

function echelonize_basecase!(x::fmpz, y::fmpz, i::Int, j::Int,
                              A::Hecke.SMat{fmpz})
  if y % x == 0
    c = -div(y, x)
    add_scaled_row!(A, i, j, c)
    return sparse_trafo_add_scaled(i, j, c)
  else
    g,a,b = gcdx(x, y)
    c = -div(y, g)
    d = div(x, g)
    Hecke.transform_row!(A, i, j, a, b, c, d)
    return sparse_trafo_para_add_scaled(i, j, a, b, c, d)
  end
end

################################################################################
#
#  Echelonization for sparse matrices
#
################################################################################

# there is some density limit at level i, at which dense echelonization
# will be invoked
#

function upper_triangular_with_transform(M::SMat, density_limit = 0.5)
  B = deepcopy(M)
  T = upper_triangular_with_transform!(B, density_limit)
  return B, T
end

function upper_triangular_with_transform!(M::SMat, density_limit::Float64 = 0.5)
  f = (A, i) -> (A.nnz > (A.r-i) * (A.c-i) * density_limit)
  return _upper_triangular_with_transform!(M, f)
end

function upper_triangular_with_transform!(M::SMat{fmpz},
                                      density_limit::Float64 = 0.5,
                                      size_limit::Int = 200)
  f =  (A, i) -> (A.nnz > (A.r-i) * (A.c-i) * density_limit || nbits(maximum(abs, A)) > size_limit)
  return _upper_triangular_with_transform!(M, f)
end

# is_dense_enough is a function (::SMat{T}, i::Int) -> Bool
# At each level i, is_dense_enough(A, i) is called.
# If it evaluates to true, then dense echelonization will be called.
function _upper_triangular_with_transform!(A::SMat{T}, is_dense_enough::Function) where T
  trafo = SparseTrafoElem[]

  for i = 1:min(nrows(A), ncols(A))
    x, t = _one_step_with_transform(A, i)
    append!(trafo, t)

    if x > A.r
      return trafo
    end

    if is_dense_enough(A, i)
      h = sub(A, i:A.r, i:A.c)

      h, U = echelonize_via_dense_with_transform(h)

      # h will have zero rows

      push!(trafo, sparse_trafo_partial_dense(i, i:A.r, i:A.c, U))

      deleteat!(A.rows, i:A.r)
      A.r -= length(i:A.r)
      @assert length(A.rows) == A.r

      # append all rows of h to A
      # including zero rows

      for k in 1:length(h.rows)
        j = h.rows[k]
        if length(j.pos) == 0
          push!(A.rows, SRow{T}())
          A.r += 1
          continue
        end
        rw = SRow{T}()
        for e in 1:length(j.pos)
          push!(rw.pos, j.pos[e] + i - 1)
          push!(rw.values, j.values[e])
        end
        push!(A.rows, rw)
        A.r += 1
      end

      k = A.r

      # Now delete trailing zero rows.
      while length(A.rows[k].pos) == 0
        deleteat!(A.rows, k)
        push!(A.rows, sparse_row(base_ring(A)))
        push!(trafo, sparse_trafo_move_row(T, k, nrows(A)))
        k -= 1
      end

      # I guess I can do something more clever then the following:
      A.nnz = 0
      for r in A.rows
        A.nnz += length(r.pos)
      end

      return trafo
    end
  end
  return trafo
end

# now the same without transformation

function upper_triangular!(M::SMat, density_limit::Float64 = 0.5)
  f = (A, i) -> (A.nnz > (A.r-i) * (A.c-i) * density_limit)
  return _upper_triangular!(M, f)
end

function upper_triangular!(M::SMat{fmpz}, density_limit::Float64 = 0.5, size_limit::Int = 200)
  f =  (A, i) -> (A.nnz > (A.r-i) * (A.c-i) * density_limit || nbits(maximum(abs, A)) > size_limit)
  return _upper_triangular!(M, f)
end

function _upper_triangular!(A::SMat{T}, is_dense_enough) where T
  for i = 1:min(nrows(A), ncols(A))
    x = _one_step(A, i)

    if x>A.r
      return nothing
    end

    if is_dense_enough(A, i)

      h = sub(A, i:A.r, i:A.c)
      deleteat!(A.rows, i:A.r)
      A.r -= length(i:A.r)
      @assert length(A.rows) == A.r

      # make dense matrix
      h = echelonize_via_dense(h)

      for j in h.rows
        rw = SRow{T}()
        for e in 1:length(j.pos)
          push!(rw.pos, j.pos[e] + i - 1)
          push!(rw.values, j.values[e])
        end
        push!(A.rows, rw)
        A.r += 1
      end

      # I guess I can do something more clever then the following:
      A.nnz = 0
      for r in A.rows
        A.nnz += length(r.pos)
      end

      return nothing
    end
  end
  return nothing
end

################################################################################
#
#   Smith normal form
#
################################################################################

function _snf_upper_triangular_with_transform(A::SMat{fmpz})
  # We assume that A is quadratic and upper triangular
  essential_index = 1

  for i in 1:nrows(A)
    @assert A.rows[i].pos[1] == i
    if A.rows[i].values[1] != 1
      essential_index = i
      break
    end
  end

  # Let us pick up the transformations

  trafos_right = []
  trafos_left = []

  for i in 1:essential_index-1
    for (j, a) in zip(A.rows[i].pos, A.rows[i].values)
      if j == i
        continue
      end
      push!(trafos_right, sparse_trafo_add_scaled(j, i, -a))
    end
  end

  essential_part = fmpz_mat(sub(A, essential_index:nrows(A), essential_index:ncols(A)))

  snfofess, ltr, rtr = snf_with_transform(essential_part, true, true)

  push!(trafos_left, sparse_trafo_partial_dense(essential_index, essential_index:nrows(A), essential_index:ncols(A), ltr))
  push!(trafos_right, sparse_trafo_partial_dense(essential_index, essential_index:nrows(A), essential_index:ncols(A), rtr))

  return snfofess, trafos_left, trafos_right
end

@doc Markdown.doc"""
    elementary_divisors(A::SMat{fmpz}) -> Array{fmpz, 1}

The elementary divisors of $A$, ie. the diagonal elements of the Smith normal
form of $A$. $A$ needs to be of full rank - currently.
"""
function elementary_divisors(A::SMat{fmpz})
  A = copy(A)
  upper_triangular(A)

  essential_index = 1

  for i in 1:nrows(A)
    @assert A.rows[i].pos[1] == i
    if A.rows[i].values[1] != 1 
      essential_index = i
      break
    end
  end

  essential_part = fmpz_mat(sub(A, essential_index:nrows(A), essential_index:ncols(A)))

  s = snf(essential_part)

  return vcat(fmpz[1 for i=1:essential_index-1], fmpz[s[i,i] for i=1:nrows(s)]) 
end
