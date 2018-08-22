# this is the old upper triangular code

function one_step(A::SMat{T}, sr = 1) where T
  i = sr
  assert(i>0)
  all_r = Array{Int}(undef, 0)
  min = A.c
  while i <= length(A.rows)
    @assert length(A.rows[i].pos)>0
    @assert A.rows[i].pos[1] >= sr
    if A.rows[i].pos[1] < min
      min = A.rows[i].pos[1]
      all_r = [i]
    elseif A.rows[i].pos[1] == min
      push!(all_r, i)
    end
    i += 1
  end

  if length(all_r) == 0
    return A.r+1
  end
#  println("found multiple $(length(all_r)) possibilities of weight $([length(A.rows[_i].pos) for _i in all_r])")
  #sorting
  sort!(all_r, lt=function(a,b) return length(A.rows[a].pos) < length(A.rows[b].pos)end)
#  println("found multiple $(length(all_r)) possibilities of weight $([length(A.rows[_i].pos) for _i in all_r])")
  # we need to have rows[all_r[1]] == sr, so that the new pivot will be in
  # row sr

  if !(sr in all_r)
    q = A.rows[sr]
    A.rows[sr] = A.rows[all_r[1]]
    A.rows[all_r[1]] = q
    all_r[1] = sr
  else
    p = findfirst(all_r, sr)
    if p > 1
      q = A.rows[sr]
      A.rows[sr] = A.rows[all_r[1]]
      A.rows[all_r[1]] = q
      all_r[p] = all_r[1]
      all_r[1] = sr
    end
  end
  if length(all_r) == 1
    return sr+1
  end

  for j=2:length(all_r)
    x = A.rows[sr].values[1]
    y = A.rows[all_r[j]].values[1]
    g = x
    @assert x!= 0
    if y % x == 0
      c = -div(y, x)
#      @assert x*c == -y
      add_scaled_row!(A, sr, all_r[j], c)
      @assert !iszero(A[sr])
    else
      g,a,b = gcdx(x, y)
#      @assert g == a*x + b*y
      c = -div(y, g)
#      @assert y == -c*g
      d = div(x, g)
#      @assert x == d*g
      transform_row!(A, sr, all_r[j], a, b, c, d)
      @assert !iszero(A[sr])
    end

#    @assert A.rows[sr].entry[1]valuesval == g
#    @assert A.rows[sr].entry[1].val != 0
#    if length(A.rows[all_r[j]].entry) == 0 ||
#             A.rows[all_r[j]].entry[1].col > min
#    else
#      println("bad", x, " and ", y, " in ", sr, ", ", all_r[j])
#      println("min: ", min)
#    end

#    @assert length(A.rows[all_r[j]].entry) == 0 ||
#             A.rows[all_r[j]].entry[1].col > min
#  println("in one step: ilog2(max) now ", nbits(maximum(abs, A)), " j:", j, " length: ", length(all_r))
  end
  sort!(all_r)
  for j=length(all_r):-1:2
    if iszero(A.rows[all_r[j]])
      deleteat!(A.rows, all_r[j])
      A.r -= 1
    end
  end
  return sr+1
end

Markdown.doc"""
  upper_triangular{T}(A::SMat{T}; mod = 0)

  Inplace: transform A into an upper triangular matrix. If mod
  is non-zero, reduce entries modulo mod during the computation.
"""
function upper_triangular(A::SMat{T}; mod = 0) where T
  for i = 1:min(rows(A), cols(A))
    x = one_step(A, i)
#    println("after one step: ilog2(max) now ", nbits(maximum(abs, A)))
    if x>A.r
      return
    end
    if A.nnz > (A.r-i) * (A.c-i) /2 || nbits(maximum(abs, A)) > 200
      #println("calling  at level ", i, " bits: ", nbits(maximum(abs, A)), "nnz: ", A.nnz)
      h = sub(A, i:A.r, i:A.c)
      deleteat!(A.rows, i:A.r)
      A.r -= length(i:A.r)
      @assert length(A.rows) == A.r
      h = fmpz_mat(h)
      #println("calling dense hnf on a ", rows(h), " by ", cols(h), " matrix")
      if mod==0
        h = hnf(h)
      else
        h = nmod_mat(mod, h)
        rref!(h)
        h = Array(lift(h))
      end
      h = SMat(h)
      for j in h.rows
        rw = SRow{T}()
        for e in 1:length(j.pos)
          push!(rw.pos, j.pos[e] + i-1)
          push!(rw.values, j.values[e])
        end
        push!(A.rows, rw)
        A.r += 1
      end

      return
    end
  end
  return
end

################################################################################
#
#  One echelonization step w/o transformations
#
################################################################################

# Perform one step in the echelonization, that is, find a pivot and clear
# elements below.
# sr = starting row
function _one_step(A::SMat{T}, sr = 1) where T
  nr, trafo = _one_step_with_trafo(A, sr)
  return nr
end

function _one_step_with_trafo(A::SMat{T}, sr = 1) where T
  trafos = Trafo[]
  i = sr
  assert(i>0)
  all_r = Array{Int}(undef, 0)
  min = A.c

  while i <= length(A.rows)
    @assert length(A.rows[i].pos)>0
    @assert A.rows[i].pos[1] >= sr
    if A.rows[i].pos[1] < min
      min = A.rows[i].pos[1]
      all_r = [i]
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
    push!(trafos, TrafoSwap{T}(sr, all_r[1]))
    q = A.rows[sr]
    A.rows[sr] = A.rows[all_r[1]]
    A.rows[all_r[1]] = q
    all_r[1] = sr
  else
    p = findfirst(all_r, sr)
    if p > 1
      push!(trafos, TrafoSwap{T}(sr, all_r[1]))

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
      push!(trafos, TrafoDeleteZero{T}(all_r[j]))
      A.r -= 1
    end
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
  return _SMat(hdense, R = R)
end

function echelonize_via_dense_with_trafo(h::SMat{fmpz})
  hdense = fmpz_mat(h)
  # echelonize
  hdense, U = hnf_with_transform(hdense)
  # put back into sparse matrix
  h = _SMat(hdense, zerorows = true)
  return h, U
end

function echelonize_via_dense(h::SMat{fmpz})
  hdense = fmpz_mat(h)
  # echelonize
  hdense = hnf(hdense)
  # put back into sparse matrix
  h = _SMat(hdense)
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
  return TrafoAddScaled(i, j, c)
end

function echelonize_basecase!(x::fmpz, y::fmpz, i::Int, j::Int,
                              A::Hecke.SMat{fmpz})
  if y % x == 0
    c = -div(y, x)
    add_scaled_row!(A, i, j, c)
    return TrafoAddScaled(i, j, c)
  else
    g,a,b = gcdx(x, y)
    c = -div(y, g)
    d = div(x, g)
    Hecke.transform_row!(A, i, j, a, b, c, d)
    return TrafoParaAddScaled(i, j, a, b, c, d)
  end
end

################################################################################
#
#  Echelonization for sparse matrices
#
################################################################################

# there is some density limit at level i, at which dense echelonization
# will be invoked
function upper_triangular_with_trafo!(M::SMat, density_limit::Float64 = 0.5)
  f = (A, i) -> (A.nnz > (A.r-i) * (A.c-i) * density_limit)
  return _upper_triangular_with_trafo!(M, f)
end

function upper_triangular_with_trafo!(M::SMat{fmpz},
                                      density_limit::Float64 = 0.5,
                                      size_limit::Int = 200)
  f =  (A, i) -> (A.nnz > (A.r-i) * (A.c-i) * density_limit || nbits(maximum(abs, A)) > size_limit)
  return _upper_triangular_with_trafo!(M, f)
end

# is_dense_enough is a function (::SMat{T}, i::Int) -> Bool
# At each level i, is_dense_enough(A, i) is called.
# If it evaluates to true, then dense echelonization will be called.
function _upper_triangular_with_trafo!(A::SMat{T}, is_dense_enough::Function) where T
  trafo = Trafo[]

  for i = 1:min(rows(A), cols(A))
    x, t = _one_step_with_trafo(A, i)
    append!(trafo, t)

    if x > A.r
      return trafo
    end

    if is_dense_enough(A, i)
      h = sub(A, i:A.r, i:A.c)

      h, U = echelonize_via_dense_with_trafo(h)

      # h will have zero rows

      push!(trafo, TrafoPartialDense(i, i:A.r, i:A.c, U))

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
        A.r -= 1
        push!(trafo, TrafoDeleteZero{T}(k))
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
  for i = 1:min(rows(A), cols(A))
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

function _snf_upper_triangular_with_trafo(A::SMat{fmpz})
  # We assume that A is quadratic and upper triangular
  essential_index = 1

  for i in 1:rows(A)
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
      push!(trafos_right, TrafoAddScaled(j, i, -a))
    end
  end

  essential_part = fmpz_mat(sub(A, essential_index:rows(A), essential_index:cols(A)))

  snfofess, ltr, rtr = snf_with_transform(essential_part, true, true)

  push!(trafos_left, TrafoPartialDense(essential_index, essential_index:rows(A), essential_index:cols(A), ltr))
  push!(trafos_right, TrafoPartialDense(essential_index, essential_index:rows(A), essential_index:cols(A), rtr))

  return snfofess, trafos_left, trafos_right
end

Markdown.doc"""
    elementary_divisors(A::SMat{fmpz}) -> Array{fmpz, 1}

> The elementary divisors of $A$, ie. the diagonal elements of the Smith normal
> form of $A$. $A$ needs to be of full rank - currently.
"""
function elementary_divisors(A::SMat{fmpz})
  A = copy(A)
  upper_triangular(A)

  essential_index = 1

  for i in 1:rows(A)
    @assert A.rows[i].pos[1] == i
    if A.rows[i].values[1] != 1 
      essential_index = i
      break
    end
  end

  essential_part = fmpz_mat(sub(A, essential_index:rows(A), essential_index:cols(A)))

  s = snf(essential_part)

  return vcat(fmpz[1 for i=1:essential_index-1], fmpz[s[i,i] for i=1:rows(s)]) 
end
