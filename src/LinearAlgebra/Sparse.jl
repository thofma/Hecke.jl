#= basic support for sparse matrices, more Magma style than Julia
  a sparse matrix is a collection (Array) of sparse rows (SmatRow)
  A sparse matrix cannot have 0 rows!
  A SmatRow is a sorted collection of Entries, an entry is a pair
  (column, value)

  The upper_triangular stuff performs very elementary transformations
  until the matrix becomes dense. At this point, the dense bit is extraced and
  converted to an fmpz_mat which is then hnf'ed.
=#  

import Base.push!, Base.max, Nemo.nbits

export Smat, SmatRow, upper_triangular, vcat!, show, sub,
       fmpz_mat, rows, cols, copy, push!, mul, mul!

################################################################################
#
# SmatRow
#
################################################################################

function show{T}(io::IO, A::SmatRow{T})
  println(io, "sparse row ", A.values, A.pos)
end

################################################################################
#
# Smat
#
################################################################################

function Smat(A::fmpz_mat)
  m = Smat{fmpz}()
  m.c = cols(A)
  m.r = 0
  for i=1:rows(A)
    if is_zero_row(A, i)
      continue
    end
    r = SmatRow{fmpz}()
    for j =1:cols(A)
      if A[i,j] != 0
        m.nnz += 1
        push!(r.values, fmpz(A[i,j]))
        push!(r.pos, j)
      end
    end
    push!(m.rows, r)
    m.r += 1
  end
  return m
end

function Smat{T}(A::Array{T, 2})
  m = Smat{T}()
  m.c = Base.size(A, 2)
  m.r = 0
  for i=1:Base.size(A, 1)
    if is_zero_row(A, i)
      continue
    end
    r = SmatRow{T}()
    for j =1:Base.size(A, 2)
      if A[i,j] != 0
        m.nnz += 1
        push!(r.values, T(A[i,j]))
        push!(r.pos, j)
      end
    end
    push!(m.rows, r)
    m.r += 1
  end
  return m
end

function show{T}(io::IO, A::Smat{T})
  println(io, "Sparse ", A.r, " x ", A.c, " matrix with ", A.nnz, " non-zero entries")
end

################################################################################
#  transpose
################################################################################
function transpose{T}(A::Smat{T})
  B = Smat{T}()
  n = rows(A)
  m = cols(A)
  B.rows = Array(SmatRow{T}, m)
  for i=1:m
    B.rows[i] = SmatRow{T}()
  end
  for i = 1:length(A.rows)
    for j = 1:length(A.rows[i].pos)
      r = A.rows[i].pos[j]
      push!(B.rows[r].pos, i)
      push!(B.rows[r].values, A.rows[i].values[j])
    end 
  end
  B.c = n
  B.r = m
  B.nnz = A.nnz

  return B
end

################################################################################
#
# multiplication of Smat * Dense
# for Dense = {Array{T, 1}, Array{T, 2}, fmpz_mat}
# both mul and mul! versions
#
################################################################################
function mul!{T}(c::Array{T, 1}, A::Smat{T}, b::Array{T, 1})
  assert( length(b) == cols(A))
  assert( length(c) == rows(A))
  for i = 1:length(A.rows)
    s = 0
    I = A.rows[i]
    for j=1:length(I.pos)
      s += I.values[j]*b[I.pos[j]]
    end
    c[i] = s
  end
  return c
end

function mul{T}(A::Smat{T}, b::Array{T, 1})
  assert( length(b) == cols(A))
  c = Array(T,rows(A))
  mul!(c, A, b)
  return c
end

function mul!{T}(c::Array{T, 2}, A::Smat{T}, b::Array{T, 2})
  sz = size(b)
  assert( sz[1] == cols(A))
  tz = size(c)
  assert( tz[1] == rows(A))
  assert( tz[2] == sz[2])
  for m = 1:sz[2]
    for i = 1:length(A.rows)
      s = 0
      for j=1:length(A.rows[i].pos)
        s += A.rows[i].values[j]*b[A.rows[i].pos[j], m]
      end
      c[i, m] = s
    end
  end
  return c
end

function mul{T}(A::Smat{T}, b::Array{T, 2})
  sz = size(b)
  assert( sz[1] == cols(A))
  c = Array(T, sz[1], sz[2])
  return mul!(c, A, b)
end

function mul!{T}(c::fmpz_mat, A::Smat{T}, b::fmpz_mat)
  assert( rows(b) == cols(A))
  assert( rows(c) == rows(A))
  assert( cols(c) == cols(b))
  for m = 1:cols(b)
    for i = 1:length(A.rows)
      s = 0
      for j=1:length(A.rows[i].pos)
        s += A.rows[i].values[j]*b[A.rows[i].pos[j], m]
      end
      c[i, m] = s
    end
  end  
  return c
end

function mul{T}(A::Smat{T}, b::fmpz_mat)
  assert( rows(b) == cols(A))
  c = MatrixSpace(ZZ, rows(A), cols(b))()
  return mul!(c, A, b)
end

################################################################################
#
# Basics: sub 
#         vcat! 
#         push! (add a SmatRow to it)
#         getindex -> A[i,j] for reading
#         rows, cols
#         copy
#
################################################################################

function sub{T}(A::Smat{T}, r::UnitRange, c::UnitRange)
  B = Smat{T}()
  B.nnz = 0
  for i=r
    rw = SmatRow{T}()
    ra = A.rows[i]
    for j=1:length(ra.values)
      if ra.pos[j] in c
        push!(rw.values, ra.values[j])
        push!(rw.pos, ra.pos[j]-c.start+1)
      end
    end
    if length(rw.pos)>0
      push!(B.rows, rw)
      B.nnz += length(rw.pos)
    end
  end
  B.r = length(r)
  B.c = length(c)
  return B
end

function copy{T}(A::Smat{T})
  return sub(A, 1:rows(A), 1:cols(A))
end

function rows(A::Smat)
  @assert A.r == length(A.rows)
  return A.r
end

function cols(A::Smat)
  return A.c
end

function getindex{T}(A::Smat{T}, i::Int, j::Int)
  if i in 1:A.r
    ra = A.rows[i]
    p = findfirst(x->x==j, ra.pos)
    if p!= 0
      return ra.values[p]
    end
  end
  return T(0)
end

function getindex{T}(A::Smat{T}, i::Int)
  if i in 1:A.r
    return A.rows[i]
  end
  return SmatRow{T}()
end


function vcat!{T}(A::Smat{T}, B::Smat{T})
  A.r += B.r
  A.c = max(A.c, B.c)
  A.nnz += B.nnz
  A.rows = vcat(A.rows, B.rows)
  @assert length(A.rows) == A.r
end

function push!{T}(A::Smat{T}, B::SmatRow{T})
  if length(B.pos)>0
    push!(A.rows, B)
    A.r += 1
    @assert length(A.rows) == A.r
    A.nnz += length(B.pos)
    A.c = max(A.c, B.pos[end])
  end
end

################################################################################
#
# convert to fmpz_mat
#
################################################################################

function fmpz_mat{T <: Integer}(A::Smat{T})
  B = MatrixSpace(FlintZZ, A.r, A.c)()
  for i = 1:length(A.rows)
    ra = A.rows[i]
    for j = 1:length(ra.pos)
      B[i, ra.pos[j]] = ra.values[j]
    end
  end
  return B
end

function fmpz_mat(A::Smat{fmpz})
  B = MatrixSpace(FlintZZ, A.r, A.c)()
  for i = 1:length(A.rows)
    ra = A.rows[i]
    for j = 1:length(ra.pos)
      B[i, ra.pos[j]] = ra.values[j]
    end
  end
  return B
end


################################################################################
#
# Echelonisation (transform to upper triangular)
#
# inplace operation, uses
#    add_scaled_row!
#    transform_row!
#
################################################################################

# rows j -> row i*c + row j
function add_scaled_row!{T}(A::Smat{T}, i::Int, j::Int, c::T)
  sr = SmatRow{T}()
  pi = 1
  pj = 1
  @assert c != 0
  while pi <= length(A.rows[i].pos) && pj <= length(A.rows[j].pos)
    if A.rows[i].pos[pi] < A.rows[j].pos[pj]
      push!(sr.pos, A.rows[i].pos[pi])
      push!(sr.values, c*A.rows[i].values[pi])
      pi += 1
    elseif A.rows[i].pos[pi] > A.rows[j].pos[pj]
      push!(sr.pos, A.rows[j].pos[pj])
      push!(sr.values, A.rows[j].values[pj])
      pj += 1
    else
      n = c*A.rows[i].values[pi] + A.rows[j].values[pj]
      if n != 0
        push!(sr.pos, A.rows[i].pos[pi])
        push!(sr.values, n)
      end
      pi += 1
      pj += 1
    end
  end
  while pi <= length(A.rows[i].pos)
    push!(sr.pos, A.rows[i].pos[pi])
    push!(sr.values, c*A.rows[i].values[pi])
    pi += 1
  end
  while pj <= length(A.rows[j].pos)
    push!(sr.pos, A.rows[j].pos[pj])
    push!(sr.values, A.rows[j].values[pj])
    pj += 1
  end
  A.nnz = A.nnz - length(A.rows[j].pos) + length(sr.pos)
  A.rows[j] = sr
  return A
end


# row i -> a*row i + b * row j
# row j -> c*row i + d * row j
function transform_row!{T}(A::Smat{T}, i::Int, j::Int, a::T, b::T, c::T, d::T)
  sr = SmatRow{T}()
  tr = SmatRow{T}()
  pi = 1
  pj = 1
  while pi <= length(A.rows[i].pos) && pj <= length(A.rows[j].pos)
    if A.rows[i].pos[pi] < A.rows[j].pos[pj]
      if a != 0
        push!(sr.pos, A.rows[i].pos[pi])
        push!(sr.values, a*A.rows[i].values[pi])
      end
      if c != 0
        push!(tr.pos, A.rows[i].pos[pi])
        push!(tr.values, c*A.rows[i].values[pi])
      end
      pi += 1
    elseif A.rows[i].pos[pi] > A.rows[j].pos[pj]
      if b != 0
        push!(sr.pos, A.rows[j].pos[pj])
        push!(sr.values, b*A.rows[j].values[pj])
      end
      if d != 0
        push!(tr.pos, A.rows[j].pos[pj])
        push!(tr.values, d*A.rows[j].values[pj])
      end
      pj += 1
    else
      m = a*A.rows[i].values[pi] + b*A.rows[j].values[pj]
      n = c*A.rows[i].values[pi] + d*A.rows[j].values[pj]
      if m != 0
        push!(sr.pos, A.rows[i].pos[pi])
        push!(sr.values, m)
      end
      if n != 0
        push!(tr.pos, A.rows[i].pos[pi])
        push!(tr.values, n)
      end
      pi += 1
      pj += 1
    end
  end
  while pi <= length(A.rows[i].pos)
    if a != 0
      push!(sr.pos, A.rows[i].pos[pi])
      push!(sr.values, a*A.rows[i].values[pi])
    end
    if c != 0
      push!(tr.pos, A.rows[i].pos[pi])
      push!(tr.values, c*A.rows[i].values[pi])
    end
    pi += 1
  end
  while pj <= length(A.rows[j].pos)
    if b != 0
      push!(sr.pos, A.rows[j].pos[pj])
      push!(sr.values, b*A.rows[j].values[pj])
    end
    if d != 0
      push!(tr.pos, A.rows[j].pos[pj])
      push!(tr.values, d*A.rows[j].values[pj])
    end
    pj += 1
  end
  A.nnz = A.nnz - length(A.rows[j].pos) + length(sr.pos) - length(A.rows[i].pos) + length(tr.pos)
  A.rows[i] = sr
  A.rows[j] = tr
  @assert i<j

  return A
end

function max(A::Smat{Int})
  m = abs(A.rows[1].values[1])
  for i in A.rows
    for j in i.values
      m = max(m, abs(j))
    end
  end
  return m
end

function max(A::Smat{BigInt})
  m = abs(A.rows[1].values[1])
  for i in A.rows
    for j in i.values
      if ccall((:__gmpz_cmpabs, :libgmp), Int, (Ptr{BigInt}, Ptr{BigInt}),
        &m, &j) < 0
        m = j
      end
    end
  end
  return abs(m)
end

function max(A::Smat{fmpz})
  m = abs(A.rows[1].values[1])
  for i in A.rows
    for j in i.values
      if cmpabs(m, j) < 0
        m = j
      end
    end
  end
  return abs(m)
end

function nbits(a::BigInt)
  return ndigits(a, 2)
end

function nbits(a::Int)
  a==0 && return 0
  return Int(ceil(log(abs(a))/log(2)))
end

function one_step{T}(A::Smat{T}, sr = 1)
  i = sr
  all_r = Array(Int, 0)
  min = A.c
  while i <= length(A.rows)
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
  if all_r[1] > sr
    q = A.rows[sr]
    A.rows[sr] = A.rows[all_r[1]]
    A.rows[all_r[1]] = q
    all_r[1] = sr
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
    else
      g,a,b = gcdx(x, y)
#      @assert g == a*x + b*y
      c = -div(y, g)
#      @assert y == -c*g
      d = div(x, g)
#      @assert x == d*g
      transform_row!(A, sr, all_r[j], a, b, c, d)
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
#  println("in one step: ilog2(max) now ", nbits(max(A)), " j:", j, " length: ", length(all_r))
  end
  for j=length(all_r):-1:2
    if length(A.rows[all_r[j]].pos) == 0
      deleteat!(A.rows, all_r[j])
      A.r -= 1
    end
  end
  return sr+1
end

function upper_triangular{T}(A::Smat{T}; mod = 0)
  for i = 1:min(rows(A), cols(A))
    x = one_step(A, i)
#    println("after one step: ilog2(max) now ", nbits(max(A)))
    if x>A.r
      return
    end
    if A.nnz > (A.r-i) * (A.c-i) /2 || max(A) > T(2)^200
#      println("calling hnf at level ", i)
      h = sub(A, i:A.r, i:A.c)
      deleteat!(A.rows, i:A.r)
      A.r -= length(i:A.r)
      @assert length(A.rows) == A.r
      h = fmpz_mat(h)
#      println("calling dense hnf on a ", rows(h), " by ", cols(h), " matrix")
      if mod==0
        h = hnf(h)
      else
        h = nmod_mat(mod, h)
        rref!(h)
        h = Array(lift(h))
      end
      h = Smat(h)
      for j in h.rows
        rw = SmatRow{T}()
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

