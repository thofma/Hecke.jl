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

export Smat, SmatRow, Entry, upper_triangular, vcat!, show, sub,
       fmpz_mat, rows, cols, copy, push!

################################################################################
#
# Entry
#
################################################################################

type Entry{T}
  col::Int
  val::T
  function Entry(c,v)
    @assert v != 0
    r = new()
    r.col = c
    r.val = v
    return r
  end
end

function show(io::IO, E::Entry)
  print(io, E.col, "->", E.val)
end

################################################################################
#
# SmatRow
#
################################################################################

type SmatRow{T}  ## terrible memory footprint!
  entry::Array{Entry{T}, 1}  # should be sorted by 1st entry
  function SmatRow()
    r = new()
    r.entry = Array(Entry{T}, 0)
    return r
  end

  function SmatRow(A::Array{Tuple{Int, T}, 1})
    r = new()
    r.entry = [Entry{T}(x[1], x[2]) for x in A]
    return r
  end

  function SmatRow(A::Array{Tuple{Int, Int}, 1})
    r = new()
    r.entry = [Entry{T}(x[1], T(x[2])) for x in A]
    return r
  end
end

function show{T}(io::IO, A::SmatRow{T})
  println(io, "sparse row ", A.entry)
end

################################################################################
#
# Smat
#
################################################################################

type Smat{T}
  r::Int
  c::Int
  rows::Array{SmatRow{T}, 1}
  nnz::Int

  function Smat()
    r = new()
    r.rows = Array(SmatRow{T}, 0)
    r.nnz = 0
    r.r = 0
    r.c = 0
    return r
  end
end

function Smat(A::fmpz_mat)
  m = Smat{BigInt}()
  m.c = cols(A)
  m.r = 0
  for i=1:rows(A)
    if is_zero_row(A, i)
      continue
    end
    r = SmatRow{BigInt}()
    for j =1:cols(A)
      if A[i,j] != 0
        m.nnz += 1
        push!(r.entry, Entry{BigInt}(j, A[i,j]))
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
        push!(r.entry, Entry{T}(j, A[i,j]))
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
    for j=A.rows[i].entry
      if j.col in c
        push!(rw.entry, Entry{T}(j.col-c.start+1, j.val))
      end
    end
    if length(rw.entry)>0
      push!(B.rows, rw)
      B.nnz += length(rw.entry)
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
    for h in A.rows[i].entry
      if h.col == j
        return h.val
      end
    end
  end
  return T(0)
end

function vcat!{T}(A::Smat{T}, B::Smat{T})
  A.r += B.r
  A.c = max(A.c, B.c)
  A.nnz += B.nnz
  A.rows = vcat(A.rows, B.rows)
  @assert length(A.rows) == A.r
end

function push!{T}(A::Smat{T}, B::SmatRow{T})
  if length(B.entry)>0
    push!(A.rows, B)
    A.r += 1
    @assert length(A.rows) == A.r
    A.nnz += length(B.entry)
    A.c = max(A.c, B.entry[end].col)
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
    for j = 1:length(A.rows[i].entry)
      B[i, A.rows[i].entry[j].col] = A.rows[i].entry[j].val
    end
  end
  return B
end

function fmpz_mat(A::Smat{fmpz})
  B = MatrixSpace(FlintZZ, A.r, A.c)()
  for i = 1:length(A.rows)
    for j = 1:length(A.rows[i].entry)
      B[i, A.rows[i].entry[j].col] = A.rows[i].entry[j].val
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
  while pi <= length(A.rows[i].entry) && pj <= length(A.rows[j].entry)
    if A.rows[i].entry[pi].col < A.rows[j].entry[pj].col
      push!(sr.entry, Entry{T}(A.rows[i].entry[pi].col, c*A.rows[i].entry[pi].val))
      pi += 1
    elseif A.rows[i].entry[pi].col > A.rows[j].entry[pj].col
      push!(sr.entry, A.rows[j].entry[pj])
      pj += 1
    else
      n = c*A.rows[i].entry[pi].val + A.rows[j].entry[pj].val
      if n != 0
        push!(sr.entry, Entry{T}(A.rows[i].entry[pi].col, n))
      end
      pi += 1
      pj += 1
    end
  end
  while pi <= length(A.rows[i].entry)
    push!(sr.entry, Entry{T}(A.rows[i].entry[pi].col, c*A.rows[i].entry[pi].val))
    pi += 1
  end
  while pj <= length(A.rows[j].entry)
    push!(sr.entry, A.rows[j].entry[pj])
    pj += 1
  end
  A.nnz = A.nnz - length(A.rows[j].entry) + length(sr.entry)
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
  while pi <= length(A.rows[i].entry) && pj <= length(A.rows[j].entry)
    if A.rows[i].entry[pi].col < A.rows[j].entry[pj].col
      if a != 0
        push!(sr.entry, Entry{T}(A.rows[i].entry[pi].col, a*A.rows[i].entry[pi].val))
      end
      if c != 0
        push!(tr.entry, Entry{T}(A.rows[i].entry[pi].col, c*A.rows[i].entry[pi].val))
      end
      pi += 1
    elseif A.rows[i].entry[pi].col > A.rows[j].entry[pj].col
      if b != 0
        push!(sr.entry, Entry{T}(A.rows[j].entry[pj].col, b*A.rows[j].entry[pj].val))
      end
      if d != 0
        push!(tr.entry, Entry{T}(A.rows[j].entry[pj].col, d*A.rows[j].entry[pj].val))
      end
      pj += 1
    else
      m = a*A.rows[i].entry[pi].val + b*A.rows[j].entry[pj].val
      n = c*A.rows[i].entry[pi].val + d*A.rows[j].entry[pj].val
      if m != 0
        push!(sr.entry, Entry{T}(A.rows[i].entry[pi].col, m))
      end
      if n != 0
        push!(tr.entry, Entry{T}(A.rows[i].entry[pi].col, n))
      end
      pi += 1
      pj += 1
    end
  end
  while pi <= length(A.rows[i].entry)
    if a != 0
      push!(sr.entry, Entry{T}(A.rows[i].entry[pi].col, a*A.rows[i].entry[pi].val))
    end
    if c != 0
      push!(tr.entry, Entry{T}(A.rows[i].entry[pi].col, c*A.rows[i].entry[pi].val))
    end
    pi += 1
  end
  while pj <= length(A.rows[j].entry)
    if b != 0
      push!(sr.entry, Entry{T}(A.rows[j].entry[pj].col, b*A.rows[j].entry[pj].val))
    end
    if d != 0
      push!(tr.entry, Entry{T}(A.rows[j].entry[pj].col, d*A.rows[j].entry[pj].val))
    end
    pj += 1
  end
  A.nnz = A.nnz - length(A.rows[j].entry) + length(sr.entry) - length(A.rows[i].entry) + length(tr.entry)
  A.rows[i] = sr
  A.rows[j] = tr
  @assert i<j

  return A
end

function max(A::Smat{Int})
  m = abs(A.rows[1].entry[1].val)
  for i in A.rows
    for j in i.entry
      m = max(m, abs(j.val))
    end
  end
  return m
end

function max(A::Smat{BigInt})
  m = abs(A.rows[1].entry[1].val)
  for i in A.rows
    for j in i.entry
      if ccall((:__gmpz_cmpabs, :libgmp), Int, (Ptr{BigInt}, Ptr{BigInt}),
        &m, &j.val) < 0
        m = j.val
      end
    end
  end
  return abs(m)
end

function max(A::Smat{fmpz})
  m = abs(A.rows[1].entry[1].val)
  for i in A.rows
    for j in i.entry
      if cmpabs(m, j.val) < 0
        m = j.val
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
    @assert A.rows[i].entry[1].col >= sr
    if A.rows[i].entry[1].col < min
      min = A.rows[i].entry[1].col
      all_r = [i]
    elseif A.rows[i].entry[1].col == min
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
    x = A.rows[sr].entry[1].val
    y = A.rows[all_r[j]].entry[1].val
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

#    @assert A.rows[sr].entry[1].val == g
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
    if length(A.rows[all_r[j]].entry) == 0
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
        for e in j.entry
          push!(rw.entry, Entry{T}(e.col + i-1, e.val))
        end
        push!(A.rows, rw)
        A.r += 1
      end
      return
    end
  end
  return
end

