#= basic support for sparse matrices, more Magma style than Julia
  a sparse matrix is a collection (Array) of sparse rows (SmatRow)
  A sparse matrix cannot have 0 rows!
  A SmatRow is two Arrays, one (pos) containing the columns, values
  contains the values.
  A[i,j] = A.rows[i].values[A.rows[i].pos[j]]
  to be formal

  The upper_triangular stuff performs very elementary transformations
  until the matrix becomes dense. At this point, the dense bit is extraced and
  converted to an fmpz_mat which is then hnf'ed.

  Missing:
   full HNF, Howell, modular and not
   better elemination strategy
=#  

import Base.push!, Base.max, Nemo.nbits, Base.sparse, Base.Array

export upper_triangular, vcat!, show, sub, Smat, SmatRow, random_SmatSLP,
       fmpz_mat, rows, cols, copy, push!, mul, mul!, abs_max, toNemo, sparse,
       valence_mc

################################################################################
#
# SmatRow
#
################################################################################

function show{T}(io::IO, A::SmatRow{T})
  print(io, "sparse row with positions $(A.pos) and values $(A.values)\n")
end

################################################################################
#
# Smat
#
################################################################################
@doc """
  Smat(A::fmpz_mat) -> Smat{fmpz}

  Constructs the Smat (Hecke-sparse matrix) with coefficients fmpz
  corresponding to A.

""" ->
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

@doc """
  Smat{T}(A::Array{T, 2}) -> Smat{T}

  Constructs the Smat (Hecke-sparse matrix) with coefficients of
  type T corresponding to A.

""" ->
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

@doc """
  toNemo(io::IOStream, A::Smat; name = "A")

  Prints the Smat as a julia-program into the file corresponding to io.
  The file can be included to get the matrix.
  "name" controls the variable name of the matrix.
"""->  
function toNemo(io::IOStream, A::Smat; name = "A")
  T = typeof(A.rows[1].values[1])
  println(io, name, " = Smat{$T}()")
  for i=A.rows
    print(io, "push!($(name), SmatRow{$T}(Tuple{Int, $T}[");
    for j=1:length(i.pos)-1
      print(io, "($(i.pos[j]), $(i.values[j])), ")
    end
    println(io, "($(i.pos[end]), $(i.values[end]))]))")
  end
end

@doc """
  toNemo(io::ASCIIString, A::Smat; name = "A")

  Prints the Smat as a julia-program into the file named io.
  The file can be included to get the matrix.
  "name" controls the variable name of the matrix.
"""->  
function toNemo(f::ASCIIString, A::Smat; name = "A")
  io = open(f, "w")
  toNemo(io, A, name=name)
  close(io)
end

################################################################################
#  transpose
################################################################################
@doc """
  transpose{T}(A::Smat{T}) -> Smat{T}

  The transpose of A
""" ->
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

function mul_mod_big!{S, T}(c::Array{S, 1}, A::Smat{T}, b::Array{S, 1}, mod::S)
  assert( length(b) == cols(A))
  assert( length(c) == rows(A))
  for i = 1:length(A.rows)
    s = 0
    I = A.rows[i]
    for j=1:length(I.pos)
      s += S(I.values[j] *b[I.pos[j]] % mod)
    end
    c[i] = s % mod
  end
  return c
end

function mul_mod!{S, T}(c::Array{S, 1}, A::Smat{T}, b::Array{S, 1}, mod::S)
  assert( length(b) == cols(A))
  assert( length(c) == rows(A))
  for i = 1:length(A.rows)
    s = 0
    I = A.rows[i]
    for j=1:length(I.pos)
      s += S(I.values[j]) *b[I.pos[j]]
    end
    c[i] = s % mod
  end
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

function SLP_AddRow{T}(i::Int, j::Int, v::T)
  assert(v != 0)
  slp = SmatSLP(i, j, SLP_AddRow_typ, v)
  return slp
end

#function SLP_SwapRows{T}(i::Int, j::Int)
#  slp = SmatSLP{T}(i, j, SLP_SwapRows_typ, T(0))
#  return slp
#end

function mul!{T}(a::Array{T, 1}, s::SmatSLP{T})
  if s.typ==SLP_AddRow_typ
    a[s.row] = a[s.row]*s.val + a[s.col]
  elseif s.typ==SLP_SwapRows_typ
    t = a[s.row]
    a[s.row] = a[s.col]
    a[s.col] = t
  end
end

function mul_t!{T}(a::Array{T, 1}, s::SmatSLP{T})
  if s.typ==SLP_AddRow_typ
    a[s.col] = a[s.col]*s.val + a[s.row]
  elseif s.typ==SLP_SwapRows_typ
    t = a[s.row]
    a[s.row] = a[s.col]
    a[s.col] = t
  end
end

function apply!{T}(a::Array{T}, b::Array{SmatSLP{T}, 1})
  for i=length(b):-1:1
    mul!(a, b[i])
  end
  return a
end

function apply_t!{T}(a::Array{T}, b::Array{SmatSLP{T}, 1})
  for i=1:length(b)
    mul_t!(a, b[i])
  end
  return a
end

function random_SmatSLP{T}(A::Smat{T}, i::Int, v::UnitRange)
  a = Array(SmatSLP{Int}, i)
  for j=1:i
    c = rand(v)
    while c==0
      c = rand(v)
    end
    i1 = rand(1:rows(A))
    i2 = rand(1:rows(A))
    while i1==i2
      i1 = rand(1:rows(A))
      i2 = rand(1:rows(A))
    end
    a[j] = SLP_AddRow(i1, i2, Int(c))
  end
  return a
end

@doc """
  valence_mc{T}(A::Smat{T}; extra_prime = 2, trans = Array{SmatSLP{T}, 1}()) -> T

  Uses a Monte-Carlo alorithm to  compute the valence of A. The valence is the vaence of the minimal polynomial f of A'*A, thus the last non-zero coefficient,
  typically f(0).

  The valence is computed modulo various primes until the computation
  stabilises for extra_prime many.

  trans, if given, is  a SLP (straight-line-program) in GL(n, Z). Then
  the valence of trans * A  is computed instead.
""" ->
function valence_mc{T}(A::Smat{T}; extra_prime = 2, trans = Array{SmatSLP{T}, 1}())
  # we work in At * A (or A * At) where we choose the smaller of the 2
  # matrices
  if false && cols(A) > rows(A)
    At = A
    A = transpose(A)
  else
    At = transpose(A)
  end
  if abs_max(A) > 2^20
    mm = mul_mod_big!
    println("mul big case")
  else
    mm = mul_mod!
    println("mul small case")
  end
  c1 = Array(Int, cols(A))
  c2 = Array(Int, rows(A))

  for i=1:cols(A)
    c1[i] = Int(rand(-10:10))
  end

  c = copy(c1) ## need the starting value for the other primes as well

  p = next_prime(2^30)
  k = FiniteField(p)
  d = 10
  v = Array{typeof(k(1)), 1}()
  push!(v, k(c1[1]))
  while true
    while length(v) <= d
      mm(c2, A, c1, p)
      if length(trans) >0
        apply_t!(c2, trans)
        apply!(c2, trans)
      end
      mm(c1, At, c2, p)
      push!(v, k(c1[1]))
    end
    fl, f = berlekamp_massey(v)
    if !fl || degree(f) > div(d, 2)-1
      d += 10
      continue
    end
    df = degree(f)
    println("Poly degree is $df, dims $(rows(A)) x $(cols(A))")

    V = fmpz(leading_coefficient(f))
    pp = fmpz(p)
      
    v = Array(typeof(k(1)), 2*degree(f)+1)
    while true
      p = next_prime(p)
      println(p)
      k = FiniteField(p)
      copy!(c1, c)
      v[1] = k(c1[1])
      @time for i=1:2*degree(f)
        mm(c2, A, c1, p)
        if length(trans) >0
          apply_t!(c2, trans)
          apply!(c2, trans)
        end
        mm(c1, At, c2, p)
        v[i+1] = k(c1[1])
      end
      @time fl, f = berlekamp_massey(v)
      if !fl || degree(f) > df
        println("initial guess was wrong...")
        d += 10
        return -1
      end

      Vn = crt(V, pp, fmpz(leading_coefficient(f)), fmpz(p))
      pp *= p
      if 2*Vn > pp
        Vn = Vn - pp
      end
      if Vn == V
        extra_prime -= 1
        if extra_prime == 0
          return V
        end
      end
      V = Vn
    end
  end
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
@doc """
  fmpz_mat{T <: Integer}(A::Smat{T})

  The same matix A, but as an fmpz_mat.
  Requires a conversion from type T to fmpz.
""" ->
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

@doc """
  fmpz_mat(A::Smat{fmpz})

  The same matix A, but as an fmpz_mat.
""" ->
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
# convert to Julia
#
################################################################################
@doc """
  sparse{T}(A::Smat{T}) -> sparse{T}

  The same matrix, but as a julia-sparse matrix
""" ->
function sparse{T}(A::Smat{T})
  I = Array(Int, A.nnz)
  J = Array(Int, A.nnz)
  V = Array(T, A.nnz)
  i = 1
  for r = 1:rows(A)
    for j=1:length(A.rows[r].pos)
      I[i] = r
      J[i] = A.rows[r].pos[j]
      V[i] = A.rows[r].values[j]
      i += 1
    end
  end
  return sparse(I, J, V)
end

@doc """
  Array{T}(A::Smat{T}) -> Array{T, 2}

  The same matrix, but as a two-dimensional julia-Array.
""" ->
function Array{T}(A::Smat{T})
  R = Array(T, A.r, A.c)
  for i=1:rows(A)
    for j=1:length(A.rows[i].pos)
      R[i,A.rows[i].pos[j]] = A.rows[i].values[j]
    end
  end
  return R
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
@doc """
  add_scaled_row!{T}(A::Smat{T}, i::Int, j::Int, c::T)

  adds, inplace, the c*i-th row to the j-th
""" ->
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
@doc """
  transform_row!{T}(A::Smat{T}, i::Int, j::Int, a::T, b::T, c::T, d::T)

  Inplace, replaces the i-th row and the j-th row by
  [a,b; c,d] * [i-th-row ; j-th row]
""" ->        
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

function abs_max(A::Smat{Int})
  m = abs(A.rows[1].values[1])
  for i in A.rows
    for j in i.values
      m = max(m, abs(j))
    end
  end
  return m
end

function abs_max(A::Smat{BigInt})
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

@doc """
  abs_max(A::Smat{Int}) -> Int
  abs_max(A::Smat{BigInt}) -> BigInt
  abs_max(A::Smat{fmpz}) -> fmpz

  Finds the largest, in absolute value, entry of A
""" ->
function abs_max(A::Smat{fmpz})
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

@doc """
  nbits(a::Int) -> Int
  nbits(a::BigInt) -> Int

  Returns the number of bits necessary to represent a
""" ->
function nbits(a::Int)
  a==0 && return 0
  return Int(ceil(log(abs(a))/log(2)))
end

function one_step{T}(A::Smat{T}, sr = 1)
  i = sr
  assert(i>0)
  all_r = Array(Int, 0)
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
  sort!(all_r)
  for j=length(all_r):-1:2
    if length(A.rows[all_r[j]].pos) == 0
      deleteat!(A.rows, all_r[j])
      A.r -= 1
    end
  end
  return sr+1
end

@doc """
  upper_triangular{T}(A::Smat{T}; mod = 0)

  Inplace: transform A into an upper triangular matrix. If mod
  is non-zero, reduce entries modulo mod during the computation.
""" ->
function upper_triangular{T}(A::Smat{T}; mod = 0)
  for i = 1:min(rows(A), cols(A))
    x = one_step(A, i)
#    println("after one step: ilog2(max) now ", nbits(max(A)))
    if x>A.r
      return
    end
    if A.nnz > (A.r-i) * (A.c-i) /2 || nbits(abs_max(A)) > 200
#      println("calling hnf at level ", i, " bits: ", nbits(abs_max(A)), "nnz: ", A.nnz)
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

function sparsity{T}(A::Smat{T})
  return A.nnz/(A.r * A.c), nbits(abs_max(A))
end
  
