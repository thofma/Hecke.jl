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

   abs_max -> maxabs according to Julia

  TODO: sort out the various upper_triangular implementations.
  One (+one with trafo) is probably enough
=#

import Base.push!, Base.max, Nemo.nbits, Base.sparse, Base.Array, 
       Base.endof, Base.start, Base.done, Base.next, Base.hcat,
       Base.vcat

export upper_triangular, vcat!, show, sub, Smat, SmatRow, random_SmatSLP,
       fmpz_mat, rows, cols, copy, push!, mul, mul!, abs_max, toNemo, sparse,
       valence_mc, swap_rows!, endof, start, done, next, elementary_divisors,
       randrow, hcat, hcat!, vcat, vcat!, mod!, mod_sym!

################################################################################
#
#  Base rings for sparse matrices
#
################################################################################

# This doesn't work for empty sparse matrices.
# The ring should actually be put into the type.
base_ring(A::Smat) = parent(A.rows[1].values[1])
base_ring(A::SmatRow) = parent(A.values[1])

=={T}(x::SmatRow{T}, y::SmatRow{T}) = (x.pos == y.pos) && (x.values == y.values)
=={T}(x::Smat{T}, y::Smat{T}) = x.rows == y.rows
################################################################################
#
#  SmatRow
#
################################################################################

function show{T}(io::IO, A::SmatRow{T})
  print(io, "sparse row with positions $(A.pos) and values $(A.values)\n")
end


function hash{T}(A::SmatRow{T}, h::UInt)
  return hash(A.pos, hash(A.values, h))
end

function hash{T}(A::Smat{T}, h::UInt)
  return hash(A.r, hash(A.c, hash(A.rows, h)))
end

function iszero{T}(A::SmatRow{T})
  return length(A.pos) == 0
end
################################################################################
#
#  Smat
#
################################################################################

doc"""
    Smat(A::fmpz_mat) -> Smat{fmpz}

>  Constructs the Smat (Hecke-sparse matrix) with coefficients fmpz
>  corresponding to A.
"""
function Smat(A::fmpz_mat)
  m = Smat{fmpz}()
  m.c = cols(A)
  m.r = 0
  for i=1:rows(A)
    if iszero_row(A, i)
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

doc"""
    Smat{T}(A::Array{T, 2}) -> Smat{T}

> Constructs the Smat (Hecke-sparse matrix) with coefficients of
> type T corresponding to A.
"""
function Smat{T}(A::Array{T, 2})
  m = Smat{T}()
  m.c = Base.size(A, 2)
  m.r = 0
  for i=1:Base.size(A, 1)
    if iszero_row(A, i)
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

################################################################################
#
#  Sparse matrix from dense (with more options)
#
################################################################################

# The the entries of the sparse matrix will be elements of the ring R
# It defaults to the base ring of the input matrix.
# If zerorows is set, then zero rows will not be remove

function _Smat{T <: MatElem, S <: Ring}(A::T; R::S = base_ring(A),
                                              zerorows::Bool = false)

  m = Smat{elem_type(R)}()
  m.c = cols(A)
  m.r = 0

  for i=1:rows(A)
    if iszero_row(A, i)
      if !zerorows
        continue
      else
        r = SmatRow{elem_type(R)}()
        #push!(m.rows, SmatRow{elem_type(R)}())
      end
    else
      r = SmatRow{elem_type(R)}()
      for j = 1:cols(A)
        t = A[i, j]
        if t != 0
          m.nnz += 1
          push!(r.values, R(t))
          push!(r.pos, j)
        end
      end
    end
    push!(m.rows, r)
    m.r += 1
  end
  return m
end

# a faster version for nmod_mat -> Smat{T}
# it avoids the creation of elements in ResidueRing(ZZ, n)
doc"""
    Smat{S <: Ring}(A::nmod_mat; R::S = base_ring(A), zerorows::Bool = false)
  
> "Lifts" the entries in $A$ to a sparse matrix over $R$.
"""
function Smat{S <: Ring}(A::nmod_mat; R::S = base_ring(A), zerorows::Bool = false)
  if R == base_ring(A)
    return _Smat(A, R = R)
  end

  m = Smat{elem_type(R)}()
  m.c = cols(A)
  m.r = 0

  for i=1:rows(A)
    if iszero_row(A, i)
      if !zerorows
        continue
      else
        #push!(m.rows, SmatRow{elem_type(R)}())
        r = SmatRow{elem_type(R)}()
      end
    else
      r = SmatRow{elem_type(R)}()
      for j =1:cols(A)
        t = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &A, i - 1, j - 1)
        if t != 0
          m.nnz += 1
          push!(r.values, R(t))
          push!(r.pos, j)
        end
      end
    end
    push!(m.rows, r)
    m.r += 1
  end
  return m
end

doc"""
    mod!(A::SmatRow{fmpz}, n::Integer)
    mod!(A::SmatRow{fmpz}, n::fmpz)

    mod!(A::Smat{fmpz}, n::Integer)
    mod!(A::Smat{fmpz}, n::fmpz)

> Inplace reduction of all entries of $A$ to the positive residue system.
"""
function mod!(A::SmatRow{fmpz}, n::Integer)
  i=1
  while i<= length(A.pos)
    v = mod(A.values[i], n)
    if v == 0
      deleteat!(A.pos, i)
      deleteat!(A.values, i)
    else
      A.values[i] = v
      i += 1
    end
  end
end

function mod!(A::SmatRow{fmpz}, n::fmpz)
  i=1
  while i<= length(A.pos)
    v = mod(A.values[i], n)
    if v == 0
      deleteat!(A.pos, i)
      deleteat!(A.values, i)
    else
      A.values[i] = v
      i += 1
    end
  end
end

function mod_sym(a::fmpz, b::fmpz)
  c = mod(a,b)
  @assert c>=0
  if b > 0 && 2*c > b
    return c-b
  elseif b < 0 && 2*c > -b
    return c+b
  else
    return c
  end
end

doc"""
    mod_sym!(A::SmatRow{fmpz}, n::Integer)
    mod_sym!(A::SmatRow{fmpz}, n::fmpz)

    mod_sym!(A::Smat{fmpz}, n::Integer)
    mod_sym!(A::Smat{fmpz}, n::fmpz)

> Inplace reduction of all entries of $A$ to the symmetric residue system.
"""
function mod_sym!(A::SmatRow{fmpz}, n::fmpz)
  i=1
  while i<= length(A.pos)
    v = mod_sym(A.values[i], n)
    if v == 0
      deleteat!(A.pos, i)
      deleteat!(A.values, i)
    else
      A.values[i] = v
      i += 1
    end
  end
end

function mod_sym!(A::Smat{fmpz}, b::fmpz)
  for i=A
    mod_sym!(i, b)
  end
end


doc"""
    Smat(A::Smat{fmpz}, n::Int) -> Smat{UIntMod}
    SmatRow(A::Smat{fmpz}, n::Int) -> SmatRow{UIntMod}

> Converts $A$ to be a sparse matrix (row) over $Z/nZ$ 
"""

function Smat(A::Smat{fmpz}, n::Int)
  z = Smat{UIntMod}()
  R = ZZModUInt(UInt(n))
  return Smat(A, R)
end

doc"""
    Smat(A::Smat{fmpz}, R::Ring) -> Smat{elem_type(R)}
    SmatRow(A::Smat{fmpz}, R::Ring) -> SmatRow{elem_type(R)}

> Convert the matrix (row) $A$ to be over $R$.
"""
function Smat{T <: Ring}(A::Smat{fmpz}, R::T)
  z = Smat{elem_type(R)}()
  z.r = A.r
  z.c = A.c
  for r in A
    rz = SmatRow(r, R)
    if length(rz.pos) != 0
      push!(z.rows, rz)
      z.nnz += length(rz.pos)
    end
  end
  return z
end

function SmatRow(A::SmatRow{fmpz}, n::Int)
  z = Smat{UIntMod}()
  R = ZZModUInt(UInt(n))
  return SmatRow(A, R)
end

function SmatRow{T <: Ring}(A::SmatRow{fmpz}, R::T)
  z = SmatRow{elem_type(R)}()
  for (i, v) in A
    nv = R(v)
    if iszero(nv)
      continue
    else
      push!(z.pos, i)
      push!(z.values, nv)
    end
  end
  return z
end

doc"""
    Smat(A::Smat{fmpz}, n::Int) -> Smat{GenRes{fmpz}}
    SmatRow(A::Smat{fmpz}, n::Int) -> SmatRow{GenRes{fmpz}}

> Converts $A$ to ba a sparse matrix (row) over $Z/nZ$ 
"""
function SmatRow(A::SmatRow{fmpz}, n::fmpz)
  R = ResidueRing(FlintZZ, n)
  return SmatRow(A, R)
end
function Smat(A::SmatRow{fmpz}, n::fmpz)
  R = ResidueRing(FlintZZ, n)
  return Smat(A, R)
end

################################################################################
#
#  String I/O
#
################################################################################

function show{T}(io::IO, A::Smat{T})
  print(io, "Sparse ", A.r, " x ", A.c, " matrix with ")
  print(io, A.nnz, " non-zero entries\n")
end

################################################################################
#
#  Conversion
#
################################################################################

doc"""
  toNemo(io::IOStream, A::Smat; name = "A")

  Prints the Smat as a julia-program into the file corresponding to io.
  The file can be included to get the matrix.
  `name` controls the variable name of the matrix.
"""
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

doc"""
  toNemo(io::String, A::Smat; name = "A")

  Prints the Smat as a julia-program into the file named io.
  The file can be included to get the matrix.
  `name` controls the variable name of the matrix.
"""
function toNemo(f::String, A::Smat; name = "A")
  io = open(f, "w")
  toNemo(io, A, name=name)
  close(io)
end

################################################################################
#
#  Transpose
#
################################################################################

doc"""
  transpose{T}(A::Smat{T}) -> Smat{T}

  The transpose of A
"""
function transpose{T}(A::Smat{T})
  B = Smat{T}()
  n = rows(A)
  m = cols(A)
  B.rows = Array{SmatRow{T}}(m)
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
# Other stuff: support iterators
################################################################################
function endof{T}(A::Smat{T})
  return length(A.rows)
end

function start{T}(A::Smat{T})
  return 1
end

function next{T}(A::Smat{T}, st::Int)
  return A.rows[st], st + 1
end

function done{T}(A::Smat{T}, st::Int)
  return st > rows(A)
end

function length(A::Smat)
  return rows(A)
end

function length(A::SmatRow)
  return length(A.pos)
end

function endof{T}(A::SmatRow{T})
  return length(A.pos)
end

function start{T}(A::SmatRow{T})
  return 1
end

function next{T}(A::SmatRow{T}, st::Int)
  return (A.pos[st], A.values[st]), st + 1
end

function done{T}(A::SmatRow{T}, st::Int)
  return st > length(A.pos)
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
  c = Array{T}(rows(A))
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
  c = Array{T}(sz[1], sz[2])
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

function mul{T}(A::SmatRow{T}, B::SmatRow{T})
  v = 0*A.values[1]
  b = 1
  for a=1:length(A.pos)
    while b<=length(B.values) && B.pos[b] < A.pos[a]
      b += 1
    end
    if b>length(B.values)
      return v
    end
    if B.pos[b] == A.pos[a]
      v += B.values[b] * A.values[a]
    end
  end
  return v
end

function mul{T}(A::Smat{T}, B::Smat{T})
  @assert A.c == B.r
  C = MatrixSpace(base_ring(A), A.r, B.c)()
  for i=1:A.r
    for j=1:B.c
      C[i,j] = mul(A[i], B[j])
    end
  end
  return C
end

function mul(A::Smat{UIntMod}, B::Smat{UIntMod})
  @assert A.c == B.r
  C = MatrixSpace(ResidueRing(FlintZZ, base_ring(A).mod.n), A.r, B.c)()
  for i=1:A.r
    for j=1:B.c
      C[i,j] = mul(A[i], B[j])
    end
  end
  return C
end

function mul{T}(A::SmatRow{T}, B::Smat{T})
  C = SmatRow{T}()
  for (p, v) = A
    C = add_scaled_row(B[p], C, v)
  end
  return C
end

function +{T}(A::SmatRow{T}, B::SmatRow{T})
  if length(A.values) == 0
    return B 
  end
  return add_scaled_row(A, B, base_ring(A)(1))
end

function +{T}(A::Smat{T}, B::Smat{T})
  C = Smat{T}()
  m = min(rows(A), rows(B))
  for i=1:m
    push!(C, A[i]+B[i])
  end
  for i=m+1:rows(A)
    push!(C, A[i])
  end
  for i=m+1:rows(B)
    push!(C, B[i])
  end
  return C
end

function -{T}(A::SmatRow{T}, B::SmatRow{T})
  if length(A.values) == 0
    return B 
  end
  return add_scaled_row(B, A, base_ring(A)(-1))
end

function -{T}(A::Smat{T}, B::Smat{T})
  C = Smat{T}()
  m = min(rows(A), rows(B))
  for i=1:m
    push!(C, A[i]-B[i])
  end
  for i=m+1:rows(A)
    push!(C, A[i])
  end
  if m < rows(B)
    n = base_ring(B)(-1)
    for i=m+1:rows(B)
      push!(C, n*B[i])
    end
  end
  return C
end

function *{T}(b::T, A::SmatRow{T})
  B = SmatRow{T}()
  if iszero(b)
    return B
  end
  for (p,v) = A
    nv = v*b
    if !iszero(nv)  # there are zero divisors - potentially
      push!(B.pos, p)
      push!(B.values, v*b)
    end
  end
  return B
end

# those two functions produce infinite recursion - why I'm not sure
#function *{T}(b::Integer, A::SmatRow{T})
#  return base_ring(A)(b)*A
#end
#
#function *{T}(b::fmpz, A::SmatRow{T})
#  return base_ring(A)(b)*A
#end

function *{T}(b::T, A::Smat{T})
  B = Smat{T}()
  if iszero(b)
    return B
  end
  for a = A
    push!(B, b*a)
  end
  return B
end

#function *{T}(b::Integer, A::Smat{T})
#  return base_ring(A)(b)*A
#end
#
#function *{T}(b::fmpz, A::Smat{T})
#  return base_ring(A)(b)*A
#end

function SLP_AddRow{T}(i::Int, j::Int, v::T)
  assert(v != 0)
  slp = TrafoAddScaled(i, j, v)
  return slp
end

function SLP_SwapRows(i::Int, j::Int)
  slp = TrafoSwap{fmpz}(i, j)
  return slp
end

# function mul!{T}(a::Array{T, 1}, s::SmatSLP_swap_row)
#   t = a[s.row]
#   a[s.row] = a[s.col]
#   a[s.col] = t
# end
# 
# function mul!{T}(a::Array{T, 1}, s::SmatSLP_add_row{T})
#   a[s.row] = a[s.row]*s.val + a[s.col]
# end
# 
# function mul_t!{T}(a::Array{T, 1}, s::SmatSLP_swap_row)
#   t = a[s.row]
#   a[s.row] = a[s.col]
#   a[s.col] = t
# end
# 
# function mul_t!{T}(a::Array{T, 1}, s::SmatSLP_add_row{T})
#   a[s.col] = a[s.col]*s.val + a[s.row]
# end
# 
# 
# function apply!{T}(a::Array{T}, b::Array{SmatSLP_add_row{T}, 1})
#   for i=length(b):-1:1
#     mul!(a, b[i])
#   end
#   return a
# end
# 
# function apply_t!{T}(a::Array{T}, b::Array{SmatSLP_add_row{T}, 1})
#   for i=1:length(b)
#     mul_t!(a, b[i])
#   end
#   return a
# end
# 
function random_SmatSLP{T}(A::Smat{T}, i::Int, v::UnitRange)
  a = Array{SmatSLP_add_row{Int}}(i)
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

doc"""
  valence_mc{T}(A::Smat{T}; extra_prime = 2, trans = Array{SmatSLP_add_row{T}, 1}()) -> T

  Uses a Monte-Carlo alorithm to  compute the valence of A. The valence is the valence of the minimal polynomial f of A'*A, thus the last non-zero coefficient,
  typically f(0).

  The valence is computed modulo various primes until the computation
  stabilises for extra_prime many.

  trans, if given, is  a SLP (straight-line-program) in GL(n, Z). Then
  the valence of trans * A  is computed instead.
"""
function valence_mc{T}(A::Smat{T}; extra_prime = 2, trans = Array{SmatSLP_add_row{T}, 1}())
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
  c1 = Array{Int}(cols(A))
  c2 = Array{Int}(rows(A))

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

    v = Array{typeof(k(1))}(2*degree(f)+1)
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

function copy{T}(A::SmatRow{T})
  sr = SmatRow{T}()
  for (p, v) = A
    push!(sr.pos, p)
    push!(sr.values, v)
  end
  return sr
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

function randrow{T}(A::Smat{T})
  return rand(A.rows)
end

function setindex!{T}(A::Smat{T}, b::SmatRow{T}, i::Int)
  A.rows[i] = b
end

doc"""
    vcat!{T}(A::Smat{T}, B::Smat{T})

> Vertically joins $A$ and $B$ inplace, ie. the rows of $B$ are
> appended to $A$.
"""
function vcat!{T}(A::Smat{T}, B::Smat{T})
  @assert length(A.rows) == A.r
  @assert length(B.rows) == B.r
  A.r += B.r
  A.c = max(A.c, B.c)
  A.nnz += B.nnz
  A.rows = vcat(A.rows, B.rows)
  @assert length(A.rows) == A.r
end


doc"""
    vcat{T}(A::Smat{T}, B::Smat{T})

> Vertically joins $A$ and $B$
"""
function vcat{T}(A::Smat{T}, B::Smat{T})
  @assert length(A.rows) == A.r
  @assert length(B.rows) == B.r
  C = copy(A)
  vcat!(C, B)
  return C
end

doc"""
    hcat!{T}(A::Smat{T}, B::Smat{T})

> Horizontally concatenates $A$ and $B$, inplace, changing $A$.
"""
function hcat!{T}(A::Smat{T}, B::Smat{T})
  o = A.c
  A.c += B.c
  nnz = A.nnz
  for i=1:min(rows(A), rows(B))
    for (p,v) in B[i]
      push!(A[i].pos, p+o)
      push!(A[i].values, v)
    end
  end
  for i=min(rows(A), rows(B))+1:rows(B)
    sr = SmatRow{T}()
    for (p,v) in B[i]
      push!(sr.pos, p+o)
      push!(sr.values, v)
    end
    push!(A, sr)
  end
  A.nnz = nnz + B.nnz #A.nnz may have changed - if B is longer
end

doc"""
    hcat{T}(A::Smat{T}, B::Smat{T})

> Horizontally concatenates $A$ and $B$.
"""
function hcat{T}(A::Smat{T}, B::Smat{T})
  C = copy(A)
  hcat!(C, B)
  return C
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
doc"""
  fmpz_mat{T <: Integer}(A::Smat{T})

  The same matix A, but as an fmpz_mat.
  Requires a conversion from type T to fmpz.
"""
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

doc"""
  fmpz_mat(A::Smat{fmpz})

  The same matix A, but as an fmpz_mat.
"""
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
doc"""
  sparse{T}(A::Smat{T}) -> sparse{T}

  The same matrix, but as a julia-sparse matrix
"""
function sparse{T}(A::Smat{T})
  I = Array{Int}(A.nnz)
  J = Array{Int}(A.nnz)
  V = Array{T}(A.nnz)
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

doc"""
  Array{T}(A::Smat{T}) -> Array{T, 2}

  The same matrix, but as a two-dimensional julia-Array.
"""
function Array{T}(A::Smat{T})
  R = zero(Array{T}(A.r, A.c)) # otherwise, most entries will be #undef
                               # at least if T is a flint-type
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

function scale_row!{T}(A::Smat{T}, i::Int, c::T)
  for j in 1:length(A.rows[i].values)
    A.rows[i].values[j] *= c
  end
end

doc"""
  swap_rows!{T}(A::Smat{T}, i::Int, j::Int)

  swaps, inplace, the i-th row and the j-th
"""
function swap_rows!{T}(A::Smat{T}, i::Int, j::Int)
  A[i], A[j] = A[j], A[i]
end

doc"""
    invert_rows!{T}(A::Smat{T})

> Inplace, inverts the rows, ie. swaps the last and the 1st, the 2nd last and the
> 2nd, ...
"""
function invert_rows!{T}(A::Smat{T})
  for i=1:div(A.r, 2)
    A[i], A[A.r+1-i] = A[A.r+1-i], A[i]
  end
end


doc"""
    swap_cols!{T}(A::Smat{T}, i::Int, j::Int)

> Swap the i-th and j-th column inplace.
"""
function swap_cols!{T}(A::Smat{T}, i::Int, j::Int)
  @assert 1 <= i <= cols(A) && 1 <= j <= cols(A)

  if i == j
    return nothing
  end

  for r in A.rows
    if i in r.pos
      i_i = findfirst(r.pos, i)
      val_i = r.values[i_i]
      if j in r.pos
        i_j = findfirst(r.pos, j)
        val_j = r.values[i_j]

        r.values[i_i], r.values[i_j] = r.values[i_j], r.values[i_i]
      else
        t = r.values[i_i]
        deleteat!(r.pos, i_i)
        deleteat!(r.values, i_i)
        k = searchsortedfirst(r.pos, j)
        insert!(r.pos, k, j)
        insert!(r.values, k, t)
      end
    else
      if j in r.pos
        i_j = findfirst(r.pos, j)
        val_j = r.values[i_j]

        t = r.values[i_j]
        deleteat!(r.pos, i_j)
        deleteat!(r.values, i_j)
        k = searchsortedfirst(r.pos, i)
        insert!(r.pos, k, i)
        insert!(r.values, k, t)
      end
    end
  end
  return nothing
end

# rows j -> row i*c + row j
doc"""
  add_scaled_row!{T}(A::Smat{T}, i::Int, j::Int, c::T)

  adds, inplace, the c*i-th row to the j-th
"""
function add_scaled_row!{T}(A::Smat{T}, i::Int, j::Int, c::T)
  A.nnz = A.nnz - length(A[j])
  A.rows[j] = add_scaled_row(A[i], A[j], c)
  A.nnz = A.nnz + length(A[j])
end

function add_scaled_row{T}(Ai::SmatRow{T}, Aj::SmatRow{T}, c::T)
  sr = SmatRow{T}()
  pi = 1
  pj = 1
  @assert c != 0
  while pi <= length(Ai.pos) && pj <= length(Aj.pos)
    if Ai.pos[pi] < Aj.pos[pj]
      push!(sr.pos, Ai.pos[pi])
      push!(sr.values, c*Ai.values[pi])
      pi += 1
    elseif Ai.pos[pi] > Aj.pos[pj]
      push!(sr.pos, Aj.pos[pj])
      push!(sr.values, Aj.values[pj])
      pj += 1
    else
      n = c*Ai.values[pi] + Aj.values[pj]
      if n != 0
        push!(sr.pos, Ai.pos[pi])
        push!(sr.values, n)
      end
      pi += 1
      pj += 1
    end
  end
  while pi <= length(Ai.pos)
    push!(sr.pos, Ai.pos[pi])
    push!(sr.values, c*Ai.values[pi])
    pi += 1
  end
  while pj <= length(Aj.pos)
    push!(sr.pos, Aj.pos[pj])
    push!(sr.values, Aj.values[pj])
    pj += 1
  end
  return sr
end

# col j -> col i*c + col j
doc"""
    add_scaled_col!{T}(A::Smat{T}, i::Int, j::Int, c::T)

> Adds, inplace, the c*i-th column to the j-th column.
"""
function add_scaled_col!{T}(A::Smat{T}, i::Int, j::Int, c::T)
  @assert c != 0

  @assert 1 <= i <= cols(A) && 1 <= j <= cols(A)

  for r in A.rows
    if i in r.pos
      i_i = findfirst(r.pos, i)
      val_i = r.values[i_i]
      if j in r.pos
        i_j = findfirst(r.pos, j)
        val_j = r.values[i_j]

        r.values[i_j] += c*r.values[i_i]
      else
        k = searchsortedfirst(r.pos, j)
        insert!(r.pos, k, j)
        insert!(r.values, k, c*r.values[i_i])
      end
    end
  end
  return nothing
end

# row i -> a*row i + b * row j
# row j -> c*row i + d * row j
doc"""
  transform_row!{T}(A::Smat{T}, i::Int, j::Int, a::T, b::T, c::T, d::T)

  Inplace, replaces the i-th row and the j-th row by
  [a,b; c,d] * [i-th-row ; j-th row]
"""
function transform_row!{T}(A::Smat{T}, i::Int, j::Int, a::T, b::T, c::T, d::T)
  A.nnz = A.nnz - length(A[i]) - length(A[j])
  A.rows[i], A.rows[j] = transform_row(A[i], A[j], a, b, c, d)
  A.nnz = A.nnz + length(A[i]) + length(A[j])
end
function transform_row{T}(Ai::SmatRow{T}, Aj::SmatRow{T}, a::T, b::T, c::T, d::T)
  sr = SmatRow{T}()
  tr = SmatRow{T}()
  pi = 1
  pj = 1
  while pi <= length(Ai) && pj <= length(Aj)
    if Ai.pos[pi] < Aj.pos[pj]
      if a != 0
        push!(sr.pos, Ai.pos[pi])
        push!(sr.values, a*Ai.values[pi])
      end
      if c != 0
        push!(tr.pos, Ai.pos[pi])
        push!(tr.values, c*Ai.values[pi])
      end
      pi += 1
    elseif Ai.pos[pi] > Aj.pos[pj]
      if b != 0
        push!(sr.pos, Aj.pos[pj])
        push!(sr.values, b*Aj.values[pj])
      end
      if d != 0
        push!(tr.pos, Aj.pos[pj])
        push!(tr.values, d*Aj.values[pj])
      end
      pj += 1
    else
      m = a*Ai.values[pi] + b*Aj.values[pj]
      n = c*Ai.values[pi] + d*Aj.values[pj]
      if m != 0
        push!(sr.pos, Ai.pos[pi])
        push!(sr.values, m)
      end
      if n != 0
        push!(tr.pos, Ai.pos[pi])
        push!(tr.values, n)
      end
      pi += 1
      pj += 1
    end
  end
  while pi <= length(Ai.pos)
    if a != 0
      push!(sr.pos, Ai.pos[pi])
      push!(sr.values, a*Ai.values[pi])
    end
    if c != 0
      push!(tr.pos, Ai.pos[pi])
      push!(tr.values, c*Ai.values[pi])
    end
    pi += 1
  end
  while pj <= length(Aj.pos)
    if b != 0
      push!(sr.pos, Aj.pos[pj])
      push!(sr.values, b*Aj.values[pj])
    end
    if d != 0
      push!(tr.pos, Aj.pos[pj])
      push!(tr.values, d*Aj.values[pj])
    end
    pj += 1
  end
  
  return sr, tr
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

function abs_max{T <: Integer}(A::SmatRow{T})
  return maxabs(A.values)
end
function abs_max{T <: fmpz}(A::SmatRow{T})
  m = abs(A.values[1])
  for v in A.values
    if ccall((:__gmpz_cmpabs, :libgmp), Int, (Ptr{BigInt}, Ptr{BigInt}), &v, &m) > 0
      m = v
    end
  end
  return abs(v)
end

doc"""
  abs_max(A::Smat{Int}) -> Int
  abs_max(A::Smat{BigInt}) -> BigInt
  abs_max(A::Smat{fmpz}) -> fmpz
  abs_max(A::SmatRow{Int}) -> Int
  abs_max(A::SmatRow{BigInt}) -> BigInt
  abs_max(A::SmatRow{fmpz}) -> fmpz

  Finds the largest, in absolute value, entry of A
"""
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

function max(A::Smat{Int})
  m = A.rows[1].values[1]
  for i in A.rows
    for j in i.values
      m = max(m, j)
    end
  end
  return m
end

function max(A::Smat{BigInt})
  m = A.rows[1].values[1]
  for i in A.rows
    for j in i.values
      if ccall((:__gmpz_cmp, :libgmp), Int, (Ptr{BigInt}, Ptr{BigInt}),
        &m, &j) < 0
        m = j
      end
    end
  end
  return m
end

function max{T <: Integer}(A::SmatRow{T})
  return maximum(A.values)
end
function max(A::SmatRow{fmpz})
  return maximum(A.values)
end

doc"""
  max(A::Smat{Int}) -> Int
  max(A::Smat{BigInt}) -> BigInt
  max(A::Smat{fmpz}) -> fmpz
  max(A::SmatRow{Int}) -> Int
  max(A::SmatRow{BigInt}) -> BigInt
  max(A::SmatRow{fmpz}) -> fmpz

  Finds the largest entry of A
"""
function max(A::Smat{fmpz})
  m = A.rows[1].values[1]
  for i in A.rows
    for j in i.values
      if cmp(m, j) < 0
        m = j
      end
    end
  end
  return m
end

function min(A::Smat{Int})
  m = 0
  for i in A.rows
    for j in i.values
      m = min(m, j)
    end
  end
  return m
end

function min(A::Smat{BigInt})
  m = BigInt(0)
  for i in A.rows
    for j in i.values
      if ccall((:__gmpz_cmp, :libgmp), Int, (Ptr{BigInt}, Ptr{BigInt}),
        &m, &j) > 0
        m = j
      end
    end
  end
  return m
end

function min{T <: Integer}(A::SmatRow{T})
  return minimum(A.values)
end
function min(A::SmatRow{fmpz})
  return minimum(A.values)
end

doc"""
  min(A::Smat{Int}) -> Int
  min(A::Smat{BigInt}) -> BigInt
  min(A::Smat{fmpz}) -> fmpz
  min(A::SmatRow{Int}) -> Int
  min(A::SmatRow{BigInt}) -> BigInt
  min(A::SmatRow{fmpz}) -> fmpz

  Finds the smallest entry of A
"""
function min(A::Smat{fmpz})
  m = fmpz(0)
  for i in A.rows
    for j in i.values
      if cmp(m, j) > 0
        m = j
      end
    end
  end
  return m
end

function nbits(a::BigInt)
  return ndigits(a, 2)
end

doc"""
  nbits(a::Int) -> Int
  nbits(a::BigInt) -> Int

  Returns the number of bits necessary to represent a
"""
function nbits(a::Int)
  a==0 && return 0
  return Int(ceil(log(abs(a))/log(2)))
end

function one_step{T}(A::Smat{T}, sr = 1)
  i = sr
  assert(i>0)
  all_r = Array{Int}(0)
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
#  println("in one step: ilog2(max) now ", nbits(max(A)), " j:", j, " length: ", length(all_r))
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

doc"""
  upper_triangular{T}(A::Smat{T}; mod = 0)

  Inplace: transform A into an upper triangular matrix. If mod
  is non-zero, reduce entries modulo mod during the computation.
"""
function upper_triangular{T}(A::Smat{T}; mod = 0)
  for i = 1:min(rows(A), cols(A))
    x = one_step(A, i)
#    println("after one step: ilog2(max) now ", nbits(max(A)))
    if x>A.r
      return
    end
    if A.nnz > (A.r-i) * (A.c-i) /2 || nbits(abs_max(A)) > 200
      #println("calling  at level ", i, " bits: ", nbits(abs_max(A)), "nnz: ", A.nnz)
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

################################################################################
#
#  Inverses of elementary matrices
#
################################################################################

function inv(t::TrafoSwap)
  return T
end

function inv(t::TrafoAddScaled)
  return TrafoAddScaled(t.i, t.j, -t.s)
end

function inv(t::TrafoPartialDense)
  return TrafoPartialDense(t.i, t.rows, t.cols, inv(t.U))
end

# TrafoParaAddScaled is missing

################################################################################
#
#  Application of a transformation on the left side of a sparse matrix
#
################################################################################

# The following function do not update the number of nonzero entries
# properly

function apply_left!{T}(A::Smat{T}, t::TrafoScale{T})
  scale_row!(A, t.i, t.c)
  return nothing
end
  
function apply_left!{T}(A::Smat{T}, t::TrafoSwap{T})
  swap_rows!(A, t.i, t.j)
  return nothing
end

function apply_left!{T}(A::Smat{T}, t::TrafoAddScaled{T})
  add_scaled_row!(A, t.i, t.j, t.s)
  return nothing
end

function apply_left!{T}(A::Smat{T}, t::TrafoParaAddScaled{T})
  transform_row!(A, t.i, t.j, t.a, t.b, t.c, t.d)
  return nothing
end

function apply_left!{T}(A::Smat{T}, t::TrafoDeleteZero{T})
  deleteat!(A.rows, t.i)
  A.r -= 1
end

function apply_left!{T, S}(A::Smat{T}, t::TrafoPartialDense{S})
  R = parent(A.rows[1].values[1])
  i = t.i
  h = sub(A, t.rows, t.cols)
  deleteat!(A.rows, t.rows)
  A.r -= length(t.rows)
  @assert length(A.rows) == A.r
  # make dense matrix
  hdense = typeof(t.U)(h)

  #println(t.U)

  hdense = t.U * hdense

  h = _Smat(hdense, R = R, zerorows = true)

  for k in 1:length(h.rows)
    j = h.rows[k]
    rw = SmatRow{T}()
    for e in 1:length(j.pos)
      push!(rw.pos, j.pos[e] + i-1)
      push!(rw.values, j.values[e])
    end
    insert!(A.rows, i + k - 1, rw)
    A.r += 1
  end
  return nothing
end

################################################################################
#
#  Application of a transformation on the right side of a sparse matrix
#
################################################################################

# The following function do not update the number of nonzero entries
# properly
function apply_right!{T}(A::Smat{T}, t::TrafoSwap{T})
  swap_cols!(A, t.i, t.j)
  return nothing
end

function apply_right!{T}(A::Smat{T}, t::TrafoAddScaled{T})
  add_scaled_col!(A, t.j, t.i, t.s)
  return nothing
end

function apply_right!{T, S}(A::Smat{T}, t::TrafoPartialDense{S})
  # this works only if there are zeros left of the block to which we apply t
  i = t.i
  h = sub(A, t.rows, t.cols)
  deleteat!(A.rows, t.rows)
  A.r -= length(t.rows)
  @assert length(A.rows) == A.r
  # make dense matrix
  hdense = typeof(t.U)(h)

  #println(t.U)

  hdense = hdense * t.U

  h = _Smat(hdense, R = parent(A.rows[1].values[1]), zerorows = true)

  for k in 1:length(h.rows)
    j = h.rows[k]
    rw = SmatRow{T}()
    for e in 1:length(j.pos)
      push!(rw.pos, j.pos[e] + i-1)
      push!(rw.values, j.values[e])
    end
    insert!(A.rows, i + k - 1, rw)
    A.r += 1
  end
  return nothing
end

################################################################################
#
#  Application of a transformation on the right hand side of a row
#
################################################################################

function apply_right!{T}(x::Array{T, 1}, t::TrafoAddScaled{T})
  x[t.i] = x[t.i] + x[t.j]*t.s
  return nothing
end

function apply_right!{T}(x::Array{T, 1}, t::TrafoSwap{T})
  r = x[t.i]
  x[t.i] = x[t.j]
  x[t.j] = r
  return nothing
end

function apply_right!{T}(x::Array{T, 1}, t::TrafoParaAddScaled{T})
  r = t.a * x[t.i] + t.c * x[t.j]
  s = t.b * x[t.i] + t.d * x[t.j]
  x[t.i] = r
  x[t.j] = s
  return nothing
end

function apply_right!{T}(x::Array{T, 1}, t::TrafoDeleteZero{T})
  # move ith position to the back
  for j in length(x):-1:t.i+1
    r = x[j]
    x[j] = x[j - 1]
    x[j - 1] = r
  end
end

function apply_right!{T}(x::Array{T, 1}, t::TrafoPartialDense)
  s = MatrixSpace(parent(x[1]), 1, rows(t.U))(x[t.rows])
  #println("s :$s")
  s = s*t.U
  for (i, j) in zip(t.rows,1:rows(t.U))
    x[i] = s[1, j]
  end
  return nothing
end

################################################################################
#
#  Application to the left of an Array of ideals
#
################################################################################

function apply_left!(x::Vector{NfMaxOrdFracIdl}, y::TrafoSwap)
  x[y.i], x[y.j] = x[y.j], x[y.i]
end

function apply_left!(x::Vector{NfMaxOrdFracIdl}, y::TrafoAddScaled)
  x[y.j] = x[y.j] * x[y.i]^Int(y.s)
end

function apply_left!(x::Vector{NfMaxOrdFracIdl}, y::TrafoPartialDense)
  z = view(deepcopy(x), y.cols)
  xx = view(x, y.cols)
  for i in 1:rows(y.U)  ## use power product instead
    xx[i] = z[1]^Int(y.U[i, 1])
    for j in 2:cols(y.U)
      xx[i] *= z[j]^Int(y.U[i, j])
    end
  end
end

################################################################################
#
#  One echelonization step w/o transformations
#
################################################################################

# Perform one step in the echelonization, that is, find a pivot and clear
# elements below.
# sr = starting row
function _one_step{T}(A::Smat{T}, sr = 1)
  nr, trafo = _one_step_with_trafo(A, sr)
  return nr
end

function _one_step_with_trafo{T}(A::Smat{T}, sr = 1)
  trafos = Trafo[]
  i = sr
  assert(i>0)
  all_r = Array{Int}(0)
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

function nmod_mat(A::Smat{UIntMod})
  R = parent(A.rows[1].values[1])
  B = nmod_mat(A.r, A.c, R.mod.n)
  B.parent = NmodMatSpace(ResidueRing(FlintZZ, R.mod.n), A.r, A.c)

  for i = 1:length(A.rows)
    ra = A.rows[i]
    for j = 1:length(ra.pos)
      # alternatively, @inline the set_entry function in Nemo/src/flint/nmod_mat
      ccall((:nmod_mat_set_entry, :libflint), Void,
          (Ptr{nmod_mat}, Int, Int, UInt), &B, i - 1, ra.pos[j] - 1, ra.values[j].m)

      #set_entry!(B, i, ra.pos[j], ra.values[j].m)
      # B[i, ra.pos[j]] = ra.values[j].m
    end
  end
  return B
end

################################################################################
#
#  Echelonization via dense matrix
#
################################################################################

# The echelonization_via_dense must not remove zero rows automatically
function echelonize_via_dense(h::Smat{UIntMod})
  R = parent(h.rows[1].values[1])
  # turn into dense structure
  hdense = nmod_mat(h)
  # echelonize
  # I need to the following trick since we do not have the transformation
  rref!(hdense)
  # put back into sparse matrix over R (!= base_ring h)
  return _Smat(hdense, R = R)
end

function echelonize_via_dense_with_trafo(h::Smat{fmpz})
  hdense = fmpz_mat(h)
  # echelonize
  hdense, U = hnf_with_transform(hdense)
  # put back into sparse matrix
  h = _Smat(hdense, zerorows = true)
  return h, U
end

function echelonize_via_dense(h::Smat{fmpz})
  hdense = fmpz_mat(h)
  # echelonize
  hdense = hnf(hdense)
  # put back into sparse matrix
  h = _Smat(hdense)
  return h
end

################################################################################
#
#  Base case of echelonization
#
################################################################################

# Given two rows i, j with entries x, y (x != 0) in the same column, this
# function must produce a zero at entry y.

function echelonize_basecase!{T}(x::T, y::T, i::Int, j::Int, A::Hecke.Smat{T})
  c = -divexact(y, x)
  add_scaled_row!(A, i, j, c)
  return TrafoAddScaled(i, j, c)
end

function echelonize_basecase!(x::fmpz, y::fmpz, i::Int, j::Int,
                              A::Hecke.Smat{fmpz})
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
function upper_triangular_with_trafo!(M::Smat, density_limit::Float64 = 0.5)
  f = (A, i) -> (A.nnz > (A.r-i) * (A.c-i) * density_limit)
  return _upper_triangular_with_trafo!(M, f)
end

function upper_triangular_with_trafo!(M::Smat{fmpz},
                                      density_limit::Float64 = 0.5,
                                      size_limit::Int = 200)
  f =  (A, i) -> (A.nnz > (A.r-i) * (A.c-i) * density_limit || nbits(abs_max(A)) > size_limit)
  return _upper_triangular_with_trafo!(M, f)
end

# is_dense_enough is a function (::Smat{T}, i::Int) -> Bool
# At each level i, is_dense_enough(A, i) is called.
# If it evaluates to true, then dense echelonization will be called.
function _upper_triangular_with_trafo!{T}(A::Smat{T}, is_dense_enough::Function)
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
          push!(A.rows, SmatRow{T}())
          A.r += 1
          continue
        end
        rw = SmatRow{T}()
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

function upper_triangular!(M::Smat, density_limit::Float64 = 0.5)
  f = (A, i) -> (A.nnz > (A.r-i) * (A.c-i) * density_limit)
  return _upper_triangular!(M, f)
end

function upper_triangular!(M::Smat{fmpz}, density_limit::Float64 = 0.5, size_limit::Int = 200)
  f =  (A, i) -> (A.nnz > (A.r-i) * (A.c-i) * density_limit || nbits(abs_max(A)) > size_limit)
  return _upper_triangular!(M, f)
end

function _upper_triangular!{T}(A::Smat{T}, is_dense_enough)
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
        rw = SmatRow{T}()
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

function _snf_upper_triangular_with_trafo(A::Smat{fmpz})
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

  snfofess, ltr, rtr = snf_with_transform(essential_part; l = true, r = true)

  push!(trafos_left, TrafoPartialDense(essential_index, essential_index:rows(A), essential_index:cols(A), ltr))
  push!(trafos_right, TrafoPartialDense(essential_index, essential_index:rows(A), essential_index:cols(A), rtr))

  return snfofess, trafos_left, trafos_right
end

doc"""
    elementary_divisors(A::Smat{fmpz}) -> Array{fmpz, 1}

> The elementary divisors of $A$, ie. the diagonal elements of the Smith normal
> form of $A$. $A$ needs to be of full rank - currently.
"""
function elementary_divisors(A::Smat{fmpz})
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
