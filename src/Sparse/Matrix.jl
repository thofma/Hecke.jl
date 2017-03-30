export SMatSpace

################################################################################
#
#  Parent constructor
#
################################################################################

function SMatSpace(R::Ring, r::Int, c::Int, cached = true)
  T = elem_type(R)
  return SMatSpace{T}(R, r, c, cached)
end

################################################################################
#
#  Parent and base ring
#
################################################################################

base_ring{T}(A::SMatSpace{T}) = A.base_ring::parent_type(T)

parent(A::SMat) = SMatSpace(base_ring(A), A.r, A.c)

base_ring{T}(A::SMat{T}) = A.base_ring::parent_type(T)

function rows(A::SMat)
  @assert A.r == length(A.rows)
  return A.r
end

function cols(A::SMat)
  return A.c
end

################################################################################
#
#  Parent object overloading
#
################################################################################

function (M::SMatSpace){T <: MatElem, S <: Ring}(A::T; R::S = base_ring(A),
                                                         keepzrows::Bool = true)
  return SMat(A, R, keepzrows)
end

function (M::SMatSpace{T}){T}()
  z = SMat{T}()
  z.r = M.rows
  z.c = M.cols
  z.rows = [ SRow(base_ring(M)) for i in 1:z.r]
  z.base_ring = base_ring(M)
  return z
end

function (M::SMatSpace){T <: MatElem}(A::Array{T, 2})
  return SMat(A)
end


################################################################################
#
#  Hashing
#
################################################################################

function hash(A::SMat, h::UInt)
  return hash(A.r, hash(A.c, hash(A.rows, h)))
end

################################################################################
#
#  Comparison
#
################################################################################

function =={T}(x::SMat{T}, y::SMat{T})
  parent(x) != parent(y) && error("Parents incompatible")
  return x.rows == y.rows
end

################################################################################
#
#  Sparsity
#
################################################################################

# this makes only sense for SMat{fmpz}
function sparsity{T}(A::SMat{T})
  return A.nnz/(A.r * A.c), nbits(maxabs(A))
end

################################################################################
#
#  String I/O
#
################################################################################

function show{T}(io::IO, A::SMat{T})
  print(io, "Sparse ", A.r, " x ", A.c, " matrix with ")
  print(io, A.nnz, " non-zero entries\n")
end

################################################################################
#
#  Empty sparse matrix (given base ring)
#
################################################################################

function SMat{T <: Ring}(R::T)
  r = SMat{elem_type(R)}()
  r.base_ring = R
  return r
end

################################################################################
#
#  Copy
#
################################################################################

function copy{T}(A::SMat{T})
  return sub(A, 1:rows(A), 1:cols(A))
end

################################################################################
#
#  Entry/row access
#
################################################################################

function getindex{T}(A::SMat{T}, i::Int, j::Int)
  if i in 1:A.r
    ra = A.rows[i]
    p = findfirst(x->x==j, ra.pos)
    if p != 0
      return ra.values[p]
    end
  end
  return zero(base_ring(A))
end

function getindex{T}(A::SMat{T}, i::Int)
  if i in 1:A.r
    return A.rows[i]
  end
  return SRow{T}()
end

function setindex!{T}(A::SMat{T}, b::SRow{T}, i::Int)
  A.rows[i] = b
end

################################################################################
#
#  Random row from sparse matrix
#
################################################################################

function randrow{T}(A::SMat{T})
  return rand(A.rows)
end

################################################################################
#
#  Sparse matrix from dense matrix
#
################################################################################

# The entries of the sparse matrix will be coerced into the ring R.
# It defaults to the base ring of the input matrix.
# If keepzrows is set, then zero rows will not be remove
function SMat{T <: MatElem, S <: Ring}(A::T; R::S = base_ring(A),
                                              keepzrows::Bool = true)

  m = SMat(R)
  m.c = cols(A)
  m.r = 0

  for i=1:rows(A)
    if iszero_row(A, i)
      if !keepzrows
        continue
      else
        r = SRow{elem_type(R)}()
        #push!(m.rows, SRow{elem_type(R)}())
      end
    else
      r = SRow{elem_type(R)}()
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

doc"""
    SMat{T}(A::Array{T, 2}) -> SMat{T}

> Constructs the SMat (Hecke-sparse matrix) with coefficients of
> type T corresponding to A.
"""
function SMat{T <: RingElem}(A::Array{T, 2})
  length(A) == 0 && error("Cannot create sparse matrix from empty array")
  m = SMat(parent(A[1, 1]))
  m.c = Base.size(A, 2)
  m.r = 0
  for i=1:size(A, 1)
    if iszero_row(A, i)
      continue
    end
    r = SRow{T}()
    for j =1:size(A, 2)
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

# a faster version for nmod_mat -> SMat{T}
# it avoids the creation of elements in ResidueRing(ZZ, n)
doc"""
    SMat{S <: Ring}(A::nmod_mat; R::S = base_ring(A), keepzrows::Bool = false)
  
> "Lifts" the entries in $A$ to a sparse matrix over $R$.
"""
function SMat{S <: Ring}(A::nmod_mat; R::S = base_ring(A), keepzrows::Bool = false)
  if R == base_ring(A)
    return _SMat(A, R = R)
  end

  m = SMat{elem_type(R)}()
  m.c = cols(A)
  m.r = 0

  for i=1:rows(A)
    if iszero_row(A, i)
      if !keepzrows
        continue
      else
        #push!(m.rows, SRow{elem_type(R)}())
        r = SRow(R)
      end
    else
      r = SRow(R)
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

################################################################################
#
#  Modular reduction
#
################################################################################

doc"""
***
    mod_sym!(A::SMat{fmpz}, n::fmpz)

> Inplace reduction of all entries of $A$ modulo $n$ to the symmetric residue
> system.
"""
function mod_sym!(A::SMat{fmpz}, b::fmpz)
  for i=A
    mod_sym!(i, b)
  end
end

################################################################################
#
#  Ring change
#
################################################################################

doc"""
    SMat(A::SMat{fmpz}, n::Int) -> SMat{UIntMod}
    SRow(A::SMat{fmpz}, n::Int) -> SRow{UIntMod}

> Converts $A$ to be a sparse matrix (row) over $Z/nZ$ 
"""
function SMat(A::SMat{fmpz}, n::Int)
  R = ZZModUInt(UInt(n))
  return SMat(A, R)
end

doc"""
    SMat(A::SMat{fmpz}, R::Ring) -> SMat{elem_type(R)}
    SRow(A::SMat{fmpz}, R::Ring) -> SRow{elem_type(R)}

> Convert the matrix (row) $A$ to be over $R$.
"""
function SMat{T <: Ring}(A::SMat{fmpz}, R::T)
  z = SMat(R)
  z.r = A.r
  z.c = A.c
  for r in A
    rz = SRow(r, R)
    if length(rz.pos) != 0
      push!(z.rows, rz)
      z.nnz += length(rz.pos)
    end
  end
  return z
end

function SMat(A::SMat{fmpz}, n::fmpz)
  R = ResidueRing(FlintZZ, n)
  return SMat(A, R)
end

################################################################################
#
#  Transpose
#
################################################################################

doc"""
***
    transpose(A::SMat) -> SMat

> Returns the transpose of $A$.
"""
function transpose(A::SMat)
  R = base_ring(A)
  B = SMat(base_ring(A))
  n = rows(A)
  m = cols(A)
  B.rows = Array{SRow{elem_type(R)}}(m)
  for i=1:m
    B.rows[i] = SRow(R)
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
#  Make sparse matrices iteratable
#
################################################################################

function endof(A::SMat)
  return length(A.rows)
end

function start(A::SMat)
  return 1
end

function next(A::SMat, st::Int)
  return A.rows[st], st + 1
end

function done(A::SMat, st::Int)
  return st > rows(A)
end

function length(A::SMat)
  return rows(A)
end

################################################################################
#
#  Multiplication
#
################################################################################

# (dense Array{T, 1}) * Smat{T} as (dense Array{T, 1}) 
# inplace
function mul!{T}(c::Array{T, 1}, A::SMat{T}, b::Array{T, 1})
  assert(length(b) == cols(A))
  assert(length(c) == rows(A))
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

# (dense Array{T, 1}) * Smat{T} as (dense Array{T, 1}) 
function mul{T}(A::SMat{T}, b::Array{T, 1})
  assert(length(b) == cols(A))
  c = Array{T}(rows(A))
  mul!(c, A, b)
  return c
end

# - (dense Array{S, 1}) * Smat{T} as (dense Array{S, 1}) modulo mod::S
# - Inplace
# - Reduction as the last step, no intermediate reductions.
function mul_mod!{S, T}(c::Array{S, 1}, A::SMat{T}, b::Array{S, 1}, mod::S)
  assert( length(b) == cols(A))
  assert( length(c) == rows(A))
  for i = 1:length(A.rows)
    s = 0
    I = A.rows[i]
    for j=1:length(I.pos)
      s += S(I.values[j]) * b[I.pos[j]]
    end
    c[i] = s % mod
  end
  return c
end

# - (dense Array{S, 1}) * Smat{T} as (dense Array{S, 1}) modulo mod::S
# - Inplace
# - Intermediate reductions.
function mul_mod_big!{S, T}(c::Array{S, 1}, A::SMat{T}, b::Array{S, 1}, mod::S)
  assert(length(b) == cols(A))
  assert(length(c) == rows(A))
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

# - Smat{T} * Array{T, 2} as Array{T, 2}
# - Inplace
function mul!{T}(c::Array{T, 2}, A::SMat{T}, b::Array{T, 2})
  sz = size(b)
  assert(sz[1] == cols(A))
  tz = size(c)
  assert(tz[1] == rows(A))
  assert(tz[2] == sz[2])
  for m = 1:sz[2]
    for i = 1:length(A.rows)
      s = 0
      for j=1:length(A.rows[i].pos)
        s += A.rows[i].values[j] * b[A.rows[i].pos[j], m]
      end
      c[i, m] = s
    end
  end
  return c
end

# - Smat{T} * Array{T, 2} as Array{T, 2}
function mul{T}(A::SMat{T}, b::Array{T, 2})
  sz = size(b)
  assert(sz[1] == cols(A))
  c = Array{T}(sz[1], sz[2])
  return mul!(c, A, b)
end

# - Smat{T} * fmpz_mat as fmpz_mat
# - Inplace
function mul!{T}(c::fmpz_mat, A::SMat{T}, b::fmpz_mat)
  assert(rows(b) == cols(A))
  assert(rows(c) == rows(A))
  assert(cols(c) == cols(b))
  for m = 1:cols(b)
    for i = 1:length(A.rows)
      s = 0
      for j=1:length(A.rows[i].pos)
        s += A.rows[i].values[j] * b[A.rows[i].pos[j], m]
      end
      c[i, m] = s
    end
  end
  return c
end

# - Smat{T} * fmpz_mat as fmpz_mat
function mul{T}(A::SMat{T}, b::fmpz_mat)
  assert(rows(b) == cols(A))
  c = MatrixSpace(ZZ, rows(A), cols(b))()
  return mul!(c, A, b)
end

# - Smat{T} * Smat{T} as MatElem{T}
function mul{T}(A::SMat{T}, B::SMat{T})
  @assert A.c == B.r
  C = MatrixSpace(base_ring(A), A.r, B.c)()
  for i=1:A.r
    for j=1:B.c
      C[i,j] = mul(A[i], B[j])
    end
  end
  return C
end

# - Smat{UIntMod} * Smat{UIntMod} as MatElem{GenRes{fmpz}}
function mul(A::SMat{UIntMod}, B::SMat{UIntMod})
  @assert A.c == B.r
  C = MatrixSpace(ResidueRing(FlintZZ, base_ring(A).mod.n), A.r, B.c)()
  for i=1:A.r
    for j=1:B.c
      C[i,j] = mul(A[i], B[j])
    end
  end
  return C
end

# - SRow{T} * Smat{T} as SRow{T}
function mul{T}(A::SRow{T}, B::SMat{T})
  C = SRow{T}()
  for (p, v) = A
    C = add_scaled_row(B[p], C, v)
  end
  return C
end

################################################################################
#
#  Addition
#
################################################################################

function +{T}(A::SMat{T}, B::SMat{T})
  C = SMat(base_ring(A))
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

function -{T}(A::SMat{T}, B::SMat{T})
  C = SMat{T}()
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

function -{T}(A::SRow{T}, B::SRow{T})
  if length(A.values) == 0
    return B 
  end
  return add_scaled_row(B, A, base_ring(A)(-1))
end

################################################################################
#
#  Scalar multiplication
#
################################################################################

# The following runs into an infinite recursion in case T = fmpz
#function *{T}(b::fmpz, A::SMat{T})
#  return base_ring(A)(b)*A
#end

function *{T}(b::T, A::SMat{T})
  B = SMat(base_ring(A))
  if iszero(b)
    return B
  end
  for a = A
    push!(B, b*a)
  end
  return B
end

function *{T}(b::Integer, A::SMat{T})
  return base_ring(A)(b)*A
end

################################################################################
#
#  Submatrix
#
################################################################################

function sub{T}(A::SMat{T}, r::UnitRange, c::UnitRange)
  B = SMat(base_ring(A))
  B.nnz = 0
  for i=r
    rw = SRow{T}()
    ra = A.rows[i]
    for j=1:length(ra.values)
      if ra.pos[j] in c
        push!(rw.values, ra.values[j])
        push!(rw.pos, ra.pos[j]-c.start+1)
      end
    end
    if true || length(rw.pos)>0
      push!(B.rows, rw)
      B.nnz += length(rw.pos)
    end
  end
  B.r = length(r)
  B.c = length(c)
  return B
end


################################################################################
#
#  Valence
#
################################################################################

doc"""
  valence_mc{T}(A::SMat{T}; extra_prime = 2, trans = Array{SMatSLP_add_row{T}, 1}()) -> T

  Uses a Monte-Carlo alorithm to  compute the valence of A. The valence is the valence of the minimal polynomial f of A'*A, thus the last non-zero coefficient,
  typically f(0).

  The valence is computed modulo various primes until the computation
  stabilises for extra_prime many.

  trans, if given, is  a SLP (straight-line-program) in GL(n, Z). Then
  the valence of trans * A  is computed instead.
"""
function valence_mc{T}(A::SMat{T}; extra_prime = 2, trans = Array{SMatSLP_add_row{T}, 1}())
  # we work in At * A (or A * At) where we choose the smaller of the 2
  # matrices
  if false && cols(A) > rows(A)
    At = A
    A = transpose(A)
  else
    At = transpose(A)
  end
  if maxabs(A) > 2^20
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
#  Vertical concatentation
#
################################################################################

doc"""
***
    vcat!{T}(A::SMat{T}, B::SMat{T})

> Vertically joins $A$ and $B$ inplace, that is, the rows of $B$ are
> appended to $A$.
"""
function vcat!{T}(A::SMat{T}, B::SMat{T})
  @assert length(A.rows) == A.r
  @assert length(B.rows) == B.r
  A.r += B.r
  A.c = max(A.c, B.c)
  A.nnz += B.nnz
  A.rows = vcat(A.rows, B.rows)
  @assert length(A.rows) == A.r
end


doc"""
***
    vcat{T}(A::SMat{T}, B::SMat{T})

> Vertically joins $A$ and $B$.
"""
function vcat{T}(A::SMat{T}, B::SMat{T})
  @assert length(A.rows) == A.r
  @assert length(B.rows) == B.r
  C = copy(A)
  vcat!(C, B)
  return C
end

################################################################################
#
#  Horizontal concatentation
#
################################################################################

doc"""
***
    hcat!{T}(A::SMat{T}, B::SMat{T})

> Horizontally concatenates $A$ and $B$, inplace, changing $A$.
"""
function hcat!{T}(A::SMat{T}, B::SMat{T})
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
    sr = SRow{T}()
    for (p,v) in B[i]
      push!(sr.pos, p+o)
      push!(sr.values, v)
    end
    push!(A, sr)
  end
  A.nnz = nnz + B.nnz #A.nnz may have changed - if B is longer
end

doc"""
***
    hcat{T}(A::SMat{T}, B::SMat{T})

> Horizontally concatenates $A$ and $B$.
"""
function hcat{T}(A::SMat{T}, B::SMat{T})
  C = copy(A)
  hcat!(C, B)
  return C
end

################################################################################
#
#  Append sparse row to sparse matrix
#
################################################################################

function push!{T}(A::SMat{T}, B::SRow{T})
  if length(B.pos) > 0
    push!(A.rows, B)
    A.r += 1
    @assert length(A.rows) == A.r
    A.nnz += length(B.pos)
    A.c = max(A.c, B.pos[end])
  end
end

################################################################################
#
#  Conversion to fmpz_mat
#
################################################################################

doc"""
***
    fmpz_mat{T <: Integer}(A::SMat{T})

> The same matix $A$, but as an fmpz_mat.
> Requires a conversion from the base ring of $A$ to $\mathbf ZZ$.
"""
function fmpz_mat{T <: Integer}(A::SMat{T})
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
***
    fmpz_mat(A::SMat{fmpz})

> The same matix $A$, but as an fmpz_mat.
"""
function fmpz_mat(A::SMat{fmpz})
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
#  Maximum, minimum and norms
#
################################################################################

doc"""
***
    norm2(A::SRow{fmpz})

> The square of the euclidean norm of $A$.
"""
function norm2(A::SRow{fmpz})
  return sum([x*x for x= A.values])
end

doc"""
***
    hadamard_bound2(A::SMat{fmpz})

> The square of the product of the norms of the rows of $A$.
"""
function hadamard_bound2(A::SMat{fmpz})
  return prod([norm2(x) for x=A])
end

#function maxabs(A::SMat{Int})
#  m = abs(A.rows[1].values[1])
#  for i in A.rows
#    for j in i.values
#      m = max(m, abs(j))
#    end
#  end
#  return m
#end
#
#function maxabs(A::SMat{BigInt})
#  m = abs(A.rows[1].values[1])
#  for i in A.rows
#    for j in i.values
#      if ccall((:__gmpz_cmpabs, :libgmp), Int, (Ptr{BigInt}, Ptr{BigInt}),
#        &m, &j) < 0
#        m = j
#      end
#    end
#  end
#  return abs(m)
#end

#function maxabs{T <: Integer}(A::SRow{T})
#  return maxabs(A.values)
#end
#
#function maxabs{BigInt}(A::SRow{BigInt})
#  m = abs(A.values[1])
#  for v in A.values
#    if ccall((:__gmpz_cmpabs, :libgmp), Int, (Ptr{BigInt}, Ptr{BigInt}), &v, &m) > 0
#      m = v
#    end
#  end
#  return abs(v)
#end

doc"""
***
    maxabs(A::SMat{fmpz}) -> fmpz

  Finds the largest, in absolute value, entry of $A$.
"""
function maxabs(A::SMat{fmpz})
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

#function max(A::SMat{Int})
#  m = A.rows[1].values[1]
#  for i in A.rows
#    for j in i.values
#      m = max(m, j)
#    end
#  end
#  return m
#end
#
#function max(A::SMat{BigInt})
#  m = A.rows[1].values[1]
#  for i in A.rows
#    for j in i.values
#      if ccall((:__gmpz_cmp, :libgmp), Int, (Ptr{BigInt}, Ptr{BigInt}),
#        &m, &j) < 0
#        m = j
#      end
#    end
#  end
#  return m
#end

#function max{T <: Integer}(A::SRow{T})
#  return maximum(A.values)
#end

doc"""
***
    max(A::SMat{fmpz}) -> fmpz

> Finds the largest entry of $A$.
"""
function max(A::SMat{fmpz})
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

#function min(A::SMat{Int})
#  m = 0
#  for i in A.rows
#    for j in i.values
#      m = min(m, j)
#    end
#  end
#  return m
#end
#
#function min(A::SMat{BigInt})
#  m = BigInt(0)
#  for i in A.rows
#    for j in i.values
#      if ccall((:__gmpz_cmp, :libgmp), Int, (Ptr{BigInt}, Ptr{BigInt}),
#        &m, &j) > 0
#        m = j
#      end
#    end
#  end
#  return m
#end
#
#function min{T <: Integer}(A::SRow{T})
#  return minimum(A.values)
#end


doc"""
***
    min(A::SMat{fmpz}) -> fmpz

> Finds the smallest entry of $A$.
"""
function min(A::SMat{fmpz})
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

################################################################################
#
#  Test upper triangular shape
#
################################################################################

doc"""
    isupper_triangular(A::SMat)
 
> Returns true iff $A$ is upper triangular.
"""
function isupper_triangular(A::SMat)
  for i=2:A.r
    if A[i-1].pos[1] >= A[i].pos[1]
      return false
    end
  end
  return true
end

################################################################################
#
#  Identity matrices
#
################################################################################

doc"""
    id{T}(::Type{SMat{T}}, n::Int) -> SMat{T}

> The $n\times n$ identity matrix as a SMat of type T.
"""
function id{T}(::Type{SMat{T}}, n::Int)
  A = SMat{T}()
  for i=1:n
    push!(A, SRow{T}([(i, T(1))]))
  end
  return A
end

doc"""
    id{S}(::Type{SMat}, R::S, n::Int) -> SMat{elem_type(R)}
    
> The $n \times n$ identity over $R$ as a SMat.
> Necessary if $T(1)$ for the type $T$ does not work.
"""
function id(::Type{SMat}, R::Ring, n::Int)
  T = elem_type(R)
  A = SMat(R)
  for i=1:n
    push!(A, SRow{T}([(i, R(1))]))
  end
  return A
end

doc"""
    isid{T}(A::SMat{T})

> Tests if $A$ is the $n \times n$ identity.
"""
function isid{T}(A::SMat{T})
  if A.c != A.r
    return false
  end
  for i = 1:A.r
    if length(A.rows[i].pos) != 1
      return false
    end
    if A.rows[i].pos[1] != i ||
       !isone(A.rows[i].values[1])
      return false
    end
  end
  return true
end

################################################################################
#
#  Serialization
#
################################################################################

doc"""
  toNemo(io::IOStream, A::SMat; name = "A")

  Prints the SMat as a julia-program into the file corresponding to io.
  The file can be included to get the matrix.
  `name` controls the variable name of the matrix.
"""
function toNemo(io::IOStream, A::SMat; name = "A")
  T = typeof(A.rows[1].values[1])
  println(io, name, " = SMat{$T}()")
  for i=A.rows
    print(io, "push!($(name), SRow{$T}(Tuple{Int, $T}[");
    for j=1:length(i.pos)-1
      print(io, "($(i.pos[j]), $(i.values[j])), ")
    end
    println(io, "($(i.pos[end]), $(i.values[end]))]))")
  end
end

doc"""
  toNemo(io::String, A::SMat; name = "A")

  Prints the SMat as a julia-program into the file named io.
  The file can be included to get the matrix.
  `name` controls the variable name of the matrix.
"""
function toNemo(f::String, A::SMat; name = "A")
  io = open(f, "w")
  toNemo(io, A, name=name)
  close(io)
end

################################################################################
#
#  Conversion to julia types
#
################################################################################

doc"""
***
    sparse{T}(A::SMat{T}) -> sparse{T}

> The same matrix, but as a sparse matrix of julia type.
"""
function sparse{T}(A::SMat{T})
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
***
    Array{T}(A::SMat{T}) -> Array{T, 2}

> The same matrix, but as a two-dimensional julia array.
"""
function Array{T}(A::SMat{T})
  R = zero(Array{T}(A.r, A.c)) # otherwise, most entries will be #undef
                               # at least if T is a flint-type
  for i=1:rows(A)
    for j=1:length(A.rows[i].pos)
      R[i,A.rows[i].pos[j]] = A.rows[i].values[j]
    end
  end
  return R
end

