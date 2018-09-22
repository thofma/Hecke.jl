export SMatSpace, sparse_matrix, nnz, sparsity, density

################################################################################
#
#  Parent constructor
#
################################################################################

function SMatSpace(R::Ring, r::Int, c::Int; cached = true)
  T = elem_type(R)
  return SMatSpace{T}(R, r, c, cached)
end

################################################################################
#
#  Basic functions
#
################################################################################

base_ring(A::SMatSpace{T}) where {T} = A.base_ring::parent_type(T)

parent(A::SMat) = SMatSpace(base_ring(A), A.r, A.c)

base_ring(A::SMat{T}) where {T} = A.base_ring::parent_type(T)

@doc Markdown.doc"""
    rows(A::SMat) -> Int

Return the number of rows of $A$.
"""
function rows(A::SMat)
  @assert A.r == length(A.rows)
  return A.r
end

@doc Markdown.doc"""
    cols(A::SMat) -> Int

Return the number of columns of $A$.
"""
function cols(A::SMat)
  return A.c
end

@doc Markdown.doc"""
    nnz(A::SMat) -> Int

Return the number of non-zero entries of $A$.
"""
function nnz(A::SMat)
  return A.nnz
end

size(A::SMat) = (rows(A), cols(A))

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

@doc Markdown.doc"""
    ==(A::SMat, B::SMat) -> Bool

Return whether $A$ is equal to $B$.
"""
function ==(x::SMat{T}, y::SMat{T}) where T
  parent(x) != parent(y) && error("Parents incompatible")
  return x.rows == y.rows
end

################################################################################
#
#  Sparsity and density
#
################################################################################

@doc Markdown.doc"""
    sparsity(A::SMat) -> Float64

Return the sparsity of `A`, that is, the number of zero-valued elements divided
by the number of all elements.
"""
function sparsity(A::SMat)
  return 1.0 - nnz(A)/(rows(A) * cols(A))
end

@doc Markdown.doc"""
    density(A::SMat) -> Float64

Return the density of `A`, that is, the number of nonzero-valued elements
divided by the number of all elements.
"""
density(A::SMat) = 1.0 - sparsity(A)

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, A::SMat{T}) where T
  print(io, "Sparse ", A.r, " x ", A.c, " matrix with ")
  print(io, A.nnz, " non-zero entries\n")
end

################################################################################
#
#  Empty sparse matrix (given base ring)
#
################################################################################

function sparse_matrix(R::T) where T <: Ring
  r = SMat{elem_type(R)}()
  r.base_ring = R
  return r
end

################################################################################
#
#  Copy
#
################################################################################

function copy(A::SMat{T}) where T
  return sub(A, 1:rows(A), 1:cols(A))
end

################################################################################
#
#  Entry/row access
#
################################################################################

function getindex(A::SMat{T}, i::Int, j::Int) where T
  if i in 1:A.r
    ra = A.rows[i]
    p = findfirst(isequal(j), ra.pos)
    if !(p === nothing)
      return ra.values[p]
    end
  end
  return zero(base_ring(A))
end

function getindex(A::SMat{T}, i::Int) where T
  (i < 1 || i > rows(A)) && error("Index must be between 1 and $(rows(A))")
  return A.rows[i]
end

function setindex!(A::SMat{T}, b::SRow{T}, i::Int) where T
  (i < 1 || i > rows(A)) && error("Index must be between 1 and $(rows(A))")
  A.rows[i] = b
end

################################################################################
#
#  Random row from sparse matrix
#
################################################################################

function randrow(A::SMat{T}) where T
  return rand(A.rows)
end

################################################################################
#
#  Sparse matrix constructors
#
################################################################################

@doc Markdown.doc"""
    sparse_matrix(A::MatElem; keepzrows::Bool = true)

Constructs thesparse matrix corresponding to the dense matrix $A$. If
`keepzrows` is false, then the constructor will drop any zero row of $A$.
"""
function sparse_matrix(A::MatElem; keepzrows::Bool = true)
  R = base_ring(A)
  m = sparse_matrix(R)
  m.c = cols(A)
  m.r = 0

  for i=1:rows(A)
    if iszero_row(A, i)
      if !keepzrows
        continue
      else
        r = SRow{elem_type(R)}()
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

@doc Markdown.doc"""
    sparse_matrix(A::Array{T, 2}) -> SMat{T}

Constructs the sparse matrix corresponding to A.
"""
function sparse_matrix(A::Array{T, 2}) where {T <: RingElem}
  length(A) == 0 && error("Cannot create sparse matrix from empty array")
  m = sparse_matrix(parent(A[1, 1]))
  m.c = Base.size(A, 2)
  m.r = 0
  for i in 1:size(A, 1)
    if iszero_row(A, i)
      continue
    end
    r = SRow{T}()
    for j in 1:size(A, 2)
      if !iszero(A[i, j])
        m.nnz += 1
        push!(r.values, A[i, j])
        push!(r.pos, j)
      end
    end
    push!(m.rows, r)
    m.r += 1
  end
  return m
end

function (M::SMatSpace)(A::T; R::S = base_ring(A),
                                 keepzrows::Bool = true) where {T <: MatElem, S <: Ring}
  return sparse_matrix(A, R, keepzrows)
end

function (M::SMatSpace)(A::Array{T, 2}) where T <: MatElem
  return sparse_matrix(A)
end

################################################################################
#
#  Modular reduction
#
################################################################################

@doc Markdown.doc"""
***
mod_sym!(A::SMat{fmpz}, n::fmpz) -> SMat{fmpz}

Inplace reduction of all entries of $A$ modulo $n$ to the symmetric residue
system.
"""
function mod_sym!(A::SMat{fmpz}, b::fmpz)
  for r in A
    mod_sym!(r, b)
  end
  return A
end

################################################################################
#
#  Ring change
#
################################################################################

@doc Markdown.doc"""
    change_ring(A::SMat, f) -> SMat

Given a sparse matrix $A$ and a callable object $f$, this function will
construct a new sparse matrix by applying $f$ to all elements of $A$.
"""
function change_ring(A::SMat{T}, f) where {T}
end

@doc Markdown.doc"""
    sparse_matrix(A::SMat{fmpz}, n::Int) -> SMat{nmod}

> Converts $A$ to be a sparse matrix (row) over $Z/nZ$ 
"""
function sparse_matrix(A::SMat{fmpz}, n::Int)
  R = ResidueRing(FlintZZ, n, cached=false)
  return sparse_matrix(A, R)
end

@doc Markdown.doc"""
    sparse_matrix(A::SMat{fmpz}, R::Ring) -> SMat{elem_type(R)}
    SRow(A::SMat{fmpz}, R::Ring) -> SRow{elem_type(R)}

> Convert the matrix (row) $A$ to be over $R$.
"""
function sparse_matrix(A::SMat, R::T) where {T <: Ring}
  z = sparse_matrix(R)
  z.r = A.r
  z.c = A.c
  for r in A
    rz = change_ring(r, R)
    if length(rz.pos) != 0
      push!(z.rows, rz)
      z.nnz += length(rz.pos)
    end
  end
  return z
end

function sparse_matrix(A::SMat{fmpz}, n::fmpz)
  R = ResidueRing(FlintZZ, n, cached=false)
  return sparse_matrix(A, R)
end

################################################################################
#
#  Transpose
#
################################################################################

@doc Markdown.doc"""
***
    transpose(A::SMat) -> SMat

> Returns the transpose of $A$.
"""
function transpose(A::SMat{T}) where {T}
  R = base_ring(A)
  B = sparse_matrix(R)
  n = rows(A)
  m = cols(A)
  B.rows = Vector{SRow{T}}(undef, m)
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

function Base.iterate(A::SMat, st::Int = 1)
  if st > rows(A)
    return nothing
  end

  return A.rows[st], st + 1
end

function length(A::SMat)
  return rows(A)
end

Base.eltype(A::SMat{T}) where {T} = SRow{T}

################################################################################
#
#  Multiplication
#
################################################################################

# (dense Array{T, 1}) * SMat{T} as (dense Array{T, 1}) 
# inplace
function mul!(c::Array{T, 1}, A::SMat{T}, b::Array{T, 1}) where T
  @assert length(b) == cols(A)
  @assert length(c) == rows(A)
  R = base_ring(A)
  for i = 1:length(A.rows)
    s = zero(R)
    I = A.rows[i]
    for j=1:length(I.pos)
      s += I.values[j] * b[I.pos[j]]
    end
    c[i] = s
  end
  return c
end

# (dense Array{T, 1}) * SMat{T} as (dense Array{T, 1}) 
function mul(A::SMat{T}, b::Array{T, 1}) where T
  @assert length(b) == cols(A)
  c = Vector{T}(undef, rows(A))
  mul!(c, A, b)
  return c
end

# - (dense Array{S, 1}) * SMat{T} as (dense Array{S, 1}) modulo mod::S
# - Inplace
# - Reduction as the last step, no intermediate reductions.
function mul_mod!(c::Array{S, 1}, A::SMat{T}, b::Array{S, 1}, mod::S) where {S, T}
  @assert length(b) == cols(A)
  @assert length(c) == rows(A)

  for i = 1:length(A.rows)
    s = S(0)
    I = A.rows[i]
    for j=1:length(I.pos)
      s += S(I.values[j]) * b[I.pos[j]]
    end
    c[i] = s % mod
  end
  return c
end

# - (dense Array{S, 1}) * SMat{T} as (dense Array{S, 1}) modulo mod::S
# - Inplace
# - Intermediate reductions.
function mul_mod_big!(c::Array{S, 1}, A::SMat{T}, b::Array{S, 1}, mod::S) where {S, T}
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

# - SMat{T} * Array{T, 2} as Array{T, 2}
# - Inplace
function mul!(c::Array{T, 2}, A::SMat{T}, b::Array{T, 2}) where T
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

# - SMat{T} * Array{T, 2} as Array{T, 2}
function mul(A::SMat{T}, b::Array{T, 2}) where T
  sz = size(b)
  assert(sz[1] == cols(A))
  c = Array{T}(undef, sz[1], sz[2])
  return mul!(c, A, b)
end

# - SMat{T} * fmpz_mat as fmpz_mat
# - Inplace
function mul!(c::fmpz_mat, A::SMat{T}, b::fmpz_mat) where T
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

# - SMat{T} * fmpz_mat as fmpz_mat
function mul(A::SMat{T}, b::fmpz_mat) where T
  assert(rows(b) == cols(A))
  c = zero_matrix(FlintZZ, rows(A), cols(b))
  return mul!(c, A, b)
end

# - SMat{T} * SMat{T} as MatElem{T}
function mul(A::SMat{T}, B::SMat{T}) where T
  @assert A.c == B.r
  C = zero_matrix(base_ring(A), A.r, B.c)
  for i=1:A.r
    for j=1:B.c
      C[i,j] = mul(A[i], B[j])
    end
  end
  return C
end

# - SMat{nmod} * SMat{nmod} as nmod_mat
function mul(A::SMat{nmod}, B::SMat{nmod})
  @assert A.c == B.r
  C = zero_matrix(base_ring(A), A.r, B.c)
  for i=1:A.r
    for j=1:B.c
      C[i,j] = mul(A[i], B[j])
    end
  end
  return C
end

# - SRow{T} * SMat{T} as SRow{T}
function mul(A::SRow{T}, B::SMat{T}) where T
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

function +(A::SMat{T}, B::SMat{T}) where T
  C = sparse_matrix(base_ring(A))
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

function -(A::SMat{T}, B::SMat{T}) where T
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

#TODO: this is a problem in anther ops as well: a length zero row does not have a base_ring
function -(A::SRow{T}, B::SRow{T}) where T
  if length(A) == 0
    if length(B) == 0
      return A
    else
      return add_scaled_row(B, A, base_ring(B)(-1))
    end
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

function *(b::T, A::SMat{T}) where T
  B = sparse_matrix(base_ring(A))
  if iszero(b)
    return B
  end
  for a = A
    push!(B, b*a)
  end
  return B
end

function *(b::Integer, A::SMat{T}) where T
  return base_ring(A)(b)*A
end

################################################################################
#
#  Submatrix
#
################################################################################

function sub(A::SMat{T}, r::UnitRange, c::UnitRange) where T
  B = sparse_matrix(base_ring(A))
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

@doc Markdown.doc"""
  valence_mc{T}(A::SMat{T}; extra_prime = 2, trans = Array{SMatSLP_add_row{T}, 1}()) -> T

Uses a Monte-Carlo alorithm to compute the valence of A. The valence is the
valence of the minimal polynomial f of A'*A, thus the last non-zero
coefficient, typically f(0).

The valence is computed modulo various primes until the computation stabilises
for extra_prime many.

trans, if given, is  a SLP (straight-line-program) in GL(n, Z). Then the
valence of trans * A  is computed instead.
"""
function valence_mc(A::SMat{T}; extra_prime = 2, trans = Array{SMatSLP_add_row{T}, 1}()) where T
  # we work in At * A (or A * At) where we choose the smaller of the 2
  # matrices
  if false && cols(A) > rows(A)
    At = A
    A = transpose(A)
  else
    At = transpose(A)
  end
  if maximum(abs, A) > 2^20
    mm = mul_mod_big!
    println("mul big case")
  else
    mm = mul_mod!
    println("mul small case")
  end
  c1 = Array{Int}(undef, cols(A))
  c2 = Array{Int}(undef, rows(A))

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
    f = berlekamp_massey(v)
    fl = true
    if !fl || degree(f) > div(d, 2)-1
      d += 10
      continue
    end
    df = degree(f)
    println("Poly degree is $df, dims $(rows(A)) x $(cols(A))")

    V = fmpz(leading_coefficient(f))
    pp = fmpz(p)

    v = Array{typeof(k(1))}(undef, 2*degree(f)+1)
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
      f = berlekamp_massey(v)
      fl = true
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

function valence_mc(A::SMat{T}, p::Int) where T
  # we work in At * A (or A * At) where we choose the smaller of the 2
  # matrices
  if false && cols(A) > rows(A)
    At = A
    A = transpose(A)
  else
    At = transpose(A)
  end
  if maximum(abs, A) > 2^20
    mm = mul_mod_big!
    println("mul big case")
  else
    mm = mul_mod!
    println("mul small case")
  end
  c1 = Array{Int}(undef, cols(A))
  c2 = Array{Int}(undef, rows(A))

  for i=1:cols(A)
    c1[i] = Int(rand(-10:10))
  end

  c = copy(c1) ## need the starting value for the other primes as well

  k = FiniteField(p)
  d = 10
  v = Array{typeof(k(1)), 1}()
  push!(v, k(c1[1]))
  while true
    while length(v) <= d
      mm(c2, A, c1, p)
      mm(c1, At, c2, p)
      push!(v, k(c1[1]))
    end
    f = berlekamp_massey(v)
    fl = true
    if !fl || degree(f) > div(d, 2)-1
      d += 10
      continue
    end
    df = degree(f)
    println("Poly degree is $df, dims $(rows(A)) x $(cols(A))")
    return f
  end  
end

################################################################################
#
#  Vertical concatentation
#
################################################################################

@doc Markdown.doc"""
***
    vcat!{T}(A::SMat{T}, B::SMat{T})

> Vertically joins $A$ and $B$ inplace, that is, the rows of $B$ are
> appended to $A$.
"""
function vcat!(A::SMat{T}, B::SMat{T}) where T
  @assert length(A.rows) == A.r
  @assert length(B.rows) == B.r
  A.r += B.r
  A.c = max(A.c, B.c)
  A.nnz += B.nnz
  A.rows = vcat(A.rows, B.rows)
  @assert length(A.rows) == A.r
end

@doc Markdown.doc"""
***
    vcat{T}(A::SMat{T}, B::SMat{T})

> Vertically joins $A$ and $B$.
"""
function vcat(A::SMat{T}, B::SMat{T}) where T
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

@doc Markdown.doc"""
***
    hcat!{T}(A::SMat{T}, B::SMat{T})

> Horizontally concatenates $A$ and $B$, inplace, changing $A$.
"""
function hcat!(A::SMat{T}, B::SMat{T}) where T
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

@doc Markdown.doc"""
***
    hcat{T}(A::SMat{T}, B::SMat{T})

> Horizontally concatenates $A$ and $B$.
"""
function hcat(A::SMat{T}, B::SMat{T}) where T
  C = copy(A)
  hcat!(C, B)
  return C
end

################################################################################
#
#  Append sparse row to sparse matrix
#
################################################################################

function push!(A::SMat{T}, B::SRow{T}) where T
  push!(A.rows, B)
  A.r += 1
  @assert length(A.rows) == A.r
  A.nnz += length(B.pos)
  if length(B.pos) > 0
    A.c = max(A.c, B.pos[end])
  end
end

################################################################################
#
#  Conversion to fmpz_mat
#
################################################################################

@doc Markdown.doc"""
***
    fmpz_mat{T <: Integer}(A::SMat{T})

> The same matix $A$, but as an fmpz_mat.
> Requires a conversion from the base ring of $A$ to $\mathbf ZZ$.
"""
function fmpz_mat(A::SMat{T}) where T <: Integer
  B = zero_matrix(FlintZZ, A.r, A.c)
  for i = 1:length(A.rows)
    ra = A.rows[i]
    for j = 1:length(ra.pos)
      B[i, ra.pos[j]] = ra.values[j]
    end
  end
  return B
end

@doc Markdown.doc"""
***
    fmpz_mat(A::SMat{fmpz})

> The same matix $A$, but as an fmpz_mat.
"""
function fmpz_mat(A::SMat{fmpz})
  B = zero_matrix(FlintZZ, A.r, A.c)
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

@doc Markdown.doc"""
***
    norm2(A::SRow{fmpz})

> The square of the euclidean norm of $A$.
"""
function norm2(A::SRow{fmpz})
  return sum([x*x for x= A.values])
end

@doc Markdown.doc"""
***
    hadamard_bound2(A::SMat{fmpz})

> The square of the product of the norms of the rows of $A$.
"""
function hadamard_bound2(A::SMat{fmpz})
  return prod([norm2(x) for x=A])
end


@doc Markdown.doc"""
***
    maximum(abs, A::SMat{fmpz}) -> fmpz

  Finds the largest, in absolute value, entry of $A$.
"""
function maximum(::typeof(abs), A::SMat{fmpz})
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

@doc Markdown.doc"""
***
    maximum(A::SMat{fmpz}) -> fmpz

> Finds the largest entry of $A$.
"""
function maximum(A::SMat{fmpz})
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



@doc Markdown.doc"""
***
    minimum(A::SMat{fmpz}) -> fmpz

> Finds the smallest entry of $A$.
"""
function minimum(A::SMat{fmpz})
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

@doc Markdown.doc"""
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
#  Sparse to dense
#
################################################################################

function Nemo.matrix(A::SMat)
  R = base_ring(A)
  M = zero_matrix(R, rows(A), cols(A))
  for i=1:rows(A)
    for j=1:length(A.rows[i].pos)
      M[i, A.rows[i].pos[j]] = A.rows[i].values[j]
    end
  end
  return M
end

################################################################################
#
#  Identity matrices
#
################################################################################

@doc Markdown.doc"""
    id{T}(::Type{SMat{T}}, n::Int) -> SMat{T}

> The $n\times n$ identity matrix as a SMat of type T.
"""
function id(::Type{SMat{T}}, n::Int) where {T}
  A = SMat{T}()
  for i=1:n
    push!(A, SRow{T}([(i, T(1))]))
  end
  return A
end

@doc Markdown.doc"""
    id{S}(::Type{SMat}, R::S, n::Int) -> SMat{elem_type(R)}
    
> The $n \times n$ identity over $R$ as a SMat.
> Necessary if $T(1)$ for the type $T$ does not work.
"""
function id(::Type{SMat}, R::Ring, n::Int)
  T = elem_type(R)
  A = sparse_matrix(R)
  for i=1:n
    push!(A, SRow{T}([(i, R(1))]))
  end
  return A
end

@doc Markdown.doc"""
   identity_matrix(::Type{SMat}, R::Ring, n::Int)
   identity_matrix(::Type{MatElem}, R::Ring, n::Int)
> Create a sparse (resp. dense) $n$ times $n$ identity matrix over $R$.   
"""
function identity_matrix(::Type{SMat}, R::Ring, n::Int)
  return id(SMat, R, n)
end

function identity_matrix(::Type{MatElem}, R::Ring, n::Int)
  return identity_matrix(R, n)
end

@doc Markdown.doc"""
   zero_matrix(::Type{SMat}, R::Ring, n::Int)
   zero_matrix(::Type{SMat}, R::Ring, n::Int, m::Int)
   zero_matrix(::Type{MatElem}, R::Ring, n::Int)
   zero_matrix(::Type{MatElem}, R::Ring, n::Int, m::Int)
> Create a sparse (resp. dense) $n$ times $n$ (resp. $n$ times $m$) zero matrix over $R$.   
"""
function zero_matrix(::Type{SMat}, R::Ring, n::Int)
  S = sparse_matrix(R)
  S.rows = [sparse_row(R) for i=1:n]
  S.c = S.r = n
  return S
end

function zero_matrix(::Type{SMat}, R::Ring, n::Int, m::Int)
  S = sparse_matrix(R)
  S.rows = [sparse_row(R) for i=1:n]
  S.r = n
  S.c = m
  return S
end

function zero_matrix(::Type{MatElem}, R::Ring, n::Int)
  return zero_matrix(R, n)
end

function zero_matrix(::Type{MatElem}, R::Ring, n::Int, m::Int)
  return zero_matrix(R, n, m)
end

function Base.cat(n::Int, A::SMat...)
  if n==1
    return vcat(A...)
  elseif n==2
    return hcat(A...)
  else
    error("dims must be 1 or 2")
  end
end


function Base.vcat(A::SMat...)
  B = copy(A[1])
  for i=2:length(A)
    for r = A[i].rows
      push!(B, copy(r))
    end
  end
  return A
end

#base case
function Base.hcat(A::SMat)
  return A
end

function Base.hcat(A::SMat, B::SMat, C::SMat...)
  return hcat(hcat(A, B), C...)
end

function Base.cat(dims::Tuple{Int, Int}, A::SMat...)
  if dims != (1,2)
    error("dims must be (1, 2)")
  end
  B = copy(A[1])
  c = B.c
  for i=2:length(A)
    for j=1:rows(A[i])
      R = SRow(base_ring(B))
      for (k,v) = A[i].rows[j]
        push!(R.pos, k+c)
        push!(R.values, v)
      end
      push!(B, R)
    end
    c += A[i].c
  end
  return B
end

@doc Markdown.doc"""
    isid{T}(A::SMat{T})

> Tests if $A$ is the $n \times n$ identity.
"""
function isid(A::SMat{T}) where T
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

@doc Markdown.doc"""
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

@doc Markdown.doc"""
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

@doc Markdown.doc"""
***
    sparse{T}(A::SMat{T}) -> sparse{T}

> The same matrix, but as a sparse matrix of julia type.
"""
function sparse(A::SMat{T}) where T
  I = Array{Int}(undef, A.nnz)
  J = Array{Int}(undef, A.nnz)
  V = Array{T}(undef, A.nnz)
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

@doc Markdown.doc"""
***
    Array{T}(A::SMat{T}) -> Array{T, 2}

> The same matrix, but as a two-dimensional julia array.
"""
function Array(A::SMat{T}) where T
  R = zero_matrix(base_ring(A), A.r, A.c) 
           # otherwise, most entries will be #undef
           # at least if T is a flint-type
  for i=1:rows(A)
    for j=1:length(A.rows[i].pos)
      R[i,A.rows[i].pos[j]] = A.rows[i].values[j]
    end
  end
  return R
end
