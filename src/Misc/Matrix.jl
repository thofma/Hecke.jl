export iszero_row, modular_hnf, howell_form, _hnf_modular, kernel_mod

import Nemo.matrix

import Base.vcat

################################################################################
#
#  Dense matrix types
#
################################################################################

dense_matrix_type(::Type{fmpz}) = fmpz_mat

dense_matrix_type(::Type{fmpq}) = fmpq_mat

dense_matrix_type(::Type{nmod}) = nmod_mat

dense_matrix_type(::Type{fq_nmod}) = fq_nmod_mat

dense_matrix_type(::Type{fq}) = fq_mat

dense_matrix_type(::Type{arb}) = arb_mat

dense_matrix_type(::Type{acb}) = acb_mat

dense_matrix_type(::Type{gfp_elem}) = gfp_mat

dense_matrix_type(::Type{T}) where {T} = Generic.Mat{T}

coefficient_type(::Type{fmpz_mat}) = fmpz

coefficient_type(::Type{fmpq_mat}) = fmpq

coefficient_type(::Type{nmod_mat}) = nmod

coefficient_type(::Type{fq_nmod_mat}) = fq_nmod

coefficient_type(::Type{fq_mat}) = fq

coefficient_type(::Type{arb_mat}) = arb

coefficient_type(::Type{acb_mat}) = acb

coefficient_type(::Type{gfp_mat}) = gfp_elem

coefficient_type(::Type{Generic.Mat{T}}) where {T} = T

################################################################################
#
#  Saturation
#
################################################################################

@doc Markdown.doc"""
    saturate(A::fmpz_mat) -> fmpz_mat

Computes the saturation of $A$, that is, a basis for $\mathbf{Q}\otimes M \meet
\mathbf{Z}^n$, where $M$ is the row span of $A$ and $n$ the number of rows of
$A$.

Equivalently, return $TA$ for an invertiable rational matrix $T$ such that $TA$
is integral and the elementary divisors of $TA$ are all trivial.
"""
function saturate(A::fmpz_mat)
  #row saturation: want
  #  TA in Z, T in Q and elem_div TA = [1]
  #
  #  AT = H (in HNF), then A = HT^-1 and H^-1A = T^-1
  # since T is uni-mod, H^-1 A is in Z with triv. elm. div

  H = hnf(A')
  H = H'
  Hi, d = pseudo_inv(sub(H, 1:nrows(H), 1:nrows(H)))
  S = Hi*A
  Sd = divexact(S, d)
#  @hassert :HNF 1  d*Sd == S
  return Sd
end

################################################################################
#
#  Zero matrix constructors
#
################################################################################

function zero_matrix(::Type{MatElem}, R::Ring, n::Int)
  return zero_matrix(R, n)
end

function zero_matrix(::Type{MatElem}, R::Ring, n::Int, m::Int)
  return zero_matrix(R, n, m)
end


function matrix(A::Array{fmpz, 2})
  m = matrix(FlintZZ, A)
  return m
end

function matrix(A::Array{T, 2}) where T <: RingElem
  r, c = size(A)
  (r < 0 || c < 0) && error("Array must be non-empty")
  m = matrix(parent(A[1, 1]), A)
  return m
end

function matrix(A::Array{T, 1}) where T <: RingElem
  return matrix(reshape(A,length(A),1))
end

function Array(a::fmpz_mat; S::Type{T} = fmpz) where T
  A = Array{T}(undef, nrows(a), ncols(a))
  for i = 1:nrows(a)
    for j = 1:ncols(a)
      A[i,j] = T(a[i,j])
    end 
  end
  return A
end

function iszero_row(M::fmpz_mat, i::Int)
  for j = 1:ncols(M)
    if M[i,j] != 0 
      return false
    end
  end
  return true
end

function iszero_row(M::nmod_mat, i::Int)
  zero = UInt(0)
  for j in 1:ncols(M)
    t = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ref{nmod_mat}, Int, Int), M, i - 1, j - 1)
    if t != zero
      return false
    end
  end
  return true
end


function iszero_row(M::MatElem{T}, i::Int) where T
  for j in 1:ncols(M)
    if !iszero(M[i,j])
      return false
    end
  end
  return true
end

function iszero_row(M::Array{T, 2}, i::Int) where T <: Integer
  for j = 1:Base.size(M, 2)
    if M[i,j] != 0 
      return false
    end
  end
  return true
end

function iszero_row(M::Array{fmpz, 2}, i::Int)
  for j = 1:Base.size(M, 2)
    if M[i,j] != 0 
      return false
    end
  end
  return true
end

function iszero_row(M::Array{T, 2}, i::Int) where T <: RingElem
  for j in 1:Base.size(M, 2)
    if !iszero(M[i,j])
      return false
    end
  end
  return true
end

function divexact!(a::fmpz_mat, b::fmpz_mat, d::fmpz)
  ccall((:fmpz_mat_scalar_divexact_fmpz, :libflint), Nothing,
               (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{fmpz}), a, a, d)
end

function mul!(a::fmpz_mat, b::fmpz_mat, c::fmpz)
  ccall((:fmpz_mat_scalar_mul_fmpz, :libflint), Nothing, 
                  (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{fmpz}), a, b, c)
end                  

#computes (hopefully) the hnf for vcat(a*I, m) and returns ONLY the
#non-singular part. By definition, the result wil have full rank
#
#Should be rewritten to use Howell and lifting rather the big HNF
#
function modular_hnf(m::fmpz, a::fmpz_mat, shape::Symbol = :upperright)
  c = vcat(parent(a)(m), a)
  n = ncols(a)
  w = view(c, n+1, 1, 2*n, n)
  ccall((:fmpz_mat_scalar_mod_fmpz, :libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{fmpz}), w, w, m)
  if shape == :lowerleft
    c = _hnf(c, shape)
    return sub(c, n+1:2*n, 1:n)
  else
    c = hnf(c)
    c = sub(c, 1:n, 1:n)
  end
end

function _hnf(x::fmpz_mat, shape::Symbol = :upperright)
  if shape == :lowerleft
    h = hnf(invert_cols(x))
    invert_cols!(h)
    invert_rows!(h)
    return h::fmpz_mat
  end
  return hnf(x)::fmpz_mat
end

function _hnf!(x::fmpz_mat, shape::Symbol = :upperright)
  if shape == :lowerleft
    _swapcols!(x)
    hnf!(x)
    _swapcols!(x)
    _swaprows!(x)
    return x::fmpz_mat
  end
  hnf!(x)
  return x::fmpz_mat
end

function hnf!(x::fmpz_mat)
  ccall((:fmpz_mat_hnf, :libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}), x, x)
  return x
end

function _hnf_modular_eldiv(x::fmpz_mat, m::fmpz, shape::Symbol = :upperright)
  if shape == :lowerleft
    h = hnf_modular_eldiv!(invert_cols(x), m)
    invert_cols!(h)
    invert_rows!(h)
    return h
  elseif shape == :upperright
    return hnf_modular_eldiv(x, m)
  else
    error("shape $shape not supported")
  end
end

function hnf_modular_eldiv!(x::fmpz_mat, d::fmpz, shape::Symbol = :upperright)
   (nrows(x) < ncols(x)) &&
                error("Matrix must have at least as many rows as columns")
   if shape == :upperright
     ccall((:fmpz_mat_hnf_modular_eldiv, :libflint), Nothing,
                  (Ref{fmpz_mat}, Ref{fmpz}), x, d)
     return x
   elseif shape == :lowerleft
     _swapcols!(x)
     ccall((:fmpz_mat_hnf_modular_eldiv, :libflint), Nothing,
                 (Ref{fmpz_mat}, Ref{fmpz}), x, d)
     _swapcols!(x)
     _swaprows!(x)
     return x
   else
     error("shape $shape is not supported")
   end
end

function ishnf(x::fmpz_mat, shape::Symbol)
  if shape == :upperright
    return ishnf(x)
  elseif shape == :lowerleft
    r = nrows(x)
    i = 0
    j_old = ncols(x) + 1

    for outer i in nrows(x):-1:1

      if iszero_row(x, i)
        break
      end

      j = ncols(x)
      while iszero(x[i, j])
        j = j - 1
      end
      x[i, j] < 0 && return false
      j >= j_old && return false
      for k in i+1:r
        x[k, j] < 0 && return false
        x[k, j] >= x[i, j] && return false
      end
      j_old = j
      i = i - 1
    end

    for l in i:-1:1
      !iszero_row(x, l) && return false
    end
    return true
  end
end

################################################################################
#
#  Inversion of rows and columns
#
################################################################################

@doc Markdown.doc"""
    invert_rows(x::fmpz_mat) -> fmpz_mat

> Swap rows $i$ and $n -i$ for $1 \leq i \leq n/2$, where $n$ is the number of
> rows of $x$.
"""
function invert_rows(x::fmpz_mat)
  y = deepcopy(x)
  invert_rows!(y)
  return y
end

@doc Markdown.doc"""
    invert_columns(x::fmpz_mat) -> fmpz_mat

> Swap columns $i$ and $n -i$ for $1 \leq i \leq n/2$, where $n$ is the number of
> columns of $x$.
"""
function invert_cols(x::fmpz_mat)
  y = deepcopy(x)
  invert_cols!(y)
  return y
end

@doc Markdown.doc"""
    invert_rows!(x::fmpz_mat) -> fmpz_mat

> Swap rows $i$ and $n -i$ for $1 \leq i \leq n/2$, where $n$ is the number of
> rows of $x$. The operations are done inplace.
"""
function invert_rows!(x::fmpz_mat)
  r = nrows(x)
  c = ncols(x)

  if r == 1
    return x
  end

  if r % 2 == 0
    for i in 1:div(r,2)
      for j = 1:c
        # we swap x[i,j] <-> x[r-i+1,j]
        s = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), x, i - 1, j - 1)
        t = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), x, (r - i + 1) - 1, j - 1)
        ccall((:fmpz_swap, :libflint), Nothing, (Ptr{fmpz}, Ptr{fmpz}), t, s)
      end
    end
  else
    for i in 1:div(r-1,2)
      for j = 1:c
        # we swap x[i,j] <-> x[r-i+1,j]
        s = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), x, i - 1, j - 1)
        t = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), x, (r - i + 1) - 1, j - 1)
        ccall((:fmpz_swap, :libflint), Nothing, (Ptr{fmpz}, Ptr{fmpz}), t, s)
      end
    end
  end
  return x
end

function _swaprows!(x::fmpz_mat, i::Int, j::Int)
  ccall((:_fmpz_mat_swap_rows, :libflint), Nothing, (Ref{fmpz_mat}, Int, Int), x, i-1, j-1)
  return x
end

function _swaprows!(x::nmod_mat, i::Int, j::Int)
  ccall((:_nmod_mat_swap_rows, :libflint), Nothing, (Ref{nmod_mat}, Int, Int), x, i-1, j-1)
  return x
end
  
@doc Markdown.doc"""
    invert_rows!(x::nmod_mat) -> nmod_mat

> Swap rows $i$ and $n -i$ for $1 \leq i \leq n/2$, where $n$ is the number of
> rows of $x$. The operations are done inplace.
"""
function invert_rows!(x::nmod_mat)
  r = nrows(x)
  c = ncols(x)

  if r == 1
    return nothing
  end

  if r % 2 == 0
    for i in 1:div(r,2)
      for j = 1:c
        # we swap x[i,j] <-> x[r-i+1,j]
        s = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ref{nmod_mat}, Int, Int), x, i - 1, j - 1)
        t = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ref{nmod_mat}, Int, Int), x, (r - i + 1) - 1, j - 1)
        set_entry!(x, r - i + 1, j, s)
        set_entry!(x, i, j, t)
      end
    end
  else
    for i in 1:div(r-1,2)
      for j = 1:c
        # we swap x[i,j] <-> x[r-i+1,j]
        s = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ref{nmod_mat}, Int, Int), x, i - 1, j - 1)
        t = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ref{nmod_mat}, Int, Int), x, (r - i + 1) - 1, j - 1)
        set_entry!(x, i, j, t)
        set_entry!(x, r - i + 1, j, s)
      end
    end
  end
  x
end

@doc Markdown.doc"""
    invert_cols!(x::nmod_mat) -> nmod_mat

> Swap columns $i$ and $n -i$ for $1 \leq i \leq n/2$, where $n$ is the number of
> columns of $x$. The operations are done inplace.
"""
function invert_cols!(x::nmod_mat)
  r = nrows(x)
  c = ncols(x)

  if c == 1
    return nothing
  end

  if c % 2 == 0
    for i in 1:div(c,2)
      for j = 1:r
        # swap x[j,i] <-> x[j,c-i+1]
        s = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ref{nmod_mat}, Int, Int), x, j - 1, i - 1)
        t = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ref{nmod_mat}, Int, Int), x, j - 1, (c - i + 1 ) - 1)
        set_entry!(x, j, i, t)
        set_entry!(x, j, c - i + 1, s)
      end
    end
  else
    for i in 1:div(c-1,2)
      for j = 1:r
        # swap x[j,i] <-> x[j,c-i+1]
        s = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ref{nmod_mat}, Int, Int), x, j - 1, i - 1)
        t = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ref{nmod_mat}, Int, Int), x, j - 1, (c - i + 1 ) - 1)
        set_entry!(x, j, i, t)
        set_entry!(x, j, c - i + 1, s)
      end
    end
  end
  return x
end

@doc Markdown.doc"""
    invert_cols!(x::fmpz_mat) -> fmpz_mat

> Swap columns $i$ and $n -i$ for $1 \leq i \leq n/2$, where $n$ is the number of
> columns of $x$. The operations are done inplace.
"""
function invert_cols!(x::fmpz_mat)
  r = nrows(x)
  c = ncols(x)

  if c == 1
    return x
  end

  if c % 2 == 0
    for i in 1:div(c,2)
      for j = 1:r
        # swap x[j,i] <-> x[j,c-i+1]
        s = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), x, j - 1, i - 1)
        t = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), x, j - 1, (c - i + 1 ) - 1)
        ccall((:fmpz_swap, :libflint), Nothing, (Ptr{fmpz}, Ptr{fmpz}), t, s)
      end
    end
  else
    for i in 1:div(c-1,2)
      for j = 1:r
        # swap x[j,i] <-> x[j,c-i+1]
        s = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), x, j - 1, i - 1)
        t = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), x, j - 1, (c - i + 1 ) - 1)
        ccall((:fmpz_swap, :libflint), Nothing, (Ptr{fmpz}, Ptr{fmpz}), t, s)
      end
    end
  end
  return x
end

@doc Markdown.doc"""
    invert_cols(x::Mat) -> Mat

> Swap columns $i$ and $n -i$ for $1 \leq i \leq n/2$, where $n$ is the number of
> columns of $x$.
"""
function invert_cols(x::Generic.Mat)
  z = deepcopy(x)
  invert_cols!(z)
  return z
end

@doc Markdown.doc"""
    invert_cols!(x::Mat) -> Mat

> Swap columns $i$ and $n -i$ for $1 \leq i \leq n/2$, where $n$ is the number of
> columns of $x$. The operations are done inplace.
"""
function invert_cols!(x::Generic.Mat)
  r = nrows(x)
  c = ncols(x)
  t = base_ring(x)(0)

  if c == 1
    return x
  end

  if c % 2 == 0
    for i in 1:div(c,2)
      for j = 1:r
        # swap x[j,i] <-> x[j,c-i+1]
        x[j, i], x[j, c - i + 1] = x[j, c - i + 1], x[j, i]
      end
    end
  else
    for i in 1:div(c-1,2)
      for j = 1:r
        # swap x[j,i] <-> x[j,c-i+1]
        x[j, i], x[j, c - i + 1] = x[j, c - i + 1], x[j, i]
      end
    end
  end
  return x
end

@doc Markdown.doc"""
    invert_rows(x::Mat) -> Mat

> Swap rows $i$ and $n -i$ for $1 \leq i \leq n/2$, where $n$ is the number of
> rows of $x$.
"""
function invert_rows(x::Generic.Mat)
  z = deepcopy(x)
  invert_rows(z)
  return z
end

@doc Markdown.doc"""
    invert_rows!(x::Mat) -> Mat

> Swap rows $i$ and $n -i$ for $1 \leq i \leq n/2$, where $n$ is the number of
> rows of $x$. The operations are done inplace.
"""
function invert_rows!(x::Generic.Mat)
  r = nrows(x)
  c = ncols(x)

  if r == 1
    return x
  end

  if r % 2 == 0
    for i in 1:div(r,2)
      for j = 1:c
        # we swap x[i,j] <-> x[r-i+1,j]
        x[i, j], x[r - i + 1, j] = x[r - i + 1, j], x[i, j]
      end
    end
  else
    for i in 1:div(r-1,2)
      for j = 1:c
        x[i, j], x[r - i + 1, j] = x[r - i + 1, j], x[i, j]
        # we swap x[i,j] <-> x[r-i+1,j]
      end
    end
  end
  return x
end

################################################################################
# 
################################################################################

function maximum(f::typeof(abs), a::fmpz_mat)
  m = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, 0,0)
  for i=1:nrows(a)
    for j=1:ncols(a)
      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, i-1, j-1)
      if ccall((:fmpz_cmpabs, :libflint), Cint, (Ptr{fmpz}, Ptr{fmpz}), m, z) < 0
        m = z
      end
    end
  end
  r = fmpz()
  ccall((:fmpz_abs, :libflint), Nothing, (Ref{fmpz}, Ptr{fmpz}), r, m)
  return r
end

function maximum(a::fmpz_mat)  
  m = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, 0,0)
  for i=1:nrows(a)
    for j=1:ncols(a)
      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, i-1, j-1)
      if ccall((:fmpz_cmp, :libflint), Cint, (Ptr{fmpz}, Ptr{fmpz}), m, z) < 0
        m = z
      end
    end
  end
  r = fmpz()
  ccall((:fmpz_set, :libflint), Nothing, (Ref{fmpz}, Ptr{fmpz}), r, m)
  return r
end

function minimum(a::fmpz_mat) 
  m = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, 0,0)
  for i=1:nrows(a)
    for j=1:ncols(a)
      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, i-1, j-1)
      if ccall((:fmpz_cmp, :libflint), Cint, (Ptr{fmpz}, Ptr{fmpz}), m, z) > 0
        m = z
      end
    end
  end
  r = fmpz()
  ccall((:fmpz_set, :libflint), Nothing, (Ref{fmpz}, Ptr{fmpz}), r, m)
  return r
end

function lift_unsigned(a::nmod_mat)
  z = zero_matrix(FlintZZ, nrows(a), ncols(a))
  ccall((:fmpz_mat_set_nmod_mat_unsigned, :libflint), Nothing,
          (Ref{fmpz_mat}, Ref{nmod_mat}), z, a)
  return z
end

################################################################################
# possibly a slice or window in fmpz_mat?
# the nr x nc matrix starting in (a,b)
################################################################################

function sub(A::fmpz_mat, r::UnitRange, c::UnitRange)
  return deepcopy(view(A, r, c))
end

################################################################################
#
#  misc.jl : At some point this should migrate to Nemo
#
################################################################################

# compute basis for the right kernel space by calling flint
# look at flint documentation of nmod_mat_nullspace

function _right_kernel(x::T) where {T <: Zmodn_mat}
  z = zero_matrix(base_ring(x), ncols(x), max(nrows(x),ncols(x)))
  n = ccall((:nmod_mat_nullspace, :libflint), Int, (Ref{T}, Ref{T}), z, x)
  return z, n
end

# compute basis for the left kernel space
# output is array of arrays, which span the kernel

function kernel(a)
  x = transpose(a)
  R = base_ring(a)
  z, n = _right_kernel(x)
  z = transpose(z)
  T = elem_type(base_ring(a))
  ar = typeof(Array{T}(undef, ncols(z)))[]
  for i in 1:n 
    t = Array{T}(undef, ncols(z))
    for j in 1:ncols(z)
      t[j] = R(z[i, j])
    end
    push!(ar,t)
  end
  return ar
end

function right_kernel(a::MatElem)
  R = base_ring(a)
  if typeof(R) <: Generic.ResRing{fmpz}
    nn, zz = _right_kernel(a)
  else
    zz, nn = nullspace(a)
  end
  #TODO: There is some inconsistency between returning the nullity or the kernel first...
  if typeof(nn) <: Integer
    n = nn
    z = zz
  else
    n = zz
    z = nn
  end
  T = elem_type(base_ring(a))
  ar = typeof(Array{T}(undef, nrows(z)))[]
  for i in 1:n
    t = Array{T}(undef, nrows(z))
    for j in 1:nrows(z)
      t[j] = R(z[j, i])
    end
    push!(ar,t)
  end
  return ar
end

left_kernel(a::MatElem) = right_kernel(transpose(a))

function lift(a::Generic.Mat{Generic.Res{fmpz}})
  z = zero_matrix(FlintZZ, nrows(a), ncols(a))
  for i in 1:nrows(a)
    for j in 1:ncols(a)
      z[i, j] = lift(a[i, j])
    end
  end
  return z
end

################################################################################
#
#  Row reduced echelon form over Z/nZ for prime n (nmod and Res{fmpz})
#
################################################################################

function _rref(a::Generic.Mat{Generic.Res{fmpz}})
  m = modulus(base_ring(a))
  b = zero_matrix(FlintZZ, nrows(a), ncols(a))
  for i in 1:nrows(b)
    for j in 1:ncols(b)
      b[i,j] = lift(a[i,j]) % m
    end
  end

  # fmpz_mat_rref_mod assumes that input is reduced modulo m
  r = ccall((:fmpz_mat_rref_mod, :libflint), Int, (Ptr{Nothing}, Ref{fmpz_mat}, Ref{fmpz}), C_NULL, b, m)
  return r, parent(a, false)(b)
end

_rref(a) = rref(a)

# now inplace
function _rref!(a::Generic.Mat{Generic.Res{fmpz}})
  m = modulus(base_ring(a))
  b = zero_matrix(FlintZZ, nrows(a), ncols(a))
  for i in 1:nrows(b)
    for j in 1:ncols(b)
      b[i,j] = lift(a[i,j]) % m
    end
  end

  # fmpz_mat_rref_mod assumes that input is reduced modulo m
  r = ccall((:fmpz_mat_rref_mod, :libflint), Int, (Ptr{Nothing}, Ref{fmpz_mat}, Ref{fmpz}), C_NULL, b, m)
  for i in 1:nrows(b)
    for j in 1:ncols(b)
      a[i, j] = b[i, j]
    end
  end

  return r
end

_rref!(a) = rref!(a)

################################################################################
#
#  LU factorization over Z/nZ for n prime (nmod and Res{fmpz})
#
################################################################################

function _lu!(P::Generic.perm, A::S) where {S <: MatElem{Generic.Res{fmpz}}}
   m = nrows(A)
   n = ncols(A)
   rank = 0
   r = 1
   c = 1
   R = base_ring(A)
   t = R()
   while r <= m && c <= n
      if A[r, c] == 0
         i = r + 1
         while i <= m
            if !iszero(A[i, c])
               for j = 1:n
                  A[i, j], A[r, j] = A[r, j], A[i, j]
               end
               P[r], P[i] = P[i], P[r]
               break
            end
            i += 1
         end
         if i > m
            c += 1
            continue
         end
      end
      rank += 1
      d = -inv(A[r, c])
      for i = r + 1:m
         q = A[i, c]*d
         for j = c + 1:n
            t = mul!(t, A[r, j], q)
            A[i, j] = addeq!(A[i, j], t)
         end
         A[i, c] = R()
         A[i, rank] = -q
      end
      r += 1
      c += 1
   end
   inv!(P)
   return rank
end

_lu!(P::Generic.perm, A) = lu!(P, A)

function _lu(A::S, P = PermGroup(nrows(A))) where {S <: MatElem{Generic.Res{fmpz}}}
   m = nrows(A)
   n = ncols(A)
   P.n != m && error("Permutation does not match matrix")
   p = P()
   R = base_ring(A)
   U = deepcopy(A)
   L = similar(A, m, m)
   rank = _lu!(p, U)
   for i = 1:m
      for j = 1:n
         if i > j
            L[i, j] = U[i, j]
            U[i, j] = R()
         elseif i == j
            L[i, j] = R(1)
         elseif j <= m
            L[i, j] = R()
         end
      end
   end
   return rank, p, L, U
end

_lu(A, P = PermGroup(nrows(A))) = lu(A, P)

function _right_kernel(a::T) where {T <: Union{Generic.Mat{Generic.Res{fmpz}}, Generic.Mat{Generic.ResF{fmpz}}}}
  r, b = _rref(a)
  pivots = Array{Int}(undef, r)
  nonpivots = Array{Int}(undef, ncols(b) - r)
  X = zero_matrix(base_ring(a),ncols(b),ncols(b) - r)

  if r == 0
    return vcat(identity_matrix(base_ring(a), ncols(b) - r), zero_matrix(base_ring(a), r, ncols(b) - r)), ncols(b)
  elseif !((ncols(b) - r) == 0)
    i = 1
    j = 1
    k = 1
    for i in 1:r
      while b[i,j] == 0
        nonpivots[k] = j
        k += 1
        j += 1
      end
      pivots[i] = j
      j += 1
    end
    while k <= ncols(b) - r
      nonpivots[k] = j
      k += 1
      j += 1
    end

    for i in 1:ncols(b) - r
      for j in 1:r
        X[pivots[j],i] = - b[j,nonpivots[i]]
      end
      X[nonpivots[i],i] = 1
    end
  end
  return X, ncols(b) - r
end

function kernel_mod(a::fmpz_mat, m::fmpz)
  b = deepcopy(a)
  for i in 1:nrows(b)
    for j in 1:ncols(b)
      b[i,j] = b[i,j] % m
    end
  end

  # fmpz_mat_rref_mod assumes that input is reduced modulo m
  r = ccall((:fmpz_mat_rref_mod, :libflint), Int, (Ptr{Nothing}, Ref{fmpz_mat}, Ref{fmpz}), C_NULL, b, m)
  pivots = Array{Int}(undef, r)
  nonpivots = Array{Int}(undef, ncols(b) - r)
  X = zero_matrixSpace(FlintZZ,ncols(b),ncols(b))

  if r == 0
    return identity_matrix(FlintZZ, ncols(b))
  elseif !((ncols(b) - r) == 0)
    i = 1
    j = 1
    k = 1
    for i in 1:r
      while b[i,j] == 0
        nonpivots[k] = j
        k += 1
        j += 1
      end
      pivots[i] = j
      j += 1
    end
    while k <= ncols(b) - r
      nonpivots[k] = j
      k += 1
      j += 1
    end

    for i in 1:ncols(b) - r
      for j in 1:r
        X[pivots[j],i] = - FlintZZ(b[j,nonpivots[i]])
      end
      X[nonpivots[i],i] = FlintZZ(1)
    end
  end
  return X, r
end

# Another kernel function
function _kernel(x::fmpz_mat)
  H, U = hnf_with_transform(x)
  i = 1
  for outer i in 1:nrows(H)
    if iszero_row(H, i)
      break
    end
  end
  return sub(U, i:nrows(U), 1:ncols(U))
end

################################################################################
#
#  Copy matrix into another matrix
#
################################################################################

# Copy B into A at position (i, j)
function _copy_matrix_into_matrix(A::fmpz_mat, i::Int, j::Int, B::fmpz_mat)
  for k in 0:nrows(B) - 1
    for l in 0:ncols(B) - 1
      d = ccall((:fmpz_mat_entry, :libflint),
                Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), B, k, l)
      t = ccall((:fmpz_mat_entry, :libflint),
                Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), A, i - 1 + k, j - 1 + l)
      ccall((:fmpz_set, :libflint), Nothing, (Ptr{fmpz}, Ptr{fmpz}), t, d)
    end
  end
end

@doc Markdown.doc"""
    isposdef(a::fmpz_mat) -> Bool

> Tests if $a$ positive definite by testing if all principal minors
> have positive determinant.
"""
function isposdef(a::fmpz_mat)
  for i=1:nrows(a)
    if det(sub(a, 1:i, 1:i)) <= 0
      return false
    end
  end
  return true
end

#scales the i-th column of a by 2^d[1,i]
function mult_by_2pow_diag!(a::Array{BigFloat, 2}, d::fmpz_mat)
  s = size(a)
  R = RealRing()::_RealRing
  tmp_mpz::BigInt = R.z1
  for i = 1:s[1]
    for j = 1:s[2]
      e = ccall((:mpfr_get_z_2exp, :libmpfr), Clong, (Ref{BigInt}, Ref{BigFloat}), tmp_mpz, a[i,j])
      ccall((:mpfr_set_z_2exp, :libmpfr), Nothing, (Ref{BigFloat}, Ref{BigInt}, Clong, Int32), a[i,j], tmp_mpz, e+Clong(Int(d[1,j])), __get_rounding_mode())
    end
  end
end

#converts BigFloat -> fmpz via round(a*2^l), in a clever(?) way
function round_scale(a::Array{BigFloat, 2}, l::Int)
  s = size(a)
  b = zero_matrix(FlintZZ, s[1], s[2])
  return round_scale!(b, a, l)
end
 
function round_scale!(b::fmpz_mat, a::Array{BigFloat, 2}, l::Int)
  s = size(a)
  R = RealRing()::_RealRing

  local tmp_mpz::BigInt, tmp_fmpz::fmpz
  tmp_mpz = R.z1
  tmp_fmpz = R.zz1
  tmp_mpfr = deepcopy(a[1,1])  #cannot use the R.?? tmp variable as it may/will
                               #have the wrong precision

  rd = __get_rounding_mode()                             
  for i = 1:s[1]
    for j = 1:s[2]
      e = a[i,j].exp
      a[i,j].exp += l
      ccall((:mpfr_round, :libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Int32), tmp_mpfr, a[i,j], rd)
      a[i,j].exp = e
      f = ccall((:mpfr_get_z_2exp, :libmpfr), Clong, (Ref{BigInt}, Ref{BigFloat}),
        tmp_mpz, tmp_mpfr)
      ccall((:fmpz_set_mpz, :libflint), Nothing, (Ref{fmpz}, Ref{BigInt}), tmp_fmpz, tmp_mpz)
      if f > 0  
        ccall((:fmpz_mul_2exp, :libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, UInt), tmp_fmpz, tmp_fmpz, f)
      else
        ccall((:fmpz_tdiv_q_2exp, :libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, UInt), tmp_fmpz, tmp_fmpz, -f);
      end
      setindex!(b, tmp_fmpz, i, j)
    end
  end
  return b
end

function round_scale!(b::fmpz_mat, a::arb_mat, l::Int)
  s = size(a)

  R = base_ring(a)
  r = R()
  for i = 1:s[1]
    for j = 1:s[2]
      v = ccall((:arb_mat_entry_ptr, :libarb), Ptr{arb},
                    (Ref{arb_mat}, Int, Int), a, i - 1, j - 1)
      ccall((:arb_mul_2exp_si, :libarb), Nothing, (Ref{arb}, Ptr{arb}, Int), r, v, l)
      b[i,j] = round(fmpz, r)
    end
  end
  return b
end

function shift!(g::fmpz_mat, l::Int)
  for i=1:nrows(g)
    for j=1:ncols(g)
      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), g, i-1, j-1)
      if l > 0
        ccall((:fmpz_mul_2exp, :libflint), Nothing, (Ptr{fmpz}, Ptr{fmpz}, Int), z, z, l)
      else
        ccall((:fmpz_tdiv_q_2exp, :libflint), Nothing, (Ptr{fmpz}, Ptr{fmpz}, Int), z, z, -l)
      end
    end
  end
  return g
end


@doc Markdown.doc"""
***
    mod!(M::fmpz_mat, p::fmpz) 
> Reduces every entry modulo $p$ in-place, ie. applies the mod function to every entry.
"""
function mod!(M::fmpz_mat, p::fmpz)
  for i=1:nrows(M)
    for j=1:ncols(M)
      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), M, i - 1, j - 1)
      ccall((:fmpz_mod, :libflint), Nothing, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), z, z, p)
    end
  end
  nothing
end

@doc Markdown.doc"""
***
    mod(M::fmpz_mat, p::fmpz) -> fmpz_mat
> Reduces every entry modulo $p$, ie. applies the mod function to every entry.
"""
function mod(M::fmpz_mat, p::fmpz)
  N = deepcopy(M)
  mod!(N, p)
  return N
end

@doc Markdown.doc"""
***
    vcat(A::Array{Generic.Mat, 1}) -> Generic.Mat
    vcat(A::Array{fmpz_mat}, 1}) -> fmpz_mat
> Forms a big matrix my vertically concatenating the matrices in $A$.
> All component matrices need to have the same number of columns.
"""
function vcat(A::Array{Generic.Mat{T}, 1}) where T
  if any(x->ncols(x) != ncols(A[1]), A)
    error("Matrices must have same number of columns")
  end
  M = zero_matrix(base_ring(A[1]), sum(rows, A), ncols(A[1]))
  s = 0
  for i=A
    for j=1:nrows(i)
      for k=1:ncols(i)
        M[s+j, k] = i[j,k]
      end
    end
    s += nrows(i)
  end
  return M
end

function vcat(A::Array{fmpz_mat, 1})
  if any(x->ncols(x) != ncols(A[1]), A)
    error("Matrices must have same number of columns")
  end
  M = zero_matrix(base_ring(A[1]), sum(nrows, A), ncols(A[1]))
  s = 0
  for i=A
    for j=1:nrows(i)
      for k=1:ncols(i)
        M[s+j, k] = i[j,k]
      end
    end
    s += nrows(i)
  end
  return M
end

function vcat(A::Array{nmod_mat, 1})
  if any(x->ncols(x) != ncols(A[1]), A)
    error("Matrices must have same number of columns")
  end
  M = zero_matrix(base_ring(A[1]), sum(nrows, A), ncols(A[1]))
  s = 0
  for i=A
    for j=1:nrows(i)
      for k=1:ncols(i)
        M[s+j, k] = i[j,k]
      end
    end
    s += nrows(i)
  end
  return M
end

################################################################################
#
#  Smith normal form with trafo
#
################################################################################

#=
g, e,f = gcdx(a, b)
U = [1 0 ; -divexact(b, g)*f 1]*[1 1; 0 1];
V = [e -divexact(b, g) ; f divexact(a, g)];

then U*[ a 0; 0 b] * V = [g 0 ; 0 l]
=#
@doc Markdown.doc"""
***
  snf_with_transform(A::fmpz_mat, l::Bool = true, r::Bool = true) -> fmpz_mat, fmpz_mat, fmpz_mat

> Given some integer matrix A, compute the Smith normal form (elementary
> divisor normal form) of A. If l and/ or r are true, then the corresponding
> left and/ or right transformation matrices are computed as well.
"""
function snf_with_transform(A::fmpz_mat, l::Bool = true, r::Bool = true)
  if r
    R = identity_matrix(FlintZZ, ncols(A))
  end

  if l
    L = identity_matrix(FlintZZ, nrows(A))
  end
  # TODO: if only one trafo is required, start with the HNF that does not
  #       compute the trafo
  #       Rationale: most of the work is on the 1st HNF..
  #
  S = deepcopy(A)
  while !isdiag(S)
    if l
      S, T = hnf_with_transform(S)
      L = T*L
    else
      S = hnf(S)
    end

    if isdiag(S)
      break
    end
    if r
      S, T = hnf_with_transform(S')
      R = T*R
    else
      S = hnf(S')
    end
    S = S'
  end
  #this is probably not really optimal...
  for i=1:min(nrows(S), ncols(S))
    if S[i,i] == 1
      continue
    end
    for j=i+1:min(nrows(S), ncols(S))
      if S[j,j] == 0
        continue
      end
      if S[i,i] != 0 && S[j,j] % S[i,i] == 0
        continue
      end
      g, e,f = gcdx(S[i,i], S[j,j])
      a = divexact(S[i,i], g)
      S[i,i] = g
      b = divexact(S[j,j], g)
      S[j,j] *= a
      if l
        # U = [1 0; -b*f 1] * [ 1 1; 0 1] = [1 1; -b*f -b*f+1]
        # so row i and j of L will be transformed. We do it naively
        # those 2x2 transformations of 2 rows should be a c-primitive
        # or at least a Nemo/Hecke primitive
        for k=1:ncols(L)
          x = -b*f
#          L[i,k], L[j,k] = L[i,k]+L[j,k], x*L[i,k]+(x+1)*L[j,k]
          L[i,k], L[j,k] = L[i,k]+L[j,k], x*(L[i,k]+L[j,k])+L[j,k]
        end
      end
      if r
        # V = [e -b ; f a];
        # so col i and j of R will be transformed. We do it naively
        # careful: at this point, R is still transposed
        for k=1:nrows(R)
          R[i, k], R[j, k] = e*R[i,k]+f*R[j,k], -b*R[i,k]+a*R[j,k]
        end
      end
    end
  end

  if l
    if r
      return S, L, R'
    else
      # last is dummy
      return S, L, L
    end
  elseif r
    # second is dummy
    return S, R, R'
  else
    # last two are dummy
    return S, S, S
  end
end

function nullspace(M::nmod_mat)
  R = base_ring(M)
  if isprime(fmpz(modulus(R)))
    k = zero_matrix(R, ncols(M), ncols(M))
    n = ccall((:nmod_mat_nullspace, :libflint), Int, (Ref{nmod_mat}, Ref{nmod_mat}), k, M)
    return (n, k)
  end

  N = hcat(M', identity_matrix(R, ncols(M)))
  ex = 0
  if nrows(N) < ncols(N)
    ex = ncols(N) - nrows(N)
    N = vcat(N, zero_matrix(R, ex, ncols(N)))
  end
  H = howell_form(N)
  nr = 1
  while nr <= nrows(H) && !iszero_row(H, nr)
    nr += 1
  end
  nr -= 1
  h = sub(H, 1:nr, 1:nrows(M))
  for i=1:nrows(h)
    if iszero_row(h, i)
      k = sub(H, i:nrows(h), nrows(M)+1:ncols(H))
      return nrows(k), k'
    end
  end
  return 0, zero_matrix(R,nrows(M),0)
end

function lift(M::FmpzMatSpace, Mp::Union{nmod_mat,Generic.Mat{Generic.Res{fmpz}}})
  @assert M.cols == ncols(Mp) && M.rows == nrows(Mp)
  N = M()
  for i=1:M.rows
    for j=1:M.cols
      N[i,j] = lift(Mp[i,j])
    end
  end
  return N
end

################################################################################
#
#  Is diagonal
#
################################################################################

@doc Markdown.doc"""
***
  isdiag(A::fmpz_mat)

> Tests if A is diagonal.
"""
function isdiag(A::fmpz_mat)
  for i = 1:ncols(A)
    for j = 1:nrows(A)
      if i != j && !iszero(A[j, i])
        return false
      end
    end
  end
  return true
end

################################################################################
#
#  Triangular solving
#
################################################################################

# Solves A x = b for A upper triangular m\times n matrix and b m\times 1.
function solve_ut(A::MatElem{T}, b::MatElem{T}) where T
  m = nrows(A)
  n = ncols(A)
  @assert m == nrows(b)
  @assert m <= n
  x = similar(A, n, 1)
  pivot_cols = Vector{Int}()
  r = 0
  last_pivot = n + 1
  for i = m:-1:1
    for j = 1:last_pivot - 1
      if iszero(A[i, j])
        continue
      end
      x[j, 1] = b[i, 1]
      for k = 1:r
        x[j, 1] -= A[i, pivot_cols[k]]*x[pivot_cols[k], 1]
      end
      x[j, 1] *= inv(A[i, j])
      last_pivot = j
      r += 1
      push!(pivot_cols, j)
      break
    end
  end
  return x
end

# Solves A x = b for A lower triangular m\times n matrix and b m\times 1.
function solve_lt(A::MatElem{T}, b::MatElem{T}) where T
  m = nrows(A)
  n = ncols(A)
  @assert m == nrows(b)
  @assert m <= n
  x = similar(A, n, 1)
  pivot_cols = Vector{Int}()
  r = 0
  last_pivot = 0
  for i = 1:m
    for j = n:-1:last_pivot + 1
      if iszero(A[i, j])
        continue
      end
      x[j, 1] = b[i, 1]
      for k = 1:r
        x[j, 1] -= A[i, pivot_cols[k]]*x[pivot_cols[k], 1]
      end
      x[j, 1] *= inv(A[i, j])
      last_pivot = j
      r += 1
      push!(pivot_cols, j)
      break
    end
  end
  return x
end

# =======================================
# Array interface for MatElem
# =======================================
#
# TODO: re-write for special types (fmpz_mat e.g.) to gain efficiency
#

length(A::Nemo.MatElem) = nrows(A) * ncols(A)
Base.ndims(A::Nemo.MatElem) = 2

function Base.size(A::Nemo.MatElem, n::Int)
  if n == 1
    return nrows(A)
  elseif n == 2
    return ncols(A)
  elseif n < 1
    error("arraysize: dimension out of range")
  else
    return 1
  end
end

function Base.axes(A::Nemo.MatElem)
  return (Base.OneTo(nrows(A)), Base.OneTo(ncols(A)))
end

function Base.axes(A::Nemo.MatElem, n::Int)
  return Base.OneTo(size(A, n))
end

function Base.eachindex(A::Nemo.MatElem)
  return Base.OneTo(length(A))
end

function Base.stride(A::Nemo.MatElem, n::Int)
  if n <= 1
    return 1
  elseif n == 2
    return nrows(A)
  else
    return length(A)
  end
end

Base.eltype(A::Nemo.MatElem{T}) where T <: Nemo.RingElem = T

getindex(A::Nemo.MatElem, n::Int) = A[1 + ((n-1) % nrows(A)), 1 + div((n-1), nrows(A))]

function setindex!(A::Nemo.MatElem{T}, n::Int, s::T) where T <: RingElem
  A[1 + ((n-1) % nrows(A)), 1 + div((n-1), nrows(A))] = s
end

function Base.iterate(A::Nemo.MatElem, state::Int = 0) 
  s = size(A)
  if state < s[1]*s[2]
    state += 1
    return A[state], state
  end
  return nothing
end

Base.IteratorSize(M::Nemo.MatElem) = Base.HasLength()
Base.IteratorEltype(M::Nemo.MatElem) = Base.HasEltype()
Base.eltype(M::Nemo.MatElem) = elem_type(base_ring(M))

function setindex!(A::Nemo.MatElem{T}, b::Nemo.MatElem{T}, ::Colon, i::Int) where T
  @assert ncols(b) == 1 && nrows(b) == nrows(A) 
  for j=1:nrows(A)
    A[j,i] = b[j]
  end
  b
end

function setindex!(A::Nemo.MatElem{T}, b::Nemo.MatElem{T}, i::Int, ::Colon) where T
  @assert nrows(b) == 1 && ncols(b) == ncols(A)
  for j=1:ncols(A)
    A[i,j] = b[j]
  end
  b
end

function setindex!(A::Nemo.MatElem, b::Array{<: Any, 1}, ::Colon, i::Int) 
  @assert length(b) == nrows(A)
  for j=1:nrows(A)
    A[j,i] = b[j]
  end
  b
end

function setindex!(A::Nemo.MatElem, b::Array{ <: Any, 1}, i::Int, ::Colon)
  @assert length(b) == ncols(A)
  for j=1:ncols(A)
    A[i,j] = b[j]
  end
  b
end

function setindex!(A::Nemo.MatElem, b, ::Colon, i::Int) 
  for j=1:nrows(A)
    A[j,i] = b
  end
  b
end

function setindex!(A::Nemo.MatElem, b, i::Int, ::Colon)
  for j=1:ncols(A)
    A[i,j] = b
  end
  b
end


getindex(A::Nemo.MatElem, i::Int, ::Colon) = A[i:i, 1:ncols(A)]
getindex(A::Nemo.MatElem, ::Colon, i::Int) = A[1:nrows(A), i:i]

function Base.hcat(A::Nemo.MatElem...)
  r = nrows(A[1])
  c = ncols(A[1])
  R = base_ring(A[1])
  for i=2:length(A)
    @assert nrows(A[i]) == r
    @assert base_ring(A[i]) == R
    c += ncols(A[i])
  end
  X = zero_matrix(R, r, c)
  o = 1
  for i=1:length(A)
    for j=1:ncols(A[i])
      X[:, o] = A[i][:, j]
      o += 1
    end
  end
  return X
end

function Base.vcat(A::Nemo.MatElem...)
  r = nrows(A[1])
  c = ncols(A[1])
  R = base_ring(A[1])
  for i=2:length(A)
    @assert ncols(A[i]) == c
    @assert base_ring(A[i]) == R
    r += nrows(A[i])
  end
  X = zero_matrix(R, r, c)
  o = 1
  for i=1:length(A)
    for j=1:nrows(A[i])
      X[o, :] = A[i][j, :]
      o += 1
    end
  end
  return X
end

function Base.cat(A::Nemo.MatElem...;dims) 
  @assert dims == (1,2) || isa(dims, Int)

  if isa(dims, Int) 
    if dims == 1
      return hcat(A...)
    elseif dims == 2
      return vcat(A...)
    else
      error("dims must be 1, 2, or (1,2)")
    end
  end

  z = [similar(x) for x = A]
  X = z[1]
  for i=1:length(A)
    if i==1
      X = hcat(A[1], z[2:end]...)
    else
      X = vcat(X, hcat(z[1:i-1]..., A[i], z[i+1:end]...))
    end
  end
  return X
end

function Base.hvcat(rows::Tuple{Vararg{Int}}, A::Nemo.MatElem...)
  B = hcat([A[i] for i=1:rows[1]]...)
  o = rows[1]
  for j=2:length(rows)
    C = hcat([A[i+o] for i=1:rows[j]]...)
    o += rows[j]
    B = vcat(B, C)
  end
  return B
end

@doc Markdown.doc"""
    reduce_mod!(A::Nemo.MatElem{T}, B::Nemo.MatElem{T}) where T <: Nemo.FieldElem

> For a reduced row echelon matrix $B$, reduce $A$ modulo $B$, ie. all the pivot
> columns will be zero afterwards.
"""
function reduce_mod!(A::Nemo.MatElem{T}, B::Nemo.MatElem{T}) where T <: Nemo.FieldElem
  @assert isrref(B)
  for h=1:nrows(A)
    j = 1
    for i=1:nrows(B)
      while iszero(B[i, j])
        j += 1
      end
      A[h, :] -= A[h, j] * B[i, :]
    end
  end
  return A
end

@doc Markdown.doc"""
    reduce_mod(A::Nemo.MatElem{T}, B::Nemo.MatElem{T}) where T <: Nemo.FieldElem -> MatElem

> For a reduced row echelon matrix $B$, reduce $A$ modulo $B$, ie. all the pivot
> columns will be zero afterwards.
"""
function Nemo.reduce_mod(A::Nemo.MatElem{T}, B::Nemo.MatElem{T}) where T <: Nemo.FieldElem
  C = deepcopy(A)
  reduce_mod!(C, B)
  return C
end

@doc Markdown.doc"""
    find_pivot(A::Nemo.MatElem{<:Nemo.RingElem}) -> Array{Int, 1}

> Find the pivot-columns of the reduced row echelon matrix $A$
"""
function find_pivot(A::Nemo.MatElem{<:Nemo.RingElem})
  @assert isrref(A)
  p = Int[]
  j = 0
  for i=1:nrows(A)
    j += 1
    if j > ncols(A)
      return p
    end
    while iszero(A[i,j])
      j += 1
      if j > ncols(A)
        return p
      end
    end
    push!(p, j)
  end
  return p
end

@doc Markdown.doc"""
    cansolve(A::Nemo.MatElem{T}, B::Nemo.MatElem{T}) where T <: Nemo.FieldElem -> Bool, MatElem
> Tries to solve $Ax = B$
"""
function Nemo.cansolve(A::Nemo.MatElem{T}, B::Nemo.MatElem{T}) where T <: Nemo.FieldElem
  R = base_ring(A)
  @assert R == base_ring(B)
  @assert nrows(A) == nrows(B)
  mu = [A B]
  rk, mu = rref(mu)
  p = find_pivot(mu)
  if any(i->i>ncols(A), p)
    return false, B
  end
  sol = zero_matrix(R, ncols(A), ncols(B))
  for i = 1:length(p)
    for j = 1:ncols(B)
      sol[p[i], j] = mu[i, ncols(A) + j]
    end
  end
  return true, sol
end

@doc Markdown.doc"""
    cansolve_with_nullspace(A::Nemo.MatElem{T}, B::Nemo.MatElem{T}) where T <: Nemo.FieldElem -> Bool, MatElem, MatElem
> Tries to solve $Ax = B$, returns a solution and the nullspace.
"""
function Nemo.cansolve_with_nullspace(A::Nemo.MatElem{T}, B::Nemo.MatElem{T}) where T <: Nemo.FieldElem
  R = base_ring(A)
  @assert R == base_ring(B)
  @assert nrows(A) == nrows(B)
  mu = [A B]
  rk, mu = rref(mu)
  p = find_pivot(mu)
  if any(i->i>ncols(A), p)
    return false, B, B
  end
  sol = zero_matrix(R, ncols(A), ncols(B))
  for i = 1:length(p)
    for j = 1:ncols(B)
      sol[p[i], j] = mu[i, ncols(A) + j]
    end
  end
  n = zero_matrix(R, ncols(A), ncols(A) - length(p))
  np = sort(setdiff(1:ncols(A), p))
  i = 0
  push!(p, ncols(A)+1)
  for j = 1:length(np)
    if np[j] >= p[i+1]
      i += 1
    end
    if i > 0
      n[p[i], j] = -mu[i, np[j]]
    end
    n[np[j], j] = 1
  end
  return true, sol, n
end

#TODO: different to cansolve*(fmpz_mat) is hnf_with_tranformation -> hnf_with_trafo
#maybe (definitely!) agree on one name and combine?

@doc Markdown.doc"""
    cansolve(A::Nemo.MatElem{T}, B::Nemo.MatElem{T}) where T <: Nemo.RingElem -> Bool, MatElem
> Tries to solve $Ax = B$ where the matrices are defined over a euclidean ring.
"""
function Nemo.cansolve(a::Nemo.MatElem{S}, b::Nemo.MatElem{S}) where S <: Nemo.RingElem
  R = base_ring(a)
  @assert R == base_ring(b)
  @assert nrows(a) == nrows(b)

  H, T = hnf_with_trafo(transpose(a))
  b = deepcopy(b)
  z = similar(a, ncols(b), ncols(a))
  l = min(nrows(a), ncols(a))
  for i = 1:ncols(b)
    for j = 1:l
      k = 1
      while k <= ncols(H) && iszero(H[j, k])
        k += 1
      end
      if k > ncols(H)
        continue
      end
      q, r = divrem(b[k, i], H[j, k])
      if !iszero(r)
        return false, b
      end
      for h = k:ncols(H)
        b[h, i] -= q*H[j, h]
      end
      z[i, j] = q
    end
  end
  if !iszero(b)
    return false, b
  end
  return true, transpose(z*T)
end

@doc Markdown.doc"""
    cansolve_with_nullspace(A::Nemo.MatElem{T}, B::Nemo.MatElem{T}) where T <: Nemo.RingElem -> Bool, MatElem, MatElem
> Tries to solve $Ax = B$ where the matrices are defined over a euclidean ring. If successful,
> a basis for the nullspace is computed as well.
"""
function Nemo.cansolve_with_nullspace(a::Nemo.MatElem{S}, b::Nemo.MatElem{S}) where S <: Nemo.RingElem
  R = base_ring(a)
  @assert R == base_ring(b)
  @assert nrows(a) == nrows(b)

  H, T = hnf_with_trafo(transpose(a))
  z = similar(a, ncols(b), ncols(a))
  l = min(nrows(a), ncols(a))
  for i=1:ncols(b)
    for j=1:l
      k = 1
      while k <= ncols(H) && iszero(H[j, k])
        k += 1
      end
      if k > ncols(H)
        continue
      end
      q, r = divrem(b[k, i], H[j, k])
      if !iszero(r)
        return false, b, b
      end
      for h=k:ncols(H)
        b[h, i] -= q*H[j, h]
      end
      z[i, k] = q
    end
  end
  if !iszero(b)
    return false, b, b
  end

  for i = nrows(H):-1:1
    for j = 1:ncols(H)
      if !iszero(H[i,j])
        N = similar(a, ncols(a), nrows(H) - i)
        for k = 1:nrows(N)
          for l = 1:ncols(N)
            N[k,l] = T[nrows(T) - l + 1, k]
          end
        end
        return true, transpose(z*T), N
      end
    end
  end
  N =  similar(a, ncols(a), 0)

  return true, (z*T), N
end

@doc Markdown.doc"""
   elementary_divisors(A::fmpz_mat) -> Array{fmpz, 1}
> The elementary divisors of $A$, ie. the diagonal entries of the Smith normal form of $A$.
"""
function elementary_divisors(A::fmpz_mat)
  s = snf(A)
  return [s[i,i] for i=1:min(ncols(s), nrows(s))]
end

@doc Markdown.doc"""
   maximal_elementary_divisors(A::fmpz_mat) -> fmpz
> The largest elementary divisor of $A$, ie. the last diagonal entry of the Smith normal form of $A$.
"""
function maximal_elementary_divisor(A::fmpz_mat)
  return elementary_divisors(A)[end]
end

################################################################################
#
#  Solve with unique solution
#
################################################################################

function _solve_unique(A::T, B::T) where {S <: FieldElem, T <: MatElem{S}}
  X = zero_matrix(base_ring(A), ncols(B), nrows(A))

  r, per, L, U = lu(B) # P*M1 = L*U

  inv!(per)
  #@assert B == per*L*U
  Ap = inv(per)*A
  Y = similar(A)

  for i in 1:ncols(Y)
    for j in 1:nrows(Y)
      s = Ap[j, i]
      for k in 1:j-1
        s = s - Y[k, i]*L[j, k]
      end
      Y[j, i] = s
    end
  end

  #@assert Ap == L*Y

  YY = sub(Y, 1:r, 1:ncols(Y))
  UU = sub(U, 1:r, 1:r)
  X = inv(UU)*YY

  #@assert Y == U * X

  @assert B*X == A
  return X
end

################################################################################
#
#  Function to convert a matrix to array
#
################################################################################

function to_array(M::fmpq_mat)
  A = Vector{fmpq}(undef, ncols(M)*nrows(M))
  for i = 1:nrows(M)
    for j = 1:ncols(M)
      A[(i-1)*ncols(M) + j] = M[i, j]
    end
  end
  return A
end

function Nemo.minpoly(M::MatElem)
  k = base_ring(M)
  kx, x = PolynomialRing(k, cached = false)
  return minpoly(kx, M)
end

function Nemo.charpoly(M::MatElem)
  k = base_ring(M)
  kx, x = PolynomialRing(k, cached = false)
  return charpoly(kx, M)
end
