export iszero_row, howell_form, kernel_basis, isdiagonal, diagonal

import Nemo.matrix

import Base.vcat

import LinearAlgebra
LinearAlgebra.dot(a::RingElem, b::RingElem) = a*b

################################################################################
#
#  Dense matrix types
#
################################################################################

dense_matrix_type(::Type{T}) where {T} = Generic.MatSpaceElem{T}

# TODO (easy): Check if the following can be simplified to
# coefficient_type(::Type{<:Mat{T}}} where {T} = T
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
#  Unsafe functions for generic matrices
#
################################################################################

#function zero!(a::MatElem)
#  for i in 1:nrows(a)
#    for j in 1:ncols(a)
#      a[i, j] = zero!(a[i, j])
#    end
#  end
#  return a
#end

function mul!(c::MatElem, a::MatElem, b::MatElem)
  ncols(a) != nrows(b) && error("Incompatible matrix dimensions")
  nrows(c) != nrows(a) && error("Incompatible matrix dimensions")
  ncols(c) != ncols(b) && error("Incompatible matrix dimensions")

  if c === a || c === b
    d = parent(a)()
    return mul!(d, a, b)
  end

  t = base_ring(a)()
  for i = 1:nrows(a)
    for j = 1:ncols(b)
      c[i, j] = zero!(c[i, j])
      for k = 1:ncols(a)
        c[i, j] = addmul_delayed_reduction!(c[i, j], a[i, k], b[k, j], t)
      end
      c[i, j] = reduce!(c[i, j])
    end
  end
  return c
end

function add!(c::MatElem, a::MatElem, b::MatElem)
  parent(a) != parent(b) && error("Parents don't match.")
  parent(c) != parent(b) && error("Parents don't match.")
  for i = 1:nrows(c)
    for j = 1:ncols(c)
      c[i, j] = add!(c[i, j], a[i, j], b[i, j])
    end
  end
  return c
end

function mul!(a::nmod_mat, b::nmod_mat, c::nmod)
  ccall((:nmod_mat_scalar_mul, libflint), Nothing,
          (Ref{nmod_mat}, Ref{nmod_mat}, UInt), a, b, c.data)
  return a
end

################################################################################
#
#  Denominator
#
################################################################################

# This function is really slow...
function denominator(M::fmpq_mat)
  d = one(FlintZZ)
  for i in 1:nrows(M)
    for j in 1:ncols(M)
      d = lcm!(d, d, denominator(M[i, j]))
    end
  end
  return d
end

################################################################################
#
#  Saturation
#
################################################################################

@doc Markdown.doc"""
    saturate(A::fmpz_mat) -> fmpz_mat

Computes the saturation of $A$, that is, a basis for $\mathbf{Q}\otimes M \cap
\mathbf{Z}^n$, where $M$ is the row span of $A$ and $n$ the number of rows of
$A$.

Equivalently, return $TA$ for an invertible rational matrix $T$ such that $TA$
is integral and the elementary divisors of $TA$ are all trivial.
"""
function saturate(A::fmpz_mat)
  #row saturation: want
  #  TA in Z, T in Q and elem_div TA = [1]
  #
  #  AT = H (in HNF), then A = HT^-1 and H^-1A = T^-1
  # since T is uni-mod, H^-1 A is in Z with triv. elm. div
  H = transpose(A)
  H = hnf!(H)
  H = sub(H, 1:ncols(H), 1:ncols(H))
ccall((:fmpz_mat_transpose, libflint), Nothing,
    (Ref{fmpz_mat}, Ref{fmpz_mat}), H, H)
Hi, d = pseudo_inv(H)
  S = Hi*A
divexact!(S, S, d)
#  @hassert :HNF 1  d*Sd == S
  return S
end


function transpose!(A::fmpz_mat, B::fmpz_mat)
  GC.@preserve A B begin
    ccall((:fmpz_mat_transpose, libflint), Nothing,
      (Ref{fmpz_mat}, Ref{fmpz_mat}), A, B)
  end
  return nothing
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


function matrix(A::Matrix{fmpz})
  m = matrix(FlintZZ, A)
  return m
end

function matrix(A::Matrix{T}) where T <: RingElem
  r, c = size(A)
  (r < 0 || c < 0) && error("Array must be non-empty")
  m = matrix(parent(A[1, 1]), A)
  return m
end

function matrix(A::Vector{T}) where T <: RingElem
  return matrix(reshape(A,length(A),1))
end

function scalar_matrix(R::Ring, n::Int, a::RingElement)
  b = R(a)
  z = zero_matrix(R, n, n)
  for i in 1:n
    z[i, i] = b
  end
  return z
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
  GC.@preserve M begin
    for j = 1:ncols(M)
      m = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), M, i - 1, j - 1)
      fl = ccall((:fmpz_is_zero, libflint), Bool, (Ptr{fmpz},), m)
      if !fl
        return false
      end
    end
  end
  return true
end

function iszero_entry(M::fmpz_mat, i::Int, j::Int)
  GC.@preserve M begin
    m = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), M, i - 1, j - 1)
    fl = ccall((:fmpz_is_zero, libflint), Bool, (Ptr{fmpz},), m)
    return fl
  end
end

function ispositive_entry(M::fmpz_mat, i::Int, j::Int)
  GC.@preserve M begin
    m = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), M, i - 1, j - 1)
    fl = ccall((:fmpz_sgn, libflint), Int, (Ptr{fmpz},), m)
    return isone(fl)
  end
end



function iszero_row(M::nmod_mat, i::Int)
  zero = UInt(0)
  for j in 1:ncols(M)
    t = ccall((:nmod_mat_get_entry, libflint), Base.GMP.Limb, (Ref{nmod_mat}, Int, Int), M, i - 1, j - 1)
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

function iszero_row(M::Matrix{T}, i::Int) where T <: Integer
  for j = 1:Base.size(M, 2)
    if M[i,j] != 0
      return false
    end
  end
  return true
end

function iszero_row(M::Matrix{fmpz}, i::Int)
  for j = 1:Base.size(M, 2)
    if M[i,j] != 0
      return false
    end
  end
  return true
end

function iszero_row(M::Matrix{T}, i::Int) where T <: RingElem
  for j in 1:Base.size(M, 2)
    if !iszero(M[i,j])
      return false
    end
  end
  return true
end

function divexact!(a::fmpz_mat, b::fmpz_mat, d::fmpz)
  ccall((:fmpz_mat_scalar_divexact_fmpz, libflint), Nothing,
               (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{fmpz}), a, a, d)
end

function mul!(a::fmpz_mat, b::fmpz_mat, c::fmpz)
  ccall((:fmpz_mat_scalar_mul_fmpz, libflint), Nothing,
                  (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{fmpz}), a, b, c)
end

function _hnf(x::T, shape::Symbol = :upperright) where {T <: MatElem}
  if shape == :lowerleft
    h = hnf(reverse_cols(x))
    reverse_cols!(h)
    reverse_rows!(h)
    return h::T
  end
  return hnf(x)::T
end

function _hnf_with_transform(x::T, shape::Symbol = :upperright) where {T <: MatElem}
  if shape == :lowerleft
    h, t = hnf_with_transform(reverse_cols(x))
    reverse_cols!(h)
    reverse_rows!(h)
#    reverse_cols!(t)
    reverse_rows!(t)
    @assert t*x==h
    return h::T, t::T
  end
  return hnf_with_transform(x)::Tuple{T, T}
end


function _hnf!(x::T, shape::Symbol = :upperright) where {T <: MatElem}
  if shape == :lowerleft
    reverse_cols!(x)
    hnf!(x)
    reverse_cols!(x)
    reverse_rows!(x)
    return x::T
  end
  hnf!(x)
  return x::T
end

function hnf!(x::fmpz_mat)
  ccall((:fmpz_mat_hnf, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}), x, x)
  return x
end

function _hnf_modular_eldiv(x::fmpz_mat, m::fmpz, shape::Symbol = :upperright)
  if shape == :lowerleft
    h = hnf_modular_eldiv!(reverse_cols(x), m)
    reverse_cols!(h)
    reverse_rows!(h)
    return h
  elseif shape == :upperright
    return hnf_modular_eldiv(x, m)
  else
    error("Shape $shape not supported")
  end
end

function hnf_modular_eldiv!(x::fmpz_mat, d::fmpz, shape::Symbol = :upperright)
   (nrows(x) < ncols(x)) &&
                error("Matrix must have at least as many rows as columns")
   if shape == :upperright
     ccall((:fmpz_mat_hnf_modular_eldiv, libflint), Nothing,
                  (Ref{fmpz_mat}, Ref{fmpz}), x, d)
     return x
   elseif shape == :lowerleft
     reverse_cols!(x)
     ccall((:fmpz_mat_hnf_modular_eldiv, libflint), Nothing,
                 (Ref{fmpz_mat}, Ref{fmpz}), x, d)
     reverse_cols!(x)
     reverse_rows!(x)
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
      while j >= 0 && iszero_entry(x, i, j)
        j = j - 1
      end
      if j == -1
        break
      end
      if !ispositive_entry(x, i, j)
        return false
      end
      piv = x[i, j]
      j >= j_old && return false
      for k in i+1:r
        if !iszero(x[k, j]) && (!ispositive_entry(x, k, j) || compare_index(x, k, j, piv) > 0)
          return false
        end
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
#  Is LLL?
#
################################################################################

function islll_reduced(x::fmpz_mat, ctx::lll_ctx = lll_ctx(0.99, 0.51))
  b = ccall((:fmpz_lll_is_reduced_d, libflint), Cint,
            (Ref{fmpz_mat}, Ref{lll_ctx}), x, ctx)
  return Bool(b)
end

################################################################################
#
################################################################################

function maximum(f::typeof(abs), a::fmpz_mat)
  m = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, 0,0)
  for i=1:nrows(a)
    for j=1:ncols(a)
      z = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, i-1, j-1)
      if ccall((:fmpz_cmpabs, libflint), Cint, (Ptr{fmpz}, Ptr{fmpz}), m, z) < 0
        m = z
      end
    end
  end
  r = fmpz()
  ccall((:fmpz_abs, libflint), Nothing, (Ref{fmpz}, Ptr{fmpz}), r, m)
  return r
end

function maximum(a::fmpz_mat)
  m = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, 0,0)
  for i=1:nrows(a)
    for j=1:ncols(a)
      z = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, i-1, j-1)
      if ccall((:fmpz_cmp, libflint), Cint, (Ptr{fmpz}, Ptr{fmpz}), m, z) < 0
        m = z
      end
    end
  end
  r = fmpz()
  ccall((:fmpz_set, libflint), Nothing, (Ref{fmpz}, Ptr{fmpz}), r, m)
  return r
end

function minimum(a::fmpz_mat)
  m = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, 0,0)
  for i=1:nrows(a)
    for j=1:ncols(a)
      z = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, i-1, j-1)
      if ccall((:fmpz_cmp, libflint), Cint, (Ptr{fmpz}, Ptr{fmpz}), m, z) > 0
        m = z
      end
    end
  end
  r = fmpz()
  ccall((:fmpz_set, libflint), Nothing, (Ref{fmpz}, Ptr{fmpz}), r, m)
  return r
end

################################################################################
#
#  Reduce mod hnf
#
################################################################################

# H must be in upper right HNF form
function reduce_mod_hnf_ur!(a::fmpz_mat, H::fmpz_mat)
  GC.@preserve a H begin
    for c = 1:nrows(a)
      j = 1
      for i=1:min(nrows(H), ncols(H))
        while j <= ncols(H) && iszero(H[i, j])
          j += 1
        end
        if j > ncols(H)
          break
        end
        n = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, c - 1, j - 1)
        m = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), H, i - 1, j - 1)
        q = fmpz()
        ccall((:fmpz_fdiv_q, libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), q, n, m)
        #q = fdiv(a[c, j], H[i, j])
        fl = ccall((:fmpz_is_zero, libflint), Bool, (Ref{fmpz},), q)
        if fl
          continue
        end
        for k = j:ncols(a)
          t = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, c - 1, k - 1)
          l = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), H, i - 1, k - 1)
          ccall((:fmpz_submul, libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), t, q, l)
          #a[c, k] = a[c, k] - q * H[i, k]
        end
      end
    end
  end
  return nothing
end

function reduce_mod_hnf_ll!(a::fmpz_mat, H::fmpz_mat)
  GC.@preserve a H begin
    for c = 1:nrows(a)
      j = ncols(H)
      for i = nrows(H):-1:1
        while j > 0 && iszero(H[i, j])
          j -= 1
        end
        if iszero(j)
          break
        end
        n = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, c - 1, j - 1)
        m = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), H, i - 1, j - 1)
        q = fmpz()
        ccall((:fmpz_fdiv_q, libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), q, n, m)
        #q = fdiv(a[c, j], H[i, j])
        fl = ccall((:fmpz_is_zero, libflint), Bool, (Ref{fmpz},), q)
        if fl
          continue
        end
        for k = 1:j
          t = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, c - 1, k - 1)
          l = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), H, i - 1, k - 1)
          ccall((:fmpz_submul, libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}), t, q, l)
        end
      end
    end
  end
  return nothing
end

################################################################################
#
#  Lift of matrices to overrings
#
################################################################################

@doc Markdown.doc"""
    lift(a::Generic.Mat{Generic.Res{fmpz}}) -> fmpz_mat

It returns a lift of the matrix to the integers.
"""
function lift(a::Generic.Mat{Generic.Res{fmpz}})
  z = zero_matrix(FlintZZ, nrows(a), ncols(a))
  for i in 1:nrows(a)
    for j in 1:ncols(a)
      z[i, j] = lift(a[i, j])
    end
  end
  return z
end

function lift(a::fmpz_mod_mat)
  z = zero_matrix(FlintZZ, nrows(a), ncols(a))
  GC.@preserve a z begin
    for i in 1:nrows(a)
      for j in 1:ncols(a)
        m = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), z, i - 1, j - 1)
        n = ccall((:fmpz_mod_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mod_mat}, Int, Int), a, i - 1 , j - 1)
        ccall((:fmpz_set, libflint), Nothing, (Ptr{fmpz}, Ptr{fmpz}), m, n)
        #z[i, j] = lift(a[i, j])
      end
    end
  end
  return z
end

function lift_nonsymmetric(a::nmod_mat)
  z = fmpz_mat(nrows(a), ncols(a))
  z.base_ring = FlintZZ
  ccall((:fmpz_mat_set_nmod_mat_unsigned, Hecke.libflint), Nothing,
          (Ref{fmpz_mat}, Ref{nmod_mat}), z, a)
  return z
end

function lift_nonsymmetric(a::gfp_mat)
  z = fmpz_mat(nrows(a), ncols(a))
  z.base_ring = FlintZZ
  ccall((:fmpz_mat_set_nmod_mat_unsigned, Hecke.libflint), Nothing,
          (Ref{fmpz_mat}, Ref{gfp_mat}), z, a)
  return z
end


if Nemo.version() > v"0.15.1"
  function lift(a::Generic.Mat{Nemo.fmpz_mod})
    z = zero_matrix(FlintZZ, nrows(a), ncols(a))
    for i in 1:nrows(a)
      for j in 1:ncols(a)
        z[i, j] = lift(a[i, j])
      end
    end
    return z
  end
end

function lift_unsigned(a::nmod_mat)
  z = zero_matrix(FlintZZ, nrows(a), ncols(a))
  ccall((:fmpz_mat_set_nmod_mat_unsigned, libflint), Nothing,
          (Ref{fmpz_mat}, Ref{nmod_mat}), z, a)
  return z
end

################################################################################
#
#  Kernel function
#
################################################################################
@doc Markdown.doc"""
    kernel_basis(a::MatElem{T}, side:: Symbol) -> Vector{Vector{T}} where {T <: AbstractAlgebra.FieldElem}

It returns a basis for the kernel of the matrix defined over a field. If side is $:right$ or not
specified, the right kernel is computed. If side is $:left$, the left kernel is computed.
"""
function kernel_basis(A::MatElem{T}, side::Symbol = :right) where T<: AbstractAlgebra.FieldElem
  if side == :right
    return right_kernel_basis(A)
  elseif side == :left
    return left_kernel_basis(A)
  else
    error("Unsupported argument: :$side for side: Must be :left or :right")
  end
end

@doc Markdown.doc"""
    right_kernel_basis(a::MatElem{T}) -> Vector{Vector{T}} where {T <: AbstractAlgebra.FieldElem}

It returns a basis for the right kernel of the matrix defined over a field.
"""
function right_kernel_basis(a::MatElem{T}) where T <: AbstractAlgebra.FieldElem
  R = base_ring(a)
  n, z = nullspace(a)
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

@doc Markdown.doc"""
    left_kernel_basis(a::MatElem{T}) -> Vector{Vector{T}}

It returns a basis for the left kernel of the matrix.
"""
left_kernel_basis(a::MatElem{T}) where T <: AbstractAlgebra.FieldElem = right_kernel_basis(transpose(a))



@doc Markdown.doc"""
    kernel(a::MatElem{T}; side::Symbol = :right) -> Int, MatElem{T}

It returns a tuple $(n, M)$, where $n$ is the rank of the kernel and $M$ is a basis for it. If side is $:right$ or not
specified, the right kernel is computed. If side is $:left$, the left kernel is computed.
"""
function kernel(A::MatElem; side::Symbol = :right)
  if side == :right
    return right_kernel(A)
  elseif side == :left
    return left_kernel(A)
  else
    error("Unsupported argument: :$side for side: Must be :left or :right")
  end
end

function right_kernel(x::gfp_mat)
  z = zero_matrix(base_ring(x), ncols(x), max(nrows(x),ncols(x)))
  n = ccall((:nmod_mat_nullspace, libflint), Int, (Ref{gfp_mat}, Ref{gfp_mat}), z, x)
  return n, z
end

function left_kernel(x::gfp_mat)
  n, M = right_kernel(transpose(x))
  return n, transpose(M)
end

@doc Markdown.doc"""
    left_kernel(a::fmpz_mat) -> Int, fmpz_mat

It returns a tuple $(n, M)$ where $M$ is a matrix whose rows generate
the kernel of $a$ and $n$ is the rank of the kernel.
"""
function left_kernel(x::fmpz_mat)
  if nrows(x) == 0
    return 0, zero(x, 0, 0)
  end
  x1 = transpose(hnf(transpose(x)))
  H, U = hnf_with_transform(x1)
  i = 1
  for outer i in 1:nrows(H)
    if iszero_row(H, i)
      break
    end
  end
  if iszero_row(H, i)
    return nrows(U)-i+1, view(U, i:nrows(U), 1:ncols(U))
  else
    return 0, zero_matrix(FlintZZ, 0, ncols(U))
  end
end

right_kernel(M::MatElem) = nullspace(M)

function left_kernel(M::MatElem)
  rk, M1 = nullspace(transpose(M))
  return rk, transpose(M1)
end

function right_kernel(x::fmpz_mat)
  n, M = left_kernel(transpose(x))
  return n, transpose(M)
end

function right_kernel(M::nmod_mat)
  R = base_ring(M)
  if isprime(modulus(R))
    k = zero_matrix(R, ncols(M), ncols(M))
    n = ccall((:nmod_mat_nullspace, libflint), Int, (Ref{nmod_mat}, Ref{nmod_mat}), k, M)
    return n, k
  end

  H = hcat(transpose(M), identity_matrix(R, ncols(M)))
  if nrows(H) < ncols(H)
    H = vcat(H, zero_matrix(R, ncols(H) - nrows(H), ncols(H)))
  end
  howell_form!(H)
  nr = 1
  while nr <= nrows(H) && !iszero_row(H, nr)
    nr += 1
  end
  nr -= 1
  h = sub(H, 1:nr, 1:nrows(M))
  for i=1:nrows(h)
    if iszero_row(h, i)
      k = sub(H, i:nrows(h), nrows(M)+1:ncols(H))
      return nrows(k), transpose(k)
    end
  end
  return 0, zero_matrix(R,nrows(M),0)
end

function left_kernel(a::nmod_mat)
  n, M = right_kernel(transpose(a))
  return n, transpose(M)
end

function right_kernel(M::fmpz_mod_mat)
  R = base_ring(M)
  N = hcat(transpose(M), identity_matrix(R, ncols(M)))
  if nrows(N) < ncols(N)
    N = vcat(N, zero_matrix(R, ncols(N) - nrows(N), ncols(N)))
  end
  howell_form!(N)
  H = N
  nr = 1
  while nr <= nrows(H) && !iszero_row(H, nr)
    nr += 1
  end
  nr -= 1
  h = sub(H, 1:nr, 1:nrows(M))
  for i=1:nrows(h)
    if iszero_row(h, i)
      k = sub(H, i:nrows(h), nrows(M)+1:ncols(H))
      return nrows(k), transpose(k)
    end
  end
  return 0, zero_matrix(R,nrows(M),0)
end

function left_kernel(a::fmpz_mod_mat)
  n, M = right_kernel(transpose(a))
  return n, transpose(M)
end

################################################################################
#
#  Kernel over different rings
#
################################################################################

@doc Markdown.doc"""
    kernel(a::MatrixElem{T}, R::Ring; side::Symbol = :right) -> n, MatElem{elem_type(R)}

It returns a tuple $(n, M)$, where $n$ is the rank of the kernel over $R$ and $M$ is a basis for it. If side is $:right$ or not
specified, the right kernel is computed. If side is $:left$, the left kernel is computed.
"""
function kernel(M::MatrixElem, R::Ring; side::Symbol = :right)
  MP = change_base_ring(R, M)
  return kernel(MP, side = side)
end

################################################################################
#
#  Diagonal (block) matrix creation
#
################################################################################

@doc Markdown.doc"""
    diagonal_matrix(x::Vector{T}) where T <: RingElem -> MatElem{T}

Returns a diagonal matrix whose diagonal entries are the elements of $x$.
"""
function diagonal_matrix(x::Vector{T}) where T <: RingElem
  M = zero_matrix(parent(x[1]), length(x), length(x))
  for i = 1:length(x)
    M[i, i] = x[i]
  end
  return M
end

function diagonal_matrix(x::T...) where T <: RingElem
  return diagonal_matrix(collect(x))
end

@doc Markdown.doc"""
    diagonal_matrix(x::Vector{T}) where T <: MatElem -> MatElem

Returns a block diagonal matrix whose diagonal blocks are the matrices in $x$.
"""
function diagonal_matrix(x::Vector{T}) where T <: MatElem
  return cat(x..., dims = (1, 2))::T
end

function diagonal_matrix(x::T...) where T <: MatElem
  return cat(x..., dims = (1, 2))::T
end
################################################################################
#
#  Copy matrix into another matrix
#
################################################################################

# Copy B into A at position (i, j)
function _copy_matrix_into_matrix(A::fmpz_mat, i::Int, j::Int, B::fmpz_mat)
  @GC.preserve A B begin
    for k in 0:nrows(B) - 1
      for l in 0:ncols(B) - 1
        d = ccall((:fmpz_mat_entry, libflint),
                  Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), B, k, l)
        t = ccall((:fmpz_mat_entry, libflint),
                  Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), A, i - 1 + k, j - 1 + l)
        ccall((:fmpz_set, libflint), Nothing, (Ptr{fmpz}, Ptr{fmpz}), t, d)
      end
    end
  end
end

function _copy_matrix_into_matrix(A::MatElem, r::Vector{Int}, c::Vector{Int}, B::MatElem)
  for i = 1:length(r)
    for j = 1:length(c)
      A[r[i], c[j]] = B[i, j]
    end
  end
  return nothing
end

@doc Markdown.doc"""
    isposdef(a::fmpz_mat) -> Bool

Tests if $a$ is positive definite by testing if all principal minors
have positive determinant.
"""
function isposdef(a::fmpz_mat)
  for i=1:nrows(a)
    if det(sub(a, 1:i, 1:i)) <= 0
      return false
    end
  end
  return true
end

#Returns a positive integer if A[i, j] > b, negative if A[i, j] < b, 0 otherwise
function compare_index(A::fmpz_mat, i::Int, j::Int, b::fmpz)
  a = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), A, i-1, j-1)
  return ccall((:fmpz_cmp, libflint), Int32, (Ptr{fmpz}, Ref{fmpz}), a, b)
end


#scales the i-th column of a by 2^d[1,i]
function mult_by_2pow_diag!(a::Matrix{BigFloat}, d::fmpz_mat, R = _RealRings[Threads.threadid()])
  s = size(a)
  tmp_mpz::BigInt = R.z1
  for i = 1:s[1]
    for j = 1:s[2]
      e = ccall((:mpfr_get_z_2exp, :libmpfr), Clong, (Ref{BigInt}, Ref{BigFloat}), tmp_mpz, a[i,j])
      ccall((:mpfr_set_z_2exp, :libmpfr), Nothing, (Ref{BigFloat}, Ref{BigInt}, Clong, Int32), a[i,j], tmp_mpz, e+Clong(Int(d[1,j])), __get_rounding_mode())
    end
  end
end

#converts BigFloat -> fmpz via round(a*2^l), in a clever(?) way
function round_scale(a::Matrix{BigFloat}, l::Int)
  s = size(a)
  b = zero_matrix(FlintZZ, s[1], s[2])
  return round_scale!(b, a, l)
end

function round_scale!(b::fmpz_mat, a::Matrix{BigFloat}, l::Int, R = _RealRings[Threads.threadid()])
  s = size(a)

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
      ccall((:fmpz_set_mpz, libflint), Nothing, (Ref{fmpz}, Ref{BigInt}), tmp_fmpz, tmp_mpz)
      if f > 0
        ccall((:fmpz_mul_2exp, libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, UInt), tmp_fmpz, tmp_fmpz, f)
      else
        ccall((:fmpz_tdiv_q_2exp, libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, UInt), tmp_fmpz, tmp_fmpz, -f);
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
      v = ccall((:arb_mat_entry_ptr, libarb), Ptr{arb},
                    (Ref{arb_mat}, Int, Int), a, i - 1, j - 1)
      ccall((:arb_mul_2exp_si, libarb), Nothing, (Ref{arb}, Ptr{arb}, Int), r, v, l)
      b[i,j] = round(fmpz, r)
    end
  end
  return b
end

function round!(b::fmpz_mat, a::arb_mat)
  s = size(a)
  for i = 1:s[1]
    for j = 1:s[2]
      b[i, j] = round(fmpz, a[i, j])
    end
  end
  return b
end


function shift!(g::fmpz_mat, l::Int)
  for i=1:nrows(g)
    for j=1:ncols(g)
      z = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), g, i-1, j-1)
      if l > 0
        ccall((:fmpz_mul_2exp, libflint), Nothing, (Ptr{fmpz}, Ptr{fmpz}, Int), z, z, l)
      else
        ccall((:fmpz_tdiv_q_2exp, libflint), Nothing, (Ptr{fmpz}, Ptr{fmpz}, Int), z, z, -l)
      end
    end
  end
  return g
end

################################################################################
#
#  Reduce the entries of a matrix modulo p
#
################################################################################

@doc Markdown.doc"""
    mod!(M::fmpz_mat, p::fmpz)

Reduces every entry modulo $p$ in-place, i.e. applies the mod function to every entry.
Positive residue system.
"""
function mod!(M::fmpz_mat, p::fmpz)
  GC.@preserve M begin
    for i=1:nrows(M)
      for j=1:ncols(M)
        z = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), M, i - 1, j - 1)
        ccall((:fmpz_mod, libflint), Nothing, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), z, z, p)
      end
    end
  end
  return nothing
end

@doc Markdown.doc"""
    mod(M::fmpz_mat, p::fmpz) -> fmpz_mat

Reduces every entry modulo $p$, i.e. applies the mod function to every entry.
"""
function mod(M::fmpz_mat, p::fmpz)
  N = deepcopy(M)
  mod!(N, p)
  return N
end

@doc Markdown.doc"""
    mod_sym!(M::fmpz_mat, p::fmpz)

Reduces every entry modulo $p$ in-place, into the symmetric residue system.
"""
function mod_sym!(M::fmpz_mat, B::fmpz)
  @assert !iszero(B)
  ccall((:fmpz_mat_scalar_smod, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{fmpz}), M, M, B)
end
mod_sym!(M::fmpz_mat, B::Integer) = mod_sym!(M, fmpz(B))

@doc Markdown.doc"""
    mod_sym(M::fmpz_mat, p::fmpz) -> fmpz_mat

Reduces every entry modulo $p$ into the symmetric residue system.
"""
function mod_sym(M::fmpz_mat, B::fmpz)
  N = zero_matrix(FlintZZ, nrows(M), ncols(M))
  ccall((:fmpz_mat_scalar_smod, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{fmpz}), N, M, B)
  return N
end
mod_sym(M::fmpz_mat, B::Integer) = mod_sym(M, fmpz(B))


################################################################################
#
#  Special map entries
#
################################################################################

function map_entries(R::NmodRing, M::fmpz_mat)
  MR = zero_matrix(R, nrows(M), ncols(M))
  ccall((:fmpz_mat_get_nmod_mat, libflint), Cvoid, (Ref{nmod_mat}, Ref{fmpz_mat}), MR, M)
  return MR
end


################################################################################
#
#  Concatenation of matrices
#
################################################################################

@doc Markdown.doc"""
    vcat(A::Vector{Generic.Mat}) -> Generic.Mat
    vcat(A::Array{fmpz_mat}, 1}) -> fmpz_mat

Forms a big matrix by vertically concatenating the matrices in $A$.
All component matrices need to have the same number of columns.
"""
function vcat(A::Vector{T})  where {S <: RingElem, T <: MatElem{S}}
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

function vcat(A::Vector{fmpz_mat})
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

function vcat(A::Vector{nmod_mat})
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

function Base.vcat(A::MatElem...)
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

function Base.hcat(A::Vector{T}) where {S <: RingElem, T <: MatElem{S}}
  if any(x->nrows(x) != nrows(A[1]), A)
    error("Matrices must have same number of rows")
  end
  M = zero_matrix(base_ring(A[1]), nrows(A[1]), sum(ncols, A))
  s = 0
  for i = A
    for j=1:ncols(i)
      for k=1:nrows(i)
        M[k, s + j] = i[k,j]
      end
    end
    s += ncols(i)
  end
  return M
end

function Base.hcat(A::MatElem...)
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


function Base.cat(A::MatElem...;dims)
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

  local X
  for i=1:length(A)
    if i==1
      X = hcat(A[1], zero_matrix(base_ring(A[1]), nrows(A[1]), sum(Int[ncols(A[j]) for j=2:length(A)])))
    else
      X = vcat(X, hcat(zero_matrix(base_ring(A[1]), nrows(A[i]), sum(ncols(A[j]) for j=1:i-1)), A[i], zero_matrix(base_ring(A[1]), nrows(A[i]), sum(Int[ncols(A[j]) for j=i+1:length(A)]))))
    end
  end
  return X
end
#= seems to be in AA now
function Base.hvcat(rows::Tuple{Vararg{Int}}, A::MatElem...)
  B = hcat([A[i] for i=1:rows[1]]...)
  o = rows[1]
  for j=2:length(rows)
    C = hcat([A[i+o] for i=1:rows[j]]...)
    o += rows[j]
    B = vcat(B, C)
  end
  return B
end
=#
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
    snf_with_transform(A::fmpz_mat, l::Bool = true, r::Bool = true) -> fmpz_mat, fmpz_mat, fmpz_mat

Given some integer matrix $A$, compute the Smith normal form (elementary
divisor normal form) of $A$. If `l` and/ or `r` are true, then the corresponding
left and/ or right transformation matrices are computed as well.
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
  S = deepcopy(A)
  while !isdiagonal(S)
    if l
      S, T = hnf_with_transform(S)
      L = T*L
    else
      S = hnf!(S)
    end

    if isdiagonal(S)
      break
    end
    if r
      S, T = hnf_with_transform(transpose(S))
      R = T*R
    else
      S = hnf!(transpose(S))
    end
    S = transpose(S)
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

  # It might be the case that S was diagonal with negative diagonal entries.
  for i in 1:min(nrows(S), ncols(S))
    if S[i, i] < 0
      if l
        multiply_column!(L, fmpz(-1), i)
      end
      S[i, i] = -S[i, i]
    end
  end

  if l
    if r
      return S, L, transpose(R)
    else
      # last is dummy
      return S, L, L
    end
  elseif r
    # second is dummy
    return S, R, transpose(R)
  else
    # last two are dummy
    return S, S, S
  end
end


function snf_for_groups(A::fmpz_mat, mod::fmpz)
  R = identity_matrix(FlintZZ, ncols(A))
  S = deepcopy(A)


  if !isdiagonal(S)
    T = zero_matrix(FlintZZ, ncols(A), ncols(A))
    GC.@preserve S R T begin
      while true
        hnf_modular_eldiv!(S, mod)
        if nrows(S) > ncols(S)
          S = view(S, 1:ncols(S), 1:ncols(S))
        end
        if islower_triangular(S)
          break
        end
        ccall((:fmpz_mat_transpose, libflint), Nothing,
           (Ref{fmpz_mat}, Ref{fmpz_mat}), S, S)
        ccall((:fmpz_mat_hnf_transform, libflint), Nothing,
           (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{fmpz_mat}), S, T, S)
        #S, T = hnf_with_transform(S)
        R = mul!(R, T, R)
        ccall((:fmpz_mat_transpose, libflint), Nothing,
           (Ref{fmpz_mat}, Ref{fmpz_mat}), S, S)
        if isupper_triangular(S)
          break
        end
      end
    end
  end
  #this is probably not really optimal...
  GC.@preserve S R begin
    for i=1:min(nrows(S), ncols(S))
      Sii = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), S, i - 1, i - 1)
      fl = ccall((:fmpz_is_one, libflint), Bool, (Ref{fmpz},), Sii)
      if fl
        continue
      end
      for j=i+1:min(nrows(S), ncols(S))
        Sjj = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), S, j - 1, j - 1)
        fl = ccall((:fmpz_is_zero, libflint), Bool, (Ref{fmpz},), Sjj)
        if fl
          continue
        end
        fl1 = ccall((:fmpz_is_zero, libflint), Bool, (Ref{fmpz},), Sii)
        if !fl1
          fl2 = Bool(ccall((:fmpz_divisible, libflint), Cint,
              (Ref{fmpz}, Ref{fmpz}), Sjj, Sii))
          if fl2
            continue
          end
        end
        #if S[i,i] != 0 && S[j,j] % S[i,i] == 0
        #  continue
        #end
        g = fmpz()
        e = fmpz()
        f = fmpz()
        ccall((:fmpz_xgcd, libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}, Ptr{fmpz}, Ptr{fmpz}), g, e, f, Sii, Sjj)
        #g, e, f = gcdx(S[i,i], S[j,j])
        a = fmpz()
        r = fmpz()
        ccall((:fmpz_tdiv_qr, libflint), Nothing,
          (Ref{fmpz}, Ref{fmpz}, Ptr{fmpz}, Ref{fmpz}), a, r, Sii, g)
        #a = divexact(S[i,i], g)
        ccall((:fmpz_set, libflint), Nothing, (Ptr{fmpz}, Ref{fmpz}), Sii, g)
        #S[i,i] = g
        b = fmpz()
        ccall((:fmpz_tdiv_qr, libflint), Nothing,
          (Ref{fmpz}, Ref{fmpz}, Ptr{fmpz}, Ref{fmpz}), b, r, Sjj, g)
        #b = divexact(S[j,j], g)
        ccall((:fmpz_mul, libflint), Nothing, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), Sjj, Sjj, a)
        #S[j,j] *= a
        # V = [e -b ; f a];
        # so col i and j of R will be transformed. We do it naively
        # careful: at this point, R is still transposed
        for k = 1:nrows(R)
          Rik = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), R, i - 1, k - 1)
          Rjk = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), R, j - 1, k - 1)
          aux = fmpz()
          ccall((:fmpz_mul, libflint), Nothing, (Ref{fmpz}, Ptr{fmpz}, Ref{fmpz}), aux, Rik, e)
          ccall((:fmpz_addmul, libflint), Nothing, (Ref{fmpz}, Ptr{fmpz}, Ref{fmpz}), aux, Rjk, f)
          aux1 = fmpz()
          ccall((:fmpz_mul, libflint), Nothing, (Ref{fmpz}, Ptr{fmpz}, Ref{fmpz}), aux1, Rjk, a)
          ccall((:fmpz_submul, libflint), Nothing, (Ref{fmpz}, Ptr{fmpz}, Ref{fmpz}), aux1, Rik, b)
          ccall((:fmpz_set, libflint), Nothing, (Ptr{fmpz}, Ref{fmpz}), Rik, aux)
          ccall((:fmpz_set, libflint), Nothing, (Ptr{fmpz}, Ref{fmpz}), Rjk, aux1)
          #R[i, k], R[j, k] = e*R[i,k]+f*R[j,k], -b*R[i,k]+a*R[j,k]
        end
      end
    end
    ccall((:fmpz_mat_transpose, libflint), Nothing,
         (Ref{fmpz_mat}, Ref{fmpz_mat}), R, R)
  end
  return S, R
end

################################################################################
#
#  IsUpper\Lower triangular
#
################################################################################

function isupper_triangular(M::MatElem)
  n = nrows(M)
  for i = 2:n
    for j = 1:min(i-1, ncols(M))
      if !iszero(M[i, j])
        return false
      end
    end
  end
  return true
end

function isupper_triangular(M::fmpz_mat)
  GC.@preserve M begin
    for i = 2:nrows(M)
      for j = 1:min(i-1, ncols(M))
        t = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), M, i - 1, j - 1)
        fl = ccall((:fmpz_is_zero, libflint), Bool, (Ref{fmpz},), t)
        if !fl
          return false
        end
      end
    end
  end
  return true
end

function islower_triangular(M::fmpz_mat)
  GC.@preserve M begin
    for i = 1:nrows(M)
      for j = i+1:ncols(M)
        t = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), M, i - 1, j - 1)
        fl = ccall((:fmpz_is_zero, libflint), Bool, (Ref{fmpz},), t)
        if !fl
          return false
        end
      end
    end
  end
  return true
end

function islower_triangular(M::MatElem)
  for i = 1:nrows(M)
    for j = i+1:ncols(M)
      if !iszero(M[i, j])
        return false
      end
    end
  end
  return true
end


################################################################################
#
#  Is diagonal
#
################################################################################

@doc Markdown.doc"""
    isdiagonal(A::Mat)

Tests if $A$ is diagonal.
"""
function isdiagonal(A::MatElem)
  for i = 1:ncols(A)
    for j = 1:nrows(A)
      if i != j && !iszero(A[j, i])
        return false
      end
    end
  end
  return true
end

function isdiagonal(A::fmpz_mat)
  for i = 1:ncols(A)
    for j = 1:nrows(A)
      if i != j
        t = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), A, j - 1, i - 1)
        fl = ccall((:fmpz_is_zero, libflint), Bool, (Ref{fmpz},), t)
        if !fl
          return false
        end
      end
    end
  end
  return true
end

################################################################################
#
#  Diagonal
#
################################################################################

@doc Markdown.doc"""
    diagonal(A::Mat{T}) -> Vector{T}

Returns the diagonal of `A` as an array.
"""
diagonal(A::MatrixElem{T}) where {T} = T[A[i, i] for i in 1:nrows(A)]

################################################################################
#
#  Product of the diagonal entries
#
################################################################################

function prod_diagonal(A::fmpz_mat)
  a = one(fmpz)
  GC.@preserve a A begin
    for i=1:nrows(A)
      b = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), A, i - 1, i - 1)
      ccall((:fmpz_mul, libflint), Nothing, (Ref{fmpz}, Ref{fmpz}, Ptr{fmpz}), a, a, b)
    end
  end
  return a
end

function prod_diagonal(A::MatrixElem{T}) where T
  @assert nrows(A) == ncols(A)
  return prod(T[A[i, i] for i = 1:nrows(A)])
end

################################################################################
#
#  Triangular solving
#
################################################################################

function _rref_with_trans(M::T) where {T <: MatElem{S} where {S <: FieldElem}}
  #does row ops
  n = hcat(M, identity_matrix(base_ring(M), nrows(M)))
  rref!(n)
  s = nrows(n)
  while s > 0 && iszero(sub(n, s:s, 1:ncols(M)))
    s -= 1
  end
  return s, sub(n, 1:nrows(M), 1:ncols(M)), sub(n, 1:nrows(M), ncols(M)+1:ncols(n))
end

# can_solve_ut over a field
#
#Given an upper triangular $m \times m$ matrix $A$ and a matrix $b$ of size $m
#\times k$, this function computes $x$ such that $Ax = b$. Might fail if
#the pivots of $A$ are not invertible.
#"""
function can_solve_rref_ut(A::MatElem{T}, b::Vector{T}; pivots::Vector{Int} = Int[]) where T <: FieldElem
  n = nrows(A)
  m = ncols(A)
  @assert n == length(b)
  x = Vector{T}(undef, m)
  K = base_ring(A)
  for i in 1:m
    x[i] = zero(K)
  end
  if length(pivots) == 0
    pivots = _get_pivots_ut(A)
  end
  @assert length(pivots) == n

  if any(i -> !iszero(b[i]) && iszero(pivots[i]), 1:n)
    return false, x
  else
    for i in 1:n
      if !iszero(pivots[i])
        x[pivots[i]] = b[i]
      end
    end
    return true, x
  end
end

function _get_pivots_ut(A::MatElem{<: FieldElem})
  n = nrows(A)
  m = ncols(A)
  pivots = fill(0, n)
  last_piv = m
  for i in n:-1:1
    for j in 1:last_piv
      if !iszero(A[i, j])
        last_piv = j
        pivots[i] = j
        break
      end
    end
  end
  return pivots
end

function can_solve_using_rref(A::MatElem{T}, b::Vector{T}) where {T}
  s, R, U = _rref_with_trans(A)
  pivots = _get_pivots_ut(R)
  fl, x = can_solve_given_rref(R, U, pivots, b)
  if fl
    @assert A * matrix(base_ring(A), length(x), 1, x) == matrix(base_ring(A), length(b), 1, b)
  end
  return fl, x
end

function can_solve_given_rref(R::MatElem{T}, U, pivots, b::Vector{T}) where {T}
  Ub = U * b
  fl, x = can_solve_rref_ut(R, Ub, pivots = pivots)
  return fl, x
end

function can_solve_given_rref(R::MatElem{T}, U, pivots, b) where {T}
  Ub = U * matrix(base_ring(R), length(b), 1, b)
  fl, x = can_solve_rref_ut(R, [Ub[i, 1] for i in 1:nrows(Ub)], pivots = pivots)
  return fl, x
end
# Solves A x = b for A upper triangular m\times n matrix and b m\times 1.

@doc Markdown.doc"""
    solve_ut(A::MatElem{T}, b::MatElem{T}) -> MatElem{T})

Given an upper triangular $m \times m$ matrix $A$ and a matrix $b$ of size $m
\times k$, this function computes $x$ such that $Ax = b$. Might fail if
the pivots of $A$ are not invertible.
"""
function solve_ut(A::MatElem{T}, b::MatElem{T}) where T
  m = nrows(A)
  n = ncols(A)
  s = ncols(b)
  @assert m == nrows(b)
  @assert m <= n
  x = zero_matrix(base_ring(A), n, s)
  pivot_cols = Vector{Int}()
  r = 0
  last_pivot = n + 1
  for i = m:-1:1
    for j = 1:last_pivot - 1
      if iszero(A[i, j])
        continue
      end
      for z = 1:s
        x[j, z] = b[i, z]
        for k = 1:r
          if !iszero(A[i, pivot_cols[k]])
            x[j, z] -= A[i, pivot_cols[k]]*x[pivot_cols[k], z]
          end
        end
        q, re = divrem(x[j, z], A[i, j])
        @assert iszero(re)
        x[j, z] = q
      end
      last_pivot = j
      r += 1
      push!(pivot_cols, j)
      break
    end
  end
  return x
end

@doc Markdown.doc"""
    solve_lt(A::MatElem{T}, b::MatElem{T}) -> MatElem{T})

Given a lower triangular $m \times m$ matrix $A$ and a matrix $b$ of size
$m \times k$, this function computes $x$ such that $Ax = b$. Might fail if the
pivots of $A$ are not invertible.
"""
function solve_lt(A::MatElem{T}, b::MatElem{T}) where T
  m = nrows(A)
  n = ncols(A)
  s = ncols(b)
  @assert m == nrows(b)
  @assert m <= n
  x = zero_matrix(base_ring(A), n, s)
  pivot_cols = Vector{Int}()
  r = 0
  last_pivot = 0
  for i = 1:m
    j = n
    while iszero(A[i, j])
      j -= 1
    end
    for z = 1:s
      x[j, z] = b[i, z]
      for k = 1:r
        if !iszero(A[i, pivot_cols[k]]) && !iszero(x[pivot_cols[k], z])
          x[j, z] -= A[i, pivot_cols[k]]*x[pivot_cols[k], z]
        end
      end
      q, re = divrem(x[j, z], A[i, j])
      @assert iszero(re)
      x[j, z] = q
    end
    last_pivot = j
    r += 1
    push!(pivot_cols, j)
  end
  return x
end

function solve_lt(A::MatElem{T}, b::Vector{T}) where T
  m = nrows(A)
  n = ncols(A)
  @assert m <= n
  x = Vector{T}(undef, n)
  pivot_cols = Vector{Int}()
  r = 0
  last_pivot = 0
  for i = 1:m
    j = n
    while iszero(A[i, j])
      j -= 1
    end
    x[j] = b[i]
    for k = 1:r
      if !iszero(A[i, pivot_cols[k]]) && !iszero(x[pivot_cols[k]])
        x[j] -= A[i, pivot_cols[k]]*x[pivot_cols[k]]
      end
    end
    q, re = divrem(x[j], A[i, j])
    @assert iszero(re)
    x[j] = q
    last_pivot = j
    r += 1
    push!(pivot_cols, j)
  end
  return x
end

@doc Markdown.doc"""
    reduce_mod!(A::MatElem{T}, B::MatElem{T}) where T <: FieldElem

For a reduced row echelon matrix $B$, reduce $A$ modulo $B$, i.e. all the pivot
columns will be zero afterwards.
"""
function reduce_mod!(A::MatElem{T}, B::MatElem{T}) where T <: FieldElem
  if isrref(B)
    scale = false
  else
    scale = true
  end

  for h=1:nrows(A)
    j = 1
    for i=1:nrows(B)
      while iszero(B[i, j])
        j += 1
      end
      if scale
        A[h, :] -= A[h, j] * (inv(B[i, j]) * B[i, :])
      else
        A[h, :] -= A[h, j] * B[i, :]
      end
    end
  end
  return A
end

@doc Markdown.doc"""
    reduce_mod(A::MatElem{T}, B::MatElem{T}) where T <: FieldElem -> MatElem

For a reduced row echelon matrix $B$, reduce $A$ modulo $B$, i.e. all the pivot
columns will be zero afterwards.
"""
function reduce_mod(A::MatElem{T}, B::MatElem{T}) where T <: FieldElem
  C = deepcopy(A)
  reduce_mod!(C, B)
  return C
end

#@doc Markdown.doc"""
#    find_pivot(A::MatElem{<:RingElem}) -> Vector{Int}
#
#Find the pivot-columns of the reduced row echelon matrix $A$.
#"""
#function find_pivot(A::MatElem{<:RingElem})
#  @assert isrref(A)
#  p = Int[]
#  j = 0
#  for i=1:nrows(A)
#    j += 1
#    if j > ncols(A)
#      return p
#    end
#    while iszero(A[i,j])
#      j += 1
#      if j > ncols(A)
#        return p
#      end
#    end
#    push!(p, j)
#  end
#  return p
#end

#@doc Markdown.doc"""
#    can_solve_with_solution(A::MatElem{T}, B::MatElem{T}; side = :right) where T <: FieldElem -> Bool, MatElem
#
#Tries to solve $Ax = B$ for $x$ if `side = :right` and $xA = B$ if `side =
#:left`.
#"""
#function can_solve_with_solution(A::MatElem{T}, B::MatElem{T};
#                                  side = :right) where T <: FieldElem
#  @assert base_ring(A) == base_ring(B)
#
#  if side === :right
#    @assert nrows(A) == nrows(B)
#    return _can_solve_with_solution(A, B)
#  elseif side === :left
#    @assert ncols(A) == ncols(B)
#    b, C = _can_solve_with_solution(transpose(A), transpose(B))
#    if b
#      return true, transpose(C)
#    else
#      return false, C
#    end
#  else
#    error("Unsupported argument :$side for side: Must be :left or :right")
#  end
#end
#
#function _can_solve_with_solution(A::MatElem{T}, B::MatElem{T}) where T <: FieldElem
#  R = base_ring(A)
#  mu = [A B]
#  rk, mu = rref(mu)
#  p = find_pivot(mu)
#  if any(i -> i > ncols(A), p)
#    return false, B
#  end
#  sol = zero_matrix(R, ncols(A), ncols(B))
#  for i = 1:length(p)
#    for j = 1:ncols(B)
#      sol[p[i], j] = mu[i, ncols(A) + j]
#    end
#  end
#  return true, sol
#end

#@doc Markdown.doc"""
#    can_solve_with_kernel(A::MatElem{T}, B::MatElem{T}; side = :right) where T <: FieldElem -> Bool, MatElem, MatElem
#
#Tries to solve $Ax = B$ for $x$ if `side = :right` or $xA = B$ if `side = :left`.
#It returns the solution and the right respectively left kernel of $A$.
#"""
#function can_solve_with_kernel(A::MatElem{T}, B::MatElem{T}; side = :right) where T <: FieldElem
#  @assert base_ring(A) == base_ring(B)
#  if side === :right
#    @assert nrows(A) == nrows(B)
#    return _can_solve_with_kernel(A, B)
#  elseif side === :left
#    b, C, K = _can_solve_with_kernel(transpose(A), transpose(B))
#    @assert ncols(A) == ncols(B)
#    if b
#      return b, transpose(C), transpose(K)
#    else
#      return b, C, K
#    end
#  else
#    error("Unsupported argument :$side for side: Must be :left or :right")
#  end
#end

#function _can_solve_with_kernel(A::MatElem{T}, B::MatElem{T}) where T <: FieldElem
#  R = base_ring(A)
#  mu = [A B]
#  rank, mu = rref(mu)
#  p = find_pivot(mu)
#  if any(i->i>ncols(A), p)
#    return false, B, B
#  end
#  sol = zero_matrix(R, ncols(A), ncols(B))
#  for i = 1:length(p)
#    for j = 1:ncols(B)
#      sol[p[i], j] = mu[i, ncols(A) + j]
#    end
#  end
#  nullity = ncols(A) - length(p)
#  X = zero(A, ncols(A), nullity)
#  pivots = zeros(Int, max(nrows(A), ncols(A)))
#  np = rank
#  j = k = 1
#  for i = 1:rank
#    while iszero(mu[i, j])
#      pivots[np + k] = j
#      j += 1
#      k += 1
#    end
#    pivots[i] = j
#    j += 1
#  end
#  while k <= nullity
#    pivots[np + k] = j
#    j += 1
#    k += 1
#  end
#  for i = 1:nullity
#    for j = 1:rank
#      X[pivots[j], i] = -mu[j, pivots[np + i]]
#    end
#    X[pivots[np + i], i] = one(R)
#  end
#  return true, sol, X
#end

#@doc Markdown.doc"""
#    can_solve_with_solution(A::MatElem{T}, B::MatElem{T}, side = :right) where T <: RingElem -> Bool, MatElem
#
#Tries to solve $Ax = B$ for $x$ if `side = :right` or $xA = B$ if `side = :left`
#over a euclidean ring.
#"""
#function can_solve_with_solution(A::MatElem{T}, B::MatElem{T};
#                                  side = :right) where T <: RingElem
#  @assert base_ring(A) == base_ring(B)
#
#  if side === :right
#    @assert nrows(A) == nrows(B)
#    return _can_solve_with_solution(A, B)
#  elseif side === :left
#    @assert ncols(A) == ncols(B)
#    b, C = _can_solve_with_solution(transpose(A), transpose(B))
#    if b
#      return true, transpose(C)
#    else
#      return false, C
#    end
#  else
#    error("Unsupported argument :$side for side: Must be :left or :right")
#  end
#end
#
#function _can_solve_with_solution(a::MatElem{S}, b::MatElem{S}, side = :left) where S <: RingElem
#  H, T = hnf_with_transform(transpose(a))
#  b = deepcopy(b)
#  z = zero_matrix(base_ring(a), ncols(b), ncols(a))
#  l = min(nrows(a), ncols(a))
#  for i = 1:ncols(b)
#    for j = 1:l
#      k = 1
#      while k <= ncols(H) && iszero(H[j, k])
#        k += 1
#      end
#      if k > ncols(H)
#        continue
#      end
#      q, r = divrem(b[k, i], H[j, k])
#      if !iszero(r)
#        return false, b
#      end
#      for h = k:ncols(H)
#        b[h, i] -= q*H[j, h]
#      end
#      z[i, j] = q
#    end
#  end
#  if !iszero(b)
#    return false, b
#  end
#  return true, transpose(z*T)
#end

#@doc Markdown.doc"""
#    can_solve_with_kernel(A::MatElem{T}, B::MatElem{T}) where T <: RingElem -> Bool, MatElem, MatElem
#
#Tries to solve $Ax = B$ for $x$ if `side = :right` or $xA = B$ if `side = :left`.
#It returns the solution and the right respectively left kernel of $A$.
#"""
#function can_solve_with_kernel(A::MatElem{T}, B::MatElem{T}; side = :right) where T <: RingElem
#  @assert base_ring(A) == base_ring(B)
#  if side === :right
#    @assert nrows(A) == nrows(B)
#    return _can_solve_with_kernel(A, B)
#  elseif side === :left
#    b, C, K = _can_solve_with_kernel(transpose(A), transpose(B))
#    @assert ncols(A) == ncols(B)
#    if b
#      return b, transpose(C), transpose(K)
#    else
#      return b, C, K
#    end
#  else
#    error("Unsupported argument :$side for side: Must be :left or :right")
#  end
#end

#function _can_solve_with_kernel(a::MatElem{S}, b::MatElem{S}) where S <: RingElem
#  H, T = hnf_with_transform(transpose(a))
#  z = zero_matrix(base_ring(a), ncols(b), ncols(a))
#  l = min(nrows(a), ncols(a))
#  b = deepcopy(b)
#  for i=1:ncols(b)
#    for j=1:l
#      k = 1
#      while k <= ncols(H) && iszero(H[j, k])
#        k += 1
#      end
#      if k > ncols(H)
#        continue
#      end
#      q, r = divrem(b[k, i], H[j, k])
#      if !iszero(r)
#        return false, b, b
#      end
#      for h=k:ncols(H)
#        b[h, i] -= q*H[j, h]
#      end
#      z[i, j] = q
#    end
#  end
#  if !iszero(b)
#    return false, b, b
#  end
#
#  for i = nrows(H):-1:1
#    for j = 1:ncols(H)
#      if !iszero(H[i,j])
#        N = zero_matrix(base_ring(a), ncols(a), nrows(H) - i)
#        for k = 1:nrows(N)
#          for l = 1:ncols(N)
#            N[k,l] = T[nrows(T) - l + 1, k]
#          end
#        end
#        return true, transpose(z*T), N
#      end
#    end
#  end
#
#  N = identity_matrix(base_ring(a), ncols(a))
#
#  return true, transpose(z*T), N
#end

################################################################################
#
#  Elementary divisors
#
################################################################################

@doc Markdown.doc"""
    elementary_divisors(A::fmpz_mat) -> Vector{fmpz}

The elementary divisors of $A$, that is, the diagonal entries of the Smith
normal form of $A$.
"""
function elementary_divisors(A::fmpz_mat)
  s = snf(A)
  return fmpz[s[i,i] for i = 1:min(ncols(s), nrows(s))]
end

@doc Markdown.doc"""
    maximal_elementary_divisor(A::fmpz_mat) -> fmpz

The largest elementary divisor of $A$, that is, the last diagonal entry of the
Smith normal form of $A$.
"""
function maximal_elementary_divisor(A::fmpz_mat)
  return elementary_divisors(A)[end]
end

@doc Markdown.doc"""
    divisors(A::fmpz_mat, d::fmpz) -> fmpz

Returns the diagonal entries of a diagonal form of $A$. We assume that all the elementary
divisors are divisors of $d$.
"""
function divisors(M::fmpz_mat, d::fmpz)
  sp = fmpz[2, 3, 5, 7, 11, 13, 17, 19, 23]
  l = fmpz[]
  for p in sp
    c, d = ppio(d, p)
    if !isone(c)
      push!(l, p)
    end
  end
  d = ispower(d)[2]
  M1 = _hnf_modular_eldiv(M, d)
  while !isdiagonal(M1)
    M1 = transpose(M1)
    hnf_modular_eldiv!(M1, d)
  end

  for j = 1:nrows(M1)
    if !isone(M1[j,j])
      push!(l, M1[j, j])
    end
  end
  return l
end

@doc Markdown.doc"""
    largest_elementary_divisor(A::fmpz_mat) -> fmpz

The largest elementary divisor of $A$, that is, the last diagonal entry of the
Smith normal form of $A$.
"""
largest_elementary_divisor(A::fmpz_mat) = maximal_elementary_divisor(A)

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

################################################################################
#
#  Minpoly and Charpoly
#
################################################################################

function minpoly(M::MatElem)
  k = base_ring(M)
  kx, x = PolynomialRing(k, cached = false)
  return minpoly(kx, M)
end

function charpoly(M::MatElem)
  k = base_ring(M)
  kx, x = PolynomialRing(k, cached = false)
  return charpoly(kx, M)
end

###############################################################################
#
#  Sub
#
###############################################################################

function sub(M::MatElem, rows::Vector{Int}, cols::Vector{Int})
  N = zero_matrix(base_ring(M), length(rows), length(cols))
  for i = 1:length(rows)
    for j = 1:length(cols)
      N[i, j] = M[rows[i], cols[j]]
    end
  end
  return N
end

function sub(M::Nemo.MatElem{T}, r::UnitRange{<:Integer}, c::UnitRange{<:Integer}) where {T}
  z = similar(M, length(r), length(c))
  for i in 1:length(r)
    for j in 1:length(c)
      z[i, j] = M[r[i], c[j]]
    end
  end
  return z
end

################################################################################
#
#  Map Entries
#
################################################################################

function map_entries(F::GaloisField, M::fmpz_mat)
  MR = zero_matrix(F, nrows(M), ncols(M))
  ccall((:fmpz_mat_get_nmod_mat, libflint), Cvoid, (Ref{gfp_mat}, Ref{fmpz_mat}), MR, M)
  return MR
end
################################################################################
#
#  Kernel of matrix over Z/nZ
#
################################################################################

function _left_kernel_of_howell_form_aurel(A::nmod_mat)
  n = nrows(A)
  m = ncols(A)
  K = zero_matrix(base_ring(A), n, n)
  for j in 1:n
    piv = 1
    while iszero(A[j, piv])
      piv += 1
    end
    @assert piv <= m
    an = annihilator(A[j, piv])
    K[j, j] = an
    if j < n
      fk = K[1:j, 1:j] * A[1:j, (piv + 1):(piv + 1)]
      pivnext = piv
      while iszero(A[j + 1, pivnext])
        pivnext += 1
      end
      for jp in 1:j
        fl, c = divides(fk[jp, 1], A[j + 1, pivnext])
        @assert fl
        K[jp, j + 1] = -c
      end
    end
  end
  return K
end

function _left_kernel_naive(A::nmod_mat)
  m = Int(modulus(base_ring(A)))
  D1 = abelian_group(Int[m for i in 1:nrows(A)])
  D2 = abelian_group(Int[m for i in 1:ncols(A)])
  im_gens = [ D2([lift(A[i, j]) for j in 1:ncols(A)]) for i in 1:nrows(A) ]
  h = hom(D1, D2, im_gens)
  K, mK = kernel(h)
  l = ngens(K)
  z = zero_matrix(base_ring(A), l, nrows(A))
  for i in 1:l
    b = mK(K[i])
    for j in 1:nrows(A)
      z[i, j] = b[j]
    end
  end
  return z
end

function left_kernel_prime_power(A::nmod_mat, p::Int, l::Int)
  R = base_ring(A)
  Alift = lift(A)
  F = GF(p)
  _, _M = left_kernel(change_base_ring(F, Alift))
  M = lift(_M)
  Mi = hnf_modular_eldiv(M, fmpz(p))
  r = nrows(Mi)
  while iszero_row(Mi, r)
    r -= 1
  end
  Mi = sub(Mi, 1:r, 1:ncols(Mi))
  Mfi = Mi * Alift
  local H
  for i in 1:(l - 1)
    _, K = left_kernel(change_base_ring(F, divexact(Mfi, p^i)))
    H = hnf_modular_eldiv(lift(K), fmpz(p))
    r = nrows(H)
    while iszero_row(H, r)
      r -= 1
    end
    H = sub(H, 1:r, 1:ncols(H))

    Mi = H * Mi
    Mfi = H * Mfi
  end
  Khow = howell_form(change_base_ring(R, Mi))
  i = 1
  while !iszero_row(Khow, i)
    i += 1
  end
  return i - 1, Khow
end



function invmod(M::fmpz_mat, d::fmpz)
  if fits(Int, d)
    RR = ResidueRing(FlintZZ, Int(d), cached = false)
    MRR = map_entries(RR, M)
    SR = zero_matrix(RR, 2*nrows(M), 2*nrows(M))
    _copy_matrix_into_matrix(SR, 1, 1, MRR)
    for i = 1:nrows(M)
      SR[i, i+nrows(M)] = 1
    end
    ccall((:nmod_mat_howell_form, libflint), Nothing, (Ref{nmod_mat}, ), SR)
    #howell_form!(SR)
    iMR = SR[1:nrows(M), nrows(M)+1:ncols(SR)]
    #@assert iMR*MRR == identity_matrix(RR, nrows(M))
    return lift(iMR)
  else
    R = ResidueRing(FlintZZ, d, cached = false)
    MR = map_entries(R, M)
    S = zero_matrix(R, 2*nrows(M), 2*nrows(M))
    _copy_matrix_into_matrix(S, 1, 1, MR)
    for i = 1:nrows(M)
      S[i, i+nrows(M)] = 1
    end
    ccall((:fmpz_mod_mat_howell_form, libflint), Nothing, (Ref{fmpz_mod_mat}, ), S)
    iM = S[1:nrows(M), nrows(M)+1:ncols(S)]
    #@assert iM*MR == identity_matrix(R, nrows(M))
    return lift(iM)
  end
end


function map_entries(R::Nemo.FmpzModRing, M::fmpz_mat)
  N = zero_matrix(R, nrows(M), ncols(M))
  GC.@preserve M N begin
    for i = 1:nrows(M)
      for j = 1:ncols(M)
        m = ccall((:fmpz_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), M, i - 1, j - 1)
        n = ccall((:fmpz_mod_mat_entry, libflint), Ptr{fmpz}, (Ref{fmpz_mod_mat}, Int, Int), N, i - 1 , j - 1)
        ccall((:fmpz_mod, libflint), Nothing, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), n, m, R.n)
      end
    end
  end
  return N
end
