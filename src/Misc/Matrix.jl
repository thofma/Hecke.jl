export is_zero_row, howell_form, kernel_basis, is_diagonal, diagonal, saturate,
       has_finite_multiplicative_order, multiplicative_order

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

function mul!(a::zzModMatrix, b::zzModMatrix, c::zzModRingElem)
  ccall((:nmod_mat_scalar_mul, libflint), Nothing,
          (Ref{zzModMatrix}, Ref{zzModMatrix}, UInt), a, b, c.data)
  return a
end

function mul!(c::MatElem, a::MatElem, b::RingElement)
  nrows(c) != nrows(a) && error("Incompatible matrix dimensions")

  if c === a || c === b
    d = parent(a)()
    return mul!(d, a, b)
  end

  t = base_ring(a)()
  for i = 1:nrows(a)
    for j = 1:ncols(a)
      c[i, j] = mul!(c[i, j], a[i, j], b)
    end
  end
  return c
end

################################################################################
#
#  Denominator
#
################################################################################

# This function is really slow...
function denominator(M::QQMatrix)
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

@doc raw"""
    saturate(A::ZZMatrix) -> ZZMatrix

Computes the saturation of $A$, that is, a basis for $\mathbf{Q}\otimes M \cap
\mathbf{Z}^n$, where $M$ is the row span of $A$ and $n$ the number of columns
of $A$.

Equivalently, return $TA$ for an invertible rational matrix $T$ such that $TA$
is integral and the elementary divisors of $TA$ are all trivial.

# Examples

```jldoctest
julia> saturate(ZZ[1 2 3;4 5 6;7 0 7])
[1    2    3]
[1    1    1]
[0   -1   -1]

julia> saturate(ZZ[1 2 3;4 5 6])
[1   2   3]
[1   1   1]

julia> saturate(ZZ[1 2;3 4;5 6])
[1   2]
[1   1]
[0   0]

```
"""
function saturate(A::ZZMatrix)
  # Let AU = H an m×n matrix of rank k in HNF.
  # Let H' in QQ^{k×m} s.t. H'H = (i==j ? 1 : 0)_ij in ZZ^{k×n},
  # and K a full rank (m-k)×n matrix with KH = 0 in ZZ^{(m-k)×n}.
  # Set T := [H'; K]. Then TH = (i==j<=k ? 1 : 0)_ij =: I',
  # by construction T has full rank, TA = THU⁻¹ = I'U⁻¹ in ZZ^{m×n},
  # and elem_div(TA) = elem_div(I'U⁻¹) = elem_div(I') = (i<=k ? 1 : 0)_i.
  # As of KA = KHU⁻¹ = 0, in our result
  # TA = [H'A; KA] = [H'A; 0matrix], so just forget about K.
  # Note that while we could compute the result as I'U⁻¹ via
  # `hnf_with_transform(Aᵀ)` and `inv(U)`, both steps would involve
  # the potentially gross matrix `U`.
  H = transpose(A)
  H = hnf!(H)
  k = rank(H)
  if k == ncols(H)
    k == nrows(H) || (H = H[1:k, :])
    # `inv` is faster on column hnf than on row hnf => transpose first
    Hi, d = pseudo_inv(transpose!(H))
    S = Hi*A
    divexact!(S, S, d)
  else
    p = pivot_cols_of_hnf(H)
    H = H[1:k, p]
    Hi, d = pseudo_inv(transpose!(H))
    S = zero(A)
    S1 = view(S, 1:k, :)
    S1[:, :] = Hi*A[p, :]
    divexact!(S1, S1, d)
  end
  return S
end

function pivot_cols_of_hnf(H::ZZMatrix)
  # H must be in row HNF
  p = Vector{Int}(undef, rank(H))
  i = 1
  for j in axes(H, 2)
    is_zero_entry(H, i, j) || (p[i] = j; i+=1)
    i == rank(H)+1 && break
  end
  return p
end

transpose!(A::Union{ZZMatrix, QQMatrix}) = transpose!(A, A)

function transpose!(A::ZZMatrix, B::ZZMatrix)
  ccall((:fmpz_mat_transpose, libflint), Nothing,
    (Ref{ZZMatrix}, Ref{ZZMatrix}), A, B)
  return A
end

function transpose!(A::QQMatrix, B::QQMatrix)
   ccall((:fmpq_mat_transpose, libflint), Nothing,
    (Ref{QQMatrix}, Ref{QQMatrix}), A, B)
  return A
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


function matrix(A::Matrix{ZZRingElem})
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

function Array(a::ZZMatrix; S::Type{T} = ZZRingElem) where T
  A = Array{T}(undef, nrows(a), ncols(a))
  for i = 1:nrows(a)
    for j = 1:ncols(a)
      A[i,j] = T(a[i,j])
    end
  end
  return A
end

function is_zero_row(M::ZZMatrix, i::Int)
  GC.@preserve M begin
    for j = 1:ncols(M)
      m = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), M, i - 1, j - 1)
      fl = ccall((:fmpz_is_zero, libflint), Bool, (Ptr{ZZRingElem},), m)
      if !fl
        return false
      end
    end
  end
  return true
end

function is_positive_entry(M::ZZMatrix, i::Int, j::Int)
  GC.@preserve M begin
    m = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), M, i - 1, j - 1)
    fl = ccall((:fmpz_sgn, libflint), Int, (Ptr{ZZRingElem},), m)
    return isone(fl)
  end
end



function is_zero_row(M::zzModMatrix, i::Int)
  zero = UInt(0)
  for j in 1:ncols(M)
    t = ccall((:nmod_mat_get_entry, libflint), Base.GMP.Limb, (Ref{zzModMatrix}, Int, Int), M, i - 1, j - 1)
    if t != zero
      return false
    end
  end
  return true
end

function is_zero_row(M::MatElem{T}, i::Int) where T
  for j in 1:ncols(M)
    if !iszero(M[i,j])
      return false
    end
  end
  return true
end

function is_zero_row(M::Matrix{T}, i::Int) where T <: Integer
  for j = 1:Base.size(M, 2)
    if M[i,j] != 0
      return false
    end
  end
  return true
end

function is_zero_row(M::Matrix{ZZRingElem}, i::Int)
  for j = 1:Base.size(M, 2)
    if M[i,j] != 0
      return false
    end
  end
  return true
end

function is_zero_row(M::Matrix{T}, i::Int) where T <: RingElem
  for j in 1:Base.size(M, 2)
    if !iszero(M[i,j])
      return false
    end
  end
  return true
end

function divexact!(a::ZZMatrix, b::ZZMatrix, d::ZZRingElem)
  ccall((:fmpz_mat_scalar_divexact_fmpz, libflint), Nothing,
               (Ref{ZZMatrix}, Ref{ZZMatrix}, Ref{ZZRingElem}), a, a, d)
end

function mul!(a::ZZMatrix, b::ZZMatrix, c::ZZRingElem)
  ccall((:fmpz_mat_scalar_mul_fmpz, libflint), Nothing,
                  (Ref{ZZMatrix}, Ref{ZZMatrix}, Ref{ZZRingElem}), a, b, c)
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

function hnf!(x::ZZMatrix)
  ccall((:fmpz_mat_hnf, libflint), Nothing, (Ref{ZZMatrix}, Ref{ZZMatrix}), x, x)
  return x
end

function _hnf_modular_eldiv(x::ZZMatrix, m::ZZRingElem, shape::Symbol = :upperright)
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

function hnf_modular_eldiv!(x::ZZMatrix, d::ZZRingElem, shape::Symbol = :upperright)
   (nrows(x) < ncols(x)) &&
                error("Matrix must have at least as many rows as columns")
   if shape == :upperright
     ccall((:fmpz_mat_hnf_modular_eldiv, libflint), Nothing,
                  (Ref{ZZMatrix}, Ref{ZZRingElem}), x, d)
     return x
   elseif shape == :lowerleft
     reverse_cols!(x)
     ccall((:fmpz_mat_hnf_modular_eldiv, libflint), Nothing,
                 (Ref{ZZMatrix}, Ref{ZZRingElem}), x, d)
     reverse_cols!(x)
     reverse_rows!(x)
     return x
   else
     error("shape $shape is not supported")
   end
end

function is_hnf(x::ZZMatrix, shape::Symbol)
  if shape == :upperright
    return is_hnf(x)
  elseif shape == :lowerleft
    r = nrows(x)
    i = 0
    j_old = ncols(x) + 1

    for outer i in nrows(x):-1:1

      if is_zero_row(x, i)
        break
      end

      j = ncols(x)
      while j >= 0 && is_zero_entry(x, i, j)
        j = j - 1
      end
      if j == -1
        break
      end
      if !is_positive_entry(x, i, j)
        return false
      end
      piv = x[i, j]
      j >= j_old && return false
      for k in i+1:r
        if !iszero(x[k, j]) && (!is_positive_entry(x, k, j) || compare_index(x, k, j, piv) > 0)
          return false
        end
      end
      j_old = j
      i = i - 1
    end

    for l in i:-1:1
      !is_zero_row(x, l) && return false
    end
    return true
  end
end

function Nemo._hnf(x::MatElem{ZZRingElem})
  if nrows(x) * ncols(x) > 100
    s = sparse_matrix(x)
    if sparsity(s) > 0.7
      return matrix(Hecke.hnf(s))
    end
  end
  return Nemo.__hnf(x) # ist die original Nemo flint hnf
end

function Nemo._hnf_with_transform(x::MatElem{ZZRingElem})
  if nrows(x) * ncols(x) > 100
    s = sparse_matrix(x)
    if sparsity(s) > 0.7
      s = hcat(s, identity_matrix(SMat, ZZ, nrows(x)))
      m = matrix(Hecke.hnf(s))
      return m[:, 1:ncols(x)], m[:, ncols(x)+1:end]
    end
  end
  return Nemo.__hnf_with_transform(x) # use original Nemo flint hnf
end

function add_to_hnf_from_matrix_stream(M::ZZMatrix, S, el = ZZRingElem(0), cutoff = true)
  # el = largest elementary divisor of M or 0
  # assume that every element of S is as large as M
  @assert is_square(M)
  if iszero(el)
    el = lcm(diagonal(M))
  end
  #@assert !is_zero(el)
  n = nrows(M)
  z = vcat(M, zero_matrix(ZZ, n, n))
  for s in S
    _copy_matrix_into_matrix(z, n + 1, 1, s)
    if !is_zero(el)
      hnf_modular_eldiv!(z, el)
    else
      hnf!(z)
    end
    el = reduce(lcm, (z[i, i] for i in 1:n)) # use that the diagonal works for non-square matrices
    if isone(el)
      break
    end
  end
  return z[1:n, 1:n]
end

################################################################################
#
#  Is LLL?
#
################################################################################

function is_lll_reduced(x::ZZMatrix, ctx::lll_ctx = lll_ctx(0.99, 0.51))
  b = ccall((:fmpz_lll_is_reduced_d, libflint), Cint,
            (Ref{ZZMatrix}, Ref{lll_ctx}), x, ctx)
  return Bool(b)
end

################################################################################
#
################################################################################

function maximum(f::typeof(abs), a::ZZMatrix)
  m = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), a, 0,0)
  for i=1:nrows(a)
    for j=1:ncols(a)
      z = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), a, i-1, j-1)
      if ccall((:fmpz_cmpabs, libflint), Cint, (Ptr{ZZRingElem}, Ptr{ZZRingElem}), m, z) < 0
        m = z
      end
    end
  end
  r = ZZRingElem()
  ccall((:fmpz_abs, libflint), Nothing, (Ref{ZZRingElem}, Ptr{ZZRingElem}), r, m)
  return r
end

function maximum(a::ZZMatrix)
  m = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), a, 0,0)
  for i=1:nrows(a)
    for j=1:ncols(a)
      z = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), a, i-1, j-1)
      if ccall((:fmpz_cmp, libflint), Cint, (Ptr{ZZRingElem}, Ptr{ZZRingElem}), m, z) < 0
        m = z
      end
    end
  end
  r = ZZRingElem()
  ccall((:fmpz_set, libflint), Nothing, (Ref{ZZRingElem}, Ptr{ZZRingElem}), r, m)
  return r
end

function minimum(a::ZZMatrix)
  m = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), a, 0,0)
  for i=1:nrows(a)
    for j=1:ncols(a)
      z = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), a, i-1, j-1)
      if ccall((:fmpz_cmp, libflint), Cint, (Ptr{ZZRingElem}, Ptr{ZZRingElem}), m, z) > 0
        m = z
      end
    end
  end
  r = ZZRingElem()
  ccall((:fmpz_set, libflint), Nothing, (Ref{ZZRingElem}, Ptr{ZZRingElem}), r, m)
  return r
end

################################################################################
#
#  Reduce mod hnf
#
################################################################################

# H must be in upper right HNF form
function reduce_mod_hnf_ur!(a::ZZMatrix, H::ZZMatrix)
  GC.@preserve a H begin
    for c = 1:nrows(a)
      j = 1
      for i=1:min(nrows(H), ncols(H))
        while j <= ncols(H) && is_zero_entry(H, i, j)
          j += 1
        end
        if j > ncols(H)
          break
        end
        n = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), a, c - 1, j - 1)
        m = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), H, i - 1, j - 1)
        q = ZZRingElem()
        ccall((:fmpz_fdiv_q, libflint), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}), q, n, m)
        #q = fdiv(a[c, j], H[i, j])
        fl = ccall((:fmpz_is_zero, libflint), Bool, (Ref{ZZRingElem},), q)
        if fl
          continue
        end
        for k = j:ncols(a)
          t = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), a, c - 1, k - 1)
          l = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), H, i - 1, k - 1)
          ccall((:fmpz_submul, libflint), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}), t, q, l)
          #a[c, k] = a[c, k] - q * H[i, k]
        end
      end
    end
  end
  return nothing
end

function reduce_mod_hnf_ll!(a::ZZMatrix, H::ZZMatrix)
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
        n = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), a, c - 1, j - 1)
        m = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), H, i - 1, j - 1)
        q = ZZRingElem()
        ccall((:fmpz_fdiv_q, libflint), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}), q, n, m)
        #q = fdiv(a[c, j], H[i, j])
        fl = ccall((:fmpz_is_zero, libflint), Bool, (Ref{ZZRingElem},), q)
        if fl
          continue
        end
        for k = 1:j
          t = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), a, c - 1, k - 1)
          l = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), H, i - 1, k - 1)
          ccall((:fmpz_submul, libflint), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}), t, q, l)
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

@doc raw"""
    lift(a::Generic.Mat{Generic.ResidueRingElem{ZZRingElem}}) -> ZZMatrix

It returns a lift of the matrix to the integers.
"""
function lift(a::Generic.Mat{Generic.ResidueRingElem{ZZRingElem}})
  z = zero_matrix(FlintZZ, nrows(a), ncols(a))
  for i in 1:nrows(a)
    for j in 1:ncols(a)
      z[i, j] = lift(a[i, j])
    end
  end
  return z
end

function lift(a::ZZModMatrix)
  z = zero_matrix(FlintZZ, nrows(a), ncols(a))
  GC.@preserve a z begin
    for i in 1:nrows(a)
      for j in 1:ncols(a)
        m = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), z, i - 1, j - 1)
        n = ccall((:fmpz_mod_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZModMatrix}, Int, Int), a, i - 1 , j - 1)
        ccall((:fmpz_set, libflint), Nothing, (Ptr{ZZRingElem}, Ptr{ZZRingElem}), m, n)
        #z[i, j] = lift(a[i, j])
      end
    end
  end
  return z
end

function lift(x::FpMatrix)
  return map_entries(lift , x)
end

function lift_nonsymmetric(a::zzModMatrix)
  z = zero_matrix(FlintZZ, nrows(a), ncols(a))
  ccall((:fmpz_mat_set_nmod_mat_unsigned, Hecke.libflint), Nothing,
          (Ref{ZZMatrix}, Ref{zzModMatrix}), z, a)
  return z
end

function lift_nonsymmetric(a::fpMatrix)
  z = zero_matrix(FlintZZ, nrows(a), ncols(a))
  ccall((:fmpz_mat_set_nmod_mat_unsigned, Hecke.libflint), Nothing,
          (Ref{ZZMatrix}, Ref{fpMatrix}), z, a)
  return z
end


if Nemo.version() > v"0.15.1"
  function lift(a::Generic.Mat{Nemo.ZZModRingElem})
    z = zero_matrix(FlintZZ, nrows(a), ncols(a))
    for i in 1:nrows(a)
      for j in 1:ncols(a)
        z[i, j] = lift(a[i, j])
      end
    end
    return z
  end
end

function lift_unsigned(a::zzModMatrix)
  z = zero_matrix(FlintZZ, nrows(a), ncols(a))
  ccall((:fmpz_mat_set_nmod_mat_unsigned, libflint), Nothing,
          (Ref{ZZMatrix}, Ref{zzModMatrix}), z, a)
  return z
end

################################################################################
#
#  Kernel function
#
################################################################################
@doc raw"""
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

@doc raw"""
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

@doc raw"""
    left_kernel_basis(a::MatElem{T}) -> Vector{Vector{T}}

It returns a basis for the left kernel of the matrix.
"""
left_kernel_basis(a::MatElem{T}) where T <: AbstractAlgebra.FieldElem = right_kernel_basis(transpose(a))



@doc raw"""
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

function right_kernel(x::fpMatrix)
  z = zero_matrix(base_ring(x), ncols(x), max(nrows(x),ncols(x)))
  n = ccall((:nmod_mat_nullspace, libflint), Int, (Ref{fpMatrix}, Ref{fpMatrix}), z, x)
  return n, z
end

function left_kernel(x::fpMatrix)
  n, M = right_kernel(transpose(x))
  return n, transpose(M)
end

@doc raw"""
    left_kernel(a::ZZMatrix) -> Int, ZZMatrix

It returns a tuple $(n, M)$ where $M$ is a matrix whose rows generate
the kernel of $a$ and $n$ is the rank of the kernel.
"""
function left_kernel(x::ZZMatrix)
  if nrows(x) == 0
    return 0, zero(x, 0, 0)
  end
  x1 = transpose(hnf(transpose(x)))
  H, U = hnf_with_transform(x1)
  i = 1
  for outer i in 1:nrows(H)
    if is_zero_row(H, i)
      break
    end
  end
  if is_zero_row(H, i)
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

function right_kernel(x::ZZMatrix)
  n, M = left_kernel(transpose(x))
  return n, transpose(M)
end

function right_kernel(M::zzModMatrix)
  R = base_ring(M)
  if is_prime(modulus(R))
    k = zero_matrix(R, ncols(M), ncols(M))
    n = ccall((:nmod_mat_nullspace, libflint), Int, (Ref{zzModMatrix}, Ref{zzModMatrix}), k, M)
    return n, k
  end

  H = hcat(transpose(M), identity_matrix(R, ncols(M)))
  if nrows(H) < ncols(H)
    H = vcat(H, zero_matrix(R, ncols(H) - nrows(H), ncols(H)))
  end
  howell_form!(H)
  nr = 1
  while nr <= nrows(H) && !is_zero_row(H, nr)
    nr += 1
  end
  nr -= 1
  h = sub(H, 1:nr, 1:nrows(M))
  for i=1:nrows(h)
    if is_zero_row(h, i)
      k = sub(H, i:nrows(h), nrows(M)+1:ncols(H))
      return nrows(k), transpose(k)
    end
  end
  return 0, zero_matrix(R,nrows(M),0)
end

function left_kernel(a::zzModMatrix)
  n, M = right_kernel(transpose(a))
  return n, transpose(M)
end

function right_kernel(M::ZZModMatrix)
  R = base_ring(M)
  N = hcat(transpose(M), identity_matrix(R, ncols(M)))
  if nrows(N) < ncols(N)
    N = vcat(N, zero_matrix(R, ncols(N) - nrows(N), ncols(N)))
  end
  howell_form!(N)
  H = N
  nr = 1
  while nr <= nrows(H) && !is_zero_row(H, nr)
    nr += 1
  end
  nr -= 1
  h = sub(H, 1:nr, 1:nrows(M))
  for i=1:nrows(h)
    if is_zero_row(h, i)
      k = sub(H, i:nrows(h), nrows(M)+1:ncols(H))
      return nrows(k), transpose(k)
    end
  end
  return 0, zero_matrix(R,nrows(M),0)
end

function left_kernel(a::ZZModMatrix)
  n, M = right_kernel(transpose(a))
  return n, transpose(M)
end

################################################################################
#
#  Kernel over different rings
#
################################################################################

@doc raw"""
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

@doc raw"""
    diagonal_matrix(x::T...) where T <: RingElem -> MatElem{T}
    diagonal_matrix(x::Vector{T}) where T <: RingElem -> MatElem{T}
    diagonal_matrix(Q, x::Vector{T}) where T <: RingElem -> MatElem{T}

Returns a diagonal matrix whose diagonal entries are the elements of $x$.

# Examples

```jldoctest
julia> diagonal_matrix(QQ(1), QQ(2))
[1   0]
[0   2]

julia> diagonal_matrix([QQ(3), QQ(4)])
[3   0]
[0   4]

julia> diagonal_matrix(QQ, [5, 6])
[5   0]
[0   6]
```
"""
function diagonal_matrix(R::Ring, x::Vector{<:RingElement})
  x = R.(x)
  M = zero_matrix(R, length(x), length(x))
  for i = 1:length(x)
    M[i, i] = x[i]
  end
  return M
end

function diagonal_matrix(x::T, xs::T...) where T <: RingElem
  return diagonal_matrix(collect((x, xs...)))
end

diagonal_matrix(x::Vector{<:RingElement}) = diagonal_matrix(parent(x[1]), x)

@doc raw"""
    diagonal_matrix(x::Vector{T}) where T <: MatElem -> MatElem

Returns a block diagonal matrix whose diagonal blocks are the matrices in $x$.
"""
function diagonal_matrix(x::Vector{T}) where T <: MatElem
  return cat(x..., dims = (1, 2))::T
end

function diagonal_matrix(x::T, xs::T...) where T <: MatElem
  return cat(x, xs..., dims = (1, 2))::T
end

function diagonal_matrix(R::Ring, x::Vector{<:MatElem})
  if length(x) == 0
    return zero_matrix(R, 0, 0)
  end
  x = [change_base_ring(R, i) for i in x]
  return diagonal_matrix(x)
end

################################################################################
#
#  Copy matrix into another matrix
#
################################################################################

# Copy B into A at position (i, j)
function _copy_matrix_into_matrix(A::ZZMatrix, i::Int, j::Int, B::ZZMatrix)
  @GC.preserve A B begin
    for k in 0:nrows(B) - 1
      for l in 0:ncols(B) - 1
        d = ccall((:fmpz_mat_entry, libflint),
                  Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), B, k, l)
        t = ccall((:fmpz_mat_entry, libflint),
                  Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), A, i - 1 + k, j - 1 + l)
        ccall((:fmpz_set, libflint), Nothing, (Ptr{ZZRingElem}, Ptr{ZZRingElem}), t, d)
      end
    end
  end
end

function _copy_matrix_into_matrix!(A::QQMatrix, i::Int, j::Int, B::QQMatrix)
  @GC.preserve A B begin
    for k in 0:nrows(B) - 1
      for l in 0:ncols(B) - 1
        d = ccall((:fmpq_mat_entry, libflint),
                  Ptr{QQFieldElem}, (Ref{QQMatrix}, Int, Int), B, k, l)
        t = ccall((:fmpq_mat_entry, libflint),
                  Ptr{QQFieldElem}, (Ref{QQMatrix}, Int, Int), A, i - 1 + k, j - 1 + l)
        ccall((:fmpq_set, libflint), Nothing, (Ptr{QQFieldElem}, Ptr{QQFieldElem}), t, d)
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

@doc raw"""
    is_positive_definite(a::ZZMatrix) -> Bool

Tests if $a$ is positive definite by testing if all principal minors
have positive determinant.
"""
function is_positive_definite(a::ZZMatrix)
  for i=1:nrows(a)
    if det(sub(a, 1:i, 1:i)) <= 0
      return false
    end
  end
  return true
end

#Returns a positive integer if A[i, j] > b, negative if A[i, j] < b, 0 otherwise
function compare_index(A::ZZMatrix, i::Int, j::Int, b::ZZRingElem)
  a = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), A, i-1, j-1)
  return ccall((:fmpz_cmp, libflint), Int32, (Ptr{ZZRingElem}, Ref{ZZRingElem}), a, b)
end


#scales the i-th column of a by 2^d[1,i]
function mult_by_2pow_diag!(a::Matrix{BigFloat}, d::ZZMatrix, R = _RealRings[Threads.threadid()])
  s = size(a)
  tmp_mpz::BigInt = R.z1
  for i = 1:s[1]
    for j = 1:s[2]
      e = ccall((:mpfr_get_z_2exp, :libmpfr), Clong, (Ref{BigInt}, Ref{BigFloat}), tmp_mpz, a[i,j])
      ccall((:mpfr_set_z_2exp, :libmpfr), Nothing, (Ref{BigFloat}, Ref{BigInt}, Clong, Int32), a[i,j], tmp_mpz, e+Clong(Int(d[1,j])), __get_rounding_mode())
    end
  end
end

#converts BigFloat -> ZZRingElem via round(a*2^l), in a clever(?) way
function round_scale(a::Matrix{BigFloat}, l::Int)
  s = size(a)
  b = zero_matrix(FlintZZ, s[1], s[2])
  return round_scale!(b, a, l)
end

function round_scale!(b::ZZMatrix, a::Matrix{BigFloat}, l::Int, R = _RealRings[Threads.threadid()])
  s = size(a)

  local tmp_mpz::BigInt, tmp_fmpz::ZZRingElem
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
      ccall((:fmpz_set_mpz, libflint), Nothing, (Ref{ZZRingElem}, Ref{BigInt}), tmp_fmpz, tmp_mpz)
      if f > 0
        ccall((:fmpz_mul_2exp, libflint), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}, UInt), tmp_fmpz, tmp_fmpz, f)
      else
        ccall((:fmpz_tdiv_q_2exp, libflint), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}, UInt), tmp_fmpz, tmp_fmpz, -f);
      end
      setindex!(b, tmp_fmpz, i, j)
    end
  end
  return b
end

function round_scale!(b::ZZMatrix, a::arb_mat, l::Int)
  s = size(a)

  R = base_ring(a)
  r = R()
  for i = 1:s[1]
    for j = 1:s[2]
      v = ccall((:arb_mat_entry_ptr, libarb), Ptr{arb},
                    (Ref{arb_mat}, Int, Int), a, i - 1, j - 1)
      ccall((:arb_mul_2exp_si, libarb), Nothing, (Ref{arb}, Ptr{arb}, Int), r, v, l)
      b[i,j] = round(ZZRingElem, r)
    end
  end
  return b
end

function round!(b::ZZMatrix, a::arb_mat)
  s = size(a)
  for i = 1:s[1]
    for j = 1:s[2]
      b[i, j] = round(ZZRingElem, a[i, j])
    end
  end
  return b
end


function shift!(g::ZZMatrix, l::Int)
  for i=1:nrows(g)
    for j=1:ncols(g)
      z = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), g, i-1, j-1)
      if l > 0
        ccall((:fmpz_mul_2exp, libflint), Nothing, (Ptr{ZZRingElem}, Ptr{ZZRingElem}, Int), z, z, l)
      else
        ccall((:fmpz_tdiv_q_2exp, libflint), Nothing, (Ptr{ZZRingElem}, Ptr{ZZRingElem}, Int), z, z, -l)
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

@doc raw"""
    mod!(M::ZZMatrix, p::ZZRingElem)

Reduces every entry modulo $p$ in-place, i.e. applies the mod function to every entry.
Positive residue system.
"""
function mod!(M::ZZMatrix, p::ZZRingElem)
  GC.@preserve M begin
    for i=1:nrows(M)
      for j=1:ncols(M)
        z = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), M, i - 1, j - 1)
        ccall((:fmpz_mod, libflint), Nothing, (Ptr{ZZRingElem}, Ptr{ZZRingElem}, Ref{ZZRingElem}), z, z, p)
      end
    end
  end
  return nothing
end

@doc raw"""
    mod(M::ZZMatrix, p::ZZRingElem) -> ZZMatrix

Reduces every entry modulo $p$, i.e. applies the mod function to every entry.
"""
function mod(M::ZZMatrix, p::ZZRingElem)
  N = deepcopy(M)
  mod!(N, p)
  return N
end

@doc raw"""
    mod_sym!(M::ZZMatrix, p::ZZRingElem)

Reduces every entry modulo $p$ in-place, into the symmetric residue system.
"""
function mod_sym!(M::ZZMatrix, B::ZZRingElem)
  @assert !iszero(B)
  ccall((:fmpz_mat_scalar_smod, libflint), Nothing, (Ref{ZZMatrix}, Ref{ZZMatrix}, Ref{ZZRingElem}), M, M, B)
end
mod_sym!(M::ZZMatrix, B::Integer) = mod_sym!(M, ZZRingElem(B))

@doc raw"""
    mod_sym(M::ZZMatrix, p::ZZRingElem) -> ZZMatrix

Reduces every entry modulo $p$ into the symmetric residue system.
"""
function mod_sym(M::ZZMatrix, B::ZZRingElem)
  N = zero_matrix(FlintZZ, nrows(M), ncols(M))
  ccall((:fmpz_mat_scalar_smod, libflint), Nothing, (Ref{ZZMatrix}, Ref{ZZMatrix}, Ref{ZZRingElem}), N, M, B)
  return N
end
mod_sym(M::ZZMatrix, B::Integer) = mod_sym(M, ZZRingElem(B))


################################################################################
#
#  Special map entries
#
################################################################################

function map_entries(R::zzModRing, M::ZZMatrix)
  MR = zero_matrix(R, nrows(M), ncols(M))
  ccall((:fmpz_mat_get_nmod_mat, libflint), Cvoid, (Ref{zzModMatrix}, Ref{ZZMatrix}), MR, M)
  return MR
end


################################################################################
#
#  Concatenation of matrices
#
################################################################################

@doc raw"""
    vcat(A::Vector{Generic.Mat}) -> Generic.Mat
    vcat(A::Array{ZZMatrix}, 1}) -> ZZMatrix

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

function vcat(A::Vector{ZZMatrix})
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

function vcat(A::Vector{zzModMatrix})
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
@doc raw"""
    snf_with_transform(A::ZZMatrix, l::Bool = true, r::Bool = true) -> ZZMatrix, ZZMatrix, ZZMatrix

Given some integer matrix $A$, compute the Smith normal form (elementary
divisor normal form) of $A$. If `l` and/ or `r` are true, then the corresponding
left and/ or right transformation matrices are computed as well.
"""
function snf_with_transform(A::ZZMatrix, l::Bool = true, r::Bool = true)
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
  while !is_diagonal(S)
    if l
      S, T = hnf_with_transform(S)
      L = T*L
    else
      S = hnf!(S)
    end

    if is_diagonal(S)
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
        multiply_row!(L, ZZRingElem(-1), i)
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


function snf_for_groups(A::ZZMatrix, mod::ZZRingElem)
  R = identity_matrix(FlintZZ, ncols(A))
  S = deepcopy(A)


  if !is_diagonal(S)
    T = zero_matrix(FlintZZ, ncols(A), ncols(A))
    GC.@preserve S R T begin
      while true
        hnf_modular_eldiv!(S, mod)
        if nrows(S) > ncols(S)
          S = view(S, 1:ncols(S), 1:ncols(S))
        end
        if is_lower_triangular(S)
          break
        end
        ccall((:fmpz_mat_transpose, libflint), Nothing,
           (Ref{ZZMatrix}, Ref{ZZMatrix}), S, S)
        ccall((:fmpz_mat_hnf_transform, libflint), Nothing,
           (Ref{ZZMatrix}, Ref{ZZMatrix}, Ref{ZZMatrix}), S, T, S)
        #S, T = hnf_with_transform(S)
        R = mul!(R, T, R)
        ccall((:fmpz_mat_transpose, libflint), Nothing,
           (Ref{ZZMatrix}, Ref{ZZMatrix}), S, S)
        if isupper_triangular(S)
          break
        end
      end
    end
  end
  #this is probably not really optimal...
  GC.@preserve S R begin
    for i=1:min(nrows(S), ncols(S))
      Sii = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), S, i - 1, i - 1)
      fl = ccall((:fmpz_is_one, libflint), Bool, (Ref{ZZRingElem},), Sii)
      if fl
        continue
      end
      for j=i+1:min(nrows(S), ncols(S))
        Sjj = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), S, j - 1, j - 1)
        fl = ccall((:fmpz_is_zero, libflint), Bool, (Ref{ZZRingElem},), Sjj)
        if fl
          continue
        end
        fl1 = ccall((:fmpz_is_zero, libflint), Bool, (Ref{ZZRingElem},), Sii)
        if !fl1
          fl2 = Bool(ccall((:fmpz_divisible, libflint), Cint,
              (Ref{ZZRingElem}, Ref{ZZRingElem}), Sjj, Sii))
          if fl2
            continue
          end
        end
        #if S[i,i] != 0 && S[j,j] % S[i,i] == 0
        #  continue
        #end
        g = ZZRingElem()
        e = ZZRingElem()
        f = ZZRingElem()
        ccall((:fmpz_xgcd, libflint), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}, Ptr{ZZRingElem}, Ptr{ZZRingElem}), g, e, f, Sii, Sjj)
        #g, e, f = gcdx(S[i,i], S[j,j])
        a = ZZRingElem()
        r = ZZRingElem()
        ccall((:fmpz_tdiv_qr, libflint), Nothing,
          (Ref{ZZRingElem}, Ref{ZZRingElem}, Ptr{ZZRingElem}, Ref{ZZRingElem}), a, r, Sii, g)
        #a = divexact(S[i,i], g)
        ccall((:fmpz_set, libflint), Nothing, (Ptr{ZZRingElem}, Ref{ZZRingElem}), Sii, g)
        #S[i,i] = g
        b = ZZRingElem()
        ccall((:fmpz_tdiv_qr, libflint), Nothing,
          (Ref{ZZRingElem}, Ref{ZZRingElem}, Ptr{ZZRingElem}, Ref{ZZRingElem}), b, r, Sjj, g)
        #b = divexact(S[j,j], g)
        ccall((:fmpz_mul, libflint), Nothing, (Ptr{ZZRingElem}, Ptr{ZZRingElem}, Ref{ZZRingElem}), Sjj, Sjj, a)
        #S[j,j] *= a
        # V = [e -b ; f a];
        # so col i and j of R will be transformed. We do it naively
        # careful: at this point, R is still transposed
        for k = 1:nrows(R)
          Rik = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), R, i - 1, k - 1)
          Rjk = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), R, j - 1, k - 1)
          aux = ZZRingElem()
          ccall((:fmpz_mul, libflint), Nothing, (Ref{ZZRingElem}, Ptr{ZZRingElem}, Ref{ZZRingElem}), aux, Rik, e)
          ccall((:fmpz_addmul, libflint), Nothing, (Ref{ZZRingElem}, Ptr{ZZRingElem}, Ref{ZZRingElem}), aux, Rjk, f)
          aux1 = ZZRingElem()
          ccall((:fmpz_mul, libflint), Nothing, (Ref{ZZRingElem}, Ptr{ZZRingElem}, Ref{ZZRingElem}), aux1, Rjk, a)
          ccall((:fmpz_submul, libflint), Nothing, (Ref{ZZRingElem}, Ptr{ZZRingElem}, Ref{ZZRingElem}), aux1, Rik, b)
          ccall((:fmpz_set, libflint), Nothing, (Ptr{ZZRingElem}, Ref{ZZRingElem}), Rik, aux)
          ccall((:fmpz_set, libflint), Nothing, (Ptr{ZZRingElem}, Ref{ZZRingElem}), Rjk, aux1)
          #R[i, k], R[j, k] = e*R[i,k]+f*R[j,k], -b*R[i,k]+a*R[j,k]
        end
      end
    end
    ccall((:fmpz_mat_transpose, libflint), Nothing,
         (Ref{ZZMatrix}, Ref{ZZMatrix}), R, R)
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

function isupper_triangular(M::ZZMatrix)
  GC.@preserve M begin
    for i = 2:nrows(M)
      for j = 1:min(i-1, ncols(M))
        t = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), M, i - 1, j - 1)
        fl = ccall((:fmpz_is_zero, libflint), Bool, (Ref{ZZRingElem},), t)
        if !fl
          return false
        end
      end
    end
  end
  return true
end

function is_lower_triangular(M::ZZMatrix)
  GC.@preserve M begin
    for i = 1:nrows(M)
      for j = i+1:ncols(M)
        t = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), M, i - 1, j - 1)
        fl = ccall((:fmpz_is_zero, libflint), Bool, (Ref{ZZRingElem},), t)
        if !fl
          return false
        end
      end
    end
  end
  return true
end

function is_lower_triangular(M::MatElem)
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

@doc raw"""
    is_diagonal(A::Mat)

Tests if $A$ is diagonal.
"""
function is_diagonal(A::MatElem)
  for i = 1:ncols(A)
    for j = 1:nrows(A)
      if i != j && !iszero(A[j, i])
        return false
      end
    end
  end
  return true
end

function is_diagonal(A::ZZMatrix)
  for i = 1:ncols(A)
    for j = 1:nrows(A)
      if i != j
        t = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), A, j - 1, i - 1)
        fl = ccall((:fmpz_is_zero, libflint), Bool, (Ref{ZZRingElem},), t)
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

@doc raw"""
    diagonal(A::Mat{T}) -> Vector{T}

Returns the diagonal of `A` as an array.
"""
diagonal(A::MatrixElem{T}) where {T} = T[A[i, i] for i in 1:nrows(A)]

################################################################################
#
#  Product of the diagonal entries
#
################################################################################

function prod_diagonal(A::ZZMatrix)
  a = one(ZZRingElem)
  GC.@preserve a A begin
    for i=1:nrows(A)
      b = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), A, i - 1, i - 1)
      ccall((:fmpz_mul, libflint), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ptr{ZZRingElem}), a, a, b)
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
function can_solve_rref_ut(A::MatElem{T}, b::Vector{T}, pivots::Vector{Int}) where T <: FieldElem
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
  fl, x = can_solve_rref_ut(R, Ub, pivots)
  return fl, x
end

function can_solve_given_rref(R::MatElem{T}, U, pivots, b) where {T}
  Ub = U * matrix(base_ring(R), length(b), 1, b)
  fl, x = can_solve_rref_ut(R, [Ub[i, 1] for i in 1:nrows(Ub)], pivots)
  return fl, x
end
# Solves A x = b for A upper triangular m\times n matrix and b m\times 1.

@doc raw"""
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

@doc raw"""
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

@doc raw"""
    reduce_mod!(A::MatElem{T}, B::MatElem{T}) where T <: FieldElem

For a reduced row echelon matrix $B$, reduce $A$ modulo $B$, i.e. all the pivot
columns will be zero afterwards.
"""
function reduce_mod!(A::MatElem{T}, B::MatElem{T}) where T <: FieldElem
  if is_rref(B)
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

@doc raw"""
    reduce_mod(A::MatElem{T}, B::MatElem{T}) where T <: FieldElem -> MatElem

For a reduced row echelon matrix $B$, reduce $A$ modulo $B$, i.e. all the pivot
columns will be zero afterwards.
"""
function reduce_mod(A::MatElem{T}, B::MatElem{T}) where T <: FieldElem
  C = deepcopy(A)
  reduce_mod!(C, B)
  return C
end

#@doc raw"""
#    find_pivot(A::MatElem{<:RingElem}) -> Vector{Int}
#
#Find the pivot-columns of the reduced row echelon matrix $A$.
#"""
#function find_pivot(A::MatElem{<:RingElem})
#  @assert is_rref(A)
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

#@doc raw"""
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

#@doc raw"""
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

#@doc raw"""
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

#@doc raw"""
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

@doc raw"""
    elementary_divisors(A::ZZMatrix) -> Vector{ZZRingElem}

The elementary divisors of $A$, that is, the diagonal entries of the Smith
normal form of $A$.
"""
function elementary_divisors(A::MatElem{T}) where T
  s = snf(A)
  return T[s[i,i] for i = 1:min(ncols(s), nrows(s))]
end

@doc raw"""
    maximal_elementary_divisor(A::ZZMatrix) -> ZZRingElem

The largest elementary divisor of $A$, that is, the last diagonal entry of the
Smith normal form of $A$.
"""
function maximal_elementary_divisor(A::ZZMatrix)
  return elementary_divisors(A)[end]
end

@doc raw"""
    divisors(A::ZZMatrix, d::ZZRingElem) -> ZZRingElem

Returns the diagonal entries of a diagonal form of $A$. We assume that all the elementary
divisors are divisors of $d$.
"""
function divisors(M::ZZMatrix, d::ZZRingElem)
  sp = ZZRingElem[2, 3, 5, 7, 11, 13, 17, 19, 23]
  l = ZZRingElem[]
  for p in sp
    c, d = ppio(d, p)
    if !isone(c)
      push!(l, p)
    end
  end
  d = is_power(d)[2]
  M1 = _hnf_modular_eldiv(M, d)
  while !is_diagonal(M1)
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

@doc raw"""
    largest_elementary_divisor(A::ZZMatrix) -> ZZRingElem

The largest elementary divisor of $A$, that is, the last diagonal entry of the
Smith normal form of $A$.
"""
largest_elementary_divisor(A::ZZMatrix) = maximal_elementary_divisor(A)

################################################################################
#
#  Function to convert a matrix to array
#
################################################################################

function to_array(M::QQMatrix)
  A = Vector{QQFieldElem}(undef, ncols(M)*nrows(M))
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
  kx, x = polynomial_ring(k, cached = false)
  return minpoly(kx, M)
end

function charpoly(M::MatElem)
  k = base_ring(M)
  kx, x = polynomial_ring(k, cached = false)
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

function map_entries(F::fpField, M::ZZMatrix)
  MR = zero_matrix(F, nrows(M), ncols(M))
  ccall((:fmpz_mat_get_nmod_mat, libflint), Cvoid, (Ref{fpMatrix}, Ref{ZZMatrix}), MR, M)
  return MR
end
################################################################################
#
#  Kernel of matrix over Z/nZ
#
################################################################################

function _left_kernel_of_howell_form_aurel(A::zzModMatrix)
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

function _left_kernel_naive(A::zzModMatrix)
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

function left_kernel_prime_power(A::zzModMatrix, p::Int, l::Int)
  R = base_ring(A)
  Alift = lift(A)
  F = GF(p)
  _, _M = left_kernel(change_base_ring(F, Alift))
  M = lift(_M)
  Mi = hnf_modular_eldiv(M, ZZRingElem(p))
  r = nrows(Mi)
  while is_zero_row(Mi, r)
    r -= 1
  end
  Mi = sub(Mi, 1:r, 1:ncols(Mi))
  Mfi = Mi * Alift
  local H
  for i in 1:(l - 1)
    _, K = left_kernel(change_base_ring(F, divexact(Mfi, p^i)))
    H = hnf_modular_eldiv(lift(K), ZZRingElem(p))
    r = nrows(H)
    while is_zero_row(H, r)
      r -= 1
    end
    H = sub(H, 1:r, 1:ncols(H))

    Mi = H * Mi
    Mfi = H * Mfi
  end
  Khow = howell_form(change_base_ring(R, Mi))
  i = 1
  while !is_zero_row(Khow, i)
    i += 1
  end
  return i - 1, Khow
end



function invmod(M::ZZMatrix, d::ZZRingElem)
  if fits(Int, d)
    RR = residue_ring(FlintZZ, Int(d), cached = false)
    MRR = map_entries(RR, M)
    SR = zero_matrix(RR, 2*nrows(M), 2*nrows(M))
    _copy_matrix_into_matrix(SR, 1, 1, MRR)
    for i = 1:nrows(M)
      SR[i, i+nrows(M)] = 1
    end
    ccall((:nmod_mat_howell_form, libflint), Nothing, (Ref{zzModMatrix}, ), SR)
    #howell_form!(SR)
    iMR = SR[1:nrows(M), nrows(M)+1:ncols(SR)]
    #@assert iMR*MRR == identity_matrix(RR, nrows(M))
    return lift(iMR)
  else
    R = residue_ring(FlintZZ, d, cached = false)
    MR = map_entries(R, M)
    S = zero_matrix(R, 2*nrows(M), 2*nrows(M))
    _copy_matrix_into_matrix(S, 1, 1, MR)
    for i = 1:nrows(M)
      S[i, i+nrows(M)] = 1
    end
    ccall((:fmpz_mod_mat_howell_form, libflint), Nothing, (Ref{ZZModMatrix}, ), S)
    iM = S[1:nrows(M), nrows(M)+1:ncols(S)]
    #@assert iM*MR == identity_matrix(R, nrows(M))
    return lift(iM)
  end
end


function map_entries(R::Nemo.ZZModRing, M::ZZMatrix)
  N = zero_matrix(R, nrows(M), ncols(M))
  GC.@preserve M N begin
    for i = 1:nrows(M)
      for j = 1:ncols(M)
        m = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), M, i - 1, j - 1)
        n = ccall((:fmpz_mod_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZModMatrix}, Int, Int), N, i - 1 , j - 1)
        ccall((:fmpz_mod, libflint), Nothing, (Ptr{ZZRingElem}, Ptr{ZZRingElem}, Ref{ZZRingElem}), n, m, R.n)
      end
    end
  end
  return N
end

################################################################################
#
#  multiplicative order ZZRingElem/QQMatrix
#
################################################################################

# we avoid to compute twice the minpoly in case of finite order
function _has_finite_multiplicative_order(f)
  @assert is_square(f)
  chi = minpoly(f)
  !Hecke.is_squarefree(chi) && return (false, [Pair(chi, 1)])
  fact = collect(factor(chi))
  return all(p -> is_cyclotomic_polynomial(p[1]), fact), fact
end

@doc raw"""
    has_finite_multiplicative_order(M::Union{ZZMatrix, QQMatrix}) -> Bool

Given a matrix `M` with integral or rational entries, return whether `M` has
finite multiplicative order.

# Examples

```jldoctest
julia> M = matrix(QQ, 4, 4, [ 1  0  0  0;
                              0 -1  0  0;
                             -1  0 -1 -1;
                              1  1  2  1])
[ 1    0    0    0]
[ 0   -1    0    0]
[-1    0   -1   -1]
[ 1    1    2    1]

julia> has_finite_multiplicative_order(M)
true

julia> N = matrix(ZZ, 2, 2, [1 1;
                             0 1])
[1   1]
[0   1]

julia> has_finite_multiplicative_order(N)
false
```
"""
function has_finite_multiplicative_order(f::Union{ZZMatrix, QQMatrix})
  @req is_square(f) "Matrix must be square"
  return _has_finite_multiplicative_order(f)[1]
end

@doc raw"""
    multiplicative_order(M::Union{ZZMatrix, QQMatrix}) -> IntExt

Given a matrix `M` with integral or rational entries, return the multiplicative
order of `M`. Note that this can be infinite, in which case the function returns
`PosInf()`.

# Examples

```jldoctest
julia> M = matrix(QQ, 4, 4, [ 1  0  0  0;
                              0 -1  0  0;
                             -1  0 -1 -1;
                              1  1  2  1])
[ 1    0    0    0]
[ 0   -1    0    0]
[-1    0   -1   -1]
[ 1    1    2    1]

julia> multiplicative_order(M)
4

julia> N = matrix(ZZ, 2, 2, [1 1;
                             0 1])
[1   1]
[0   1]

julia> multiplicative_order(N)
PosInf()
```
"""
function multiplicative_order(f::Union{ZZMatrix, QQMatrix})
  @req is_invertible(f) "Matrix must be invertible"
  bool, fact = _has_finite_multiplicative_order(f)
  bool || return PosInf()
  degs = unique([degree(p[1]) for p in fact])
  exps = Int.(euler_phi_inv(degs[1]))
  for i in 1:length(degs)
    union!(exps, Int.(euler_phi_inv(degs[i])))
  end
  maxdeg = lcm(exps)
  divmd = sort(divisors(maxdeg))
  n = findfirst(k -> isone(f^k), divmd)
  @assert n !== nothing
  return divmd[n]
end

################################################################################
#
#  Linear solve context
#
################################################################################

mutable struct LinearSolveCtx{S, T}
  A::S
  R::S # rref
  U::S # U * A = R
  v::T # temp vector
  pivots::Vector{Int}

  function LinearSolveCtx{S}() where {T, S <: MatElem{T}}
    return new{S, Vector{T}}()
  end

  function LinearSolveCtx(A::MatElem{T}, side::Symbol) where {T <: RingElem}
    @assert side === :right
    r, R, U = _rref_with_trans(A)
    pivots = _get_pivots_ut(R)
    v = [zero(base_ring(A)) for i in 1:ncols(U)]
    z = new{typeof(A), Vector{T}}(A, R, U, v, pivots)
  end
end

function solve_context(A; side::Symbol)
  return LinearSolveCtx(A, side)
end

function solve(L::LinearSolveCtx, b::Vector)
  L.v = mul!(L.v, L.U, b)
  fl, w = can_solve_rref_ut(L.R, L.v, L.pivots)
  # entries of w are aliasing v, which we don't want for some reason
  #if fl
  #  @assert L.A * w == b
  #end
  return fl, deepcopy(w)
end
