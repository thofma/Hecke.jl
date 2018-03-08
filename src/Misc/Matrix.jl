export iszero_row, modular_hnf, howell_form, _hnf_modular, kernel_mod

import Nemo.matrix

import Base.vcat

# 

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
  A = Array{T}(rows(a), cols(a))
  for i = 1:rows(a)
    for j = 1:cols(a)
      A[i,j] = T(a[i,j])
    end 
  end
  return A
end

function iszero_row(M::fmpz_mat, i::Int)
  for j = 1:cols(M)
    if M[i,j] != 0 
      return false
    end
  end
  return true
end

function iszero_row(M::nmod_mat, i::Int)
  zero = UInt(0)
  for j in 1:cols(M)
    t = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ref{nmod_mat}, Int, Int), M, i - 1, j - 1)
    if t != zero
      return false
    end
  end
  return true
end


function iszero_row(M::MatElem{T}, i::Int) where T
  for j in 1:cols(M)
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
  ccall((:fmpz_mat_scalar_divexact_fmpz, :libflint), Void,
               (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{fmpz}), a, a, d)
end

function mul!(a::fmpz_mat, b::fmpz_mat, c::fmpz)
  ccall((:fmpz_mat_scalar_mul_fmpz, :libflint), Void, 
                  (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{fmpz}), a, b, c)
end                  

#computes (hopefully) the hnf for vcat(a*I, m) and returns ONLY the
#non-singular part. By definition, the result wil have full rank
#
#Should be rewritten to use Howell and lifting rather the big HNF
#
function modular_hnf(m::fmpz, a::fmpz_mat, shape::Symbol = :upperright)
  c = vcat(parent(a)(m), a)
  n = cols(a)
  w = view(c, n+1, 1, 2*n, n)
  ccall((:fmpz_mat_scalar_mod_fmpz, :libflint), Void, (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{fmpz}), w, w, m)
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
    h = hnf(_swapcols(x))
    _swapcols!(h)
    _swaprows!(h)
    return h::fmpz_mat
  end
  return hnf(x)::fmpz_mat
end

function _hnf_modular_eldiv(x::fmpz_mat, m::fmpz, shape::Symbol = :upperright)
  if shape == :lowerleft
    h = hnf_modular_eldiv(_swapcols(x), m)
    _swapcols!(h)
    _swaprows!(h)
    return h
  elseif shape == :upperright
    return hnf_modular_eldiv(x, m)
  else
    error("shape $shape not supported")
  end
end

function hnf_modular_eldiv!(x::fmpz_mat, d::fmpz)
   (rows(x) < cols(x)) &&
                error("Matrix must have at least as many rows as columns")
   ccall((:fmpz_mat_hnf_modular_eldiv, :libflint), Void,
                (Ref{fmpz_mat}, Ref{fmpz}), x, d)
   return x
end

function ishnf(x::fmpz_mat, shape::Symbol)
  if shape == :upperright
    return ishnf(x)
  elseif shape == :lowerleft
    r = rows(x)
    i = 0
    j_old = cols(x) + 1

    for i in rows(x):-1:1

      if iszero_row(x, i)
        break
      end

      j = cols(x)
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

    for k in i:-1:1
      !iszero_row(x, k) && return false
    end
    return true
  end
end

function _swaprows(x::fmpz_mat)
  y = deepcopy(x)
  _swaprows!(y)
  return y
end

function _swapcols(x::fmpz_mat)
  y = deepcopy(x)
  _swapcols!(y)
  return y
end

function _swaprows!(x::fmpz_mat)
  r = rows(x)
  c = cols(x)

  if r == 1
    return x
  end

  if r % 2 == 0
    for i in 1:div(r,2)
      for j = 1:c
        # we swap x[i,j] <-> x[r-i+1,j]
        s = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), x, i - 1, j - 1)
        t = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), x, (r - i + 1) - 1, j - 1)
        ccall((:fmpz_swap, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), t, s)
      end
    end
  else
    for i in 1:div(r-1,2)
      for j = 1:c
        # we swap x[i,j] <-> x[r-i+1,j]
        s = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), x, i - 1, j - 1)
        t = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), x, (r - i + 1) - 1, j - 1)
        ccall((:fmpz_swap, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), t, s)
      end
    end
  end
  nothing
end

function _swaprows!(x::fmpz_mat, i::Int, j::Int)
  ccall((:_fmpz_mat_swap_rows, :libflint), Void, (Ref{fmpz_mat}, Int, Int), x, i-1, j-1)
  nothing
end

function _swaprows!(x::nmod_mat, i::Int, j::Int)
  ccall((:_nmod_mat_swap_rows, :libflint), Void, (Ref{nmod_mat}, Int, Int), x, i-1, j-1)
  nothing
end
  

function _swaprows!(x::nmod_mat)
  r = rows(x)
  c = cols(x)

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
  nothing
end

function _swapcols!(x::nmod_mat)
  r = rows(x)
  c = cols(x)

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
  nothing
end

function _swapcols!(x::fmpz_mat)
  r = rows(x)
  c = cols(x)

  if c == 1
    return x
  end

  if c % 2 == 0
    for i in 1:div(c,2)
      for j = 1:r
        # swap x[j,i] <-> x[j,c-i+1]
        s = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), x, j - 1, i - 1)
        t = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), x, j - 1, (c - i + 1 ) - 1)
        ccall((:fmpz_swap, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), t, s)
      end
    end
  else
    for i in 1:div(c-1,2)
      for j = 1:r
        # swap x[j,i] <-> x[j,c-i+1]
        s = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), x, j - 1, i - 1)
        t = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), x, j - 1, (c - i + 1 ) - 1)
        ccall((:fmpz_swap, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), t, s)
      end
    end
  end
  nothing
end

function _swapcols(x::Generic.Mat)
  z = deepcopy(x)
  _swapcols!(z)
  return z
end

function _swapcols!(x::Generic.Mat)
  r = rows(x)
  c = cols(x)
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
  nothing
end

function _swaprows(x::Generic.Mat)
  z = deepcopy(x)
  _swaprows(z)
  return z
end

function _swaprows!(x::Generic.Mat)
  r = rows(x)
  c = cols(x)

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
  nothing
end
################################################################################
# 
################################################################################

function maximum(f::typeof(abs), a::fmpz_mat)
  m = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, 0,0)
  for i=1:rows(a)
    for j=1:cols(a)
      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, i-1, j-1)
      if ccall((:fmpz_cmpabs, :libflint), Cint, (Ptr{fmpz}, Ptr{fmpz}), m, z) < 0
        m = z
      end
    end
  end
  r = fmpz()
  ccall((:fmpz_abs, :libflint), Void, (Ref{fmpz}, Ptr{fmpz}), r, m)
  return r
end

function maximum(a::fmpz_mat)  
  m = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, 0,0)
  for i=1:rows(a)
    for j=1:cols(a)
      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, i-1, j-1)
      if ccall((:fmpz_cmp, :libflint), Cint, (Ptr{fmpz}, Ptr{fmpz}), m, z) < 0
        m = z
      end
    end
  end
  r = fmpz()
  ccall((:fmpz_set, :libflint), Void, (Ref{fmpz}, Ptr{fmpz}), r, m)
  return r
end

function minimum(a::fmpz_mat) 
  m = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, 0,0)
  for i=1:rows(a)
    for j=1:cols(a)
      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), a, i-1, j-1)
      if ccall((:fmpz_cmp, :libflint), Cint, (Ptr{fmpz}, Ptr{fmpz}), m, z) > 0
        m = z
      end
    end
  end
  r = fmpz()
  ccall((:fmpz_set, :libflint), Void, (Ref{fmpz}, Ptr{fmpz}), r, m)
  return r
end

function lift_unsigned(a::nmod_mat)
  z = zero_matrix(FlintZZ, rows(a), cols(a))
  ccall((:fmpz_mat_set_nmod_mat_unsigned, :libflint), Void,
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

function _right_kernel(x::nmod_mat)
  z = zero_matrix(base_ring(x), cols(x), max(rows(x),cols(x)))
  n = ccall((:nmod_mat_nullspace, :libflint), Int, (Ref{nmod_mat}, Ref{nmod_mat}), z, x)
  return z,n
end

# compute basis for the left kernel space
# output is array of arrays, which span the kernel

function kernel(a)
  x = transpose(a)
  R = base_ring(a)
  z, n = _right_kernel(x)
  z = transpose(z)
  T = elem_type(base_ring(a))
  ar = typeof(Array{T}(cols(z)))[]
  for i in 1:n 
    t = Array{T}(cols(z))
    for j in 1:cols(z)
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
  ar = typeof(Array{T}(rows(z)))[]
  for i in 1:n
    t = Array{T}(rows(z))
    for j in 1:rows(z)
      t[j] = R(z[j, i])
    end
    push!(ar,t)
  end
  return ar
end

left_kernel(a::MatElem) = right_kernel(transpose(a))

function lift(a::Generic.Mat{Generic.Res{fmpz}})
  z = zero_matrix(FlintZZ, rows(a), cols(a))
  for i in 1:rows(a)
    for j in 1:cols(a)
      z[i, j] = lift(a[i, j])
    end
  end
  return z
end

function _rref(a::Generic.Mat{Generic.Res{fmpz}})
  m = modulus(base_ring(a))
  b = zero_matrix(FlintZZ, rows(a), cols(a))
  # I actually don't know if this is necessary
  for i in 1:rows(b)
    for j in 1:cols(b)
      b[i,j] = lift(a[i,j]) % m
    end
  end

  # fmpz_mat_rref_mod assumes that input is reduced modulo m
  r = ccall((:fmpz_mat_rref_mod, :libflint), Int, (Ptr{Void}, Ref{fmpz_mat}, Ref{fmpz}), C_NULL, b, m)
  return r, parent(a,false)(b)
end

function _rref(a::nmod_mat)
  b = rref(a)
  # TODO: Clean up one we use new Nemo version.
  if length(b) == 1
    return rank(b), b
  else
    return b
  end
end

function _right_kernel(a::Generic.Mat{Generic.Res{fmpz}})
  r, b = _rref(a)
  pivots = Array{Int}(r)
  nonpivots = Array{Int}(cols(b) - r)
  X = zero_matrix(base_ring(a),cols(b),cols(b) - r)

  if r == 0
    return vcat(identity_matrix(FlintZZ, cols(b) - r), zero_matrix(FlintZZ, r, cols(b) - r)), cols(b)
  elseif !((cols(b) - r) == 0)
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
    while k <= cols(b) - r
      nonpivots[k] = j
      k += 1
      j += 1
    end

    for i in 1:cols(b) - r
      for j in 1:r
        X[pivots[j],i] = - b[j,nonpivots[i]]
      end
      X[nonpivots[i],i] = 1
    end
  end
  return X, cols(b) - r
end

function kernel_mod(a::fmpz_mat, m::fmpz)
  b = deepcopy(a)
  for i in 1:rows(b)
    for j in 1:cols(b)
      b[i,j] = b[i,j] % m
    end
  end

  # fmpz_mat_rref_mod assumes that input is reduced modulo m
  r = ccall((:fmpz_mat_rref_mod, :libflint), Int, (Ptr{Void}, Ref{fmpz_mat}, Ref{fmpz}), C_NULL, b, m)
  pivots = Array{Int}(r)
  nonpivots = Array{Int}(cols(b) - r)
  X = zero_matrixSpace(FlintZZ,cols(b),cols(b))

  if r == 0
    return identity_matrix(FlintZZ, cols(b))
  elseif !((cols(b) - r) == 0)
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
    while k <= cols(b) - r
      nonpivots[k] = j
      k += 1
      j += 1
    end

    for i in 1:cols(b) - r
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
  for i in 1:rows(H)
    if iszero_row(H, i)
      break
    end
  end
  return sub(U, i:rows(U), 1:cols(U))
end

################################################################################
#
#  Copy matrix into another matrix
#
################################################################################

# Copy B into A at position (i, j)
function _copy_matrix_into_matrix(A::fmpz_mat, i::Int, j::Int, B::fmpz_mat)
  for k in 0:rows(B) - 1
    for l in 0:cols(B) - 1
      d = ccall((:fmpz_mat_entry, :libflint),
                Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), B, k, l)
      t = ccall((:fmpz_mat_entry, :libflint),
                Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), A, i - 1 + k, j - 1 + l)
      ccall((:fmpz_set, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), t, d)
    end
  end
end

doc"""
    isposdef(a::fmpz_mat) -> Bool

> Tests if $a$ positive definite by testing if all principal minors
> have positive determinant.
"""
function isposdef(a::fmpz_mat)
  for i=1:rows(a)
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
      ccall((:mpfr_set_z_2exp, :libmpfr), Void, (Ref{BigFloat}, Ref{BigInt}, Clong, Int32), a[i,j], tmp_mpz, e+Clong(Int(d[1,j])), __get_rounding_mode())
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
      ccall((:fmpz_set_mpz, :libflint), Void, (Ref{fmpz}, Ref{BigInt}), tmp_fmpz, tmp_mpz)
      if f > 0  
        ccall((:fmpz_mul_2exp, :libflint), Void, (Ref{fmpz}, Ref{fmpz}, UInt), tmp_fmpz, tmp_fmpz, f)
      else
        ccall((:fmpz_tdiv_q_2exp, :libflint), Void, (Ref{fmpz}, Ref{fmpz}, UInt), tmp_fmpz, tmp_fmpz, -f);
      end
      setindex!(b, tmp_fmpz, i, j)
    end
  end
  return b
end

function shift!(g::fmpz_mat, l::Int)
  for i=1:rows(g)
    for j=1:cols(g)
      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), g, i-1, j-1)
      if l > 0
        ccall((:fmpz_mul_2exp, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}, Int), z, z, l)
      else
        ccall((:fmpz_tdiv_q_2exp, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}, Int), z, z, -l)
      end
    end
  end
  return g
end


doc"""
***
    mod!(M::fmpz_mat, p::fmpz) 
> Reduces every entry modulo $p$ in-place, ie. applies the mod function to every entry.
"""
function mod!(M::fmpz_mat, p::fmpz)
  for i=1:rows(M)
    for j=1:cols(M)
      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), M, i - 1, j - 1)
      ccall((:fmpz_mod, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}, Ref{fmpz}), z, z, p)
    end
  end
  nothing
end

doc"""
***
    mod(M::fmpz_mat, p::fmpz) -> fmpz_mat
> Reduces every entry modulo $p$, ie. applies the mod function to every entry.
"""
function mod(M::fmpz_mat, p::fmpz)
  N = deepcopy(M)
  mod!(N, p)
  return N
end

doc"""
***
    vcat(A::Array{Generic.Mat, 1}) -> Generic.Mat
    vcat(A::Array{fmpz_mat}, 1}) -> fmpz_mat
> Forms a big matrix my vertically concatenating the matrices in $A$.
> All component matrices need to have the same number of columns.
"""
function vcat(A::Array{Generic.Mat{T}, 1}) where T
  if any(x->cols(x) != cols(A[1]), A)
    error("Matrices must have same number of columns")
  end
  M = zero_matrix(base_ring(A[1]), sum(rows, A), cols(A[1]))
  s = 0
  for i=A
    for j=1:rows(i)
      for k=1:cols(i)
        M[s+j, k] = i[j,k]
      end
    end
    s += rows(i)
  end
  return M
end

function vcat(A::Array{fmpz_mat, 1})
  if any(x->cols(x) != cols(A[1]), A)
    error("Matrices must have same number of columns")
  end
  M = zero_matrix(base_ring(A[1]), sum(rows, A), cols(A[1]))
  s = 0
  for i=A
    for j=1:rows(i)
      for k=1:cols(i)
        M[s+j, k] = i[j,k]
      end
    end
    s += rows(i)
  end
  return M
end

function vcat(A::Array{nmod_mat, 1})
  if any(x->cols(x) != cols(A[1]), A)
    error("Matrices must have same number of columns")
  end
  M = zero_matrix(base_ring(A[1]), sum(rows, A), cols(A[1]))
  s = 0
  for i=A
    for j=1:rows(i)
      for k=1:cols(i)
        M[s+j, k] = i[j,k]
      end
    end
    s += rows(i)
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
doc"""
***
  snf_with_transform(A::fmpz_mat, l::Bool = true, r::Bool = true) -> fmpz_mat, fmpz_mat, fmpz_mat

> Given some integer matrix A, compute the Smith normal form (elementary
> divisor normal form) of A. If l and/ or r are true, then the corresponding
> left and/ or right transformation matrices are computed as well.
"""
function snf_with_transform(A::fmpz_mat, l::Bool = true, r::Bool = true)
  if r
    R = identity_matrix(FlintZZ, cols(A))
  end

  if l
    L = identity_matrix(FlintZZ, rows(A))
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
  for i=1:min(rows(S), cols(S))
    if S[i,i] == 1
      continue
    end
    for j=i+1:min(rows(S), cols(S))
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
        for k=1:cols(L)
          x = -b*f
#          L[i,k], L[j,k] = L[i,k]+L[j,k], x*L[i,k]+(x+1)*L[j,k]
          L[i,k], L[j,k] = L[i,k]+L[j,k], x*(L[i,k]+L[j,k])+L[j,k]
        end
      end
      if r
        # V = [e -b ; f a];
        # so col i and j of R will be transformed. We do it naively
        # careful: at this point, R is still transposed
        for k=1:rows(R)
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

function Base.nullspace(M::nmod_mat)
  R = base_ring(M)
  if isprime(fmpz(modulus(R)))
    k = zero_matrix(R, cols(M), cols(M))
    n = ccall((:nmod_mat_nullspace, :libflint), Int, (Ref{nmod_mat}, Ref{nmod_mat}), k, M)
    return (k, n)
  end

  N = hcat(M', identity_matrix(R, cols(M)))
  ex = 0
  if rows(N) < cols(N)
    ex = cols(N) - rows(N)
    N = vcat(N, zero_matrix(R, ex, cols(N)))
  end
  H = howell_form(N)
  nr = 1
  while nr <= rows(H) && !iszero_row(H, nr)
    nr += 1
  end
  nr -= 1
  h = sub(H, 1:nr, 1:rows(M))
  for i=1:rows(h)
    if iszero_row(h, i)
      k = sub(H, i:rows(h), rows(M)+1:cols(H))
      return k', rows(k)
    end
  end
end

function lift(M::FmpzMatSpace, Mp::Union{nmod_mat,Generic.Mat{Generic.Res{fmpz}}})
  @assert M.cols == cols(Mp) && M.rows == rows(Mp)
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

doc"""
***
  isdiag(A::fmpz_mat)

> Tests if A is diagonal.
"""
function isdiag(A::fmpz_mat)
  for i = 1:cols(A)
    for j = 1:rows(A)
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
  m = rows(A)
  n = cols(A)
  @assert m == rows(b)
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
  m = rows(A)
  n = cols(A)
  @assert m == rows(b)
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

length(A::Nemo.MatElem) = rows(A) * cols(A)
Base.ndims(A::Nemo.MatElem) = 2

function Base.size(A::Nemo.MatElem, n::Int)
  if n == 1
    return rows(A)
  elseif n == 2
    return cols(A)
  elseif n < 1
    error("arraysize: dimension out of range")
  else
    return 1
  end
end

function Base.indices(A::Nemo.MatElem)
  return (Base.OneTo(rows(A)), Base.InTo(cols(A)))
end

function Base.indices(A::Nemo.MatElem, n::Int)
  return Base.OneTo(size(A, n))
end

function Base.eachindex(A::Nemo.MatElem)
  return Base.OneTo(length(A))
end

function Base.stride(A::Nemo.MatElem, n::Int)
  if n <= 1
    return 1
  elseif n == 2
    return rows(A)
  else
    return length(A)
  end
end

Base.eltype(A::Nemo.MatElem{T}) where T <: Nemo.RingElem = T

getindex(A::Nemo.MatElem, n::Int) = A[1 + ((n-1) % rows(A)), 1 + div((n-1), rows(A))]

function setindex!(A::Nemo.MatElem{T}, n::Int, s::T) where T <: RingElem
  A[1 + ((n-1) % rows(A)), 1 + div((n-1), rows(A))] = s
end

Base.start(A::Nemo.MatElem) = 1
Base.next(A::Nemo.MatElem, i::Int) = A[i], i+1
Base.done(A::Nemo.MatElem, i::Int) = i > length(A)

function setindex!(A::Nemo.MatElem{T}, b::Nemo.MatElem{T}, ::Colon, i::Int) where T
  @assert cols(b) == 1 && rows(b) == rows(A) 
  for j=1:rows(A)
    A[j,i] = b[j]
  end
  b
end

function setindex!(A::Nemo.MatElem{T}, b::Nemo.MatElem{T}, i::Int, ::Colon) where T
  @assert rows(b) == 1 && cols(b) == cols(A)
  for j=1:cols(A)
    A[i,j] = b[j]
  end
  b
end

function setindex!(A::Nemo.MatElem, b::Array{<: Any, 1}, ::Colon, i::Int) 
  @assert length(b) == rows(A)
  for j=1:rows(A)
    A[j,i] = b[j]
  end
  b
end

function setindex!(A::Nemo.MatElem, b::Array{ <: Any, 1}, i::Int, ::Colon)
  @assert length(b) == cols(A)
  for j=1:cols(A)
    A[i,j] = b[j]
  end
  b
end

function setindex!(A::Nemo.MatElem, b, ::Colon, i::Int) 
  for j=1:rows(A)
    A[j,i] = b
  end
  b
end

function setindex!(A::Nemo.MatElem, b, i::Int, ::Colon)
  for j=1:cols(A)
    A[i,j] = b
  end
  b
end


getindex(A::Nemo.MatElem, i::Int, ::Colon) = A[i:i, 1:cols(A)]
getindex(A::Nemo.MatElem, ::Colon, i::Int) = A[1:rows(A), i:i]


function Base.hcat(A::Nemo.MatElem...)
  r = rows(A[1])
  c = cols(A[1])
  R = base_ring(A[1])
  for i=2:length(A)
    @assert rows(A[i]) == r
    @assert base_ring(A[i]) == R
    c += cols(A[i])
  end
  X = zero_matrix(R, r, c)
  o = 1
  for i=1:length(A)
    for j=1:cols(A[i])
      X[:, o] = A[i][:, j]
      o += 1
    end
  end
  return X
end

function Base.vcat(A::Nemo.MatElem...)
  r = rows(A[1])
  c = cols(A[1])
  R = base_ring(A[1])
  for i=2:length(A)
    @assert cols(A[i]) == c
    @assert base_ring(A[i]) == R
    r += rows(A[i])
  end
  X = zero_matrix(R, r, c)
  o = 1
  for i=1:length(A)
    for j=1:rows(A[i])
      X[o, :] = A[i][j, :]
      o += 1
    end
  end
  return X
end

function Base.cat(n::Int, A::Nemo.MatElem...) 
  if n==1
    return vcat(A...)
  elseif n==2
    return hcat(A...)
  else
    error("does not make sense here")
  end
end

function Base.cat(dims::Tuple{Int, Int}, A::Nemo.MatElem...) 
  @assert dims == (1,2)

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

Base.cat(dims, A::Nemo.MatElem...) = cat(Tuple(dims), A...)

doc"""
    reduce_mod!(A::Nemo.MatElem{T}, B::Nemo.MatElem{T}) where T <: Nemo.FieldElem

> For a reduced row echelon matrix $B$, reduce $A$ modulo $B$, ie. all the pivot
> columns will be zero afterwards.
"""
function reduce_mod!(A::Nemo.MatElem{T}, B::Nemo.MatElem{T}) where T <: Nemo.FieldElem
  @assert isrref(B)
  for h=1:rows(A)
    j = 1
    for i=1:rows(B)
      while iszero(B[i, j])
        j += 1
      end
      A[h, :] -= A[h, j] * B[i, :]
    end
  end
  return A
end

doc"""
    reduce_mod(A::Nemo.MatElem{T}, B::Nemo.MatElem{T}) where T <: Nemo.FieldElem -> MatElem

> For a reduced row echelon matrix $B$, reduce $A$ modulo $B$, ie. all the pivot
> columns will be zero afterwards.
"""
function reduce_mod(A::Nemo.MatElem{T}, B::Nemo.MatElem{T}) where T <: Nemo.FieldElem
  C = deepcopy(A)
  reduce_mod!(C, B)
  return C
end

doc"""
    find_pivot(A::Nemo.MatElem{<:Nemo.RingElem}) -> Array{Int, 1}

> Find the pivot-columns of the reduced row echelon matrix $A$
"""
function find_pivot(A::Nemo.MatElem{<:Nemo.RingElem})
  @assert isrref(A)
  p = Int[]
  j = 0
  for i=1:rows(A)
    j += 1
    if j > cols(A)
      return p
    end
    while iszero(A[i,j])
      j += 1
      if j > cols(A)
        return p
      end
    end
    push!(p, j)
  end
  return p
end

doc"""
    cansolve(A::Nemo.MatElem{T}, B::Nemo.MatElem{T}) where T <: Nemo.FieldElem -> Bool, MatElem
> Tries to solve $Ax = B$
"""
function Nemo.cansolve(A::Nemo.MatElem{T}, B::Nemo.MatElem{T}) where T <: Nemo.FieldElem
  R = base_ring(A)
  @assert R == base_ring(B)
  @assert rows(A) == rows(B)
  mu = [A B]
  rk = rref!(mu)
  p = find_pivot(mu)
  if any(i->i>cols(A), p)
    return false, B
  end
  sol = zero_matrix(R, cols(A), cols(B))
  for i = 1:length(p)
    for j = 1:cols(B)
      sol[p[i], j] = mu[i, cols(A) + j]
    end
  end
  return true, sol
end

