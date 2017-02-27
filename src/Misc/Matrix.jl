export is_zero_row, modular_hnf, submat, howell_form, _hnf_modular, kernel_mod, matrix, zeromatrix

# 

function matrix{T <: RingElem}(A::Array{T, 2})
  r, c = size(A)
  (r < 0 || c < 0) && error("Array must be non-empty")
  m = MatrixSpace(parent(A[1, 1]), size(A)...)(A)
  return m
end

function matrix{T <: RingElem}(A::Array{T, 1})
  return matrix(reshape(A,length(A),1))
end

function matrix{T}(R::Ring, n::Int, m::Int, A::Array{T, 2})
  m = MatrixSpace(R, n, m)(A)
  return m
end

function zeromatrix(R::Ring, n::Int, m::Int)
  return MatrixSpace(R, n, m)()
end

#

function Array{T}(a::fmpz_mat; S::Type{T} = fmpz)
  A = Array(T, rows(a), cols(a))
  for i = 1:rows(a)
    for j = 1:cols(a)
      A[i,j] = T(a[i,j])
    end 
  end
  return A
end

function is_zero_row(M::fmpz_mat, i::Int)
  for j = 1:cols(M)
    if M[i,j] != 0 
      return false
    end
  end
  return true
end

function is_zero_row(M::nmod_mat, i::Int)
  zero = UInt(0)
  for j in 1:cols(M)
    t = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &M, i - 1, j - 1)
    if t != zero
      return false
    end
  end
  return true
end


function is_zero_row{T}(M::MatElem{T}, i::Int)
  for j in 1:cols(M)
    if !iszero(M[i,j])
      return false
    end
  end
  return true
end

function is_zero_row{T <: Integer}(M::Array{T, 2}, i::Int)
  for j = 1:Base.size(M, 2)
    if M[i,j] != 0 
      return false
    end
  end
  return true
end

function is_zero_row(M::Array{fmpz, 2}, i::Int)
  for j = 1:Base.size(M, 2)
    if M[i,j] != 0 
      return false
    end
  end
  return true
end

function is_zero_row{T <: RingElem}(M::Array{T, 2}, i::Int)
  for j in 1:Base.size(M, 2)
    if !iszero(M[i,j])
      return false
    end
  end
  return true
end

function divexact!(a::fmpz_mat, b::fmpz_mat, d::fmpz)
  ccall((:fmpz_mat_scalar_divexact_fmpz, :libflint), Void,
               (Ptr{fmpz_mat}, Ptr{fmpz_mat}, Ptr{fmpz}), &a, &a, &d)
end

function mul!(a::fmpz_mat, b::fmpz_mat, c::fmpz)
  ccall((:fmpz_mat_scalar_mul_fmpz, :libflint), Void, 
                  (Ptr{fmpz_mat}, Ptr{fmpz_mat}, Ptr{fmpz}), &a, &b, &c)
end                  

#computes (hopefully) the hnf for vcat(a*I, m) and returns ONLY the
#non-singular part. By definition, the result wil have full rank
#
#Should be rewritten to use Howell and lifting rather the big HNF
#
function modular_hnf(m::fmpz, a::fmpz_mat, shape::Symbol = :upperright)
  c = vcat(parent(a)(m), a)
  n = cols(a)
  w = window(c, n+1, 1, 2*n, n)
  ccall((:fmpz_mat_scalar_mod_fmpz, :libflint), Void, (Ptr{fmpz_mat}, Ptr{fmpz_mat}, Ptr{fmpz}), &w, &w, &m)
  if shape == :lowerleft
    c = _hnf(c, shape)
    return sub(c, n+1:2*n, 1:n)
  else
    c = hnf(c)
    c = sub(c, 1:n, 1:n)
  end
end

#function _lift_howell_to_hnf(x::nmod_mat)
## Assume that x is square, in howell normal form and all non-zero rows are at the bottom
## NOTE: _OUR_ Howell normal form algorithm always puts the rows at the right position
## If row i is non-zero then i is the rightmost non-zero entry
## Thus lifting is just replacing zero diagonal entries
#  !issquare(x) && error("Matrix has to be square")
#  y = lift_unsigned(x)
#  for i in cols(y):-1:1
#    z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &y, i - 1, i - 1)
#    if Bool(ccall((:fmpz_is_zero, :libflint), Int, (Ptr{fmpz}, ), z))
##      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &y, 0, i - 1)
#      ccall((:fmpz_set_ui, :libflint), Void, (Ptr{fmpz}, UInt), z, x._n)
##      for k in 1:i-1
##        _swaprows!(y, k, k+1)
##      end
#    end
#  end
#  return y
#end

function submat{T <: Integer}(x::nmod_mat, r::UnitRange{T}, c::UnitRange{T})
  z = deepcopy(window(x, r, c))
  return z
end

function submat{T <: Integer}(x::fmpz_mat, r::UnitRange{T}, c::UnitRange{T})
  z = deepcopy(window(x, r, c))
  return z
end

#function _hnf_modular(x::fmpz_mat, m::fmpz, shape::Symbol = :lowerleft)
#  if abs(m) < fmpz(typemax(UInt))
#    y = MatrixSpace(ResidueRing(FlintZZ, m), rows(x), cols(x))(x)
#    howell_form!(y, shape)
#    y = submat(y, rows(y) - cols(y) + 1:rows(y), 1:cols(y))
#    return _lift_howell_to_hnf(y)
#  end
#  return __hnf_modular(x, m, shape)
#end
#
#function __hnf_modular(x::fmpz_mat, m::fmpz, shape::Symbol = :lowerleft)
## See remarks above
#  y = deepcopy(x)
#  howell_form!(y, m, shape)
#  y = submat(y, rows(y) - cols(y) + 1:rows(y), 1:cols(y))
#  for i in cols(y):-1:1
#    z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &y, i - 1, i - 1)
#    if Bool(ccall((:fmpz_is_zero, :libflint), Int, (Ptr{fmpz}, ), z))
#    #if ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &x, i - 1, i - 1) == 0
##      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &y, 0, i - 1)
#      ccall((:fmpz_set, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), z, &m)
##      for k in 1:i-1
##        _swaprows!(y, k, k+1)
##      end
#    end
#  end
#  return y
#end

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
  end
end

function hnf_modular_eldiv!(x::fmpz_mat, d::fmpz)
   (rows(x) < cols(x)) &&
                error("Matrix must have at least as many rows as columns")
   ccall((:fmpz_mat_hnf_modular_eldiv, :libflint), Void,
                (Ptr{fmpz_mat}, Ptr{fmpz}), &x, &d)
   return x
end

function is_hnf(x::fmpz_mat, shape::Symbol)
  if shape == :upperright
    return is_hnf(x)
  elseif shape == :lowerleft
    r = rows(x)
    i = 0
    j_old = cols(x) + 1

    for i in rows(x):-1:1

      if is_zero_row(x, i)
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
      !is_zero_row(x, k) && return false
    end
    return true
  end
end

#function howell_form!(x::fmpz_mat, m::fmpz, shape::Symbol = :upperright)
#  if shape == :lowerleft
#    _swapcols!(x)
#    ccall((:_fmpz_mat_howell, :libflint), Int, (Ptr{fmpz_mat}, Ptr{fmpz}), &x, &m)
#    _swapcols!(x)
#    _swaprows!(x)
#  else
#    ccall((:_fmpz_mat_howell, :libflint), Int, (Ptr{fmpz_mat}, Ptr{fmpz}), &x, &m)
#  end
#end
#
#function howell_form(x::fmpz_mat, m::fmpz, shape::Symbol = :upperright)
#  y = deepcopy(x)
#  howell_form!(y, m, shape)
#  return y
#end
#
#function howell_form!(x::nmod_mat, shape::Symbol = :upperright)
#  if shape == :lowerleft
#    _swapcols!(x)
#    ccall((:_nmod_mat_howell, :libflint), Int, (Ptr{nmod_mat}, ), &x)
#    _swapcols!(x)
#    _swaprows!(x)
#  else
#    ccall((:_nmod_mat_howell, :libflint), Int, (Ptr{nmod_mat}, ), &x)
#  end
#end
#
#function howell_form(x::nmod_mat, shape::Symbol = :upperright)
#  y = deepcopy(x)
#  howell_form!(y, shape)
#  return y
#end

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
        s = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &x, i - 1, j - 1)
        t = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &x, (r - i + 1) - 1, j - 1)
        ccall((:fmpz_swap, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), t, s)
      end
    end
  else
    for i in 1:div(r-1,2)
      for j = 1:c
        # we swap x[i,j] <-> x[r-i+1,j]
        s = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &x, i - 1, j - 1)
        t = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &x, (r - i + 1) - 1, j - 1)
        ccall((:fmpz_swap, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), t, s)
      end
    end
  end
  nothing
end

function _swaprows!(x::fmpz_mat, i::Int, j::Int)
  ccall((:_fmpz_mat_swap_rows, :libflint), Void, (Ptr{fmpz_mat}, Int, Int), &x, i-1, j-1)
  nothing
end

function _swaprows!(x::nmod_mat, i::Int, j::Int)
  ccall((:_nmod_mat_swap_rows, :libflint), Void, (Ptr{nmod_mat}, Int, Int), &x, i-1, j-1)
#  for k in 1:rows(x)
#    s = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Lim, (Ptr{nmod_mat}, Int, Int), &x, i, k)
#    t = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Lim, (Ptr{nmod_mat}, Int, Int), &x, j, k)
#    set_entry!(x, i, k, t)
#    set_entry!(y, j, k, s)
#  end
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
        s = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &x, i - 1, j - 1)
        t = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &x, (r - i + 1) - 1, j - 1)
        set_entry!(x, r - i + 1, j, s)
        set_entry!(x, i, j, t)
      end
    end
  else
    for i in 1:div(r-1,2)
      for j = 1:c
        # we swap x[i,j] <-> x[r-i+1,j]
        s = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &x, i - 1, j - 1)
        t = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &x, (r - i + 1) - 1, j - 1)
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
        s = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &x, j - 1, i - 1)
        t = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &x, j - 1, (c - i + 1 ) - 1)
        set_entry!(x, j, i, t)
        set_entry!(x, j, c - i + 1, s)
      end
    end
  else
    for i in 1:div(c-1,2)
      for j = 1:r
        # swap x[j,i] <-> x[j,c-i+1]
        s = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &x, j - 1, i - 1)
        t = ccall((:nmod_mat_get_entry, :libflint), Base.GMP.Limb, (Ptr{nmod_mat}, Int, Int), &x, j - 1, (c - i + 1 ) - 1)
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
        s = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &x, j - 1, i - 1)
        t = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &x, j - 1, (c - i + 1 ) - 1)
        ccall((:fmpz_swap, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), t, s)
      end
    end
  else
    for i in 1:div(c-1,2)
      for j = 1:r
        # swap x[j,i] <-> x[j,c-i+1]
        s = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &x, j - 1, i - 1)
        t = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &x, j - 1, (c - i + 1 ) - 1)
        ccall((:fmpz_swap, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), t, s)
      end
    end
  end
  nothing
end

function _swapcols(x::GenMat)
  z = deepcopy(x)
  _swapcols!(z)
  return z
end

function _swapcols!(x::GenMat)
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

function _swaprows(x::GenMat)
  z = deepcopy(x)
  _swaprows(z)
  return z
end

function _swaprows!(x::GenMat)
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

function abs_max(a::fmpz_mat)
  m = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &a, 0,0)
  for i=1:rows(a)
    for j=1:cols(a)
      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &a, i-1, j-1)
      if ccall((:fmpz_cmpabs, :libflint), Cint, (Ptr{fmpz}, Ptr{fmpz}), m, z) < 0
        m = z
      end
    end
  end
  r = fmpz()
  ccall((:fmpz_abs, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), &r, m)
  return r
end

function max(a::fmpz_mat)  #should be maximum in julia
  m = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &a, 0,0)
  for i=1:rows(a)
    for j=1:cols(a)
      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &a, i-1, j-1)
      if ccall((:fmpz_cmp, :libflint), Cint, (Ptr{fmpz}, Ptr{fmpz}), m, z) < 0
        m = z
      end
    end
  end
  r = fmpz()
  ccall((:fmpz_set, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), &r, m)
  return r
end

function min(a::fmpz_mat)  #should be minimum in julia
  m = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &a, 0,0)
  for i=1:rows(a)
    for j=1:cols(a)
      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &a, i-1, j-1)
      if ccall((:fmpz_cmp, :libflint), Cint, (Ptr{fmpz}, Ptr{fmpz}), m, z) > 0
        m = z
      end
    end
  end
  r = fmpz()
  ccall((:fmpz_set, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), &r, m)
  return r
end

function lift_unsigned(a::nmod_mat)
  z = MatrixSpace(FlintZZ, rows(a), cols(a))()
  ccall((:fmpz_mat_set_nmod_mat_unsigned, :libflint), Void,
          (Ptr{fmpz_mat}, Ptr{nmod_mat}), &z, &a)
  return z
end

################################################################################
# possibly a slice or window in fmpz_mat?
# the nr x nc matrix starting in (a,b)
################################################################################

function submat(A::fmpz_mat, a::Int, b::Int, nr::Int, nc::Int)
  @assert nr >= 0 && nc >= 0
  @assert a+nr-1 <= rows(A) && b+nc-1 <= cols(A)
  M = MatrixSpace(FlintZZ, nr, nc)()::fmpz_mat
  t = ZZ()
  for i = 1:nr
    for j = 1:nc
      getindex!(t, A, a+i-1, b+j-1)
      M[i,j] = t
    end
  end
  return M
end

function submat{T <: Integer}(A::fmpz_mat, r::UnitRange{T}, c::UnitRange)
  @assert !isdefined(r, :step) || r.step==1
  @assert !isdefined(c, :step) || c.step==1
  return submat(A, r.start, c.start, r.stop-r.start+1, c.stop-c.start+1)::fmpz_mat
end


function sub(A::fmpz_mat, r::UnitRange, c::UnitRange)
  @assert !isdefined(r, :step) || r.step==1
  @assert !isdefined(c, :step) || c.step==1
  return submat(A, r.start, c.start, r.stop-r.start+1, c.stop-c.start+1)::fmpz_mat
end

################################################################################
#
#  misc.jl : At some point this should migrate to Nemo
#
################################################################################

# compute basis for the right kernel space by calling flint
# look at flint documentation of nmod_mat_nullspace

function _right_kernel(x::nmod_mat)
  z = MatrixSpace(base_ring(x), cols(x), max(rows(x),cols(x)))()
  n = ccall((:nmod_mat_nullspace, :libflint), Clong, (Ptr{nmod_mat}, Ptr{nmod_mat}), &z, &x)
  return z,n
end

# compute basis for the left kernel space
# output is array of arrays, which span the kernel

function kernel(a::nmod_mat)
  x = transpose(a)
  z,n = _right_kernel(x)
  z = transpose(z)
  #println(z)
  ar = typeof(Array(GenRes{fmpz}, cols(z)))[]
  for i in 1:n 
    t = Array(GenRes{fmpz}, cols(z))
    for j in 1:cols(z)
      t[j] = z[i,j]
    end
    push!(ar,t)
  end
  #println(ar)
  return ar
end

function kernel_mod(a::fmpz_mat, m::fmpz)
  b = deepcopy(a)
  for i in 1:rows(b)
    for j in 1:cols(b)
      b[i,j] = b[i,j] % m
    end
  end

  # fmpz_mat_rref_mod assumes that input is reduced modulo m
  r = ccall((:fmpz_mat_rref_mod, :libflint), Int, (Ptr{Void}, Ptr{fmpz_mat}, Ptr{fmpz}), C_NULL, &b, &m)
  pivots = Array(Int, r)
  nonpivots = Array(Int, cols(b) - r)
  X = zero(MatrixSpace(ZZ,cols(b),cols(b)))

  if r == 0
    return one(MatrixSpace(ZZ, cols(b), cols(b)))
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
        X[pivots[j],i] = - ZZ(b[j,nonpivots[i]])
      end
      X[nonpivots[i],i] = ZZ(1)
    end
  end
  return X, r
end

# Another kernel function
function _kernel(x::fmpz_mat)
  H, U = hnf_with_transform(x)
  i = 1
  for i in 1:rows(H)
    if is_zero_row(H, i)
      break
    end
  end
  return submat(U, i:rows(U), 1:cols(U))
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
                Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &B, k, l)
      t = ccall((:fmpz_mat_entry, :libflint),
                Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &A, i - 1 + k, j - 1 + l)
      ccall((:fmpz_set, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), t, d)
    end
  end
end

function swap_rows!(M::MatElem, i::Int, j::Int)
  for k in 1:cols(M)
    t = M[i, k]
    M[i, k] = M[j, k]
    M[j, k] = t
  end
end
