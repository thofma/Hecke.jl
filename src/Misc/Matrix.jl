import Nemo.matrix

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

Equivalently, return $TA$ (minus zero rows) for an invertible rational matrix
$T$ such that $TA$ is integral and the elementary divisors of $TA$ are all
trivial.

# Examples

```jldoctest
julia> saturate(ZZ[1 2 3;4 5 6;7 0 7])
[1    2    3]
[1    1    1]
[0   -1   -1]

julia> saturate(ZZ[1 2 3;4 5 6;7 8 9])
[1   2   3]
[1   1   1]

julia> saturate(ZZ[1 2 3;4 5 6])
[1   2   3]
[1   1   1]

julia> saturate(ZZ[1 2;3 4;5 6])
[1   2]
[1   1]

```
"""
function saturate(A::ZZMatrix) :: ZZMatrix
  # Let AU = [H 0matrix] in HNF and HS = A = [H 0matrix]U⁻¹
  # We have S == U⁻¹[1:rank(H), :] in ZZ with trivial elementary divisors.
  # For any invertible H' with H'H = 1, also S = H'HS = H'A.
  H = hnf!(transpose(A))
  H = transpose(H[1:rank(H), :])
  S = solve(H, A; side = :right)
  @assert rank(S) == rank(H)
  return S
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

function is_lll_reduced(x::ZZMatrix, ctx::LLLContext = LLLContext(0.99, 0.51))
  b = ccall((:fmpz_lll_is_reduced_d, libflint), Cint,
            (Ref{ZZMatrix}, Ref{LLLContext}), x, ctx)
  return Bool(b)
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

function lift_unsigned(a::zzModMatrix)
  z = zero_matrix(FlintZZ, nrows(a), ncols(a))
  ccall((:fmpz_mat_set_nmod_mat_unsigned, libflint), Nothing,
          (Ref{ZZMatrix}, Ref{zzModMatrix}), z, a)
  return z
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

#scales the i-th column of a by 2^d[1,i]
function mult_by_2pow_diag!(a::Matrix{BigFloat}, d::ZZMatrix, R=_RealRings[Threads.threadid()])
  s = size(a)
  tmp_mpz::BigInt = R.z1
  for i = 1:s[1]
      for j = 1:s[2]
          e = ccall((:mpfr_get_z_2exp, :libmpfr), Clong, (Ref{BigInt}, Ref{BigFloat}), tmp_mpz, a[i, j])
          ccall((:mpfr_set_z_2exp, :libmpfr), Nothing, (Ref{BigFloat}, Ref{BigInt}, Clong, Int32), a[i, j], tmp_mpz, e + Clong(Int(d[1, j])), __get_rounding_mode())
      end
  end
end

#converts BigFloat -> ZZRingElem via round(a*2^l), in a clever(?) way
function round_scale(a::Matrix{BigFloat}, l::Int)
  s = size(a)
  b = zero_matrix(FlintZZ, s[1], s[2])
  return round_scale!(b, a, l)
end

function round_scale!(b::ZZMatrix, a::Matrix{BigFloat}, l::Int, R=_RealRings[Threads.threadid()])
  s = size(a)

  local tmp_mpz::BigInt, tmp_fmpz::ZZRingElem
  tmp_mpz = R.z1
  tmp_fmpz = R.zz1
  tmp_mpfr = deepcopy(a[1, 1])  #cannot use the R.?? tmp variable as it may/will
  #have the wrong precision

  rd = __get_rounding_mode()
  for i = 1:s[1]
      for j = 1:s[2]
          e = a[i, j].exp
          a[i, j].exp += l
          ccall((:mpfr_round, :libmpfr), Int32, (Ref{BigFloat}, Ref{BigFloat}, Int32), tmp_mpfr, a[i, j], rd)
          a[i, j].exp = e
          f = ccall((:mpfr_get_z_2exp, :libmpfr), Clong, (Ref{BigInt}, Ref{BigFloat}),
              tmp_mpz, tmp_mpfr)
          ccall((:fmpz_set_mpz, libflint), Nothing, (Ref{ZZRingElem}, Ref{BigInt}), tmp_fmpz, tmp_mpz)
          if f > 0
              ccall((:fmpz_mul_2exp, libflint), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}, UInt), tmp_fmpz, tmp_fmpz, f)
          else
              ccall((:fmpz_tdiv_q_2exp, libflint), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}, UInt), tmp_fmpz, tmp_fmpz, -f)
          end
          setindex!(b, tmp_fmpz, i, j)
      end
  end
  return b
end

function round_scale!(b::ZZMatrix, a::ArbMatrix, l::Int)
  s = size(a)

  R = base_ring(a)
  r = R()
  for i = 1:s[1]
      for j = 1:s[2]
          v = ccall((:arb_mat_entry_ptr, libarb), Ptr{ArbFieldElem},
              (Ref{ArbMatrix}, Int, Int), a, i - 1, j - 1)
          ccall((:arb_mul_2exp_si, libarb), Nothing, (Ref{ArbFieldElem}, Ptr{ArbFieldElem}, Int), r, v, l)
          b[i, j] = round(ZZRingElem, r)
      end
  end
  return b
end

################################################################################
#
#  Smith normal form with trafo
#
################################################################################

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
        if is_upper_triangular(S)
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

# Solves A x = b for A upper triangular m\times n matrix and b m\times 1.
@doc raw"""
    _solve_ut(A::MatElem{T}, b::MatElem{T}) -> MatElem{T})

Given an upper triangular $m \times m$ matrix $A$ and a matrix $b$ of size $m
\times k$, this function computes $x$ such that $Ax = b$. Might fail if
the pivots of $A$ are not invertible.
"""
function _solve_ut(A::MatElem{T}, b::MatElem{T}) where T
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
    _solve_lt(A::MatElem{T}, b::MatElem{T}) -> MatElem{T})

Given a lower triangular $m \times m$ matrix $A$ and a matrix $b$ of size
$m \times k$, this function computes $x$ such that $Ax = b$. Might fail if the
pivots of $A$ are not invertible.
"""
function _solve_lt(A::MatElem{T}, b::MatElem{T}) where T
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

function _solve_lt(A::MatElem{T}, b::Vector{T}) where T
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

"""
    pivots_of_ref(H::MatrixElem) -> Tuple{Int, BitVector}

Return `rank(H), p` such that `p[j]` states whether the `j`th column is a pivot column.
The input `H` must be in row echelon form.

See also: `rank_of_ref`, `pivot_cols_of_ref`, `non_pivot_cols_of_ref`.

# Examples
```jldoctest
julia> Hecke.pivots_of_ref(QQ[1 1; 0 1])
(2, Bool[1, 1])

julia> Hecke.pivots_of_ref(QQ[1 1; 0 0])
(1, Bool[1, 0])

julia> Hecke.pivots_of_ref(QQ[0 2 2 2 2; 0 0 3 3 3; 0 0 0 4 4])
(3, Bool[0, 1, 1, 1, 0])

```
"""
function pivots_of_ref(H::MatrixElem) :: Tuple{Int, BitVector}
  p = falses(ncols(H))
  i = 1
  for j in axes(H, 2)
    i == nrows(H)+1 && break
    is_zero_entry(H, i, j) || (p[j] = true; i+=1)
  end
  return i-1, p
end

"""
    rank_of_ref(H::MatrixElem) -> Int

Rank of a row echelon matrix.

See also: `pivots_of_ref`, `pivot_cols_of_ref`, `non_pivot_cols_of_ref`.

# Examples
```jldoctest
julia> Hecke.rank_of_ref(QQ[1 1; 0 1])
2

julia> Hecke.rank_of_ref(QQ[1 1; 0 0])
1

julia> Hecke.rank_of_ref(QQ[0 2 2 2 2; 0 0 3 3 3; 0 0 0 4 4])
3

```
"""
function rank_of_ref(H::MatrixElem)
  i = 1
  for j in axes(H, 2)
    i == nrows(H)+1 && break
    is_zero_entry(H, i, j) || (i+=1)
  end
  return i-1
end

"""
    pivot_cols_of_ref(H::MatrixElem) -> Vector{Int}

Vector of the indices of pivot columns of a row echelon matrix in increasing order.

See also: `pivots_of_ref`, `rank_of_ref`, `non_pivot_cols_of_ref`.

# Examples
```jldoctest
julia> Hecke.pivot_cols_of_ref(QQ[1 1; 0 1])
2-element Vector{Int64}:
 1
 2

julia> Hecke.pivot_cols_of_ref(QQ[1 1; 0 0])
1-element Vector{Int64}:
 1

julia> Hecke.pivot_cols_of_ref(QQ[0 2 2 2 2; 0 0 3 3 3; 0 0 0 4 4])
3-element Vector{Int64}:
 2
 3
 4

```
"""
pivot_cols_of_ref(H::MatrixElem) = findall(pivots_of_ref(H)[2])

"""
    non_pivot_cols_of_ref(H::MatrixElem) -> Vector{Int}

Vector of the indices of non-pivot columns of a row echelon matrix in increasing order.

See also: `pivots_of_ref`, `rank_of_ref`, `pivot_cols_of_ref`

# Examples
```jldoctest
julia> Hecke.non_pivot_cols_of_ref(QQ[1 1; 0 1])
Int64[]

julia> Hecke.non_pivot_cols_of_ref(QQ[1 1; 0 0])
1-element Vector{Int64}:
 2

julia> Hecke.non_pivot_cols_of_ref(QQ[0 2 2 2 2; 0 0 3 3 3; 0 0 0 4 4])
2-element Vector{Int64}:
 1
 5

```
"""
non_pivot_cols_of_ref(H::MatrixElem) = findall(!, pivots_of_ref(H)[2])

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
#  Kernel of matrix over Z/nZ
#
################################################################################

function __left_kernel_of_howell_form_aurel(A::zzModMatrix)
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

function __left_kernel_naive(A::zzModMatrix)
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

function _left_kernel_prime_power(A::zzModMatrix, p::Int, l::Int)
  R = base_ring(A)
  Alift = lift(A)
  F = GF(p)
  _M = kernel(change_base_ring(F, Alift), side = :left)
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
    K = kernel(change_base_ring(F, divexact(Mfi, p^i)), side = :left)
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
    RR = residue_ring(FlintZZ, Int(d), cached = false)[1]
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
    R = residue_ring(FlintZZ, d, cached = false)[1]
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
infinity
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
#  Determinant of triangular matrix
#
################################################################################

# Compute the determinant of a (lower-left or upper-right) triangular matrix by
# multiplying the diagonal entries. Nothing is checked.
function _det_triangular(M::MatElem)
  R = base_ring(M)
  d = one(R)
  for i in 1:nrows(M)
    mul!(d, d, M[i, i])
  end
  return d
end

function remove_row(M, r)
  N = zero_matrix(base_ring(M), nrows(M) - 1, ncols(M))
  n = nrows(M)
  m = ncols(M)
  l = 1
  for i in 1:n
    if i == r
      continue
    end
    for j in 1:m
      N[l, j] = M[i, j]
    end
    l += 1
  end
  return N
end
