################################################################################
#
# Implementation of "FLATTER" algorithm
#
# Based on the flatter GitHub repository, which is based on:
#   "Fast Practical Lattice Reduction through Iterated Compression"
#   Keegan Ryan, Nadia Heninger
#   University of California, San Diego
#   https://eprint.iacr.org/2023/237
#
################################################################################

# Exponent (floor(log2(|x|))) approximation for ArbFieldElem
function _flatter_exponent(x::ArbFieldElem)
  iszero(x) && return typemin(Int) >> 2
  # arb_mid_ptr returns pointer to the midpoint (arf_t)
  # arf_abs_bound_lt_2exp_si gives e such that |x| < 2^e
  m = ccall((:arb_mid_ptr, libflint), Ptr{Nothing}, (Ref{ArbFieldElem},), x)
  e = ccall((:arf_abs_bound_lt_2exp_si, libflint), Int, (Ptr{Nothing},), m)
  return e - 1
end

function _flatter_exponent(x::ZZRingElem)
  iszero(x) && return typemin(Int) >> 2
  return nbits(x) - 1
end

# Compare |x| and |y|: returns positive if |x| > |y|, negative if |x| < |y|, 0 if equal
function _flatter_abs_cmp(x::ArbFieldElem, y::ArbFieldElem)
  # Use exponents as a proxy; for flatter we only need >= checks
  ex = _flatter_exponent(x)
  ey = _flatter_exponent(y)
  return ex - ey
end

# Compute the "drop" (slope measure)
function _flatter_drop(R, n::Int)
  n == 0 && return 0
  s = 0
  m = _flatter_exponent(R[1, 1])
  for i in 2:n
    if _flatter_abs_cmp(R[i, i], R[i - 1, i - 1]) >= 0
      s += m - _flatter_exponent(R[i - 1, i - 1])
      m = _flatter_exponent(R[i, i])
    end
  end
  s += m - _flatter_exponent(R[n, n])
  return s
end

# Compute the potential
function _flatter_potential(R, n::Int)
  s = 0
  mul = n - 1
  for i in 1:n
    s += mul * _flatter_exponent(R[i, i])
    mul -= 2
  end
  return s
end

# Spread of diagonal
function _flatter_spread(R, n::Int)
  n == 0 && return 0
  m = _flatter_exponent(R[1, 1])
  M = m
  for i in 2:n
    e = _flatter_exponent(R[i, i])
    m = min(m, e)
    M = max(M, e)
  end
  return M - m
end

# Condition number bound for upper-triangular matrix (Higham Algo 8.13)
function _flatter_condition_bound(U, n::Int)
  n == 0 && return 0
  y = Vector{Int}(undef, n)
  y[n] = -_flatter_exponent(U[n, n])
  e = y[n]
  for i in (n - 1):-1:1
    s = 0
    for j in (i + 1):n
      s = max(s, _flatter_exponent(U[i, j]) + y[j])
    end
    y[i] = s - _flatter_exponent(U[i, i])
    e = max(e, y[i])
  end
  mx = typemin(Int) >> 2
  for i in 1:n, j in i:n
    mx = max(mx, _flatter_exponent(U[i, j]))
  end
  return mx + e
end

function _flatter_gs_extraprec(L, n::Int)
  C = _flatter_condition_bound(L, n)
  S = _flatter_spread(L, n)
  r = max(2 * S + 2 * n, C - S - 2 * n)
  # Clamp to avoid overflow in precision computation
  return clamp(r, 0, 2^28)
end

# Classical modified Gram-Schmidt QR: M = Q * R, return R (upper-triangular)
# M is n x d ArbMatrix (n <= d). Returns n x n upper-triangular R, or nothing on failure.
function _arb_qr_r(M::ArbMatrix, prec::Int)
  n = nrows(M)
  d = ncols(M)
  RR = base_ring(M)
  R = zero_matrix(RR, n, n)
  Q = zero_matrix(RR, n, d)
  for i in 1:n
    for j in 1:d
      Q[i, j] = M[i, j]
    end
    for k in 1:(i - 1)
      dot_num = RR()
      dot_den = RR()
      for j in 1:d
        dot_num = dot_num + Q[i, j] * Q[k, j]
        dot_den = dot_den + Q[k, j] * Q[k, j]
      end
      iszero(dot_den) && return nothing
      R[k, i] = dot_num
      mu = dot_num * inv(dot_den)
      for j in 1:d
        Q[i, j] = Q[i, j] - mu * Q[k, j]
      end
    end
    dot = RR()
    for j in 1:d
      dot = dot + Q[i, j] * Q[i, j]
    end
    iszero(dot) && return nothing
    R[i, i] = sqrt(dot)
    rinv = inv(R[i, i])
    for j in 1:d
      Q[i, j] = Q[i, j] * rinv
    end
  end
  return R
end

# Gram-Schmidt with dynamic precision.
# Input: M with columns as basis vectors
# Output: upper-triangular R from column-based QR (M = Q*R)
function _flatter_gramschmidt(M::ZZMatrix)
  n = ncols(M)
  n == 0 && return zero_matrix(ArbField(64), 0, 0)
  minprec = n + 30
  bitprec = minprec
  # We do row-QR on M^T to get column-QR of M
  Mt = transpose(M)
  while true
    prec = max(64, min(bitprec, 2^28))
    prec = ((prec + 63) >> 6) << 6
    RR = ArbField(prec)
    Ma = change_base_ring(RR, Mt)
    R = _arb_qr_r(Ma, prec)
    if R !== nothing
      ok = true
      for i in 1:n
        if iszero(R[i, i]) || _flatter_exponent(R[i, i]) > typemax(Int) >> 2
          ok = false
          break
        end
      end
      if ok
        mbitprec = minprec + _flatter_gs_extraprec(R, n)
        if bitprec >= mbitprec
          return R
        end
        bitprec = max(div(4 * bitprec, 3), mbitprec)
        continue
      end
    end
    bitprec *= 2
  end
end

# Round ArbMatrix to ZZMatrix (entry-wise)
function _flatter_round_matrix(M::ArbMatrix)
  n = nrows(M)
  m = ncols(M)
  prec = precision(base_ring(M))
  R = zero_matrix(ZZ, n, m)
  for i in 1:n, j in 1:m
    v = setprecision(BigFloat, prec) do
      BigFloat(M[i, j])
    end
    if isnan(v) || isinf(v)
      continue
    end
    R[i, j] = round(ZZRingElem, v)
  end
  return R
end

# Solve R1 * X = R2 for upper-triangular R1 via back substitution
function _flatter_solve_upper(R1::ArbMatrix, R2::ArbMatrix)
  n = nrows(R1)
  m = ncols(R2)
  RR = base_ring(R1)
  X = zero_matrix(RR, n, m)
  for j in 1:m
    for i in n:-1:1
      s = R2[i, j]
      for k in (i + 1):n
        s = s - R1[i, k] * X[k, j]
      end
      X[i, j] = s * inv(R1[i, i])
    end
  end
  return X
end

# Size reduction: -T1 * round(T1^{-1} * (R1^{-1} * R2) * T3)
function _flatter_sizered(T1::ZZMatrix, T3::ZZMatrix, R1::ArbMatrix, R2::ArbMatrix)
  RR = base_ring(R1)
  X = _flatter_solve_upper(R1, R2)
  T1inv = _flatter_inv_unimodular(T1)
  T1inv_a = change_base_ring(RR, T1inv)
  T3_a = change_base_ring(RR, T3)
  M = T1inv_a * X * T3_a
  return -T1 * _flatter_round_matrix(M)
end

function _flatter_inv_unimodular(M::ZZMatrix)
  n = nrows(M)
  fl, Minv = can_solve_with_solution(M, identity_matrix(ZZ, n); side = :left)
  @assert fl
  return Minv
end

# Convert upper-triangular ArbMatrix to ZZMatrix via scaling and rounding.
# We scale so that the smallest diagonal entry becomes O(2^n) in magnitude,
# preserving the relative structure for LLL.
function _flatter_arb_to_ZZ(R::ArbMatrix)
  n = nrows(R)
  n == 0 && return zero_matrix(ZZ, 0, 0)
  # Find minimum exponent of diagonal entries (defines the scale)
  min_exp = typemax(Int) >> 2
  for i in 1:n
    if !iszero(R[i, i])
      e = _flatter_exponent(R[i, i])
      min_exp = min(min_exp, e)
    end
  end
  p = -(min_exp - n)
  M = zero_matrix(ZZ, n, n)
  prec = precision(base_ring(R))
  for i in 1:n, j in i:n
    if iszero(R[i, j])
      continue
    end
    # Convert to BigFloat, scale by 2^p via ldexp, then round
    v = setprecision(BigFloat, prec) do
      ldexp(BigFloat(R[i, j]), p)
    end
    if isnan(v) || isinf(v)
      continue
    end
    M[i, j] = round(ZZRingElem, v)
  end
  return M
end

# One step of the flatter algorithm.
# M has columns as basis vectors. Returns (M', T, drop, potential) where M' = M * T.
function _flatter_step(M::ZZMatrix)
  k = ncols(M)
  n = k >> 1
  n2 = k - n
  m = n >> 1

  R = _flatter_gramschmidt(M)

  R1 = sub(R, 1:n, 1:n)
  R2 = sub(R, 1:n, (n + 1):k)
  R3 = sub(R, (n + 1):k, (n + 1):k)

  # LLL on column vectors of R1 and R3:
  # lll_with_transform(A^T) gives (L, T) with T * A^T = L, hence A * T^T = L^T
  T1 = _flatter_lll_cols(_flatter_arb_to_ZZ(R1))
  T3 = _flatter_lll_cols(_flatter_arb_to_ZZ(R3))

  T2 = _flatter_sizered(T1, T3, R1, R2)

  T = vcat(hcat(T1, T2), hcat(zero_matrix(ZZ, n2, n), T3))
  M = M * T

  # Second phase: LLL on the middle block
  R = _flatter_gramschmidt(M)
  R3mid = sub(R, (m + 1):(m + n2), (m + 1):(m + n2))
  T3mid = _flatter_lll_cols(_flatter_arb_to_ZZ(R3mid))

  S = identity_matrix(ZZ, k)
  for i in 1:n2, j in 1:n2
    S[m + i, m + j] = T3mid[i, j]
  end

  M = M * S
  T = T * S

  d = _flatter_drop(R, k)
  p = _flatter_potential(R, k)

  return M, T, d, p
end

# Threshold tables for flatter dispatch, indexed by n-3 (Julia 1-based: index = n-2).
# For regular matrices:
const _FLATTER_THRE = Int[
  31783,34393,20894,22525,13533,1928,672,671,
  422,506,315,313,222,205,167,154,139,138,
  110,120,98,94,81,75,74,64,74,74,
  79,96,112,111,105,104,96,86,84,78,75,70,66,62,62,57,56,47,45,52,50,44,48,42,36,35,35,34,40,33,34,32,36,31,
  38,38,40,38,38,37,35,31,34,36,34,32,34,32,28,27,25,31,25,27,28,26,25,21,21,25,25,22,21,24,24,22,21,23,22,22,22,22,21,24,21,22,19,20,19,20,19,19,19,18,19,18,18,20,19,20,18,19,18,21,18,20,18,18]
# For knapsack-shaped matrices:
const _FLATTER_THSN = Int[
  23280,30486,50077,44136,78724,15690,1801,1611,
  981,1359,978,1042,815,866,788,775,726,712,
  626,613,548,564,474,481,504,447,453,508,
  705,794,1008,946,767,898,886,763,842,757,
  725,774,639,655,705,627,635,704,511,613,
  583,595,568,640,541,640,567,540,577,584,
  546,509,526,572,637,746,772,743,743,742,800,708,832,768,707,692,692,768,696,635,709,694,768,719,655,569,590,644,685,623,627,720,633,636,602,635,575,631,642,647,632,656,573,511,688,640,528,616,511,559,601,620,635,688,608,768,658,582,644,704,555,673,600,601,641,661,601,670]

# Check if a square upper-triangular ZZMatrix has knapsack structure:
# rows 2..n are zero except on the diagonal.
function _flatter_is_knapsack(A::ZZMatrix)
  n = nrows(A)
  n != ncols(A) && return false
  for i in 2:n, j in 1:n
    i != j && !iszero(A[i, j]) && return false
  end
  return true
end

# Determine whether an upper-triangular integer matrix warrants recursive flatter,
# using threshold tables (spread/size vs dimension-dependent threshold).
function _flatter_use_flatter(A::ZZMatrix)
  n = nrows(A)
  n <= 2 && return false
  idx = min(n - 2, length(_FLATTER_THRE))
  # Compute spread and sup-norm exponent of the diagonal / entries
  lo = typemax(Int)
  hi = typemin(Int)
  mx = typemin(Int)
  for i in 1:n
    if !iszero(A[i, i])
      e = nbits(A[i, i]) - 1
      lo = min(lo, e)
      hi = max(hi, e)
    else
      lo = typemin(Int) >> 2
    end
    for j in i:n
      if !iszero(A[i, j])
        mx = max(mx, nbits(A[i, j]) - 1)
      end
    end
  end
  spr = lo == typemax(Int) ? 0 : hi - lo
  sz = mx == typemin(Int) ? 0 : mx
  if _flatter_is_knapsack(A)
    thr = _FLATTER_THSN[idx]
  else
    thr = _FLATTER_THRE[idx]
    if n >= 10
      sz = spr
    end
  end
  return sz >= thr
end

# LLL on columns with threshold-based dispatch.
# Given upper-triangular A, return T such that A * T has reduced columns.
# If the spread/size exceeds dimension-dependent thresholds, use recursive flatter.
function _flatter_lll_cols(A::ZZMatrix)
  n = nrows(A)
  if n >= 3 && _flatter_use_flatter(A)
    At = transpose(A)
    _, T = flatter_with_transform(At)
    return transpose(T)
  end
  ctx = LLLContext(0.99, 0.51)
  _, T = lll_with_transform(transpose(A), ctx)
  return transpose(T)
end

@doc raw"""
    flatter(M::ZZMatrix) -> ZZMatrix

Reduce the rows of the integer matrix `M` using the FLATTER algorithm, an
iterated compression approach to lattice reduction.

Returns the reduced matrix whose rows span the same lattice as those of `M`.

# Reference

"Fast Practical Lattice Reduction through Iterated Compression",
Keegan Ryan, Nadia Heninger, https://eprint.iacr.org/2023/237

The implementation follows the flatter GitHub repository.
"""
function flatter(M::ZZMatrix)
  R, _ = flatter_with_transform(M)
  return R
end

@doc raw"""
    flatter_with_transform(M::ZZMatrix) -> (ZZMatrix, ZZMatrix)

Reduce the rows of the integer matrix `M` using the FLATTER algorithm.

Returns `(L, T)` such that `L = T * M` is reduced and `T` is unimodular.
"""
function flatter_with_transform(M::ZZMatrix)
  n = nrows(M)
  if n <= 2
    return _flatter_small(M)
  end

  # Internally work in column convention (transpose)
  Mc = transpose(M)
  T = nothing
  s = -1
  pot = typemax(Int)

  for i in 1:10000
    Mc2, U, t, pot2 = _flatter_step(Mc)
    if t == 0
      break
    end
    if s >= 0
      if s == t && pot >= pot2
        break
      end
      if s < t && i > 20
        break
      end
    end
    s = t
    pot = pot2
    Mc = Mc2
    T = T === nothing ? U : T * U
  end

  if T === nothing
    return M, identity_matrix(ZZ, n)
  end
  # In column convention: M^T * T = reduced^T
  # In row convention: T^T * M = reduced
  Tr = transpose(T)
  return Tr * M, Tr
end

function _flatter_small(M::ZZMatrix)
  n = nrows(M)
  if n <= 1
    return M, identity_matrix(ZZ, n)
  end
  ctx = LLLContext(0.99, 0.51)
  L, T = lll_with_transform(M, ctx)
  return L, T
end

@doc raw"""
    flatter_gram(G::ZZMatrix) -> ZZMatrix

Reduce a lattice given by its Gram matrix `G` using the FLATTER algorithm via
Cholesky decomposition.

Returns the reduced Gram matrix `T * G * T'` for a unimodular `T`.
"""
function flatter_gram(G::ZZMatrix)
  T = flatter_gram_with_transform(G)
  return T === nothing ? G : T * G * transpose(T)
end

@doc raw"""
    flatter_gram_with_transform(G::ZZMatrix) -> Union{ZZMatrix, Nothing}

Reduce a lattice given by its Gram matrix `G` using the FLATTER algorithm.

Returns the unimodular transformation `T` such that `T * G * T'` is reduced,
or `nothing` if `G` is already reduced.
"""
function flatter_gram_with_transform(G::ZZMatrix)
  n = nrows(G)
  n <= 2 && return _flatter_gram_small(G)

  T = nothing
  s = -1

  for i in 1:10000
    S = _flattergram_step(G)
    t = _flatter_mat_norm_exp(S)
    if t == 0
      break
    end
    if s >= 0
      st = s - t
      if st == 0
        break
      end
      if st < 0 && i > 20
        break
      end
    end
    T = T === nothing ? S : S * T
    G = S * G * transpose(S)
    s = t
  end

  if T !== nothing && T == identity_matrix(ZZ, n)
    return nothing
  end
  return T
end

function _flattergram_step(G::ZZMatrix)
  R = _flatter_cholesky_dynprec(G)
  A = _flatter_arb_to_ZZ(R)
  n = nrows(A)
  if n >= 3 && _flatter_use_flatter(A)
    _, T = flatter_with_transform(A)
    return T
  end
  ctx = LLLContext(0.99, 0.51)
  _, T = lll_with_transform(A, ctx)
  return T
end

# Cholesky with dynamic precision for Gram matrix
function _flatter_cholesky_dynprec(G::ZZMatrix)
  n = nrows(G)
  n == 0 && return zero_matrix(ArbField(64), 0, 0)
  minprec = n + 30
  bitprec = minprec
  while true
    prec = max(64, min(bitprec, 2^28))
    prec = ((prec + 63) >> 6) << 6
    RR = ArbField(prec)
    Ga = change_base_ring(RR, G)
    L = similar(Ga, n, n)
    fl = ccall((:arb_mat_cho, libflint), Cint,
               (Ref{ArbMatrix}, Ref{ArbMatrix}, Int), L, Ga, prec)
    if fl != 0
      R = transpose(L)  # arb_mat_cho gives lower-triangular; we need upper
      ok = true
      for i in 1:n
        if iszero(R[i, i]) || _flatter_exponent(R[i, i]) > typemax(Int) >> 2
          ok = false
          break
        end
      end
      if ok
        mbitprec = minprec + _flatter_gs_extraprec(R, n)
        if bitprec >= mbitprec
          return R
        end
        bitprec = max(div(4 * bitprec, 3), mbitprec)
        continue
      end
    end
    bitprec *= 2
  end
end

function _flatter_gram_small(G::ZZMatrix)
  n = nrows(G)
  n <= 1 && return nothing
  ctx = LLLContext(0.99, 0.51, :gram)
  _, T = lll_gram_with_transform(G, ctx)
  T == identity_matrix(ZZ, n) && return nothing
  return T
end

# Max bit-size of entries of a ZZMatrix
function _flatter_mat_norm_exp(S::ZZMatrix)
  mx = 0
  for i in 1:nrows(S), j in 1:ncols(S)
    b = nbits(S[i, j])
    mx = max(mx, b)
  end
  return mx
end
