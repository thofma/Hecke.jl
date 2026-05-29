
################################################################################
#
#  Integer-only Fincke-Pohst enumeration (finckepohstint)
#
#  Inspired by https://github.com/olitb/lattools from Chenevier and Taibi
#
################################################################################

struct FinckePohstInt end

# Permuted Gaussian reduction with denominators.
#
# Like a Cholesky decomposition, but at each step we pick the basis vector
# with smallest diagonal entry, and we track lcm of denominators at each
# level of the recursion.
#
# Returns (per, R, c) where:
#   per: permutation (1-indexed)
#   R: Vector of (diagonal_entry, off_diagonal_coefficients)
#   c: Vector of lcm denominators, length n+1, with c[n+1] = 1

function _cholesky_integral_denom(gram::Matrix{QQFieldElem})
  n = size(gram, 1)
  if n == 1
    return Int[1], Tuple{QQFieldElem, Vector{QQFieldElem}}[(gram[1, 1], QQFieldElem[])], QQFieldElem[QQ(denominator(gram[1, 1])), QQ(1)]
  end
  # Find index with smallest diagonal
  mi = 1
  m = gram[1, 1]
  for i in 2:n
    if gram[i, i] < m
      m = gram[i, i]
      mi = i
    end
  end
  # lcm of all denominators in the matrix
  d = one(ZZ)
  temp = ZZ()
  for i in 1:n
    for j in 1:i
      d = lcm!(d, d, denominator!(temp, gram[i, j]))
    end
  end
  # Extract submatrix and linear form
  # indices other than mi
  idx = deleteat!(collect(1:n), mi)
  subgram = Matrix{QQFieldElem}(undef, n - 1, n - 1)
  lin = Vector{QQFieldElem}(undef, n - 1)
  for (a, i) in enumerate(idx)
    lin[a] = set!(QQ(), gram[mi, i]) # we modify it later
    for (b, j) in enumerate(idx)
      subgram[a, b] = set!(QQ(), gram[i, j]) # we modify it later
    end
  end
  # Schur complement: subgram -= lin * lin^T / m
  tmpqq  = QQ()
  for a in 1:n-1
    for b in 1:n-1
      tmpqq = mul!(tmpqq, lin[a], lin[b])
      tmpqq = divexact!(tmpqq, m)
      sub!(subgram[a, b], tmpqq)
      #subgram[a, b] -= lin[a] * lin[b] // m
    end
  end
  # lin /= m
  for a in 1:n-1
    divexact!(lin[a], m)
    #lin[a] = lin[a] // m
  end
  # recursion
  subper, subres, subc = _cholesky_integral_denom(subgram)
  # assemble the permutaion
  per = Vector{Int}(undef, n)
  per[1] = mi
  for i in 1:length(subper)
    s = subper[i]
    per[i + 1] = s < mi ? s : s + 1
  end
  # Reorder lin according to subper
  lin_reordered = QQFieldElem[lin[subper[i]] for i in 1:length(subper)]
  R = append!(Tuple{QQFieldElem, Vector{QQFieldElem}}[(m, lin_reordered)], subres)
  c = append!(QQFieldElem[QQ(d)], subc)
  return per, R, c
end

# Context for integer-only enumeration
mutable struct FinckePohstIntCtx{T}
  M::T                  # upper bound
  n::Int                  # dimension
  e::Vector{Vector{T}}  # off-diagonal (integer)
  b::Vector{T}          # denominators
  doc::Vector{T}        # d[i]/c[i]
  docp1::Vector{T}      # d[i]/c[i+1]
  mu::Vector{T}         # scaled diagonal
  lambda::Vector{T}     # c[i] * R[i][1]
  tlob::Vector{T}       # 2 * lambda[i] / b[i]
  x::Vector{T}          # current vector
end

# Preprocess gram matrix for integer-only enumeration.
# gram must be a positive definite integral matrix, M the upper bound.
# If dolll is true, applies LLL first.
# Returns (ok, ctx, per_or_U) where ok is true if preprocessing succeeded.
# If overflow occurs during the _ub check, returns false and no ctx.
# per_or_U is either a permutation (Vector{Int}) or a ZZMatrix transform.
function _try_prepare_finckepohstint_small(gram::ZZMatrix, M::Int)
  n = nrows(gram)
  @assert n > 0
  @assert M > 0

  gramQQ = Matrix{QQFieldElem}(undef, n, n)
  for i in 1:n
    for j in 1:n
      gramQQ[i, j] = QQ(gram[i, j])
    end
  end

  per, R, c = _cholesky_integral_denom(gramQQ)

  # Convert c to integers (they are lcm of denominators, hence integers)
  c_int = Vector{Int}(undef, n + 1)
  c_int_large = Vector{ZZRingElem}(undef, n + 1) # we need to compute lcms later of the c_int elements and check for overflow
  for i in 1:n+1
    nc = numerator(c[i])
    if !fits(Int, nc)
      return false, nothing, nothing
    else
      c_int_large[i] = nc
      c_int[i] = Int(nc)
    end
  end

  # Compute derived integer arrays
  d = Vector{Int}(undef, n)
  b = Vector{Int}(undef, n)
  mu = Vector{Int}(undef, n)
  e_arr = Vector{Vector{Int}}(undef, n)
  lambda = Vector{Int}(undef, n)
  tlob = Vector{Int}(undef, n)
  doc = Vector{Int}(undef, n)
  docp1 = Vector{Int}(undef, n)

  for i in 1:n
    l = lcm(c_int_large[i], c_int_large[i + 1])
    if !fits(Int, l)
      return false, nothing, nothing
    else
      d[i] = Int(l)
    end
  end

  for i in 1:n
    # b[i] = lcm of denominators of R[i][2]
    if isempty(R[i][2])
      b[i] = 1
    else
      b[i] = Int(reduce(lcm, (denominator(q) for q in R[i][2])))
    end
  end

  for i in 1:n
    # mu[i] = d[i] * R[i][1] / b[i]^2
    mu_val = d[i] * (R[i][1] // b[i]) // b[i]
    @assert is_integer(mu_val)
    if !fits(Int, numerator(mu_val))
      return false, nothing, nothing
    end
    mu[i] = Int(numerator(mu_val))

    # e[i] = vector of b[i] * R[i][2][j] for j in 1:n-i
    e_arr[i] = Int[Int(numerator(b[i] * R[i][2][j])) for j in 1:length(R[i][2])]

    # lambda[i] = c[i] * R[i][1]
    lambda_val = c_int[i] * R[i][1]
    @assert is_integer(lambda_val)
    if !fits(Int, numerator(lambda_val))
      return false, nothing, nothing
    end
    lambda[i] = Int(numerator(lambda_val))

    # tlob[i] = 2 * lambda[i] / b[i]
    tlob_val, rem = divrem(2 * lambda[i], b[i])
    @assert is_zero(rem)
    tlob[i] = tlob_val

    # doc[i] = d[i] / c[i]
    doc[i] = divexact(d[i], c_int[i])

    # docp1[i] = d[i] / c[i+1]
    docp1[i] = divexact(d[i], c_int[i + 1])
  end

  # Overflow check: compute an upper bound on all intermediate values
  # in _finckepohstint_rec! and verify that they fit in Int.
  # This follows the approach of Chenevier-Taibi (prepare_finckepohstint in lattools).
  _ub = max(ZZ(M) * ZZ(maximum(d)), 2 * ZZ(maximum(lambda)))
  _ub = max(_ub, ZZ(maximum(b)))
  _ub = max(_ub, ZZ(maximum(tlob)))
  _ub = max(_ub, ZZ(maximum(mu)))

  _gram_inv = Matrix{QQFieldElem}(inv(matrix(QQ, gramQQ)))
  _ubx = ZZRingElem[isqrt(floor(ZZRingElem, M * _gram_inv[i, i])) for i in 1:n]
  _ub = max(_ub, 1 + maximum(_ubx))
  if n > 1
    _emax = ZZ(0)
    for i in 1:n - 1
      if !isempty(e_arr[i])
        _emax = max(_emax, ZZ(maximum(abs, e_arr[i])))
      end
    end
    _ub = max(_ub, _emax)
    for i in 1:n - 1
      _s = ZZ(0)
      for j in (i + 1):n
        _s += ZZ(abs(e_arr[i][j - i])) * _ubx[j]
      end
      _ub = max(_ub, _s)
    end
  end
  for i in 1:n
    _ub = max(_ub, ZZ(mu[i]) * ZZ(b[i] - 1)^2)
  end
  for i in 1:n
    _ub = max(_ub, isqrt(4 * ZZ(lambda[i]) * ZZ(c_int[i]) * ZZ(M)) + ZZ(lambda[i]))
  end
  if _ub > typemax(Int)
    return false, nothing, nothing
  end

  x = zeros(Int, n)
  ctx = FinckePohstIntCtx(M, n, e_arr, b, doc, docp1, mu, lambda, tlob, x)
  return true, ctx, per
end

function _prepare_finckepohstint_large(gram::ZZMatrix, M::ZZRingElem)
  n = nrows(gram)
  @assert n > 0
  @assert M > 0

  gramQQ = Matrix{QQFieldElem}(undef, n, n)
  for i in 1:n
    for j in 1:n
      gramQQ[i, j] = QQ(gram[i, j])
    end
  end

  per, R, c = _cholesky_integral_denom(gramQQ)

  # Convert c to integers (they are lcm of denominators, hence integers)
  c_int = ZZRingElem[numerator(c[i]) for i in 1:n+1]

  # Compute derived integer arrays
  d = Vector{ZZRingElem}(undef, n)
  b = Vector{ZZRingElem}(undef, n)
  mu = Vector{ZZRingElem}(undef, n)
  e_arr = Vector{Vector{ZZRingElem}}(undef, n)
  lambda = Vector{ZZRingElem}(undef, n)
  tlob = Vector{ZZRingElem}(undef, n)
  doc = Vector{ZZRingElem}(undef, n)
  docp1 = Vector{ZZRingElem}(undef, n)

  for i in 1:n
    d[i] = lcm(c_int[i], c_int[i + 1])
  end

  for i in 1:n
    # b[i] = lcm of denominators of R[i][2]
    if isempty(R[i][2])
      b[i] = one(ZZ)
    else
      b[i] = reduce(lcm, (denominator(q) for q in R[i][2]))
    end
  end

  for i in 1:n
    # mu[i] = d[i] * R[i][1] / b[i]^2
    mu_val = d[i] * R[i][1] // (b[i]^2)
    @assert is_integer(mu_val)
    mu[i] = numerator(mu_val)

    # e[i] = vector of b[i] * R[i][2][j] for j in 1:n-i
    e_arr[i] = ZZRingElem[numerator(b[i] * R[i][2][j]) for j in 1:length(R[i][2])]

    # lambda[i] = c[i] * R[i][1]
    lambda_val = c_int[i] * R[i][1]
    @assert is_integer(lambda_val)
    lambda[i] = numerator(lambda_val)

    # tlob[i] = 2 * lambda[i] / b[i]
    tlob_val, rem = divrem(2 * lambda[i], b[i])
    @assert is_zero(rem)
    tlob[i] = tlob_val

    # doc[i] = d[i] / c[i]
    doc[i] = divexact(d[i], c_int[i])

    # docp1[i] = d[i] / c[i+1]
    docp1[i] = divexact(d[i], c_int[i + 1])
  end

  x = zeros_array(ZZ, n)
  ctx = FinckePohstIntCtx{ZZRingElem}(M, n, e_arr, b, doc, docp1, mu, lambda, tlob, x)
  return ctx, per
end

# Core recursive enumeration. Calls f(x, norm) for each vector found.
# Ni is the remaining bound (integer), i is the current dimension (1-indexed),
# zero_so_far tracks whether all x[j] for j > i are zero (for sign reduction).
function _finckepohstint_rec!(f::F, ctx::FinckePohstIntCtx, i::Int, Ni,
                        zero_so_far::Bool) where {F}
  Ni < 0 && return
  if i == 0
    zero_so_far && return
    f(ctx.x, ctx.M - Ni)
    return
  end
  # Compute S = -sum(e[i][j-i] * x[j] for j in i+1:n)
  S = 0
  @inbounds for j in (i + 1):ctx.n
    S -= ctx.e[i][j - i] * ctx.x[j]
  end
  # Floor division toward -infinity
  @inbounds in_xi = fld(S, ctx.b[i])
  @inbounds r = mod(S, ctx.b[i])
  # Core recurrence: all integer arithmetic
  @inbounds in_Nim1 = div((Ni * ctx.docp1[i] - ctx.mu[i] * r * r), ctx.doc[i])
  @inbounds in_dNim1 = -ctx.tlob[i] * r + ctx.lambda[i]
  # Negative direction: x[i] = in_xi, in_xi-1, in_xi-2, ...
  @inbounds ctx.x[i] = in_xi
  Nim1 = in_Nim1
  dNim1 = in_dNim1
  while Nim1 >= 0
    if zero_so_far
      @inbounds ctx.x[i] < 0 && break
      @inbounds _finckepohstint_rec!(f, ctx, i - 1, Nim1, ctx.x[i] == 0)
    else
      _finckepohstint_rec!(f, ctx, i - 1, Nim1, false)
    end
    @inbounds ctx.x[i] -= 1
    @inbounds dNim1 -= 2 * ctx.lambda[i]
    Nim1 += dNim1
  end
  # Positive direction: x[i] = in_xi+1, in_xi+2, ...
  @inbounds ctx.x[i] = in_xi + 1
  dNim1 = -in_dNim1
  Nim1 = in_Nim1 + dNim1
  while Nim1 >= 0
    if zero_so_far
      @inbounds if ctx.x[i] >= 0
        @inbounds _finckepohstint_rec!(f, ctx, i - 1, Nim1, ctx.x[i] == 0)
      end
    else
      _finckepohstint_rec!(f, ctx, i - 1, Nim1, false)
    end
    @inbounds ctx.x[i] += 1
    @inbounds dNim1 -= 2 * ctx.lambda[i]
    Nim1 += dNim1
  end
  return
end

# Enumerate short vectors of an integral gram matrix using integer-only
# Fincke-Pohst.
#
# Returns (ok, Vector{Tuple{Vector{Int}, Int}}) where ok indicates whether
# the integer-only routine could be prepared. The second argument is always
# a Vector{Tuple{Vector{Int}, Int}}.
function _finckepohstint(gram::ZZMatrix, M::Int)
  n = nrows(gram)
  if n == 0
    return true, Tuple{Vector{Int}, Int}[]
  end

  success, ctx, per = _try_prepare_finckepohstint_small(gram, M)
  if !success
    return false, Tuple{Vector{Int}, Int}[]
  end

  result = Tuple{Vector{Int}, Int}[]

  _finckepohstint_collect!(result, ctx, nothing, per)

  return true, result
end

# Separate function to avoid closure overhead
function _finckepohstint_collect!(result::Vector{Tuple{Vector{Int}, Int}},
                            ctx::FinckePohstIntCtx,
                            U_int::Union{Nothing, Matrix{Int}},
                            per::Union{Nothing, Vector{Int}})
  n = ctx.n
  _finckepohstint_rec!(ctx, n, ctx.M, true) do x, norm
    v = Vector{Int}(undef, n)
    if per !== nothing
      @inbounds for j in 1:n
        v[per[j]] = x[j]
      end
    end
    _canonicalize_finckepohstint!(v)
    push!(result, (v, norm))
  end
end

function _canonicalize_finckepohstint!(v::Vector, l::Int = length(v))
  for i in 1:l
    if v[i] != 0
      if v[i] < 0
        @inbounds for j in i:l
          v[j] = -v[j]
        end
      end
      return v
    end
  end
  return v
end

# High-level interface matching the existing _short_vectors_gram pattern.
# Enumerates vectors v with lb <= v*G*v^t <= ub using integer-only arithmetic.
# G must be integral and positive definite with denominator already cleared.
function _short_vectors_gram_finckepohstint(G::ZZMatrix, lb::Int, ub::Int;
                                      transform::Union{Nothing, ZZMatrix} = nothing, normtype = Int)
  n = nrows(G)
  if n == 0
    return Tuple{Vector{Int}, Int}[]
  end

  success, raw = _finckepohstint(G, ub)
  if !success
    error("Asds")
    return Tuple{Vector{Int}, normtype}[]
  end

  # Filter by lower bound and apply transform
  result = Tuple{Vector{Int}, normtype}[]
  for (v, norm) in raw
    norm >= lb || continue
    _norm = (normtype === Int ? norm : normtype(norm))::normtype
    if transform !== nothing && !isone(transform)
      w = Vector{Int}(undef, n)
      @inbounds for i in 1:n
        s = 0
        for j in 1:n
          s += v[j] * Int(transform[j, i])
        end
        w[i] = s
      end
      _canonicalize_finckepohstint!(w)
      push!(result, (w, _norm))
    else
      push!(result, (v, _norm))
    end
  end
  return result
end

function __enumerate_gram_fp(T, Gi::ZZMatrix, mi, ma, a, b, c, ::Type{Int})
  @assert a === QQFieldElem
  @assert b === c === identity
  return _short_vectors_gram_finckepohstint(Gi, Int(mi), Int(ma); normtype = ZZRingElem)
end

struct _FPCallback{S, T, U, V, W, X}
  result::S
  per::T
  l::U
  pp_vector::V
  pp_length::W
  n::X
end

function (f::_FPCallback{S, T, U, V, W, X})(x, norm) where {S, T, U, V, W, X}
  l = f.l
  if !(l isa Nothing)
    if norm < l
      return
    end
  end

  n = f.n
  per = f.per
  pp_vector = f.pp_vector
  pp_length = f.pp_length
  result = f.result

  v = Vector{Int}(undef, n)
  if per !== nothing
    @inbounds for j in 1:n
      v[per[j]] = x[j]
    end
  end
  _canonicalize_finckepohstint!(v)
  push!(result, (pp_vector(v), pp_length(norm)))
end

function __enumerate_gram(::Type{FinckePohstInt}, G::ZZMatrix, l::Union{Int, ZZRingElem, Nothing}, c::Union{Int, ZZRingElem}, ::Type{NormType}, pp_vector::X, pp_length::Y, ::Type{ElemType}) where {X, Y, ElemType, NormType}
  gram = G
  n = nrows(gram)
  if n == 0
    return Tuple{Vector{ElemType}, NormType}[]
  end

  if fits(Int, c) && begin success, ctx, per = _try_prepare_finckepohstint_small(gram, Int(c)); success end
    result = Tuple{Vector{ElemType}, NormType}[]
    n = ctx.n
    callback = _FPCallback(result, per, l, pp_vector, pp_length, n)
    _finckepohstint_rec!(callback, ctx, n, ctx.M, true)
    return result
  else
    ctx, per = _prepare_finckepohstint_large(gram, ZZ(c))
    result = Tuple{Vector{ElemType}, NormType}[]
    _callback = _FPCallback(result, per, l, pp_vector, pp_length, n)
    _finckepohstint_rec!(_callback, ctx, n, ctx.M, true)
    return result
  end
end

################################################################################
#
#  Iterator version of the integral Fincke-Pohst algorithm
#
#  Converts _finckepohstint_rec! from a recursive callback to a lazy Julia
#  iterator using the same @label/@goto state machine design as LatEnumCtx in
#  Enumeration.jl.
#
################################################################################

# Per-level state arrays store exactly what is needed to resume the two-phase
# enumeration (negative direction then positive direction) at each depth.
mutable struct FinckePohstIntIterCtx{T, F1, F2, ElemType, NormType}
  ctx::FinckePohstIntCtx{T}
  per::Union{Nothing, Vector{Int}}
  l::Union{T, Nothing}          # lower bound, or nothing
  pp_vector::F1
  pp_length::F2
  Nim1::Vector{T}               # current remaining bound at each level
  dNim1::Vector{T}              # current derivative of remaining bound
  in_xi::Vector{T}              # floor value at each level (for phase switch)
  in_Nim1::Vector{T}            # initial Nim1 at entry (for phase switch)
  in_dNim1::Vector{T}           # initial dNim1 at entry (for phase switch)
  phase::Vector{Int8}           # 0 = negative direction, 1 = positive direction
  zero_so_far::Vector{Bool}     # whether all x[j] for j > i are zero at level i
  tmp_v::Vector{ElemType}       # scratch buffer for building output vector
end

Base.eltype(::Type{FinckePohstIntIterCtx{T, F1, F2, ElemType, NormType}}) where {T, F1, F2, ElemType, NormType} =
  Tuple{Vector{ElemType}, NormType}

Base.IteratorSize(::Type{S}) where {S <: FinckePohstIntIterCtx}= Base.SizeUnknown()

# First iterate: initialise state at the top level and run state machine.
function Base.iterate(C::FinckePohstIntIterCtx{T, F1, F2, ElemType, NormType}) where {T, F1, F2, ElemType, NormType}
  ctx = C.ctx
  n   = ctx.n
  x   = ctx.x
  if n == 0
    return nothing
  end
  Nim1    = C.Nim1
  dNim1   = C.dNim1
  in_xi   = C.in_xi
  in_Nim1  = C.in_Nim1
  in_dNim1 = C.in_dNim1
  phase   = C.phase
  per     = C.per
  l       = C.l
  pp_vector   = C.pp_vector
  pp_length   = C.pp_length
  tmp_v       = C.tmp_v
  zero_so_far = C.zero_so_far
  i = n

  # ---- enter_level -------------------------------------------------------
  # Compute the state at level i given the bound Ni from the parent.
  @label enter_level
  S = zero(T)
  @inbounds for j in (i + 1):n
    S -= ctx.e[i][j - i] * x[j]
  end
  @inbounds xi = fld(S, ctx.b[i])
  @inbounds r  = mod(S, ctx.b[i])
  Ni = i == n ? ctx.M : @inbounds(Nim1[i + 1])
  @inbounds Nim1[i]    = div(Ni * ctx.docp1[i] - ctx.mu[i] * r * r, ctx.doc[i])
  @inbounds dNim1[i]   = -ctx.tlob[i] * r + ctx.lambda[i]
  @inbounds in_xi[i]   = xi
  @inbounds in_Nim1[i]  = Nim1[i]
  @inbounds in_dNim1[i] = dNim1[i]
  @inbounds x[i]       = xi
  @inbounds phase[i]   = zero(Int8)
  @inbounds zero_so_far[i] = (i == n) || (zero_so_far[i + 1] && iszero(x[i + 1]))

  # ---- try_descend -------------------------------------------------------
  # Decide whether to descend, yield, skip, or terminate, based on current
  # state at level i.
  @label try_descend
  zero_so_far_i = @inbounds zero_so_far[i]
  if @inbounds(phase[i]) == 0
    # ---- negative direction ----
    @inbounds(Nim1[i]) < 0 && @goto switch_phase
    (zero_so_far_i && @inbounds(x[i]) < 0) && @goto switch_phase
    if i == 1
      zero_next = zero_so_far_i && @inbounds(iszero(x[1]))
      if !zero_next
        norm = ctx.M - @inbounds(Nim1[1])
        if l isa Nothing || norm >= l
          if per !== nothing
            @inbounds for j in 1:n; tmp_v[per[j]] = Int(x[j]); end
          else
            @inbounds for j in 1:n; tmp_v[j] = Int(x[j]); end
          end
          _canonicalize_finckepohstint!(tmp_v)
          return (pp_vector(tmp_v), pp_length(norm)), 1
        end
      end
      @goto update_neg
    else
      i -= 1
      @goto enter_level
    end
  else
    # ---- positive direction ----
    @inbounds(Nim1[i]) < 0 && @goto ascend
    (zero_so_far_i && @inbounds(x[i]) < 0) && @goto update_pos
    if i == 1
      zero_next = zero_so_far_i && @inbounds(iszero(x[1]))
      if !zero_next
        norm = ctx.M - @inbounds(Nim1[1])
        if l isa Nothing || norm >= l
          if per !== nothing
            @inbounds for j in 1:n; tmp_v[per[j]] = Int(x[j]); end
          else
            @inbounds for j in 1:n; tmp_v[j] = Int(x[j]); end
          end
          _canonicalize_finckepohstint!(tmp_v)
          return (pp_vector(tmp_v), pp_length(norm)), 1
        end
      end
      @goto update_pos
    else
      i -= 1
      @goto enter_level
    end
  end

  # ---- update_neg --------------------------------------------------------
  @label update_neg
  @inbounds x[i]     -= 1
  @inbounds dNim1[i] -= 2 * ctx.lambda[i]
  @inbounds Nim1[i]  += dNim1[i]
  @goto try_descend

  # ---- switch_phase ------------------------------------------------------
  @label switch_phase
  @inbounds x[i]     = in_xi[i] + 1
  @inbounds dNim1[i] = -in_dNim1[i]
  @inbounds Nim1[i]  = in_Nim1[i] + dNim1[i]
  @inbounds phase[i] = one(Int8)
  @goto try_descend

  # ---- update_pos --------------------------------------------------------
  @label update_pos
  @inbounds x[i]     += 1
  @inbounds dNim1[i] -= 2 * ctx.lambda[i]
  @inbounds Nim1[i]  += dNim1[i]
  @goto try_descend

  # ---- ascend ------------------------------------------------------------
  @label ascend
  i += 1
  i > n && return nothing
  @inbounds(phase[i]) == 0 ? (@goto update_neg) : (@goto update_pos)
end

# Continuation iterate: resume from the saved per-level state.
# `it` is always 1 (the level at which vectors are yielded).
#
# Performance note: the hot path caches the level-1 scalars (_N1, _dN1, _x1,
# _ph1, _zsf1, _lam1) in local variables.  This mirrors how _finckepohstint_rec!
# keeps Nim1/dNim1 as call-stack locals (register-resident) rather than heap
# arrays, eliminating per-step array loads/stores in the innermost loop.
# The general state machine below only handles levels i >= 2; when it descends
# back to level 1 it reloads the locals and returns to the hot path.
@inline function Base.iterate(C::FinckePohstIntIterCtx{T, F1, F2, ElemType, NormType}, it::Int) where {T, F1, F2, ElemType, NormType}
  ctx      = C.ctx
  n        = ctx.n
  x        = ctx.x
  Nim1     = C.Nim1
  dNim1    = C.dNim1
  in_xi    = C.in_xi
  in_Nim1  = C.in_Nim1
  in_dNim1 = C.in_dNim1
  phase    = C.phase
  per      = C.per
  l        = C.l
  pp_vector  = C.pp_vector
  pp_length  = C.pp_length
  tmp_v      = C.tmp_v
  zero_so_far = C.zero_so_far
  lambda   = ctx.lambda
  i = 2   # general state machine loop variable; always re-assigned before use

  # Load level-1 state into local variables (register-promotable).
  _N1   = @inbounds Nim1[1]
  _dN1  = @inbounds dNim1[1]
  _x1   = @inbounds x[1]
  _ph1  = @inbounds phase[1]
  _zsf1 = @inbounds zero_so_far[1]
  _lam1 = @inbounds lambda[1]

  # Resume: advance x[1] past the previously yielded position.
  if _ph1 == 0
    _x1 -= 1; _dN1 -= 2 * _lam1; _N1 += _dN1
    @goto try_neg
  else
    _x1 += 1; _dN1 -= 2 * _lam1; _N1 += _dN1
    @goto try_pos
  end

  # ---- Negative-direction hot loop at level 1 ----------------------------
  @label try_neg
  _N1 < 0 && @goto switch_phase_1
  (_zsf1 && _x1 < 0) && @goto switch_phase_1
  if !(_zsf1 && iszero(_x1))
    norm = ctx.M - _N1
    if l isa Nothing || norm >= l
      @inbounds x[1] = _x1
      @inbounds Nim1[1] = _N1; @inbounds dNim1[1] = _dN1; @inbounds phase[1] = _ph1
      if per !== nothing
        @inbounds for j in 1:n; tmp_v[per[j]] = Int(x[j]); end
      else
        @inbounds for j in 1:n; tmp_v[j] = Int(x[j]); end
      end
      _canonicalize_finckepohstint!(tmp_v)
      return (pp_vector(tmp_v), pp_length(norm)), 1
    end
  end
  _x1 -= 1; _dN1 -= 2 * _lam1; _N1 += _dN1
  @goto try_neg

  # ---- Switch negative → positive direction at level 1 -------------------
  @label switch_phase_1
  _x1  = @inbounds(in_xi[1]) + 1
  _dN1 = -@inbounds(in_dNim1[1])
  _N1  = @inbounds(in_Nim1[1]) + _dN1
  _ph1 = one(Int8)

  # ---- Positive-direction hot loop at level 1 ----------------------------
  @label try_pos
  if _N1 < 0
    # Level 1 exhausted: write back and enter the general state machine.
    @inbounds x[1] = _x1; @inbounds Nim1[1] = _N1
    @inbounds dNim1[1] = _dN1; @inbounds phase[1] = _ph1
    i = 2
    i > n && return nothing
    @inbounds(phase[i]) == 0 ? (@goto update_neg) : (@goto update_pos)
  end
  if !(_zsf1 && _x1 < 0)
    if !(_zsf1 && iszero(_x1))
      norm = ctx.M - _N1
      if l isa Nothing || norm >= l
        @inbounds x[1] = _x1
        @inbounds Nim1[1] = _N1; @inbounds dNim1[1] = _dN1; @inbounds phase[1] = _ph1
        if per !== nothing
          @inbounds for j in 1:n; tmp_v[per[j]] = Int(x[j]); end
        else
          @inbounds for j in 1:n; tmp_v[j] = Int(x[j]); end
        end
        _canonicalize_finckepohstint!(tmp_v)
        return (pp_vector(tmp_v), pp_length(norm)), 1
      end
    end
  end
  _x1 += 1; _dN1 -= 2 * _lam1; _N1 += _dN1
  @goto try_pos

  # ---- General state machine for levels i >= 2 ---------------------------
  # Reached only when level 1 is exhausted and we need to advance higher
  # levels.  When descending back to level 1, reloads locals and returns
  # control to the hot path above.

  @label enter_level
  S = zero(T)
  @inbounds for j in (i + 1):n
    S -= ctx.e[i][j - i] * x[j]
  end
  @inbounds xi = fld(S, ctx.b[i])
  @inbounds r  = mod(S, ctx.b[i])
  Ni = i == n ? ctx.M : @inbounds(Nim1[i + 1])
  @inbounds Nim1[i]    = div(Ni * ctx.docp1[i] - ctx.mu[i] * r * r, ctx.doc[i])
  @inbounds dNim1[i]   = -ctx.tlob[i] * r + lambda[i]
  @inbounds in_xi[i]   = xi
  @inbounds in_Nim1[i]  = Nim1[i]
  @inbounds in_dNim1[i] = dNim1[i]
  @inbounds x[i]       = xi
  @inbounds phase[i]   = zero(Int8)
  @inbounds zero_so_far[i] = (i == n) || (zero_so_far[i + 1] && iszero(x[i + 1]))
  if i == 1
    # Returning to level 1: reload locals and re-enter the hot path.
    _x1   = xi
    _N1   = @inbounds Nim1[1]
    _dN1  = @inbounds dNim1[1]
    _ph1  = zero(Int8)
    _zsf1 = @inbounds zero_so_far[1]
    @goto try_neg
  end

  @label try_descend
  zero_so_far_i = @inbounds zero_so_far[i]
  if @inbounds(phase[i]) == 0
    @inbounds(Nim1[i]) < 0 && @goto switch_phase
    (zero_so_far_i && @inbounds(x[i]) < 0) && @goto switch_phase
    i -= 1
    @goto enter_level
  else
    @inbounds(Nim1[i]) < 0 && @goto ascend
    (zero_so_far_i && @inbounds(x[i]) < 0) && @goto update_pos
    i -= 1
    @goto enter_level
  end

  @label update_neg
  @inbounds x[i]     -= 1
  @inbounds dNim1[i] -= 2 * lambda[i]
  @inbounds Nim1[i]  += dNim1[i]
  @goto try_descend

  @label switch_phase
  @inbounds x[i]     = in_xi[i] + 1
  @inbounds dNim1[i] = -in_dNim1[i]
  @inbounds Nim1[i]  = in_Nim1[i] + dNim1[i]
  @inbounds phase[i] = one(Int8)
  @goto try_descend

  @label update_pos
  @inbounds x[i]     += 1
  @inbounds dNim1[i] -= 2 * lambda[i]
  @inbounds Nim1[i]  += dNim1[i]
  @goto try_descend

  @label ascend
  i += 1
  i > n && return nothing
  @inbounds(phase[i]) == 0 ? (@goto update_neg) : (@goto update_pos)
end

# Dispatch hook: create a FinckePohstIntIterCtx for the given gram matrix.
# Tries the small (Int) path first; falls back to the large (ZZRingElem) path.
function __enumerate_gram(::Type{FinckePohstIntIterCtx}, G::ZZMatrix, l::Union{Int, ZZRingElem, Nothing}, c::Union{Int, ZZRingElem}, ::Type{NormType}, pp_vector::F1, pp_length::F2, ::Type{ElemType}) where {F1, F2, ElemType, NormType}
  n = nrows(G)
  if n == 0
    dummy = FinckePohstIntCtx{Int}(0, 0, Vector{Vector{Int}}(), Int[], Int[], Int[], Int[], Int[], Int[], Int[])
    return FinckePohstIntIterCtx{ElemType, F1, F2, ElemType, NormType}(
      dummy, nothing, nothing, pp_vector, pp_length,
      Int[], Int[], Int[], Int[], Int[], Int8[], Bool[], Int[])
  end
  if fits(Int, c) && begin success, ctx, per = _try_prepare_finckepohstint_small(G, Int(c)); success end
    _l = l isa Nothing ? nothing : Int(l)
    return FinckePohstIntIterCtx{Int, F1, F2, ElemType, NormType}(
      ctx, per, _l, pp_vector, pp_length,
      zeros(Int, n), zeros(Int, n), zeros(Int, n),
      zeros(Int, n), zeros(Int, n), zeros(Int8, n), falses(n), zeros(Int, n))
  else
    ctx, per = _prepare_finckepohstint_large(G, ZZ(c))
    _l = l isa Nothing ? nothing : ZZ(l)
    return FinckePohstIntIterCtx{ZZRingElem, F1, F2, ElemType, NormType}(
      ctx, per, _l, pp_vector, pp_length,
      zeros_array(ZZ, n), zeros_array(ZZ, n), zeros_array(ZZ, n),
      zeros_array(ZZ, n), zeros_array(ZZ, n), zeros(Int8, n), falses(n), zeros(Int, n))
  end
end
