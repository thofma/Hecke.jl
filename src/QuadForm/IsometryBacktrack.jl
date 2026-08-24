################################################################################
#
#  Isometries of definite lattices by short vector backtracking
#
################################################################################
#
#  This computes the isometry group of a definite integral lattice, and decides
#  whether two such lattices are isometric.
#
#  As in the algorithm of Plesken and Souvignier
#
#    W. Plesken, B. Souvignier, Computing isometries of lattices,
#    J. Symbolic Comput. 24 (1997), 327-334,
#
#  the search backtracks over the possible images of a basis inside the set of
#  short vectors.  The bookkeeping however is organised around partition
#  refinement, which is what makes it fast:
#
#   * The short vectors are enumerated once into a dense `Int32` matrix,
#     together with the matrix of their scalar products with the basis vectors.
#     A hash table recognises a vector in constant time.
#
#   * The order of the basis and the numbers of possible continuations (the
#     "fingerprint") are computed by refining an ordered partition of the set of
#     short vectors, one basis vector at a time, instead of by the quadratic
#     scans of `possible`.  Blocks which contain no basis vector consist of
#     vectors which cannot be the image of anything and are discarded, so the
#     partition shrinks rapidly.  The refinement also produces, for free, the
#     candidate list for every prefix of the base consisting of standard basis
#     vectors, which is exactly what the outer loop of the stabiliser chain
#     needs.
#
#   * During the backtrack a pool of still relevant short vectors is carried
#     along.  Each pool entry stores a bit mask of the levels of the base for
#     which it is still a possible image.  Descending one level costs a single
#     scalar product per pool entry and updates the candidate sets of all deeper
#     levels simultaneously.  The number of candidates of a level is compared
#     against the fingerprint of the source lattice, which prunes a partial map
#     as soon as it cannot be part of an isometry.
#
#   * Group elements are turned into permutations of the short vectors as soon
#     as they are applied often enough (and always for the large orbits at the
#     top of the stabiliser chain), which makes the orbit computations of the
#     stabiliser chain essentially free.  Orbits are closed by advancing the
#     generators in a round robin fashion and stop as soon as the orbit has the
#     length predicted by the fingerprint.
#
#  Correctness.  Every step is exact integer arithmetic; no floating point
#  number enters a decision.
#
#   * The enumeration of the short vectors uses fraction free (Bareiss)
#     elimination and integer square roots, see the comment below; it is
#     therefore provably complete, which matters because a missing short vector
#     would silently make the isometry group too small.  (Floating point is used
#     in one place, as a first guess for an integer square root, and the guess
#     is corrected by exact integer comparisons.)
#   * The inner loops work with `Int32`; the constructor bounds every partial
#     sum that can occur and throws `BTOverflow` if `Int32` might not suffice,
#     so that the caller falls back to the generic implementation.  The
#     enumeration picks `Int` or `Int128` after bounding its intermediate
#     values, and throws `BTOverflow` if neither suffices.
#   * All pruning criteria are necessary conditions for a partial map to extend
#     to an isometry, so the backtrack is exhaustive; and every isometry that is
#     returned is verified with an exact matrix product.
#
################################################################################

struct BTOverflow <: Exception end

struct BTError <: Exception
  msg::String
end

################################################################################
#
#  Short vectors
#
################################################################################

# The enumeration of the short vectors is done with exact integer arithmetic
# only, so that the list of short vectors is provably complete: a missing short
# vector would silently make the isometry group too small.
#
# Write d_k for the determinant of the leading k x k minor of G (with d_0 = 1)
# and let S^(k) be the Schur complement of that minor, that is the Gram matrix
# of the projection of the lattice orthogonally to the first k - 1 basis
# vectors.  By Sylvester's identity the matrix
#
#     M^(k) := d_{k-1} * S^(k)
#
# is integral; its entries are the k x k minors of G produced by fraction free
# (Bareiss) Gaussian elimination, and M^(k)[k,k] = d_k.  For a partial vector
# x_k, ..., x_n the quantity
#
#     P_k(x) := d_{k-1} * (x_{>=k} * S^(k) * transpose(x_{>=k}))
#             = x_{>=k} * M^(k) * transpose(x_{>=k})
#
# is therefore an integer, and d_{k-1}^{-1} * P_k is exactly the minimum of
# x*G*transpose(x) over all real values of x_1, ..., x_{k-1}.  Hence
#
#     the partial vector can be completed to a vector of norm <= b
#         <=>  P_k <= b * d_{k-1},
#
# which is a comparison of integers, and P_1 is the norm of the full vector.
# Setting B_k = sum_{j>k} M^(k)[k,j]*x_j and w_k = d_k*x_k + B_k one has the
# (integral) recursion
#
#     P_k = (d_{k-1}*P_{k+1} + w_k^2) / d_k,
#
# and the admissible range for x_k is given by w_k^2 <= d_{k-1}*(b*d_k - P_{k+1}),
# that is by an integer square root.  No floating point number is involved.

# Fraction free (Bareiss) elimination.  Returns the rows
# `C[k][j - k + 1] = M^(k)[k, j]` for j >= k and the leading principal minors
# `d[k + 1] = d_k` (so that `d[1] = d_0 = 1`).
function _bt_bareiss(G::Matrix{Int})
  n = size(G, 1)
  A = Matrix{ZZRingElem}(undef, n, n)
  for i in 1:n, j in 1:n
    A[i, j] = ZZRingElem(G[i, j])
  end
  C = Vector{Vector{ZZRingElem}}(undef, n)
  d = Vector{ZZRingElem}(undef, n + 1)
  d[1] = one(ZZRingElem)
  prev = one(ZZRingElem)
  for k in 1:n
    C[k] = ZZRingElem[A[k, j] for j in k:n]
    d[k + 1] = A[k, k]
    # Sylvester's criterion: d[k+1] is the k-th leading principal minor
    A[k, k] > 0 || throw(BTError("Gram matrix is not positive definite"))
    k == n && break
    akk = A[k, k]
    for i in (k + 1):n
      aik = A[i, k]
      for j in (k + 1):n
        A[i, j] = divexact(akk * A[i, j] - aik * A[k, j], prev)
      end
    end
    prev = akk
  end
  return C, d
end

# inverse of an odd d modulo 2^(8*sizeof(T)), by Newton iteration; used to turn
# the exact divisions of the enumeration into multiplications
@inline function _bt_oddinv(d::T) where {T <: Integer}
  x = d
  for _ in 1:7
    x = x * (T(2) - d * x)
  end
  return x
end

# exact division by `di`: a shift and a multiplication with the inverse of the
# odd part of `di` replace the division
@inline _bt_exdiv(a::T, di::T, sh::Int, iv::T) where {T <: Union{Int, Int128}} =
  (a >> sh) * iv
# largest integer s with s^2 <= K, for K >= 0
# largest s with s^2 <= typemax(T); below it `s * s` cannot overflow
@inline _bt_sqrtmax(::Type{Int}) = 3037000499
@inline _bt_sqrtmax(::Type{Int128}) = 13043817825332782212 % Int128

@inline function _bt_isqrt(K::T) where {T <: Union{Int, Int128}}
  K <= 0 && return zero(T)
  s = unsafe_trunc(T, sqrt(Float64(K)))
  s < one(T) && (s = one(T))
  # Two exact multiplications decide whether the Float64 guess is already the
  # answer, which it is whenever `K` is small enough for a Float64 to hold it
  # exactly.  Everything below is only reached for a guess that is off, and it
  # is exact for an arbitrarily bad one: `div(K, s)` for an `s` at most the
  # result is at least the result, and Newton's iteration started from an upper
  # bound decreases monotonically to the exact value.
  if s <= _bt_sqrtmax(T) && s * s <= K
    # (s + 1)^2 can only overflow when it is larger than `typemax(T) >= K`, so
    # an overflow here answers the question just as well
    (s + one(T)) * (s + one(T)) > K && return s
    s = div(K, s)
  end
  while true
    q = div(K, s)
    s <= q && return s
    s = div(s + q, T(2))
  end
end

mutable struct BTEnumBuf
  coords::Vector{Int32}
  norms::Vector{Int}
  nc::Int
  nn::Int
end

BTEnumBuf() = BTEnumBuf(Vector{Int32}(undef, 1 << 14), Vector{Int}(undef, 1 << 10), 0, 0)

# Enumerate all v != 0 with v*G*transpose(v) <= bound, one out of each pair
# {v, -v}; the representative is the one whose last non-zero coordinate is
# positive.  `P` is the value P_{i+1} of the comment above.
function _bt_enum!(buf::BTEnumBuf, C::Vector{Vector{T}}, d::Vector{T},
                   dsh::Vector{Int}, dinv::Vector{T}, x::Vector{Int32},
                   nz::Vector{Int32}, nnz::Int, n::Int,
                   i::Int, P::T, allzero::Bool, bnd::T) where {T <: Integer}
  @inbounds di = d[i + 1]
  @inbounds dm = d[i]
  K = dm * (bnd * di - P)
  K < 0 && return nothing
  Ci = C[i]
  B = zero(T)
  # only the coordinates which have been set to something non zero contribute,
  # and a short vector has few of those
  @inbounds for t in 1:nnz
    j = Int(nz[t])
    B += Ci[j - i + 1] * T(x[j])
  end
  # The range of x_i is the interval of integers with (di*x + B)^2 <= K.  Its
  # real centre is -B/di; a Float64 division locates an integer next to it, and
  # the two loops below move that integer to the nearest one exactly.  There
  # |w| is minimal over all integers, so the interval is empty precisely when
  # even that w fails the test, and its ends are found by walking outwards.
  # Every decision is an exact integer comparison -- the Float64 division only
  # says where to start -- so no square root and no division by di are needed.
  hd = di >> 1
  xc = unsafe_trunc(T, round(-Float64(B) / Float64(di)))
  w = di * xc + B
  while w > hd
    xc -= one(T)
    w -= di
  end
  while w < -hd
    xc += one(T)
    w += di
  end
  w * w > K && return nothing
  hi = xc
  wu = w
  while true
    wu += di
    wu * wu > K && break
    hi += one(T)
  end
  lo = xc
  wd = w
  while true
    wd -= di
    wd * wd > K && break
    lo -= one(T)
  end
  if allzero && lo < 0
    lo = zero(T)
    lo > hi && return nothing
  end
  # P_i = (dm*P + w^2) / di is an exact division, so it can be done by a shift
  # and a multiplication with the inverse of the odd part of di
  @inbounds sh = dsh[i]
  @inbounds iv = dinv[i]
  base = dm * P
  w = di * lo + B
  if i == 1
    @inbounds for xi in lo:hi
      if !(allzero && xi == 0)
        P1 = _bt_exdiv(base + w * w, di, sh, iv)
        if P1 > 0
          x[1] = Int32(xi)
          if buf.nc + n > length(buf.coords)
            resize!(buf.coords, max(2 * length(buf.coords), buf.nc + n))
          end
          if buf.nn >= length(buf.norms)
            resize!(buf.norms, 2 * length(buf.norms))
          end
          c = buf.nc
          for k in 1:n
            buf.coords[c + k] = x[k]
          end
          buf.nc = c + n
          buf.nn += 1
          buf.norms[buf.nn] = Int(P1)
        end
      end
      w += di
    end
    x[1] = Int32(0)
    return nothing
  end
  @inbounds for xi in lo:hi
    x[i] = Int32(xi)
    Pi = _bt_exdiv(base + w * w, di, sh, iv)
    if xi == 0
      _bt_enum!(buf, C, d, dsh, dinv, x, nz, nnz, n, i - 1, Pi, allzero, bnd)
    else
      # the entry has to be written again for every value of x_i: a call which
      # did not use it has overwritten the slot with its own position
      nz[nnz + 1] = Int32(i)
      _bt_enum!(buf, C, d, dsh, dinv, x, nz, nnz + 1, n, i - 1, Pi, false, bnd)
    end
    w += di
  end
  x[i] = Int32(0)
  return nothing
end

# Runs the enumeration with the smallest machine integer type for which no
# intermediate result can overflow; throws `BTOverflow` if `Int128` does not
# suffice either.
# Fallback for lattices whose leading principal minors are too large for the
# integral enumeration; uses the exact (rational) enumeration of `short_vectors`.
function _bt_short_vectors_generic(G::Matrix{Int}, bound::Int)
  n = size(G, 1)
  Gz = matrix(ZZ, n, n, [ZZRingElem(G[i, j]) for i in 1:n for j in 1:n])
  L = integer_lattice(gram = Gz; cached = false)
  sv = short_vectors(L, 1, bound)
  nv = length(sv)
  V = Matrix{Int32}(undef, n, nv)
  norms = Vector{Int}(undef, nv)
  for (j, (v, m)) in enumerate(sv)
    s = 1
    for i in n:-1:1
      if !is_zero(v[i])
        s = v[i] > 0 ? 1 : -1
        break
      end
    end
    for i in 1:n
      V[i, j] = Int32(s * v[i])
    end
    norms[j] = Int(m)
  end
  return V, norms
end

# The shape of the enumeration tree depends on the order of the basis.  The
# number of nodes at level `i` is the number of lattice points of the
# projection onto the last `n - i + 1` coordinates inside a ball of radius
# sqrt(bound), which by the volume heuristic is
#
#     V_k * bound^(k/2) * sqrt(d_i / det),   k = n - i + 1,
#
# where `d_i` is the determinant of the first `i - 1` basis vectors.  An order
# which keeps those determinants small therefore shrinks the tree, sometimes by
# orders of magnitude.  Only the running time depends on the choice -- every
# order enumerates the same set -- so the estimate may be made in Float64 and
# the enumeration itself stays exact.
#
# `q[k]` are the squared Gram-Schmidt norms of the permuted basis; `false` if
# the elimination breaks down numerically, in which case the order is skipped.
function _bt_gs_norms!(q::Vector{Float64}, A::Matrix{Float64}, G::Matrix{Int},
                       per::Vector{Int}, n::Int)
  @inbounds for j in 1:n, i in 1:n
    A[i, j] = Float64(G[per[i], per[j]])
  end
  @inbounds for k in 1:n
    dk = A[k, k]
    dk > 0 || return false
    q[k] = dk
    for i in (k + 1):n
      f = A[i, k] / dk
      f == 0 && continue
      for j in (k + 1):n
        A[i, j] -= f * A[k, j]
      end
    end
  end
  return true
end

# logarithm of the size of the largest level of the tree
function _bt_enum_cost(q::Vector{Float64}, n::Int, bound::Float64,
                       lv::Vector{Float64})
  ldet = 0.0
  @inbounds for k in 1:n
    ldet += log(q[k])
  end
  lb = log(bound)
  ld = 0.0
  best = -Inf
  @inbounds for i in 1:n
    k = n - i + 1
    lw = lv[k] + (k / 2) * lb + (ld - ldet) / 2
    lw > best && (best = lw)
    ld += log(q[i])
  end
  return best
end

# lv[k] = log of the volume of the unit ball in dimension k, from
# Gamma(x + 1) = x * Gamma(x) in steps of one, which is a step of two in k
function _bt_ball_volumes(n::Int)
  lg = Vector{Float64}(undef, n + 1)         # lg[k + 1] = log Gamma(k/2 + 1)
  lg[1] = 0.0
  n >= 1 && (lg[2] = log(pi) / 2 - log(2.0))
  for k in 2:n
    lg[k + 1] = lg[k - 1] + log(k / 2)
  end
  return Float64[(k / 2) * log(pi) - lg[k + 1] for k in 1:n]
end

function _bt_enum_order(G::Matrix{Int}, bound::Int)
  n = size(G, 1)
  n <= 2 && return collect(1:n)
  lv = _bt_ball_volumes(n)
  A = Matrix{Float64}(undef, n, n)
  q = Vector{Float64}(undef, n)
  # the order the caller supplied (usually LLL reduced, which is already good)
  idp = collect(1:n)
  best = idp
  bs = Inf
  if _bt_gs_norms!(q, A, G, idp, n)
    bs = _bt_enum_cost(q, n, Float64(bound), lv)
  end
  # taking the vector with the smallest projected norm at every step keeps the
  # partial determinants small, which is a different trade off and wins on
  # bases whose order carries no information
  @inbounds for j in 1:n, i in 1:n
    A[i, j] = Float64(G[i, j])
  end
  used = falses(n)
  gr = Vector{Int}(undef, n)
  @inbounds for k in 1:n
    bi = 0
    bv = Inf
    for j in 1:n
      if !used[j] && A[j, j] < bv
        bv = A[j, j]
        bi = j
      end
    end
    gr[k] = bi
    used[bi] = true
    (k == n || !(bv > 0)) && continue
    for i in 1:n
      used[i] && continue
      f = A[i, bi] / bv
      f == 0 && continue
      for j in 1:n
        used[j] || (A[i, j] -= f * A[bi, j])
      end
    end
  end
  for per in (gr, reverse(gr))
    if _bt_gs_norms!(q, A, G, per, n)
      c = _bt_enum_cost(q, n, Float64(bound), lv)
      if c < bs
        bs = c
        best = per
      end
    end
  end
  return best
end

# Gram matrix of the projections of b_k, ..., b_j orthogonally to
# b_1, ..., b_{k-1}, scaled by the determinant of the first k - 1 of them so
# that it stays integral (Sylvester).
function _bt_proj_gram(G::ZZMatrix, k::Int, j::Int)
  k == 1 && return G[1:j, 1:j]
  A = G[1:(k - 1), 1:(k - 1)]
  B = G[1:(k - 1), k:j]
  Aq = inv(change_base_ring(QQ, A))
  P = change_base_ring(QQ, G[k:j, k:j]) -
      change_base_ring(QQ, transpose(B)) * Aq * change_base_ring(QQ, B)
  return map_entries(ZZ, det(A) * P)
end

# A block Korkine-Zolotarev reduction of the Gram matrix: every basis vector is
# made a shortest vector of the lattice its `beta` successors project to.  The
# result is only another basis of the same lattice, so this is a pure speed
# heuristic for the enumeration; the transform is checked to be unimodular and
# to give the Gram matrix back, so a bug here cannot make the result wrong.
# Returns the new Gram matrix and the transform, or `nothing`.
function _bt_bkz_gram(G::ZZMatrix, beta::Int, tours::Int)
  n = nrows(G)
  Gc, U = lll_gram_with_transform(G)
  for _ in 1:tours
    changed = false
    for k in 1:(n - 1)
      j = min(k + beta - 1, n)
      j <= k && continue
      M = _bt_proj_gram(Gc, k, j)
      m = nrows(M)
      L = integer_lattice(; gram = M, cached = false)
      y = ZZRingElem[]
      bn = M[1, 1]
      for v in shortest_vectors(L)
        c = ZZRingElem[v[i] for i in 1:m]
        r = (matrix(ZZ, 1, m, c) * M * transpose(matrix(ZZ, 1, m, c)))[1, 1]
        if r < bn
          bn = r
          y = c
        end
      end
      isempty(y) && continue
      # complete y to a unimodular transform of the block whose first row it is
      H, T = hnf_with_transform(matrix(ZZ, m, 1, y))
      H[1, 1] == 1 || continue
      W = transpose(inv(T))
      Un = identity_matrix(ZZ, n)
      for a in 1:m, b in 1:m
        Un[k + a - 1, k + b - 1] = W[a, b]
      end
      U = Un * U
      Gc = Un * Gc * transpose(Un)
      Gc, T2 = lll_gram_with_transform(Gc)
      U = T2 * U
      changed = true
    end
    changed || break
  end
  return Gc, U
end

# The enumeration may be run in any basis of the lattice.  When the tree the
# current one gives is predicted to be big, a block reduction is tried and kept
# if it is predicted to be better; the cost of the reduction is only worth it
# then.  `nothing` means "keep the basis as it is".
function _bt_enum_basis(G::Matrix{Int}, bound::Int)
  n = size(G, 1)
  n < 12 && return nothing
  lv = _bt_ball_volumes(n)
  A = Matrix{Float64}(undef, n, n)
  q = Vector{Float64}(undef, n)
  idp = collect(1:n)
  _bt_gs_norms!(q, A, G, idp, n) || return nothing
  c0 = _bt_enum_cost(q, n, Float64(bound), lv)
  # below this the whole enumeration is cheaper than the reduction would be
  c0 > log(1.0e6) || return nothing
  GZ = matrix(ZZ, n, n, [ZZRingElem(G[i, j]) for i in 1:n for j in 1:n])
  local Gb, U
  try
    Gb, U = _bt_bkz_gram(GZ, min(20, n), 2)
  catch
    return nothing
  end
  # the reduction is a heuristic, but a wrong transform would give wrong
  # vectors, so both of its defining properties are checked
  abs(det(U)) == 1 || return nothing
  Gb == U * GZ * transpose(U) || return nothing
  Gn = Matrix{Int}(undef, n, n)
  for i in 1:n, j in 1:n
    fits(Int, Gb[i, j]) || return nothing
    Gn[i, j] = Int(Gb[i, j])
  end
  _bt_gs_norms!(q, A, Gn, idp, n) || return nothing
  _bt_enum_cost(q, n, Float64(bound), lv) < c0 || return nothing
  Um = Matrix{Int}(undef, n, n)
  for i in 1:n, j in 1:n
    fits(Int, U[i, j]) || return nothing
    Um[i, j] = Int(U[i, j])
  end
  return Gn, Um
end

function _bt_short_vectors(G::Matrix{Int}, bound::Int)
  n = size(G, 1)
  bas = _bt_enum_basis(G, bound)
  if bas !== nothing
    Gn, U = bas
    Vn, nrm = _bt_short_vectors_perm(Gn, bound)
    # a vector with coordinates y in the new basis has coordinates transpose(U)
    # times y in the old one
    V = Matrix{Int32}(undef, n, size(Vn, 2))
    @inbounds for j in 1:size(Vn, 2)
      for i in 1:n
        t = 0
        for k in 1:n
          t += U[k, i] * Int(Vn[k, j])
        end
        V[i, j] = Int32(t)
      end
      for i in n:-1:1
        if V[i, j] != 0
          if V[i, j] < 0
            for l in 1:i
              V[l, j] = -V[l, j]
            end
          end
          break
        end
      end
    end
    return V, nrm
  end
  return _bt_short_vectors_perm(G, bound)
end

# Enumerate in the order which the fingerprint of the tree predicts to be the
# cheapest, and put the coordinates back afterwards.
function _bt_short_vectors_perm(G::Matrix{Int}, bound::Int)
  n = size(G, 1)
  per = _bt_enum_order(G, bound)
  if per != 1:n
    Gp = Matrix{Int}(undef, n, n)
    @inbounds for j in 1:n, i in 1:n
      Gp[i, j] = G[per[i], per[j]]
    end
    Vp, nrm = _bt_short_vectors_ordered(Gp, bound)
    V = Matrix{Int32}(undef, n, size(Vp, 2))
    @inbounds for j in 1:size(Vp, 2)
      for i in 1:n
        V[per[i], j] = Vp[i, j]
      end
      # the enumeration picks the representative of {v, -v} whose last non zero
      # coordinate is positive, but in the permuted coordinates; the lookup of
      # a vector relies on that convention, so it has to be restored here
      for i in n:-1:1
        if V[i, j] != 0
          if V[i, j] < 0
            for l in 1:i
              V[l, j] = -V[l, j]
            end
          end
          break
        end
      end
    end
    return V, nrm
  end
  return _bt_short_vectors_ordered(G, bound)
end

function _bt_short_vectors_ordered(G::Matrix{Int}, bound::Int)
  n = size(G, 1)
  C, d = _bt_bareiss(G)
  bz = ZZRingElem(bound)
  # a priori bound for the coordinates: x*G*transpose(x) <= b implies
  # x[j]^2 <= b * (G^-1)[j,j]
  Gq = inv(change_base_ring(QQ, matrix(ZZ, n, n, [ZZRingElem(G[i, j]) for i in 1:n for j in 1:n])))
  X = Vector{ZZRingElem}(undef, n)
  for j in 1:n
    t = bz * Gq[j, j]
    X[j] = isqrt(floor(ZZRingElem, t))
  end
  # every intermediate value is bounded by `lim`
  lim = ZZRingElem(1)
  for i in 1:n
    kmax = d[i] * (bz * d[i + 1])          # >= K and >= w^2 and >= d_{i-1}*P
    lim = max(lim, 2 * kmax)
    bb = ZZRingElem(0)
    for j in (i + 1):n
      bb += abs(C[i][j - i + 1]) * X[j]
    end
    lim = max(lim, bb + d[i + 1] * X[i])
    # the search for the ends of the range looks at one w past either end
    ww = bb + d[i + 1] * (X[i] + 1)
    lim = max(lim, 2 * ww * ww)
  end
  x = zeros(Int32, n)
  nz = zeros(Int32, n + 1)
  buf = BTEnumBuf()
  if lim >= ZZRingElem(2)^120
    # The intermediate values of the integral enumeration are of size
    # `bound * d_{i-1} * d_i`, so they grow with the square of the determinant.
    # When they no longer fit into an `Int128`, fall back to the exact
    # enumeration of `short_vectors`, which works with rational arithmetic: it
    # is slower, but it is exact as well, and it is the same enumeration the
    # Plesken-Souvignier implementation uses, so nothing is lost against it.
    return _bt_short_vectors_generic(G, bound)
  elseif lim < ZZRingElem(2)^62
    Ci = Vector{Vector{Int}}(undef, n)
    for i in 1:n
      Ci[i] = Int[Int(c) for c in C[i]]
    end
    di = Int[Int(t) for t in d]
    dsh = Int[trailing_zeros(di[i + 1]) for i in 1:n]
    dinv = Int[_bt_oddinv(di[i + 1] >> dsh[i]) for i in 1:n]
    _bt_enum!(buf, Ci, di, dsh, dinv, x, nz, 0, n, n, 0, true, bound)
  else
    Ci = Vector{Vector{Int128}}(undef, n)
    for i in 1:n
      Ci[i] = Int128[Int128(c) for c in C[i]]
    end
    di = Int128[Int128(t) for t in d]
    dsh = Int[trailing_zeros(di[i + 1]) for i in 1:n]
    dinv = Int128[_bt_oddinv(di[i + 1] >> dsh[i]) for i in 1:n]
    _bt_enum!(buf, Ci, di, dsh, dinv, x, nz, 0, n, n, Int128(0), true,
              Int128(bound))
  end
  nv = buf.nn
  V = Matrix{Int32}(undef, n, nv)
  co = buf.coords
  @inbounds for j in 1:nv
    for i in 1:n
      V[i, j] = co[(j - 1) * n + i]
    end
  end
  return V, buf.norms[1:nv]
end

################################################################################
#
#  The context
#
################################################################################

mutable struct BTCtx{T <: Signed}
  n::Int                    # rank
  G::Matrix{Int}            # Gram matrix, positive definite, integral
  bound::Int                # max_i G[i,i]
  nv::Int                   # number of short vectors up to sign
  V::Matrix{T}              # n x nv, column j = j-th short vector
  W::Matrix{T}              # n x nv, column j = G * V[:,j]
  Wt::Matrix{T}             # nv x n, Wt[j,i] = W[i,j]  (row access)
  nrm::Vector{Int}          # nrm[j] = V[:,j]*G*V[:,j]^t
  htab::Vector{Int32}       # hash table, entries are indices into V
  hmask::UInt64
  bidx::Vector{Int32}       # bidx[i] = signed index of the i-th basis vector
  maxv::Int                 # largest absolute coordinate of a short vector
  colors::Vector{UInt64}    # an isometry invariant colour of each short vector
                            # (empty if all vectors have the same colour)
  rhov::Vector{Int32}       # rhov[j] = <v_j, rho> for the Weyl vector rho, so
                            # that the search finds Aut(L, rho) and not
                            # Aut(L, {rho, -rho}); empty when there are no roots
  comps_ok::Bool            # whether the orthogonal decomposition was computed
  comp_sig::UInt64          # invariant of the whole decomposition
  ytmp::Vector{T}
  wtmp::Vector{T}
end

# A linear hash sum_i v[i]*R[i]: the summands are independent, so the loop
# vectorises, in contrast to the usual iterated-multiplication hashes.
const _BT_HASHR = let r = Vector{UInt64}(undef, 1024)
  x = 0x9e3779b97f4a7c15 % UInt64
  for i in 1:1024
    x = x * 6364136223846793005 + 1442695040888963407
    y = x
    y = xor(y, y >> 30) * 0xbf58476d1ce4e5b9
    y = xor(y, y >> 27) * 0x94d049bb133111eb
    y = xor(y, y >> 31)
    r[i] = y | 0x1
  end
  r
end

@inline function _bt_mix(h::UInt64)
  h = xor(h, h >> 33) * 0xff51afd7ed558ccd
  h = xor(h, h >> 33)
  return h
end

@inline function _bt_hash(v::AbstractVector{<:Signed})
  h = UInt64(0)
  R = _BT_HASHR
  @inbounds @simd for i in eachindex(v)
    h += (((v[i] % Int32) % UInt32) % UInt64) * R[i]
  end
  return _bt_mix(h)
end

@inline function _bt_hashcol(V::Matrix{<:Signed}, j::Int, n::Int)
  h = UInt64(0)
  R = _BT_HASHR
  @inbounds @simd for i in 1:n
    h += (((V[i, j] % Int32) % UInt32) % UInt64) * R[i]
  end
  return _bt_mix(h)
end

function _bt_build_hash!(ctx::BTCtx)
  nv = ctx.nv
  sz = 4
  while sz < 4 * nv
    sz *= 2
  end
  ctx.htab = zeros(Int32, sz)
  ctx.hmask = UInt64(sz - 1)
  n = ctx.n
  @inbounds for j in 1:nv
    h = _bt_hashcol(ctx.V, j, n)
    p = (h & ctx.hmask) % Int + 1
    while ctx.htab[p] != 0
      p = p == sz ? 1 : p + 1
    end
    ctx.htab[p] = Int32(j)
  end
  return ctx
end

# Look up the (signed) index of the vector `w`; returns 0 if it is not a short
# vector.  `w` is normalised in place (and restored).
function _bt_find(ctx::BTCtx{T}, w::Vector{T}) where {T}
  n = ctx.n
  s = 0
  @inbounds for i in n:-1:1
    if w[i] != 0
      s = w[i] > 0 ? 1 : -1
      break
    end
  end
  s == 0 && return 0
  if s < 0
    @inbounds for i in 1:n
      w[i] = -w[i]
    end
  end
  h = _bt_hash(w)
  sz = length(ctx.htab)
  p = (h & ctx.hmask) % Int + 1
  res = 0
  @inbounds while true
    j = ctx.htab[p]
    j == 0 && break
    eq = true
    for i in 1:n
      if ctx.V[i, j] != w[i]
        eq = false
        break
      end
    end
    if eq
      res = Int(j)
      break
    end
    p = p == sz ? 1 : p + 1
  end
  if s < 0
    @inbounds for i in 1:n
      w[i] = -w[i]
    end
  end
  return s * res
end

function BTCtx(G::Matrix{Int}, bound::Int = -1; comp_budget::Int = -1,
               force::Union{Nothing, DataType} = nothing)
  n = size(G, 1)
  @assert size(G, 2) == n
  n <= length(_BT_HASHR) || throw(BTOverflow())
  if bound < 0
    bound = 0
    for i in 1:n
      bound = max(bound, G[i, i])
    end
  end
  V, nrm = _bt_short_vectors(G, bound)
  nv = size(V, 2)
  # Overflow guard, part one: the entries of `W` are computed by accumulating
  # products V[k,j]*G[i,k] in Int32, so bound those before computing them.
  mv = 0; mg = 0
  @inbounds for j in 1:nv, i in 1:n
    mv = max(mv, abs(Int(V[i, j])))
  end
  for i in 1:n, j in 1:n
    mg = max(mg, abs(G[i, j]))
  end
  lim = div(typemax(Int32), 2)
  if n * mv * mg >= lim || n * mv * mv >= lim
    throw(BTOverflow())
  end
  G32 = Matrix{Int32}(undef, n, n)
  @inbounds for i in 1:n, k in 1:n
    G32[i, k] = Int32(G[i, k])
  end
  W = zeros(Int32, n, nv)
  @inbounds for j in 1:nv
    for k in 1:n
      c = V[k, j]
      if c != 0
        @simd for i in 1:n
          W[i, j] += c * G32[i, k]
        end
      end
    end
  end
  # the norms come out of the enumeration exactly; cross check them against the
  # scalar products, which are computed independently
  @hassert :Lattice 1 all(j -> nrm[j] == sum(Int(V[i, j]) * Int(W[i, j]) for i in 1:n),
                          1:nv)
  # Overflow guard for the Int32 arithmetic of the inner loops.  Every partial
  # sum occurring later is of one of the forms
  #     sum_i V[i,j]*W[i,k]   (scalar products),
  #     sum_l V[l,k]*M[l,i]   (applying an isometry, |M| <= mv),
  #     sum_k V[k,j]*G[i,k]   (the matrix W itself),
  # so bounding all three by `typemax(Int32)/2` proves that no Int32 operation
  # below can overflow.
  mw = 0
  @inbounds for j in 1:nv, i in 1:n
    mw = max(mw, abs(Int(W[i, j])))
  end
  if n * mv * mw >= lim
    throw(BTOverflow())
  end
  # The coordinates and their scalar products are stored in the narrowest
  # integer type that holds them.  Every sweep of the search reads these two
  # matrices, so halving their width halves the memory traffic of the whole
  # algorithm; the accumulators stay `Int32`, which the guard above bounds.
  if force !== nothing
    return _bt_ctx_finish(force, n, G, bound, nv, V, W, nrm, comp_budget)
  end
  if max(mv, mw) <= typemax(Int16)
    return _bt_ctx_finish(Int16, n, G, bound, nv, V, W, nrm, comp_budget)
  end
  return _bt_ctx_finish(Int32, n, G, bound, nv, V, W, nrm, comp_budget)
end

function _bt_ctx_finish(::Type{T}, n::Int, G::Matrix{Int}, bound::Int, nv::Int,
                        V32::Matrix{Int32}, W32::Matrix{Int32},
                        nrm::Vector{Int}, comp_budget::Int) where {T <: Signed}
  V = Matrix{T}(undef, n, nv)
  W = Matrix{T}(undef, n, nv)
  Wt = Matrix{T}(undef, nv, n)
  @inbounds for j in 1:nv, i in 1:n
    V[i, j] = T(V32[i, j])
    W[i, j] = T(W32[i, j])
  end
  @inbounds for i in 1:n, j in 1:nv
    Wt[j, i] = W[i, j]
  end
  mv = 0
  @inbounds for j in 1:nv, i in 1:n
    a = Int(V[i, j])
    a < 0 && (a = -a)
    a > mv && (mv = a)
  end
  ctx = BTCtx{T}(n, G, bound, nv, V, W, Wt, nrm, Int32[], UInt64(0), Int32[], mv,
                 UInt64[], Int32[], false, UInt64(0), Vector{T}(undef, n),
                 Vector{T}(undef, n))
  _bt_build_hash!(ctx)
  # locate the basis vectors (they are short unless the bound was lowered by
  # the caller, which only happens for the target of an isometry test, where
  # the indices are not used)
  bidx = zeros(Int32, n)
  w = Vector{T}(undef, n)
  for i in 1:n
    fill!(w, T(0))
    w[i] = T(1)
    bidx[i] = Int32(_bt_find(ctx, w))
  end
  ctx.bidx = bidx
  _bt_component_colors!(ctx, comp_budget)
  return ctx
end

# Connected components of the graph on the vectors listed in `idx`, where two
# vectors are joined if they are not orthogonal.  Returns the component index of
# every vector of `idx` and the members of each component, or `nothing` if the
# work budget was exceeded.  `work` is shared between calls.
function _bt_components(ctx::BTCtx, idx::Vector{Int32}, budget::Int,
                        work::Base.RefValue{Int})
  n = ctx.n
  nv = ctx.nv
  comp = zeros(Int32, nv)
  free = copy(idx)
  stack = Int32[]
  members = Vector{Vector{Int32}}()
  y = Vector{eltype(ctx.V)}(undef, n)
  @inbounds while !isempty(free)
    seed = pop!(free)
    push!(members, Int32[seed])
    c = Int32(length(members))
    comp[seed] = c
    empty!(stack)
    push!(stack, seed)
    while !isempty(stack)
      u = pop!(stack)
      _bt_load_y!(y, ctx, Int(u))
      work[] += length(free)
      work[] > budget && return nothing, members
      k = 0
      for t in 1:length(free)
        j = free[t]
        if _bt_dot(ctx.V, Int(j), y, n) != 0
          comp[j] = c
          push!(members[c], j)
          push!(stack, j)
        else
          k += 1
          free[k] = j
        end
      end
      resize!(free, k)
    end
  end
  return comp, members
end

@doc raw"""
    _bt_component_colors!(ctx::BTCtx)

For every norm `t` occurring among the short vectors, split the vectors of norm
at most `t` into the connected components of the graph in which two vectors are
joined if they are not orthogonal.  These components are the orthogonal
decomposition of the sublattice generated by the vectors of norm at most `t`,
hence an isometry invariant.  Every vector gets a colour recording the sizes and
norm distributions of the components it lies in, and the whole family gets a
signature `ctx.comp_sig`.

This sees things no count of short vectors can see.  The two even unimodular
lattices of rank 16 have the same theta series, so no shell count tells them
apart; but the sublattice generated by their 480 roots is `E8 + E8` in one case
and the indecomposable `D16` in the other, which the invariant does see.

`ctx.comps_ok` stays `false` if the graphs are so sparse that the search would
be more expensive than the rest of the computation; the invariant must then not
be used, since whether the bound is hit could depend on the numbering of the
vectors.
"""
function _bt_component_colors!(ctx::BTCtx, comp_budget::Int = -1)
  nv = ctx.nv
  nv == 0 && return ctx
  comp_budget == 0 && return ctx
  norms = sort(unique(ctx.nrm))
  # For a dense graph every sweep removes a large part of the vectors still to
  # be assigned, and the computation is linear in `nv`.  For a sparse one it
  # degenerates towards `nv^2`; that is worth paying for an isometry test, where
  # the invariant can save an enormous backtrack, but not for the automorphism
  # group, where the caller passes a small budget.
  # comp_budget: >= 0 an explicit budget, -1 the full one, -2 a cheap one which
  # only pays off on the dense graphs, where the sweep is linear in `nv`
  budget = comp_budget >= 0 ? comp_budget :
           comp_budget == -2 ? 8 * nv + 512 :
           max(64 * nv + 4096, min(nv * nv + nv, 8_000_000))
  work = Ref(0)
  colacc = fill(0x243f6a8885a308d3 % UInt64, nv)
  sig = 0x9e3779b97f4a7c15 % UInt64
  hist = Dict{Int, Int}()
  ks = Int[]
  for t in norms
    idx = Int32[j for j in 1:nv if ctx.nrm[j] <= t]
    comp, members = _bt_components(ctx, idx, budget, work)
    comp === nothing && return ctx
    nc = length(members)
    ccol = Vector{UInt64}(undef, nc)
    for c in 1:nc
      mem = members[c]
      empty!(hist)
      for j in mem
        hist[ctx.nrm[j]] = get(hist, ctx.nrm[j], 0) + 1
      end
      empty!(ks)
      append!(ks, keys(hist))
      sort!(ks)
      h = _bt_mix(UInt64(0x243f6a8885a308d3) + UInt64(length(mem)) * 0x9e3779b97f4a7c15)
      for k in ks
        h = _bt_mix(h + UInt64(k % UInt32) * 0xc2b2ae3d27d4eb4f)
        h = _bt_mix(h + UInt64(hist[k]) * 0x165667b19e3779f9)
      end
      ccol[c] = h
    end
    sig = _bt_mix(sig + UInt64(t % UInt32) * 0xff51afd7ed558ccd)
    for h in sort(ccol)
      sig = _bt_mix(sig + h)
    end
    @inbounds for j in idx
      colacc[j] = _bt_mix(colacc[j] + ccol[comp[j]])
    end
    # once everything is in one component, larger shells cannot split anything
    nc == 1 && length(idx) == nv && break
  end
  ctx.comps_ok = true
  ctx.comp_sig = sig
  if any(!isequal(colacc[1]), colacc)
    ctx.colors = colacc
  end
  return ctx
end

# scalar product of the short vector number `j` with the short vector with
# signed index `p`
@inline function _bt_sp(ctx::BTCtx, j::Int, p::Int)
  n = ctx.n
  V = ctx.V
  W = ctx.W
  k = p < 0 ? -p : p
  s = Int32(0)
  @inbounds @simd for i in 1:n
    s += V[i, j] * W[i, k]
  end
  return p < 0 ? -Int(s) : Int(s)
end

# fill y with (the sign adjusted) column of W belonging to the signed index p
@inline function _bt_load_y!(y::Vector{T}, ctx::BTCtx{T}, p::Int) where {T}
  n = ctx.n
  k = p < 0 ? -p : p
  W = ctx.W
  if p < 0
    @inbounds for i in 1:n
      y[i] = -W[i, k]
    end
  else
    @inbounds for i in 1:n
      y[i] = W[i, k]
    end
  end
  return y
end

# The accumulator is `Int32` for every supported width: the constructor bounds
# n * max|V| * max|W| by `typemax(Int32)/2`, so no partial sum can overflow.
# For `T == Int16` this is the pattern LLVM turns into a single widening
# multiply-add per 16 coordinates.
@inline function _bt_dot(V::Matrix{T}, j::Int, y::Vector{T}, n::Int) where {T <: Signed}
  s = Int32(0)
  @inbounds @simd for i in 1:n
    s += Int32(V[i, j]) * Int32(y[i])
  end
  return Int(s)
end
################################################################################
#
#  Fingerprint by partition refinement
#
################################################################################

# The items of the partition are
#     1 .. nv          the short vectors  v_1, ..., v_nv
#   nv+1 .. 2nv        their negatives   -v_1, ..., -v_nv
#  2nv+1 .. 2nv+n      the basis vectors  b_1, ..., b_n
#
# Two items lie in the same block after k refinement steps if and only if they
# have the same norm and the same scalar products with b_{per[1]},...,b_{per[k]}.
# Hence the block of the basis item b_i consists precisely of the short vectors
# which are possible images of b_i once b_{per[1]},...,b_{per[k]} are fixed.
#
# Blocks which contain no basis vector consist of short vectors which cannot be
# the image of any basis vector; they are discarded, which shrinks the partition
# quickly.

mutable struct BTFingerprint
  per::Vector{Int}
  fp::Matrix{Int}                # fp[k, i]: number of candidates for b_i after
                                 # k - 1 refinement steps
  fpd::Vector{Int}               # fpd[k] = fp[k, per[k]]
  order::Vector{Vector{Int32}}   # order[k]: items sorted blockwise after k-1 steps
  bs::Matrix{Int32}              # bs[k, i], be[k, i]: block of the basis item i
  be::Matrix{Int32}              #   inside order[k]
end

function _bt_fingerprint(ctx::BTCtx)
  n = ctx.n
  nv = ctx.nv
  G = ctx.G
  Wt = ctx.Wt
  nrm = ctx.nrm
  bound = ctx.bound

  # ---------------------------------------------------------------- initial
  # partition by the norm and the colour of a vector; only the classes which
  # occur for a basis vector can be hit at all, everything else is dropped
  hascol = !isempty(ctx.colors)
  bcol = zeros(UInt64, n)
  if hascol
    for i in 1:n
      k = abs(Int(ctx.bidx[i]))
      bcol[i] = ctx.colors[k]
    end
  end
  # The pairing with the Weyl vector is part of the class, and it changes sign
  # with the vector, so the two signs no longer share a class: an isometry
  # which respects the classes fixes rho instead of only fixing {rho, -rho}.
  hasrho = !isempty(ctx.rhov)
  brho = zeros(Int, n)
  if hasrho
    for i in 1:n
      p = Int(ctx.bidx[i])
      k = p < 0 ? -p : p
      brho[i] = p < 0 ? -Int(ctx.rhov[k]) : Int(ctx.rhov[k])
    end
  end
  ids = Dict{Tuple{Int, UInt64, Int}, Int}()
  bcls = zeros(Int, n)
  for i in 1:n
    key = (G[i, i], bcol[i], brho[i])
    c = get(ids, key, 0)
    if c == 0
      c = length(ids) + 1
      ids[key] = c
    end
    bcls[i] = c
  end
  nc = length(ids)
  # without colours a plain table replaces the lookup; the pairing with rho is
  # bounded, so it can be folded into the index
  rmax = 0
  if hasrho
    for j in 1:nv
      a = Int(ctx.rhov[j])
      a < 0 && (a = -a)
      a > rmax && (rmax = a)
    end
    for i in 1:n
      a = brho[i] < 0 ? -brho[i] : brho[i]
      a > rmax && (rmax = a)
    end
  end
  rwid = 2 * rmax + 1
  idbynorm = zeros(Int, (bound + 1) * rwid)
  if !hascol
    for i in 1:n
      idbynorm[G[i, i] * rwid + brho[i] + rmax + 1] = bcls[i]
    end
  end
  cnt = zeros(Int, nc)
  vclsp = zeros(Int32, nv)
  vclsm = zeros(Int32, nv)
  # The lookups are written out rather than put in a closure: a closure over
  # `rmax`, which is assigned in a loop above, is boxed and costs more than the
  # lookup itself on a lattice with a hundred thousand short vectors.
  if hasrho
    if hascol
      @inbounds for j in 1:nv
        rv = Int(ctx.rhov[j])
        cp = get(ids, (nrm[j], ctx.colors[j], rv), 0)
        cm = get(ids, (nrm[j], ctx.colors[j], -rv), 0)
        vclsp[j] = Int32(cp); vclsm[j] = Int32(cm)
        cp > 0 && (cnt[cp] += 1)
        cm > 0 && (cnt[cm] += 1)
      end
    else
      @inbounds for j in 1:nv
        rv = Int(ctx.rhov[j])
        base = nrm[j] * rwid + rmax + 1
        cp = (rv < -rmax || rv > rmax) ? 0 : idbynorm[base + rv]
        cm = (rv < -rmax || rv > rmax) ? 0 : idbynorm[base - rv]
        vclsp[j] = Int32(cp); vclsm[j] = Int32(cm)
        cp > 0 && (cnt[cp] += 1)
        cm > 0 && (cnt[cm] += 1)
      end
    end
  elseif hascol
    @inbounds for j in 1:nv
      c = get(ids, (nrm[j], ctx.colors[j], 0), 0)
      vclsp[j] = Int32(c); vclsm[j] = Int32(c)
      c > 0 && (cnt[c] += 2)
    end
  else
    # the two signs share a class here, which is one lookup instead of two
    @inbounds for j in 1:nv
      c = idbynorm[nrm[j] * rwid + rmax + 1]
      vclsp[j] = Int32(c); vclsm[j] = Int32(c)
      c > 0 && (cnt[c] += 2)
    end
  end
  for i in 1:n
    cnt[bcls[i]] += 1
  end
  N = sum(cnt)
  order = Vector{Int32}(undef, N)
  off = zeros(Int, nc)
  acc = 1
  for c in 1:nc
    off[c] = acc
    acc += cnt[c]
  end
  blkof = zeros(Int32, 2 * nv + n)
  bstart = Int32[]
  bstop = Int32[]
  for c in 1:nc
    if cnt[c] > 0
      push!(bstart, Int32(off[c]))
      push!(bstop, Int32(off[c] + cnt[c] - 1))
    end
  end
  # fill
  pos = copy(off)
  @inbounds for j in 1:nv
    c = Int(vclsp[j])
    if c > 0
      order[pos[c]] = Int32(j); pos[c] += 1
    end
    c = Int(vclsm[j])
    if c > 0
      order[pos[c]] = Int32(nv + j); pos[c] += 1
    end
  end
  @inbounds for i in 1:n
    c = bcls[i]
    order[pos[c]] = Int32(2 * nv + i); pos[c] += 1
  end
  b = 0
  @inbounds for c in 1:nc
    if cnt[c] > 0
      b += 1
      for t in off[c]:(off[c] + cnt[c] - 1)
        blkof[order[t]] = Int32(b)
      end
    end
  end

  per = zeros(Int, n)
  used = falses(n)
  fp = zeros(Int, n, n)
  fpd = zeros(Int, n)
  orders = Vector{Vector{Int32}}(undef, n)
  bs = zeros(Int32, n, n)
  be = zeros(Int32, n, n)

  vals = zeros(Int32, 2 * nv + n)
  tmp = Vector{Int32}(undef, N)
  ccnt = zeros(Int, 2 * bound + 1)
  nbas = Int[]

  for k in 1:n
    orders[k] = copy(order)
    nb = length(bstart)
    resize!(nbas, nb)
    fill!(nbas, 0)
    @inbounds for t in 1:N
      if order[t] > 2 * nv
        nbas[blkof[order[t]]] += 1
      end
    end
    @inbounds for i in 1:n
      bb = blkof[2 * nv + i]
      bs[k, i] = bstart[bb]
      be[k, i] = bstop[bb]
      fp[k, i] = (bstop[bb] - bstart[bb] + 1) - nbas[bb]
    end
    mi = 0
    for i in 1:n
      if !used[i] && (mi == 0 || fp[k, i] < fp[k, mi])
        mi = i
      end
    end
    per[k] = mi
    used[mi] = true
    fpd[k] = fp[k, mi]
    k == n && break

    # ------------------------------------------------------------- refine
    pk = mi
    @inbounds for t in 1:N
      it = order[t]
      if it <= nv
        vals[it] = Wt[it, pk]
      elseif it <= 2 * nv
        vals[it] = -Wt[it - nv, pk]
      else
        vals[it] = Int32(G[it - 2 * nv, pk])
      end
    end
    newstart = Int32[]
    newstop = Int32[]
    @inbounds for bb in 1:nb
      s0 = Int(bstart[bb])
      e0 = Int(bstop[bb])
      if s0 == e0
        push!(newstart, Int32(s0))
        push!(newstop, Int32(e0))
        continue
      end
      fill!(ccnt, 0)
      for t in s0:e0
        ccnt[vals[order[t]] + bound + 1] += 1
      end
      acc2 = s0
      for c in 1:(2 * bound + 1)
        if ccnt[c] > 0
          m = ccnt[c]
          ccnt[c] = acc2
          acc2 += m
        end
      end
      for t in s0:e0
        it = order[t]
        c = vals[it] + bound + 1
        tmp[ccnt[c]] = it
        ccnt[c] += 1
      end
      for t in s0:e0
        order[t] = tmp[t]
      end
      u = s0
      for t in (s0 + 1):(e0 + 1)
        if t == e0 + 1 || vals[order[t]] != vals[order[u]]
          push!(newstart, Int32(u))
          push!(newstop, Int32(t - 1))
          u = t
        end
      end
    end
    # ----------------------------------------- drop blocks without basis item
    nb2 = length(newstart)
    hasb = falses(nb2)
    @inbounds for bb in 1:nb2
      for t in newstart[bb]:newstop[bb]
        if order[t] > 2 * nv
          hasb[bb] = true
          break
        end
      end
    end
    bstart = Int32[]
    bstop = Int32[]
    w = 0
    @inbounds for bb in 1:nb2
      hasb[bb] || continue
      s0 = Int(newstart[bb]); e0 = Int(newstop[bb])
      push!(bstart, Int32(w + 1))
      for t in s0:e0
        w += 1
        tmp[w] = order[t]
      end
      push!(bstop, Int32(w))
    end
    N = w
    @inbounds for t in 1:N
      order[t] = tmp[t]
    end
    resize!(order, N)
    @inbounds for bb in 1:length(bstart)
      for t in bstart[bb]:bstop[bb]
        blkof[order[t]] = Int32(bb)
      end
    end
  end

  return BTFingerprint(per, fp, fpd, orders, bs, be)
end
# Verify, in exact arithmetic, that `M*G2*transpose(M) == G1`.  This is a
# certificate for the result: it is cheap (one matrix product per generator)
# and it does not rely on any invariant of the search.
function _bt_verify(M::Matrix{Int}, G2::Matrix{Int}, G1::Matrix{Int})
  n = size(M, 1)
  mv = 0; mg = 0
  @inbounds for i in 1:n, j in 1:n
    mv = max(mv, abs(M[i, j]))
    mg = max(mg, abs(G2[i, j]))
  end
  # (M*G2)[i,k] is a sum of n products of size mv*mg, and (M*G2*M^t)[i,l] a sum
  # of n products of that with an entry of M
  if mv == 0 || n * mv * mg <= div(typemax(Int), 2 * n * mv)
    T = zeros(Int, n, n)
    @inbounds for i in 1:n, k in 1:n
      t = 0
      for j in 1:n
        t += M[i, j] * G2[j, k]
      end
      T[i, k] = t
    end
    @inbounds for i in 1:n, l in 1:n
      t = 0
      for k in 1:n
        t += T[i, k] * M[l, k]
      end
      t == G1[i, l] || return false
    end
    return true
  end
  Mz = matrix(ZZ, n, n, [ZZRingElem(M[i, j]) for i in 1:n for j in 1:n])
  A = matrix(ZZ, n, n, [ZZRingElem(G2[i, j]) for i in 1:n for j in 1:n])
  B = matrix(ZZ, n, n, [ZZRingElem(G1[i, j]) for i in 1:n for j in 1:n])
  return Mz * A * transpose(Mz) == B
end

# the colours of the basis vectors, indexed by the basis
function _bt_basis_colors(ctx::BTCtx)
  isempty(ctx.colors) && return UInt64[]
  n = ctx.n
  res = zeros(UInt64, n)
  for i in 1:n
    k = abs(Int(ctx.bidx[i]))
    k == 0 && return UInt64[]
    res[i] = ctx.colors[k]
  end
  return res
end

################################################################################
#
#  Root system
#
################################################################################

# A vector `r` of `L` is a root when the reflection in it maps `L` to itself,
# that is when 2<x,r>/<r,r> is an integer for every `x` in `L`.  Writing `d` for
# the divisor of `r` -- the positive generator of the ideal of the <x,r> -- the
# norm <r,r> is either `d` or `2d`, and r/d lies in the dual, so `d` divides the
# exponent of the discriminant group.
#
# A root of divisor `d` therefore lies in
#
#     L  intersect  d L^*  =  { x : G x = 0 mod d },
#
# which is a *sublattice* of `L`: enumerating it up to norm 2d finds far fewer
# vectors than enumerating the dual, which is coarser than `L` and full of short
# vectors.  One Smith normal form gives a basis of all of them at once: with
# S = T G U the condition becomes (U^-1 x)_i = 0 mod d/gcd(S_ii, d).
#
# Roots of norm greater than two are what turns A_2 into G_2, D_4 into F_4 and
# Z^n into B_n, and they are the whole root system of a rescaled lattice such as
# E_8(2), where roots of norm two do not exist at all.
#
# Returns one representative of each pair {r, -r} with its norm, or `nothing`
# when the enumeration is out of range.
# Whether a vector is a root, and its norm, or `nothing`.  Only primitive
# vectors are considered: the reflection in r is the reflection in r/c for any
# scalar multiple, so a non primitive root adds nothing to the group, and
# dropping them is what keeps the system reduced -- a lattice can otherwise
# have both r and 2r as roots, and no irreducible type allows three lengths.
@inline function _bt_is_root(G::Matrix{Int}, x::Vector{Int}, n::Int)
  g = 0
  @inbounds for i in 1:n
    g = gcd(g, x[i])
  end
  g == 1 || return 0
  m = 0
  @inbounds for i in 1:n
    t = 0
    for k in 1:n
      t += G[i, k] * x[k]
    end
    m += t * x[i]
  end
  m > 0 || return 0
  @inbounds for i in 1:n
    t = 0
    for k in 1:n
      t += G[i, k] * x[k]
    end
    mod(2 * t, m) == 0 || return 0
  end
  return m
end

# The roots among vectors which have already been enumerated.  Every root of
# norm at most the bound of that enumeration is found, and that is all the
# decomposition needs: `Aut(L) = W' semidirect Stab(chamber)` holds for any
# subsystem which is closed under its own reflections and stable under
# `Aut(L)`, and the roots up to a norm bound are such a subsystem, because
# reflections preserve norms.  Stopping early therefore never costs
# correctness, only a smaller `W'` and more left for the search.
function _bt_roots_among(ctx::BTCtx)
  n = ctx.n
  V = ctx.V
  W = ctx.W                                        # W[:, j] = G * V[:, j]
  nrm = ctx.nrm
  res = Tuple{Vector{Int}, Int}[]
  @inbounds for j in 1:ctx.nv
    # the norm and the pairings with the basis are already there, so the test
    # is a few operations per vector instead of two matrix products
    m = nrm[j]
    m > 0 || continue
    g = 0
    for i in 1:n
      g = gcd(g, Int(V[i, j]))
      g == 1 && break
    end
    g == 1 || continue                             # only primitive roots
    ok = true
    for i in 1:n
      if mod(2 * Int(W[i, j]), m) != 0
        ok = false
        break
      end
    end
    ok || continue
    r = Vector{Int}(undef, n)
    for i in 1:n
      r[i] = Int(V[i, j])
    end
    for i in 1:n                                   # one of {r, -r}
      if r[i] != 0
        r[i] < 0 && (r .= .-r)
        break
      end
    end
    push!(res, (r, m))
  end
  return res
end

# Roots for the decomposition, given the short vectors the algorithm has
# enumerated anyway and the bound they go up to.  Those give every root of norm
# at most `bound` for one pass; the roots of larger norm, whose divisor `d`
# satisfies 2d > bound, need a sublattice each and are looked for only while
# the budget lasts.
#
# Stopping early is safe.  A set of roots picked out by norm and divisor is
# stable under `Aut(L)` -- isometries preserve both -- and closed under its own
# reflections, so it is a subsystem for which `W' semidirect Stab(chamber)` is
# still all of `Aut(L)`.  A smaller subsystem only leaves more for the search.
function _bt_roots(ctx::BTCtx; budget::Float64 = 0.001)
  n = ctx.n
  G = ctx.G
  bound = ctx.bound
  rts = _bt_roots_among(ctx)
  GZ = matrix(ZZ, n, n, [ZZRingElem(G[i, j]) for i in 1:n for j in 1:n])
  # Roots of norm above the bound need a sublattice each, which costs matrix
  # arithmetic over ZZ.  That is worth it when only a little is missing -- Z^n,
  # D_4 and D_5 owe their B_n, F_4 and C_5 to exactly one such norm -- and not
  # when the discriminant group is far bigger than the bound, where there are
  # many divisors to try and, on the lattices seen so far, nothing to find.
  # The determinant is a multiple of the exponent and much cheaper than either
  # the elementary divisors or the Smith form, so it decides this first.
  dt = abs(det(GZ))
  (dt <= 0 || !fits(Int, dt) || Int(dt) > 2 * bound) && return rts
  local S, U
  try
    S, _, U = snf_with_transform(GZ)
  catch
    return rts
  end
  e = S[n, n]
  (e <= 0 || !fits(Int, e)) && return rts
  2 * Int(e) <= bound && return rts               # nothing can be left
  seen = Set{Vector{Int}}()
  for (r, _) in rts
    push!(seen, r)
  end
  t0 = time()
  x = Vector{Int}(undef, n)
  for d in 1:Int(e)
    Int(e) % d == 0 || continue
    2 * d > bound || continue                     # already covered by the sweep
    time() - t0 > budget && break
    B = zero_matrix(ZZ, n, n)
    for j in 1:n
      c = divexact(ZZRingElem(d), gcd(S[j, j], ZZRingElem(d)))
      for i in 1:n
        B[i, j] = U[i, j] * c
      end
    end
    H = transpose(B) * GZ * B
    H, Tr = lll_gram_with_transform(H)             # the Smith basis is very skew
    B = B * transpose(Tr)
    all(y -> fits(Int, y), H) || continue
    local W, wn
    try
      W, wn = _bt_short_vectors(Matrix{Int}(H), 2 * d)
    catch
      continue
    end
    Bm = Matrix{Int}(B)
    for t in 1:size(W, 2)
      (wn[t] == d || wn[t] == 2 * d) || continue
      @inbounds for i in 1:n
        v = 0
        for k in 1:n
          v += Bm[i, k] * Int(W[k, t])
        end
        x[i] = v
      end
      m = _bt_is_root(G, x, n)
      m == 0 && continue
      r = copy(x)
      for i in 1:n
        if r[i] != 0
          r[i] < 0 && (r .= .-r)
          break
        end
      end
      r in seen && continue
      push!(seen, r)
      push!(rts, (r, m))
    end
  end
  return rts
end

function _bt_all_roots(G::Matrix{Int})
  n = size(G, 1)
  GZ = matrix(ZZ, n, n, [ZZRingElem(G[i, j]) for i in 1:n for j in 1:n])
  S, _, U = snf_with_transform(GZ)
  e = S[n, n]
  (e <= 0 || !fits(Int, e)) && return nothing
  res = Tuple{Vector{Int}, Int}[]
  seen = Set{Vector{Int}}()
  x = Vector{Int}(undef, n)
  for d in 1:Int(e)
    Int(e) % d == 0 || continue
    # basis of { x : G x = 0 mod d }, as columns
    B = zero_matrix(ZZ, n, n)
    for j in 1:n
      c = divexact(ZZRingElem(d), gcd(S[j, j], ZZRingElem(d)))
      for i in 1:n
        B[i, j] = U[i, j] * c
      end
    end
    H = transpose(B) * GZ * B
    # the basis coming out of the Smith form is very skew, which would make the
    # enumeration tree enormous; reducing it first is what keeps this cheap
    H, Tr = lll_gram_with_transform(H)
    B = B * transpose(Tr)
    all(y -> fits(Int, y), H) || return nothing
    local V, nrm
    try
      V, nrm = _bt_short_vectors(Matrix{Int}(H), 2 * d)
    catch
      return nothing
    end
    Bm = Matrix{Int}(B)
    for t in 1:size(V, 2)
      m = nrm[t]
      (m == d || m == 2 * d) || continue          # <r,r> is d or 2d
      @inbounds for i in 1:n
        v = 0
        for k in 1:n
          v += Bm[i, k] * Int(V[k, t])
        end
        x[i] = v
      end
      # the defining condition, checked exactly on the basis of L
      ok = true
      @inbounds for i in 1:n
        g = 0
        for k in 1:n
          g += G[i, k] * x[k]
        end
        if mod(2 * g, m) != 0
          ok = false
          break
        end
      end
      ok || continue
      # The reflection in r is the reflection in r/c for any scalar multiple, so
      # a non primitive root contributes nothing new -- and dropping those is
      # what makes the system reduced: without it a lattice can have both r and
      # 2r as roots (norms 2 and 8), which no irreducible type allows.
      g = 0
      @inbounds for i in 1:n
        g = gcd(g, x[i])
      end
      g == 1 || continue
      r = copy(x)
      for i in 1:n                                 # one of {r, -r}
        if r[i] != 0
          r[i] < 0 && (r .= .-r)
          break
        end
      end
      r in seen && continue
      push!(seen, r)
      push!(res, (r, m))
    end
  end
  return res
end

# The type of an irreducible root system is fixed by its rank, its number of
# roots and how many of them are short.  Whether there are two root lengths has
# to be asked first: B_6 and C_6 have as many roots as E_6, and B_2 as many as
# A_1 + A_1 would if it were irreducible, so testing the simply laced shapes
# first misreads them.
function _bt_irr_type(k::Int, nroots::Int, nshort::Int)
  k == 1 && return (:A, 1)
  if nshort == nroots                              # one root length
    nroots == k * (k + 1) && return (:A, k)
    k >= 4 && nroots == 2 * k * (k - 1) && return (:D, k)
    k == 6 && nroots == 72 && return (:E, 6)
    k == 7 && nroots == 126 && return (:E, 7)
    k == 8 && nroots == 240 && return (:E, 8)
    return (:unknown, k)
  end
  k == 2 && nroots == 12 && return (:G, 2)
  k == 4 && nroots == 48 && return (:F, 4)
  nroots == 2 * k * k && return nshort == 2 * k ? (:B, k) : (:C, k)
  return (:unknown, k)
end

# Simple roots, the types of the components, the order of the Weyl group and a
# vector fixed by everything which preserves the chamber.
#
# Taking the representative of each pair {r, -r} whose first non zero
# coordinate is positive is a choice of positive system: that is the
# lexicographic order, which is a linear order compatible with addition.  The
# sum of the positive coroots is then 2*rho^, and a positive root is simple
# exactly when its pairing with it is 2; everything is scaled by the least
# common multiple of the root norms to keep it integral.
#
# `nothing` when the roots are out of range or a component is not recognised.
# The reflection in the root `r` of norm `m`, as a matrix acting on coordinate
# rows: b_i goes to b_i - (2<b_i,r>/m) r, integral because r is a root.
# The stabiliser of the chamber permutes the simple roots, so the multiset of
# the scalar products of a short vector with them does not depend on which
# permutation, only on the vector: it is an invariant of everything the search
# is still looking for, and it is far finer than the pairing with rho alone,
# which only records the sum.
#
# Colours are compared without regard to sign, so the multiset of `v` and the
# negated one of `-v` are folded together by taking the smaller of the two.
function _bt_root_colors!(ctx::BTCtx, simple::Vector{Vector{Int}})
  n = ctx.n
  nv = ctx.nv
  ns = length(simple)
  (ns == 0 || nv == 0) && return ctx
  # G * a for each simple root, so that a pairing is one dot product
  ga = [Int[sum(ctx.G[i, k] * a[k] for k in 1:n) for i in 1:n] for a in simple]
  old = ctx.colors
  cols = Vector{UInt64}(undef, nv)
  @inbounds for j in 1:nv
    # The first three power sums do not depend on the order of the terms, so
    # they describe the multiset without sorting it, and they cost three
    # multiplications where hashing every term cost a hash.  The pairings are
    # bounded by the norms, so nothing here can grow.
    p1 = 0; p2 = 0; p3 = 0
    for t in 1:ns
      s = 0
      gat = ga[t]
      for i in 1:n
        s += Int(ctx.V[i, j]) * gat[i]
      end
      p1 += s
      p2 += s * s
      p3 += s * s * s
    end
    # negating the vector negates the odd power sums; fixing their sign makes
    # the colour the same for v and -v, which is how colours are compared
    if p1 < 0 || (p1 == 0 && p3 < 0)
      p1 = -p1
      p3 = -p3
    end
    cols[j] = hash(p1, hash(p2, hash(p3, isempty(old) ? UInt64(0) : old[j])))
  end
  ctx.colors = cols
  return ctx
end

function _bt_reflection(G::Matrix{Int}, r::Vector{Int}, m::Int)
  n = size(G, 1)
  M = zeros(Int, n, n)
  @inbounds for i in 1:n
    t = 0
    for k in 1:n
      t += G[i, k] * r[k]
    end
    f = div(2 * t, m)
    for j in 1:n
      M[i, j] = (i == j ? 1 : 0) - f * r[j]
    end
  end
  return M
end

function _bt_root_data(G::Matrix{Int})
  rts = _bt_all_roots(G)
  rts === nothing && return nothing
  return _bt_root_data(G, rts)
end

function _bt_root_data(G::Matrix{Int}, rts::Vector{Tuple{Vector{Int}, Int}})
  n = size(G, 1)
  isempty(rts) && return (types = Tuple{Symbol, Int}[], worder = one(ZZRingElem),
                          rho = zeros(Int, n), simple = Vector{Int}[])
  K = 2
  for (_, m) in rts
    K = lcm(K, 2 * m)
  end
  w = zeros(Int, n)                                # K * rho^
  for (r, m) in rts
    f = div(K, m)
    for i in 1:n
      w[i] += f * r[i]
    end
  end
  wd = zeros(Int, n)                               # G * w
  for i in 1:n
    t = 0
    for k in 1:n
      t += G[i, k] * w[k]
    end
    wd[i] = t
  end
  simple = Vector{Int}[]
  snorm = Int[]
  for (r, m) in rts
    t = 0
    for i in 1:n
      t += wd[i] * r[i]
    end
    if t == K
      push!(simple, r); push!(snorm, m)
    elseif t == -K
      push!(simple, .-r); push!(snorm, m)
    end
  end
  isempty(simple) && return nothing
  ns = length(simple)
  # the components: simple roots are joined when they are not orthogonal
  sd = [Int[sum(G[i, k] * a[k] for k in 1:n) for i in 1:n] for a in simple]
  comp = zeros(Int, ns)
  nc = 0
  stack = Int[]
  for i in 1:ns
    comp[i] != 0 && continue
    nc += 1; comp[i] = nc; push!(stack, i)
    while !isempty(stack)
      a = pop!(stack)
      for b in 1:ns
        comp[b] == 0 || continue
        t = 0
        for k in 1:n
          t += sd[a][k] * simple[b][k]
        end
        t == 0 && continue
        comp[b] = nc; push!(stack, b)
      end
    end
  end
  types = Tuple{Symbol, Int}[]
  for c in 1:nc
    inc = Int[]                                    # the roots of this component
    for (t, (r, m)) in enumerate(rts)
      # the components are mutually orthogonal, so a root belongs to this one
      # exactly when it is orthogonal to every simple root outside it
      out = false
      for b in 1:ns
        comp[b] == c && continue
        s = 0
        for k in 1:n
          s += sd[b][k] * r[k]
        end
        if s != 0
          out = true
          break
        end
      end
      out || push!(inc, t)
    end
    isempty(inc) && return nothing
    mn = minimum(rts[t][2] for t in inc)
    nshort = 2 * count(t -> rts[t][2] == mn, inc)
    ty = _bt_irr_type(count(==(c), comp), 2 * length(inc), nshort)
    ty[1] === :unknown && return nothing
    push!(types, ty)
  end
  sort!(types)
  return (types = types, worder = _weyl_group_order(types), rho = w, simple = simple)
end

################################################################################
#
#  Spheres around a short vector
#
################################################################################

# The value `t` for which the "sphere"
#
#     S(p) = { w short : <w, p> = t }
#
# around the short vector `p` is smallest, together with its size.  An isometry
# maps S(p) onto S(g(p)), so restricting a test to that sphere costs |S(p)|
# instead of |V| per sweep and keeps it a necessary condition.
function _bt_sphere_value(ctx::BTCtx, p::Int)
  n = ctx.n
  nv = ctx.nv
  y = _bt_load_y!(ctx.ytmp, ctx, p)
  cnt = zeros(Int, 2 * ctx.bound + 1)
  @inbounds for j in 1:nv
    sp = _bt_dot(ctx.V, j, y, n)
    (sp < -ctx.bound || sp > ctx.bound) && continue
    cnt[sp + ctx.bound + 1] += 1
    cnt[-sp + ctx.bound + 1] += 1
  end
  # the smallest non empty sphere with a positive scalar product, excluding the
  # vector itself
  best = 0
  bestc = typemax(Int)
  nrmp = ctx.nrm[abs(p)]
  for c in 1:(ctx.bound)
    c == nrmp && continue
    if 0 < cnt[c + ctx.bound + 1] < bestc
      bestc = cnt[c + ctx.bound + 1]
      best = c
    end
  end
  return best, bestc
end

################################################################################
#
#  Scalar product combinations ("vector sums")
#
################################################################################

# The pruning by scalar products alone only ever looks at one candidate at a
# time, so a partial map which is consistent but does not extend is only found
# out deep in the search, and the subtree below it can be astronomically large.
# The following global test rules such a partial map out in one sweep over the
# short vectors, and usually even produces the isometry outright.
#
# Fix `dep` base vectors.  Every short vector `w` has a signature
#
#     sigma(w) = (<w, b_{per[1]}>, ..., <w, b_{per[dep]}>)
#
# and an isometry `g` with `g(b_{per[k]}) = x_k` maps the vectors of signature
# `s` bijectively onto the vectors `w'` with `(<w',x_1>,...,<w',x_dep>) = s`.
# Hence it maps the *sum* of the former onto the sum of the latter.  Collect
# those sums into a matrix `A` (one row per signature) and write `A = U^-1 * H`
# with `H = U*A` in Hermite normal form.  If `A` has rank `n`, the first `n`
# rows `B` of `H` are a basis of the lattice generated by the sums, and
#
#     B' := trans * A'     (trans = the first n rows of U)
#
# is what `g` must do to `B`.  Two integral identities must then hold, namely
# `B' * G * transpose(B') == B * G * transpose(B)` and `coef * B' == A'`; if one
# of them fails, no isometry extends the partial map.  If they hold, `B -> B'`
# already determines a candidate for `g`, which is checked directly, so that the
# whole subtree collapses into this single sweep.
mutable struct BTCombs
  dep::Int                   # how many base vectors the signature uses
  first::Int                 # signature uses x_first, ..., x_{first+dep-1}
  rlevel::Int                # 0, or the level whose class the test is restricted to
  rvalue::Int                # the scalar product defining that class
  nsig::Int
  radix::Int
  shift::Int
  packmax::Int
  sigof::Vector{Int32}       # packed signature -> class index (0: does not occur)
  negof::Vector{Int32}       # class index of the negated signature
  csize::Vector{Int}         # number of source vectors in each class
  srcsum::Matrix{Int32}      # n x nsig, the class sums of the source
  Q::Matrix{Int}             # nsig x nsig, Gram matrix of the class sums
  spans::Bool                # whether the class sums span the whole space
  piv::Vector{Int}           # n classes whose sums are linearly independent
  prime::Int                 # a prime for the modular solve
  Binv::Matrix{Int}          # inverse of the matrix of those sums, mod prime
  asum::Matrix{Int32}        # n x nsig scratch
  gsum::Matrix{Int}          # n x nsig scratch, G * asum
  Qt::Matrix{Int}            # nsig x nsig scratch
  rpow::Int                  # radix^(dep - 1): the weight of the last digit
  corder::Vector{Int}        # classes by increasing size: the cheapest test first
  cls::Vector{Int32}         # scratch: class of every vector of the class
  ccnt::Vector{Int}          # scratch: class sizes of the image
  cptr::Vector{Int}          # scratch: start of every class in `cord`
  cpos::Vector{Int}          # scratch
  cord::Vector{Int32}        # scratch: the class vectors grouped by class
end

@inline function _bt_pack(v::AbstractVector{Int}, radix::Int, shift::Int, dep::Int)
  k = 0
  @inbounds for t in dep:-1:1
    k = k * radix + (v[t] + shift)
  end
  return k
end

# Gram matrix of the columns of `A` with respect to `G`, using `GA` as scratch
function _bt_sums_gram!(Q::Matrix{Int}, GA::Matrix{Int}, A::Matrix{Int32},
                        G::Matrix{Int}, n::Int, m::Int)
  @inbounds for c in 1:m
    for i in 1:n
      t = 0
      for k in 1:n
        t += G[i, k] * Int(A[k, c])
      end
      GA[i, c] = t
    end
  end
  @inbounds for c in 1:m
    for d in c:m
      t = 0
      for i in 1:n
        t += Int(A[i, c]) * GA[i, d]
      end
      Q[c, d] = t
      Q[d, c] = t
    end
  end
  return Q
end

# `true` if the Gram matrix of the columns of `A` equals `Q`; stops at the
# first difference, which is what happens for almost every rejected candidate
function _bt_sums_gram_eq(Q::Matrix{Int}, GA::Matrix{Int}, A::Matrix{Int32},
                          G::Matrix{Int}, n::Int, m::Int)
  # the column G * A[:, d] is only needed once the first d - 1 columns have
  # matched, and almost every candidate is rejected within the first few, so
  # the product is done column by column instead of in one go
  @inbounds for d in 1:m
    for i in 1:n
      t = 0
      for k in 1:n
        t += G[i, k] * Int(A[k, d])
      end
      GA[i, d] = t
    end
    for c in 1:d
      t = 0
      for i in 1:n
        t += Int(A[i, c]) * GA[i, d]
      end
      t == Q[c, d] || return false
    end
  end
  return true
end

# Build the combination data for the base vectors b_{per[first]}, ...,
# b_{per[first+dep-1]}, or `nothing` if the sums do not span the whole space
# (the test is then useless), if the signatures do not fit, or if the machine
# integer arithmetic could overflow.
function _bt_combs(ctx::BTCtx, per::Vector{Int}, first::Int, dep::Int;
                   rlevel::Int = 0, rvalue::Int = 0)
  n = ctx.n
  nv = ctx.nv
  shift = ctx.bound
  radix = 2 * ctx.bound + 1
  packmax = radix^dep
  (packmax <= 0 || packmax > 1 << 22) && return nothing
  sigof = zeros(Int32, packmax)
  negl = Int32[]
  sig = Vector{Int}(undef, dep)
  nsig = 0
  # the signed vectors the test runs over: everything, or only those in the
  # class of the level `rlevel`, which makes a sweep cost |class| instead of |V|
  sel = Vector{Int32}(undef, 2 * nv)
  ns = 0
  if rlevel == 0
    @inbounds for j in 1:nv
      sel[ns + 1] = Int32(j)
      sel[ns + 2] = Int32(-j)
      ns += 2
    end
  else
    q = per[rlevel]
    @inbounds for j in 1:nv
      w = Int(ctx.Wt[j, q])
      if w == rvalue
        ns += 1
        sel[ns] = Int32(j)
      end
      if -w == rvalue
        ns += 1
        sel[ns] = Int32(-j)
      end
    end
  end
  ns == 0 && return nothing
  resize!(sel, ns)
  @inbounds for uu in sel
    u = Int(uu)
    j = u > 0 ? u : -u
    sgn = u > 0 ? 1 : -1
    for t in 1:dep
      sig[t] = sgn * Int(ctx.Wt[j, per[first + t - 1]])
    end
    k = _bt_pack(sig, radix, shift, dep) + 1
    if sigof[k] == 0
      nsig += 1
      sigof[k] = Int32(nsig)
      push!(negl, Int32(nsig))
    end
  end
  # the Gram matrix of the sums costs nsig^2 scalar products per node
  (nsig < 2 || nsig > 1024) && return nothing
  # overflow bound for the Gram matrix of the sums
  mv = ctx.maxv
  mg = 0
  for i in 1:n, j in 1:n
    mg = max(mg, abs(ctx.G[i, j]))
  end
  # |Q| <= n^2 * mg * (nv*mv)^2 must fit into an Int with room to spare
  ma = ZZRingElem(nv) * mv
  ZZRingElem(n)^2 * mg * ma^2 < div(typemax(Int), 4) || return nothing
  A = zeros(Int, n, nsig)
  csize = zeros(Int, nsig)
  @inbounds for uu in sel
    u = Int(uu)
    j = u > 0 ? u : -u
    sgn = u > 0 ? 1 : -1
    for t in 1:dep
      sig[t] = sgn * Int(ctx.Wt[j, per[first + t - 1]])
    end
    c = Int(sigof[_bt_pack(sig, radix, shift, dep) + 1])
    csize[c] += 1
    for i in 1:n
      A[i, c] += sgn * Int(ctx.V[i, j])
    end
  end
  ma2 = 0
  for c in 1:nsig, i in 1:n
    ma2 = max(ma2, abs(A[i, c]))
  end
  ma2 < div(typemax(Int32), 2) || return nothing
  A32 = Matrix{Int32}(undef, n, nsig)
  for c in 1:nsig, i in 1:n
    A32[i, c] = Int32(A[i, c])
  end
  Q = zeros(Int, nsig, nsig)
  GA = zeros(Int, n, nsig)
  _bt_sums_gram!(Q, GA, A32, ctx.G, n, nsig)
  # If the sums span, n of them determine the isometry and the test becomes
  # decisive; if they do not, the Gram matrix of the sums is still a necessary
  # condition, and a very effective one.
  piv = Int[]
  spans = false
  if nsig >= n
    Aq = matrix(QQ, n, nsig, [QQFieldElem(A[i, c]) for i in 1:n for c in 1:nsig])
    r = 0
    work = zero_matrix(QQ, n, 0)
    for c in 1:nsig
      cand = hcat(work, Aq[:, c:c])
      if rank(cand) > r
        r += 1
        push!(piv, c)
        work = cand
        r == n && break
      end
    end
    spans = (r == n)
  end
  # The linear map is recovered by a solve modulo a prime: its entries are
  # coordinates of short vectors, hence tiny, so the symmetric lift of the
  # modular solution is the exact map -- and whatever comes out is verified
  # exactly afterwards, so the modulus can never make the result wrong.
  prime = 2147483647
  Binv = zeros(Int, 0, 0)
  if spans
    B = _bt_inv_mod(A, piv, n, prime)
    if B === nothing
      spans = false
    else
      Binv = B
    end
  end
  return BTCombs(dep, first, rlevel, rvalue, nsig, radix, shift, packmax, sigof,
                 negl, csize, A32, Q, spans, piv, prime, Binv,
                 zeros(Int32, n, nsig), zeros(Int, n, nsig),
                 zeros(Int, nsig, nsig), radix^(dep - 1), sortperm(csize), Int32[],
                 zeros(Int, nsig), zeros(Int, nsig + 1), zeros(Int, nsig),
                 Int32[])
end

# inverse of the n x n matrix with rows A[:, piv[t]] modulo the prime `p`
function _bt_inv_mod(A::Matrix{Int}, piv::Vector{Int}, n::Int, p::Int)
  M = zeros(Int, n, 2 * n)
  @inbounds for t in 1:n
    c = piv[t]
    for i in 1:n
      M[t, i] = mod(A[i, c], p)
    end
    M[t, n + t] = 1
  end
  @inbounds for col in 1:n
    r = 0
    for t in col:n
      if M[t, col] != 0
        r = t
        break
      end
    end
    r == 0 && return nothing
    if r != col
      for j in 1:(2 * n)
        M[col, j], M[r, j] = M[r, j], M[col, j]
      end
    end
    iv = invmod(M[col, col], p)
    for j in 1:(2 * n)
      M[col, j] = mod(M[col, j] * iv, p)
    end
    for t in 1:n
      t == col && continue
      f = M[t, col]
      f == 0 && continue
      for j in 1:(2 * n)
        M[t, j] = mod(M[t, j] - f * M[col, j], p)
      end
    end
  end
  R = zeros(Int, n, n)
  @inbounds for i in 1:n, j in 1:n
    R[i, j] = M[i, n + j]
  end
  return R
end

################################################################################
#
#  The backtrack search
#
################################################################################

# `poolv[d + 1]` holds the short vectors which can still be the image of at
# least one of the basis vectors b_{per[I]}, I > d, once the images
# x[1], ..., x[d] are fixed.  `poolp` and `poolm` hold, for the vector and its
# negative, the bit mask of the levels I for which it is still possible.

mutable struct BTSearch{T <: Signed}
  n::Int
  nw::Int                          # number of UInt64's per level mask
  tgt::BTCtx{T}
  per::Vector{Int}
  src::BTCtx{T}                    # source context (equal to tgt for Aut)
  Gsrc::Matrix{Int}                # Gram matrix of the source
  TS::Matrix{Int}                  # TS[I, k] = <b_{per[I]}, b_{per[k]}> (source)
  TN::Vector{Int}                  # TN[I] = <b_{per[I]}, b_{per[I]}> (source)
  fp::Matrix{Int}                  # fingerprint of the source
  fpd::Vector{Int}
  TC::Vector{UInt64}               # TC[I]: colour of b_{per[I]} in the source
  TR::Vector{Int}                  # TR[I] = <b_{per[I]}, rho> in the source
  x::Vector{Int}                   # signed indices of the current images
  poolv::Vector{Vector{Int32}}
  poolp::Vector{Vector{UInt64}}
  poolm::Vector{Vector{UInt64}}
  plen::Vector{Int}
  cand::Vector{Vector{Int32}}
  vals::Vector{Vector{Int}}        # vals[k]: distinct values of TS[I, k], I > k
  vmask::Vector{Vector{UInt64}}    # vmask[k]: nw words per entry of vals[k]
  ytmp::Vector{T}
  wa::Vector{UInt64}
  wb::Vector{UInt64}
  clearw::Vector{UInt64}
  cnts::Vector{Int}
  nodes::Int
  lookahead::Int
  combs::Vector{Union{Nothing, BTCombs}}   # combs[d]: test after fixing x_1..x_d
  sigtmp::Vector{Int}
  spd::Vector{Vector{Int32}}               # spd[k]: <v_j, x_k> for all j
  spdx::Vector{Int}                        # which x_k the cache belongs to
  ycols::Vector{Vector{T}}                 # scratch: one n-vector per depth
  clsidx::Vector{Int32}                    # signed indices of the restricting class
  clsV::Matrix{T}                          # their coordinates, sign applied
  clsfor::Int                              # the image the class was built for
  clsval::Int
  usecombs::Bool                           # whether the test is switched on
  maxlevel::Int                            # levels above this are never reached
  step::Int                                # first level of the current step
  usepool::Bool                            # pool sweep, or per level filtering
  pfx::Vector{Vector{Int32}}               # per level: packed signature of the
  pfxx::Vector{Vector{Int}}                #   images which are fixed there,
  pfxgen::Vector{Int}                      #   and what it was built for
  pfxok::Vector{Bool}
  clsgen::Int                              # bumped whenever the class changes
  bkt::Vector{Vector{Int32}}               # short vectors by <., x_step>
  bktfor::Int                              # the image the buckets belong to
  yk::Vector{Vector{T}}                    # yk[k] = G * x_k, for the dot products
  ykfor::Vector{Int}
  combsdone::Vector{Bool}                  # which levels have been built
  combsrval::Int                           # class value used for the restriction
  combsmaxdep::Int
  work::Int                                # vectors looked at, for the same purpose
  worklimit::Int
  nodelimit::Int
  aborted::Bool
  solved::Bool
  solution::Matrix{Int}
end

@inline _bt_word(I::Int) = (I - 1) >> 6 + 1
@inline _bt_bit(I::Int) = UInt64(1) << ((I - 1) & 63)

function BTSearch(tgt::BTCtx{T}, per::Vector{Int}, Gsrc::Matrix{Int},
                  fp::Matrix{Int}, fpd::Vector{Int},
                  bcolors::Vector{UInt64} = UInt64[]; lookahead::Int = 2,
                  src::BTCtx{T} = tgt) where {T <: Signed}
  n = tgt.n
  nw = cld(n, 64)
  TS = zeros(Int, n, n)
  TN = zeros(Int, n)
  TC = zeros(UInt64, n)
  TR = zeros(Int, n)
  if !isempty(src.rhov)
    for I in 1:n
      p = Int(src.bidx[per[I]])
      k = p < 0 ? -p : p
      TR[I] = p < 0 ? -Int(src.rhov[k]) : Int(src.rhov[k])
    end
  end
  if !isempty(bcolors)
    for I in 1:n
      TC[I] = bcolors[per[I]]
    end
  end
  for I in 1:n
    TN[I] = Gsrc[per[I], per[I]]
    for k in 1:n
      TS[I, k] = Gsrc[per[I], per[k]]
    end
  end
  vals = Vector{Vector{Int}}(undef, n)
  vmask = Vector{Vector{UInt64}}(undef, n)
  for k in 1:n
    vv = Int[]
    for I in (k + 1):n
      TS[I, k] in vv || push!(vv, TS[I, k])
    end
    mm = zeros(UInt64, nw * length(vv))
    for (a, v) in enumerate(vv)
      for I in (k + 1):n
        if TS[I, k] == v
          mm[(a - 1) * nw + _bt_word(I)] |= _bt_bit(I)
        end
      end
    end
    vals[k] = vv
    vmask[k] = mm
  end
  poolv = [Int32[] for _ in 1:(n + 1)]
  poolp = [UInt64[] for _ in 1:(n + 1)]
  poolm = [UInt64[] for _ in 1:(n + 1)]
  cand = [Int32[] for _ in 1:(n + 1)]
  return BTSearch{T}(n, nw, tgt, per, src, Gsrc, TS, TN, fp, fpd, TC, TR,
                  zeros(Int, n), poolv,
                  poolp, poolm, zeros(Int, n + 1), cand, vals, vmask,
                  Vector{T}(undef, n), zeros(UInt64, nw), zeros(UInt64, nw),
                  zeros(UInt64, nw), zeros(Int, n + 1), 0, lookahead,
                  Union{Nothing, BTCombs}[nothing for _ in 1:n], Int[],
                  [Int32[] for _ in 1:n], zeros(Int, n),
                  [zeros(T, n) for _ in 1:8], Int32[],
                  zeros(T, n, 0),
                  0, 0,
                  false,                                   # usecombs
                  n,                                       # maxlevel
                  1,                                       # step
                  true,                                    # usepool
                  [Int32[] for _ in 1:n],                  # pfx
                  [zeros(Int, n) for _ in 1:n],            # pfxx
                  fill(-1, n),                             # pfxgen
                  falses(n),                               # pfxok
                  0,                                       # clsgen
                  [Int32[] for _ in 1:(2 * tgt.bound + 1)], # bkt
                  0,                                       # bktfor
                  [zeros(T, n) for _ in 1:n],              # yk
                  zeros(Int, n),                           # ykfor
                  falses(n),                               # combsdone
                  0,                                       # combsrval
                  3,                                       # combsmaxdep
                  0,                                       # work
                  typemax(Int),                            # worklimit
                  typemax(Int),                            # nodelimit
                  false,                                   # aborted
                  false,                                   # solved
                  zeros(Int, 0, 0))                        # solution
end

# Prepare the scalar product combination test for every level.  `dep` is the
# number of base vectors a signature uses; the smallest one for which the sums
# span is used, since a smaller `dep` means the test bites earlier.
function _bt_setup_combs!(S::BTSearch, ctx::BTCtx; maxdep::Int = 3,
                          budget::Float64 = Inf)
  n = S.n
  # the value defining the smallest class of the first base vector; restricting
  # the test to that class makes a sweep cost |class| instead of |V|
  p1 = Int(ctx.bidx[S.per[1]])
  S.combsrval = p1 == 0 ? 0 : _bt_sphere_value(ctx, p1)[1]
  S.combsmaxdep = maxdep
  S.sigtmp = zeros(Int, max(1, maxdep))
  for k in 1:n
    S.spd[k] = zeros(Int32, S.tgt.nv)
  end
  fill!(S.spdx, 0)
  fill!(S.combsdone, false)
  # Where the class sums span, the test is decisive: it either produces the
  # isometry or rules the partial map out, so the search never descends below
  # that level.  Levels beyond it (and beyond the last branching level, which
  # the outer loop still visits) therefore never have to be carried along in
  # the pool, which is what the descent pays for.
  dlast = 1
  for d in 1:n
    S.fpd[d] > 1 && (dlast = d)
  end
  # Looking for the level where they span costs one full test per level, which
  # for a lattice whose short vectors do not span at all is spent for nothing:
  # no level spans and `maxlevel` ends up being `n` anyway.  Since the answer
  # is only used through `max(dspan, dlast)`, a level beyond `dlast` is worth
  # probing only while it is still cheap, so the search stops there.
  dspan = 0
  t0 = time()
  for d in 1:min(n, max(dlast, 2))
    c = _bt_combs_at!(S, d)
    if c !== nothing && c.spans
      dspan = d
      break
    end
    # the answer is worth no more than the search which asked for it
    d >= 2 && time() - t0 > budget && break
  end
  S.maxlevel = dspan == 0 ? n : max(dspan, dlast)
  @vprintln :Lattice 1 "backtrack: combinations decisive from level $(dspan), tracking $(S.maxlevel) of $(n) levels"
  return S
end

# The combination data of a level is only built when that level is first
# reached: on a lattice with many levels most of them are never used, and each
# one costs a sweep over the short vectors to set up.
function _bt_combs_at!(S::BTSearch, d::Int)
  @inbounds S.combsdone[d] && return S.combs[d]
  ctx = S.src
  maxdep = S.combsmaxdep
  best = nothing
  # The signature of depth `dep` uses the levels d - dep + 1, ..., d, so the
  # one of depth dep - 1 forgets its first digit: its classes are unions of
  # these, and their sums span a subspace of what these span.  The longest
  # signature which can be built is therefore the only one that has to be
  # looked at -- if it does not span, no shorter one does either.
  for dep in min(maxdep, d):-1:1
    c = _bt_combs(ctx, S.per, d - dep + 1, dep)
    c === nothing && continue
    best = c
    break
  end
  # a restricted test is far cheaper; use it unless the unrestricted one is
  # decisive
  if d >= 2 && S.combsrval != 0 && (best === nothing || !best.spans)
    for dep in min(maxdep, d - 1):-1:1
      c = _bt_combs(ctx, S.per, d - dep + 1, dep; rlevel = 1, rvalue = S.combsrval)
      c === nothing && continue
      best = c
      break
    end
  end
  @inbounds S.combs[d] = best
  @inbounds S.combsdone[d] = true
  return best
end

# The test of the comment above.  Returns 0 if no isometry can extend the
# partial map x_1, ..., x_d, 2 if the isometry was determined outright (it is
# then in `S.solution`) and 1 if nothing was decided.
# The class the restricted test runs over only has to be determined once for
# each image of the restricting level; the test below then costs |class|
# instead of |V|.
function _bt_ensure_class!(S::BTSearch, C::BTCombs)
  ctx = S.tgt
  n = ctx.n
  nv = ctx.nv
  (S.clsfor == S.x[C.rlevel] && S.clsval == C.rvalue) && return nothing
  y = _bt_load_y!(S.ytmp, ctx, S.x[C.rlevel])
  empty!(S.clsidx)
  @inbounds for j in 1:nv
    w = _bt_dot(ctx.V, j, y, n)
    if w == C.rvalue
      push!(S.clsidx, Int32(j))
    elseif -w == C.rvalue
      push!(S.clsidx, Int32(-j))
    end
  end
  S.clsfor = S.x[C.rlevel]
  S.clsval = C.rvalue
  S.clsgen += 1
  m = length(S.clsidx)
  T = eltype(ctx.V)
  S.clsV = Matrix{T}(undef, n, m)
  @inbounds for a in 1:m
    u = Int(S.clsidx[a])
    k = u > 0 ? u : -u
    if u > 0
      for i in 1:n
        S.clsV[i, a] = ctx.V[i, k]
      end
    else
      for i in 1:n
        S.clsV[i, a] = -ctx.V[i, k]
      end
    end
  end
  return nothing
end


# The signature of the test at level `d` is read off the images
# x_first, ..., x_d.  All but the last of them are fixed while the candidates
# of level `d` are being scanned, so their digits of the packed signature are
# the same for every candidate; they are computed here once per node instead of
# once per candidate.  `false` if one of them is out of range, which rules out
# every candidate of the node at once.
function _bt_pfx!(S::BTSearch, d::Int, C::BTCombs)
  dep = C.dep
  m = size(S.clsV, 2)
  @inbounds pf = S.pfx[d]
  if length(pf) < m
    pf = Vector{Int32}(undef, m)
    @inbounds S.pfx[d] = pf
  end
  @inbounds xs = S.pfxx[d]
  ok = @inbounds S.pfxgen[d] == S.clsgen
  if ok
    @inbounds for t in 1:(dep - 1)
      if xs[t] != S.x[C.first + t - 1]
        ok = false
        break
      end
    end
  end
  ok && return @inbounds S.pfxok[d]
  ctx = S.tgt
  n = ctx.n
  CV = S.clsV
  radix = C.radix
  shift = C.shift
  yy = S.ycols
  good = true
  @inbounds for a in 1:m
    pf[a] = Int32(0)
  end
  @inbounds for t in (dep - 1):-1:1
    y = yy[t]
    wt = radix^(t - 1)
    for a in 1:m
      v = _bt_dot(CV, a, y, n)
      if v < -shift || v > shift
        good = false
        break
      end
      pf[a] += Int32((v + shift) * wt)
    end
    good || break
  end
  @inbounds for t in 1:(dep - 1)
    xs[t] = S.x[C.first + t - 1]
  end
  @inbounds S.pfxgen[d] = S.clsgen
  @inbounds S.pfxok[d] = good
  return good
end

function _bt_combs_check!(S::BTSearch, d::Int)
  S.usecombs || return 1
  (d < 1 || d > S.n) && return 1
  C = _bt_combs_at!(S, d)
  C === nothing && return 1
  ctx = S.tgt
  n = ctx.n
  nv = ctx.nv
  dep = C.dep
  # scalar products with x_{first}, ..., x_{first+dep-1}; they are cached per
  # level, so that going one level deeper costs a single sweep
  if C.rlevel == 0
    @inbounds for t in 1:dep
      k = C.first + t - 1
      if S.spdx[k] != S.x[k]
        y = _bt_load_y!(S.ytmp, ctx, S.x[k])
        col = S.spd[k]
        for j in 1:nv
          col[j] = Int32(_bt_dot(ctx.V, j, y, n))
        end
        S.spdx[k] = S.x[k]
      end
    end
  else
    _bt_ensure_class!(S, C)
  end
  A = C.asum
  gramdone = false
  fill!(A, 0)
  sig = S.sigtmp
  radix = C.radix
  shift = C.shift
  V = ctx.V
  if C.rlevel == 0
    @inbounds for j in 1:nv
      for sgn in (1, -1)
        for t in 1:dep
          v = sgn * Int(S.spd[C.first + t - 1][j])
          (v < -shift || v > shift) && return 0
          sig[t] = v
        end
        c = Int(C.sigof[_bt_pack(sig, radix, shift, dep) + 1])
        c == 0 && return 0
        for i in 1:n
          A[i, c] += Int32(sgn) * V[i, j]
        end
      end
    end
  else
    # Only the vectors of the restricting class.  The class of every one of
    # them is determined first; the sums themselves are then formed one class
    # at a time, starting with the smallest, and each one is checked against
    # the source before the next is built.  Almost every candidate fails on the
    # first of them, so the sum over the whole class is rarely paid for.
    yy = S.ycols
    @inbounds for t in 1:dep
      _bt_load_y!(yy[t], ctx, S.x[C.first + t - 1])
    end
    sigof = C.sigof
    CV = S.clsV
    m = size(CV, 2)
    nsig = C.nsig
    cls = C.cls
    length(cls) < m && resize!(cls, m)
    cnt = C.ccnt
    csz = C.csize
    fill!(cnt, 0)
    if dep == 1
      y1 = yy[1]
      @inbounds for a in 1:m
        v = _bt_dot(CV, a, y1, n)
        (v < -shift || v > shift) && return 0
        c = Int(sigof[v + shift + 1])
        c == 0 && return 0
        cls[a] = Int32(c)
        cnt[c] += 1
        cnt[c] > csz[c] && return 0
      end
    else
      _bt_pfx!(S, d, C) || return 0
      pf = S.pfx[d]
      rpow = C.rpow
      yd = yy[dep]
      @inbounds for a in 1:m
        v = _bt_dot(CV, a, yd, n)
        (v < -shift || v > shift) && return 0
        c = Int(sigof[Int(pf[a]) + (v + shift) * rpow + 1])
        c == 0 && return 0
        cls[a] = Int32(c)
        cnt[c] += 1
        cnt[c] > csz[c] && return 0
      end
    end
    # the class sizes themselves are a necessary condition; the loop above
    # already stopped at the first class that grew too large
    @inbounds for c in 1:nsig
      cnt[c] == csz[c] || return 0
    end
    ord = C.cord
    length(ord) < m && resize!(ord, m)
    ptr = C.cptr
    pos = C.cpos
    q = 1
    @inbounds for c in 1:nsig
      ptr[c] = q
      pos[c] = q
      q += cnt[c]
    end
    @inbounds ptr[nsig + 1] = q
    @inbounds for a in 1:m
      c = Int(cls[a])
      ord[pos[c]] = Int32(a)
      pos[c] += 1
    end
    GA = C.gsum
    G = ctx.G
    Q = C.Q
    corder = C.corder
    @inbounds for t in 1:nsig
      c = corder[t]
      for i in 1:n
        A[i, c] = 0
      end
      for r in ptr[c]:(ptr[c + 1] - 1)
        a = Int(ord[r])
        @simd for i in 1:n
          A[i, c] += CV[i, a]
        end
      end
      for i in 1:n
        u = 0
        for k in 1:n
          u += G[i, k] * Int(A[k, c])
        end
        GA[i, c] = u
      end
      for w in 1:t
        e = corder[w]
        u = 0
        for i in 1:n
          u += Int(A[i, e]) * GA[i, c]
        end
        u == Q[e, c] || return 0
      end
    end
    gramdone = true
  end
  # the sums have to have the same Gram matrix as on the source side
  if !gramdone
    _bt_sums_gram_eq(C.Q, C.gsum, A, ctx.G, n, C.nsig) || return 0
  end
  C.spans || return 1
  # The class sums span, so an isometry extending the partial map is uniquely
  # determined by them: it is the linear map sending the source sums to the
  # target sums.  Everything below is therefore decisive -- if the map it
  # produces is not an isometry extending the partial map, none exists.
  pmod = C.prime
  Bi = C.Binv
  Mi = Matrix{Int}(undef, n, n)
  half = pmod >> 1
  @inbounds for i in 1:n
    for j in 1:n
      t = 0
      for k in 1:n
        t = (t + Bi[i, k] * mod(A[j, C.piv[k]], pmod)) % pmod
      end
      Mi[i, j] = t > half ? t - pmod : t
    end
  end
  # all class sums, not only the chosen ones, have to be mapped correctly
  As = C.srcsum
  @inbounds for c in 1:C.nsig
    for j in 1:n
      t = 0
      for i in 1:n
        t += As[i, c] * Mi[i, j]
      end
      t == A[j, c] || return 0
    end
  end
  _bt_verify(Mi, ctx.G, S.Gsrc) || return 0
  # and it has to extend the partial map
  @inbounds for k in 1:d
    p = S.x[k]
    r = S.per[k]
    if p > 0
      for j in 1:n
        Mi[r, j] == Int(V[j, p]) || return 0
      end
    else
      for j in 1:n
        Mi[r, j] == -Int(V[j, -p]) || return 0
      end
    end
  end
  S.solution = Mi
  S.solved = true
  return 2
end

@inline function _bt_findval(vv::Vector{Int}, s::Int)
  @inbounds for a in 1:length(vv)
    vv[a] == s && return a
  end
  return 0
end

function _bt_reserve!(S::BTSearch, idx::Int, cap::Int)
  nw = S.nw
  if length(S.poolv[idx]) < cap
    resize!(S.poolv[idx], cap)
    resize!(S.poolp[idx], cap * nw)
    resize!(S.poolm[idx], cap * nw)
  end
  return nothing
end

# x[I] has just been set; compute the pool at depth I from the pool at depth
# I - 1 and the candidate list of the next level.
# Bucket the short vectors by their scalar product with the first image the
# current step varies.  This is done once per image of that level; afterwards
# the candidate list of a level is a filter of one bucket instead of a sweep
# over everything that is still relevant.
function _bt_build_buckets!(S::BTSearch, s::Int)
  S.bktfor == S.x[s] && return nothing
  ctx = S.tgt
  n = ctx.n
  nv = ctx.nv
  b = ctx.bound
  y = _bt_load_y!(S.ytmp, ctx, S.x[s])
  @inbounds for c in 1:(2 * b + 1)
    empty!(S.bkt[c])
  end
  @inbounds for j in 1:nv
    v = _bt_dot(ctx.V, j, y, n)
    push!(S.bkt[v + b + 1], Int32(j))
    push!(S.bkt[-v + b + 1], Int32(-j))
  end
  S.bktfor = S.x[s]
  return nothing
end

@inline function _bt_set_y!(S::BTSearch, k::Int)
  if S.ykfor[k] != S.x[k]
    _bt_load_y!(S.yk[k], S.tgt, S.x[k])
    S.ykfor[k] = S.x[k]
  end
  return S.yk[k]
end

# There are two ways to produce the candidates of the next level: sweeping the
# pool of everything that can still be the image of *some* later level, or
# filtering the bucket of the vectors with the right scalar product with
# x_step.  The pool shrinks quickly with the depth but carries every level
# along, so it is the better one for a search that goes deep; the bucket does
# not shrink but only ever holds a single level, so it is the better one for a
# search that is wide and shallow.  Which of the two wins is a property of the
# lattice, and the fingerprint gives the size of both at every depth.
function _bt_prefer_pool(F::BTFingerprint, per::Vector{Int}, st::Int, ml::Int,
                         n::Int, nv::Int)
  cpool = 0
  cbkt = 0
  k = min(2, n)
  @inbounds for d in st:ml
    p = 0
    for I in d:ml
      p += F.fp[d, per[I]]
      p >= nv && break
    end
    cpool += min(p, nv)
    d + 1 <= n && (cbkt += F.fp[k, per[d + 1]])
  end
  return cpool <= cbkt
end

# Candidate list of level `I`, given the images x_1, ..., x_{I-1}.  The levels
# before the current step are standard basis vectors, so those constraints are
# a table lookup; the remaining ones cost a scalar product, and the whole thing
# runs over one bucket rather than over all short vectors.
function _bt_cands!(S::BTSearch, I::Int, d::Int)
  S.nodes += 1
  if S.nodes > S.nodelimit || S.work > S.worklimit
    S.aborted = true
    return false
  end
  ctx = S.tgt
  n = ctx.n
  b = ctx.bound
  st = S.step
  _bt_build_buckets!(S, st)
  cl = S.cand[I]
  empty!(cl)
  src = S.bkt[S.TS[I, st] + b + 1]
  S.work += length(src)
  Wt = ctx.Wt
  per = S.per
  nrm = ctx.nrm
  colors = ctx.colors
  hascol = !isempty(colors)
  tn = S.TN[I]
  tc = S.TC[I]
  rhov = ctx.rhov
  hasrho = !isempty(rhov)
  tr = S.TR[I]
  want = S.fpd[I]
  # the scalar product rows of the images which need a real product
  for k in (st + 1):d
    _bt_set_y!(S, k)
  end
  cnt = 0
  @inbounds for u in src
    j = u > 0 ? Int(u) : -Int(u)
    nrm[j] == tn || continue
    (!hascol || colors[j] == tc) || continue
    sg = u > 0
    # the pairing with rho changes sign with the vector, so this is what makes
    # the search find Aut(L, rho) rather than Aut(L, {rho, -rho})
    if hasrho
      rv = Int(rhov[j])
      sg || (rv = -rv)
      rv == tr || continue
    end
    ok = true
    for k in 1:(st - 1)
      w = Int(Wt[j, per[k]])
      sg || (w = -w)
      if w != S.TS[I, k]
        ok = false
        break
      end
    end
    ok || continue
    for k in (st + 1):d
      w = _bt_dot(ctx.V, j, S.yk[k], n)
      sg || (w = -w)
      if w != S.TS[I, k]
        ok = false
        break
      end
    end
    ok || continue
    cnt += 1
    cnt > want && return false
    push!(cl, u)
  end
  return cnt == want
end

function _bt_descend!(S::BTSearch, I::Int)
  n = S.n
  nw = S.nw
  S.nodes += 1
  if S.nodes > S.nodelimit || S.work > S.worklimit
    S.aborted = true
    return false
  end
  p = S.x[I]
  y = _bt_load_y!(S.ytmp, S.tgt, p)
  V = S.tgt.V
  L = S.plen[I]
  S.work += L
  _bt_reserve!(S, I + 1, L)
  pv = S.poolv[I]; pp = S.poolp[I]; pm = S.poolm[I]
  qv = S.poolv[I + 1]; qp = S.poolp[I + 1]; qm = S.poolm[I + 1]
  vv = S.vals[I]; vm = S.vmask[I]
  wa = S.wa; wb = S.wb; clearw = S.clearw
  @inbounds for w in 1:nw
    clearw[w] = ~UInt64(0)
  end
  @inbounds for J in 1:I
    clearw[_bt_word(J)] &= ~_bt_bit(J)
  end
  # candidate list of the next level; the deeper levels are only counted, which
  # already gives a strong pruning criterion
  hi = min(n, I + S.lookahead, S.maxlevel)
  empty!(S.cand[I + 1])
  @inbounds for J in (I + 1):hi
    S.cnts[J] = 0
  end
  nx = I + 1
  wnx = _bt_word(nx)
  bnx = _bt_bit(nx)
  cnt = 0
  @inbounds for t in 1:L
    j = Int(pv[t])
    base = (t - 1) * nw
    anya = false
    anyb = false
    for w in 1:nw
      a = pp[base + w] & clearw[w]
      b = pm[base + w] & clearw[w]
      wa[w] = a
      wb[w] = b
      anya |= a != 0
      anyb |= b != 0
    end
    (anya || anyb) || continue
    sp = _bt_dot(V, j, y, n)
    ia = anya ? _bt_findval(vv, sp) : 0
    ib = anyb ? _bt_findval(vv, -sp) : 0
    anya = false
    anyb = false
    if ia == 0
      for w in 1:nw
        wa[w] = UInt64(0)
      end
    else
      off = (ia - 1) * nw
      for w in 1:nw
        wa[w] &= vm[off + w]
        anya |= wa[w] != 0
      end
    end
    if ib == 0
      for w in 1:nw
        wb[w] = UInt64(0)
      end
    else
      off = (ib - 1) * nw
      for w in 1:nw
        wb[w] &= vm[off + w]
        anyb |= wb[w] != 0
      end
    end
    (anya || anyb) || continue
    cnt += 1
    qv[cnt] = Int32(j)
    obase = (cnt - 1) * nw
    for w in 1:nw
      qp[obase + w] = wa[w]
      qm[obase + w] = wb[w]
    end
    if wa[wnx] & bnx != 0
      push!(S.cand[nx], Int32(j))
      S.cnts[nx] += 1
    end
    if wb[wnx] & bnx != 0
      push!(S.cand[nx], Int32(-j))
      S.cnts[nx] += 1
    end
    for J in (I + 2):hi
      w = _bt_word(J)
      bt = _bt_bit(J)
      if wa[w] & bt != 0
        S.cnts[J] += 1
      end
      if wb[w] & bt != 0
        S.cnts[J] += 1
      end
    end
  end
  S.plen[I + 1] = cnt
  # every level must have exactly as many candidates as the fingerprint of the
  # source lattice predicts
  @inbounds for J in (I + 1):hi
    S.cnts[J] == S.fp[I + 1, S.per[J]] || return false
  end
  return true
end

function _bt_extend!(S::BTSearch, d::Int)
  n = S.n
  d == n && return true
  I = d + 1
  I > S.maxlevel &&
    throw(BTError("internal error: search went past the tracked levels"))
  cl = S.cand[I]
  @inbounds for idx in 1:length(cl)
    S.aborted && return false
    S.x[I] = Int(cl[idx])
    if I == n
      return true
    end
    r = _bt_combs_check!(S, I)
    r == 0 && continue
    r == 2 && return true
    if S.usepool ? _bt_descend!(S, I) : _bt_cands!(S, I + 1, I)
      _bt_extend!(S, I) && return true
    end
  end
  return false
end

# the matrix of the isometry determined by x
function _bt_matrix(S::BTSearch)
  n = S.n
  V = S.tgt.V
  M = zeros(Int, n, n)
  @inbounds for i in 1:n
    p = S.x[i]
    r = S.per[i]
    if p > 0
      for j in 1:n
        M[r, j] = Int(V[j, p])
      end
    else
      for j in 1:n
        M[r, j] = -Int(V[j, -p])
      end
    end
  end
  return M
end
################################################################################
#
#  Group elements, orbits
#
################################################################################

# An isometry, stored by its matrix.  As soon as it has been applied to many
# short vectors we replace the repeated matrix vector products by the induced
# permutation of the short vectors, which is computed in one sweep.
mutable struct BTGen{T <: Signed}
  M::Matrix{Int}          # row per[i] is the image of the per[i]-th basis vector
  Mt::Matrix{T}           # transpose of M, for fast row access
  perm::Vector{Int32}     # induced permutation of the short vectors (or empty)
  hits::Int
end


function BTGen(::Type{T}, M::Matrix{Int}) where {T <: Signed}
  n = size(M, 1)
  Mt = Matrix{T}(undef, n, n)
  @inbounds for i in 1:n, l in 1:n
    Mt[i, l] = T(M[l, i])
  end
  return BTGen{T}(M, Mt, Int32[], 0)
end

BTGen(ctx::BTCtx{T}, M::Matrix{Int}) where {T} = BTGen(T, M)

function _bt_image_coords!(w::Vector{T}, ctx::BTCtx{T}, g::BTGen{T}, k::Int) where {T}
  n = ctx.n
  V = ctx.V
  Mt = g.Mt
  @inbounds for i in 1:n
    w[i] = Int32(0)
  end
  @inbounds for l in 1:n
    c = V[l, k]
    if c != 0
      @simd for i in 1:n
        w[i] += c * Mt[i, l]
      end
    end
  end
  return w
end

function _bt_build_perm!(ctx::BTCtx{T}, g::BTGen{T}) where {T}
  nv = ctx.nv
  n = ctx.n
  perm = Vector{Int32}(undef, nv)
  w = Vector{T}(undef, n)
  @inbounds for k in 1:nv
    _bt_image_coords!(w, ctx, g, k)
    q = _bt_find(ctx, w)
    q == 0 && throw(BTError("image of a short vector is not short"))
    perm[k] = Int32(q)
  end
  g.perm = perm
  return g
end

@inline function _bt_apply(ctx::BTCtx{T}, g::BTGen{T}, p::Int) where {T}
  k = p < 0 ? -p : p
  if !isempty(g.perm)
    q = Int(g.perm[k])
    return p < 0 ? -q : q
  end
  g.hits += 1
  if g.hits > ctx.nv >> 2
    _bt_build_perm!(ctx, g)
    q = Int(g.perm[k])
    return p < 0 ? -q : q
  end
  w = _bt_image_coords!(ctx.wtmp, ctx, g, k)
  q = _bt_find(ctx, w)
  q == 0 && throw(BTError("image of a short vector is not short"))
  return p < 0 ? -q : q
end

# An orbit which can be enlarged when new generators show up.
mutable struct BTOrbit
  pts::Vector{Int32}
  seen::Vector{UInt8}      # bit 1: +v_j in the orbit, bit 2: -v_j in the orbit
  cursor::Vector{Int}      # per generator: number of points already processed
  # -1 is an automorphism of every lattice, so the orbit of the *first* base
  # point is closed under negation.  Only one of the two signs is then kept in
  # `pts` (the other one is marked as seen right away), which halves the work
  # of the closure and saves the search a generator.
  neg::Bool
end

function BTOrbit(nv::Int, pt::Int, neg::Bool = false)
  seen = zeros(UInt8, nv)
  k = pt < 0 ? -pt : pt
  seen[k] = neg ? 0x03 : (pt < 0 ? 0x02 : 0x01)
  return BTOrbit(Int32[Int32(pt)], seen, Int[], neg)
end

BTOrbit(nv::Int, neg::Bool) = BTOrbit(Int32[], zeros(UInt8, nv), Int[], neg)

# number of points in the orbit; `pts` holds only one of every pair {p, -p}
# when the orbit is closed under negation
@inline _bt_orbit_size(o::BTOrbit) = o.neg ? 2 * length(o.pts) : length(o.pts)

# Put a point into an orbit set; the closure picks it up on the next call.
@inline function _bt_add!(o::BTOrbit, p::Int)
  _bt_seen(o, p) && return false
  _bt_mark!(o, p)
  push!(o.pts, Int32(p))
  return true
end

@inline function _bt_seen(o::BTOrbit, p::Int)
  k = p < 0 ? -p : p
  m = p < 0 ? 0x02 : 0x01
  return o.seen[k] & m != 0
end

@inline function _bt_mark!(o::BTOrbit, p::Int)
  k = p < 0 ? -p : p
  o.seen[k] |= o.neg ? 0x03 : (p < 0 ? 0x02 : 0x01)
  return nothing
end

# Enlarge the orbit until it is closed under `H`, or until it has reached
# `target` points.  The generators are advanced in a round robin fashion, so
# that the orbit grows as fast as possible: if it is known in advance (from the
# fingerprint) how many points the orbit must have, the closure can be stopped
# as soon as that many points are reached, which saves a factor of |H|.
function _bt_close!(o::BTOrbit, ctx::BTCtx{T}, H::Vector{BTGen{T}},
                    target::Int = typemax(Int)) where {T}
  ng = length(H)
  ng == 0 && return o
  while length(o.cursor) < ng
    push!(o.cursor, 0)
  end
  _bt_orbit_size(o) >= target && return o
  # for a large orbit every generator will be applied to a large part of the
  # short vectors anyway; computing the induced permutation in one sweep is
  # then cheaper than the individual matrix vector products
  if target > (ctx.nv >> 2)
    for g in H
      isempty(g.perm) && _bt_build_perm!(ctx, g)
    end
  end
  @inbounds while true
    moved = false
    for gi in 1:ng
      if o.cursor[gi] < length(o.pts)
        o.cursor[gi] += 1
        moved = true
        q = _bt_apply(ctx, H[gi], Int(o.pts[o.cursor[gi]]))
        if !_bt_seen(o, q)
          _bt_mark!(o, q)
          push!(o.pts, Int32(q))
          _bt_orbit_size(o) >= target && return o
        end
      end
    end
    moved || break
  end
  return o
end

function _bt_orbit(ctx::BTCtx{T}, H::Vector{BTGen{T}}, pt::Int,
                  target::Int = typemax(Int); neg::Bool = false) where {T}
  o = BTOrbit(ctx.nv, pt, neg)
  return _bt_close!(o, ctx, H, target)
end

# min(#orbit, limit)
function _bt_orbit_len(ctx::BTCtx{T}, H::Vector{BTGen{T}}, pt::Int, limit::Int) where {T}
  o = BTOrbit(ctx.nv, pt)
  _bt_close!(o, ctx, H, limit)
  return _bt_orbit_size(o)
end

# remove the points of the orbit `o` from `lst`
function _bt_remove!(lst::Vector{Int32}, o::BTOrbit)
  k = 0
  @inbounds for t in 1:length(lst)
    p = Int(lst[t])
    if !_bt_seen(o, p)
      k += 1
      lst[k] = lst[t]
    end
  end
  resize!(lst, k)
  return lst
end

################################################################################
#
#  Initialising the pool
#
################################################################################

# The pool at depth s - 1, where the first s - 1 images are the basis vectors
# b_{per[1]}, ..., b_{per[s-1]} themselves.
function _bt_init_pool_std!(S::BTSearch, F::BTFingerprint, s::Int, ctx::BTCtx,
                            tmpp::Vector{UInt64}, tmpm::Vector{UInt64})
  n = S.n
  nw = S.nw
  nv = ctx.nv
  fill!(tmpp, UInt64(0))
  fill!(tmpm, UInt64(0))
  ord = F.order[s]
  # group the levels by their block, so that every block is visited once
  done = falses(n)
  @inbounds for I in s:min(n, S.maxlevel)
    done[I] && continue
    b0 = F.bs[s, S.per[I]]
    b1 = F.be[s, S.per[I]]
    msk = zeros(UInt64, nw)
    for J in I:min(n, S.maxlevel)
      if F.bs[s, S.per[J]] == b0
        done[J] = true
        msk[_bt_word(J)] |= _bt_bit(J)
      end
    end
    for t in b0:b1
      it = Int(ord[t])
      if it <= nv
        for w in 1:nw
          tmpp[(it - 1) * nw + w] |= msk[w]
        end
      elseif it <= 2 * nv
        j = it - nv
        for w in 1:nw
          tmpm[(j - 1) * nw + w] |= msk[w]
        end
      end
    end
  end
  _bt_reserve!(S, s, nv)
  pv = S.poolv[s]; pp = S.poolp[s]; pm = S.poolm[s]
  empty!(S.cand[s])
  ws = _bt_word(s)
  bs = _bt_bit(s)
  cnt = 0
  @inbounds for j in 1:nv
    base = (j - 1) * nw
    any = false
    for w in 1:nw
      if tmpp[base + w] != 0 || tmpm[base + w] != 0
        any = true
        break
      end
    end
    any || continue
    cnt += 1
    pv[cnt] = Int32(j)
    ob = (cnt - 1) * nw
    for w in 1:nw
      pp[ob + w] = tmpp[base + w]
      pm[ob + w] = tmpm[base + w]
    end
    if tmpp[base + ws] & bs != 0
      push!(S.cand[s], Int32(j))
    end
    if tmpm[base + ws] & bs != 0
      push!(S.cand[s], Int32(-j))
    end
  end
  S.plen[s] = cnt
  return nothing
end

# The pool at depth 0 (nothing fixed yet): all short vectors whose norm occurs
# among the norms of the basis vectors of the source lattice.
function _bt_init_pool_free!(S::BTSearch, ctx::BTCtx)
  n = S.n
  nw = S.nw
  nv = ctx.nv
  _bt_reserve!(S, 1, nv)
  pv = S.poolv[1]; pp = S.poolp[1]; pm = S.poolm[1]
  empty!(S.cand[1])
  mskp = zeros(UInt64, nw)
  mskm = zeros(UInt64, nw)
  hascol = !isempty(ctx.colors)
  hasrho = !isempty(ctx.rhov)
  cnt = 0
  @inbounds for j in 1:nv
    fill!(mskp, UInt64(0))
    fill!(mskm, UInt64(0))
    any = false
    cj = hascol ? ctx.colors[j] : UInt64(0)
    rp = hasrho ? Int(ctx.rhov[j]) : 0
    for I in 1:n
      (ctx.nrm[j] == S.TN[I] && cj == S.TC[I]) || continue
      # the pairing with rho separates the two signs, so they no longer share
      # a mask
      if !hasrho || rp == S.TR[I]
        mskp[_bt_word(I)] |= _bt_bit(I)
        any = true
      end
      if !hasrho || -rp == S.TR[I]
        mskm[_bt_word(I)] |= _bt_bit(I)
        any = true
      end
    end
    any || continue
    cnt += 1
    pv[cnt] = Int32(j)
    ob = (cnt - 1) * nw
    for w in 1:nw
      pp[ob + w] = mskp[w]
      pm[ob + w] = mskm[w]
    end
    if mskp[_bt_word(1)] & _bt_bit(1) != 0
      push!(S.cand[1], Int32(j))
    end
    if mskm[_bt_word(1)] & _bt_bit(1) != 0
      push!(S.cand[1], Int32(-j))
    end
  end
  S.plen[1] = cnt
  # the numbers of possible images have to agree with the fingerprint of the
  # source lattice
  @inbounds for I in 1:n
    c = 0
    for t in 1:cnt
      j = Int(pv[t])
      ob = (t - 1) * nw
      w = _bt_word(I)
      bt = _bt_bit(I)
      pp[ob + w] & bt != 0 && (c += 1)
      pm[ob + w] & bt != 0 && (c += 1)
    end
    c == S.fp[1, S.per[I]] || return false
  end
  return true
end

################################################################################
#
#  Automorphism group
#
################################################################################

function _bt_automorphism_group_data(G::Matrix{Int}; verbose::Bool = false)
  # the component invariant is only used to refine the initial partition here,
  # which the fingerprint does anyway, so it must not cost more than a sweep
  t0 = time()
  ctx = BTCtx(G; comp_budget = -2)
  n = ctx.n
  nv = ctx.nv
  @vprintln :Lattice 1 "backtrack: rank $(n), $(nv) short vectors of norm <= $(ctx.bound), setup $(round(time() - t0, digits = 3))s"
  # The reflections in the roots generate a group W which is already inside the
  # isometry group, and the isometry group is W semidirect the stabiliser of a
  # Weyl chamber.  Fixing the vector rho of that chamber costs nothing -- it is
  # a pairing per short vector, folded into the initial partition -- and what
  # is left to search for is only the stabiliser.
  rd = _bt_root_data(G, _bt_roots(ctx))
  worder = one(ZZRingElem)
  wgens = Matrix{Int}[]
  if rd !== nothing && !isempty(rd.types)
    worder = rd.worder
    rho = rd.rho
    gr = zeros(Int, n)
    for i in 1:n
      t = 0
      for k in 1:n
        t += G[i, k] * rho[k]
      end
      gr[i] = t
    end
    rv = Vector{Int32}(undef, nv)
    ok = true
    @inbounds for j in 1:nv
      t = 0
      for i in 1:n
        t += Int(ctx.V[i, j]) * gr[i]
      end
      if !(typemin(Int32) < t < typemax(Int32))
        ok = false
        break
      end
      rv[j] = Int32(t)
    end
    if ok
      ctx.rhov = rv
      _bt_root_colors!(ctx, rd.simple)
      for a in rd.simple
        m = _bt_is_root(G, a, n)
        m == 0 && (ok = false; break)
        push!(wgens, _bt_reflection(G, a, m))
      end
    end
    if !ok
      ctx.rhov = Int32[]
      empty!(wgens)
      worder = one(ZZRingElem)
    end
    @vprintln :Lattice 1 "backtrack: root system $(rd.types), |W| = $(worder)"
  end
  F = _bt_fingerprint(ctx)
  @vprintln :Lattice 1 "backtrack: fingerprint $(F.fpd)"
  @vprintln :Lattice 2 "backtrack: order of the base $(F.per)"
  verbose && println("|V| = ", nv, "  fpd = ", F.fpd, "\n per = ", F.per)
  S = BTSearch(ctx, F.per, G, F.fp, F.fpd, _bt_basis_colors(ctx))
  nw = S.nw
  std = [Int(ctx.bidx[F.per[i]]) for i in 1:n]
  tmpp = zeros(UInt64, nv * nw)
  tmpm = zeros(UInt64, nv * nw)

  # -1 is an automorphism of every lattice, but it sends rho to -rho, so it is
  # not in the group being searched for once rho is fixed; the orbit of the
  # first base point may then not be closed under negation either
  negok = isempty(ctx.rhov)
  Tv = eltype(ctx.V)
  g = [BTGen{Tv}[] for _ in 1:n]
  orders = ones(Int, n)
  seed = 0x2545f4914f6cdd1d % UInt64
  tpool = 0.0; torb = 0.0; tsearch = 0.0; tcombs = 0.0

  for step in 1:n
    # the image of b_{per[step]} is already determined by the previous ones
    F.fpd[step] == 1 && continue
    H = BTGen{Tv}[]
    for i in step:n
      append!(H, g[i])
    end
    for i in 1:(step - 1)
      S.x[i] = std[i]
    end
    S.step = step
    S.bktfor = 0
    S.usepool = _bt_prefer_pool(F, S.per, step, min(n, S.maxlevel), n, ctx.nv)
    tpool += @elapsed _bt_init_pool_std!(S, F, step, ctx, tmpp, tmpm)
    remaining = copy(S.cand[step])
    ncand = length(remaining)
    # Images which are known to be impossible.  If no automorphism maps the
    # base point to `p`, then none maps it to `h(p)` for a known automorphism
    # `h` either, so this set is closed under `H`; and because `H` grows during
    # the step, it has to be closed again every time it does.
    bad = BTOrbit(ctx.nv, negok && step == 1)
    local o
    torb += @elapsed (o = _bt_orbit(ctx, H, std[step], ncand;
                                    neg = negok && step == 1))
    orders[step] = _bt_orbit_size(o)
    _bt_remove!(remaining, o)
    tstep = time()
    ntry = 0
    nfail = 0
    node0 = S.nodes
    @vprintln :Lattice 1 "backtrack: step $(step): $(ncand) candidates, orbit $(length(o.pts)) from $(length(H)) generators"
    while !isempty(remaining)
      # picking the next candidate pseudo randomly (instead of the first one)
      # makes the found generators move the base point around much more, so
      # that the orbit is exhausted with considerably fewer generators
      seed = seed * 6364136223846793005 + 1442695040888963407
      im = Int(remaining[(seed >> 33) % length(remaining) + 1])
      S.x[step] = im
      ntry += 1
      if get_verbosity_level(:Lattice) >= 2 && (ntry <= 12 || ntry % 32 == 0)
        println("backtrack:   step $(step): tried $(ntry) ($(nfail) failed), ",
                "$(length(remaining)) left, orbit $(orders[step]), ",
                "$(S.nodes - node0) nodes, $(round(time() - tstep, digits = 2))s",
                S.usecombs ? " [combs]" : "")
        flush(stdout)
      end
      found = false
      local M
      # A partial map which is consistent but does not extend is only detected
      # deep in the search, and its subtree can be huge.  As long as the search
      # is cheap this does not matter, so the (expensive but very effective)
      # scalar product combination test is only switched on once a single
      # candidate has cost more than `nodelimit` nodes.
      tt0 = time()
      while true
        S.aborted = false
        S.solved = false
        S.nodelimit = S.usecombs ? typemax(Int) : S.nodes + 400
        # a node costs a sweep whose length depends on the lattice, so the
        # number of nodes alone does not bound the time a single candidate can
        # take; both are capped
        S.worklimit = S.usecombs ? typemax(Int) : S.work + 32 * ctx.nv
        if step == n
          found = true
        else
          # the cheap invariants first: they need no pool, and a failure here
          # saves the sweep of the descent
          r = _bt_combs_check!(S, step)
          if r == 2
            found = true
          elseif r == 1
            found = (S.usepool ? _bt_descend!(S, step) :
                     _bt_cands!(S, step + 1, step)) && _bt_extend!(S, step)
          end
        end
        if S.aborted
          if !S.usecombs
            @vprintln :Lattice 1 "backtrack: switching on the scalar product combinations"
            tc = time()
            _bt_setup_combs!(S, ctx; budget = time() - tt0)
            S.usecombs = true
            # the combinations bound the depth the search can reach, which is
            # what decides between the pool and the per level filtering
            S.usepool = _bt_prefer_pool(F, S.per, step, min(n, S.maxlevel), n,
                                        ctx.nv)
            @vprintln :Lattice 1 "backtrack: combinations ready in $(round(time() - tc, digits = 3))s"
            continue
          end
        end
        break
      end
      tsearch += time() - tt0
      if found
        M = S.solved ? S.solution : _bt_matrix(S)
        _bt_verify(M, G, G) ||
          throw(BTError("internal error: produced matrix is not an isometry"))
        ng = BTGen(ctx, M)
        push!(g[step], ng)
        push!(H, ng)
        torb += @elapsed _bt_close!(o, ctx, H, ncand)
        orders[step] = _bt_orbit_size(o)
        _bt_remove!(remaining, o)
        # the new generator usually merges several of the orbits which were
        # ruled out before it was known
        if !isempty(bad.pts)
          torb += @elapsed _bt_close!(bad, ctx, H)
          _bt_remove!(remaining, bad)
        end
      else
        nfail += 1
        _bt_add!(bad, im)
        torb += @elapsed _bt_close!(bad, ctx, H)
        _bt_remove!(remaining, bad)
      end
    end
    @vprintln :Lattice 1 "backtrack: step $(step): orbit $(orders[step]), $(length(g[step])) new generators, $(ntry) tries ($(nfail) failed), $(S.nodes - node0) nodes, $(round(time() - tstep, digits = 3))s"
    verbose && println("step ", step, ": order ", orders[step], " (fpd ",
                       F.fpd[step], "), gens ", length(g[step]),
                       ", nodes ", S.nodes)
  end
  @vprintln :Lattice 1 "backtrack: pool $(round(tpool, digits = 2))s, orbits $(round(torb, digits = 2))s, search $(round(tsearch, digits = 2))s"
  # -1 is an automorphism of every lattice.  The orbit of the first base point
  # was taken to be closed under negation, so it has to be among the generators
  # for the product of the orbit lengths to be the group order.
  if negok
    mid = zeros(Int, n, n)
    for i in 1:n
      mid[i, i] = -1
    end
    _bt_verify(mid, G, G) ||
      throw(BTError("internal error: -1 is not an automorphism"))
    push!(g[1], BTGen(ctx, mid))
  end
  # the stabiliser chain: an element of g[i] must fix the first i - 1 base
  # points, otherwise the product of the orbit lengths is not the group order
  tchain = @elapsed for i in 1:n
    for gg in g[i]
      for k in 1:(i - 1)
        _bt_apply(ctx, gg, std[k]) == std[k] ||
          throw(BTError("internal error: broken stabiliser chain"))
      end
    end
  end
  @vprintln :Lattice 1 "backtrack: chain check $(round(tchain, digits = 2))s"
  gens = Matrix{Int}[]
  for i in 1:n
    for gg in g[i]
      push!(gens, gg.M)
    end
  end
  ord = one(ZZRingElem)
  for i in 1:n
    ord *= orders[i]
  end
  # what the search found is the stabiliser of the chamber; the reflections
  # make up the rest of the group
  for M in wgens
    _bt_verify(M, G, G) ||
      throw(BTError("internal error: a reflection is not an isometry"))
    push!(gens, M)
  end
  ord *= worder
  return gens, ord, orders, S.nodes
end

@doc raw"""
    _bt_automorphism_group(G::Matrix{Int}) -> Vector{Matrix{Int}}, ZZRingElem

Return generators of $\{g \in GL_n(\mathbf{Z}) : g G g^t = G\}$ together with
the order of that group, for a positive definite integral `G`.  The rows of the
generators are the images of the standard basis vectors.
"""
function _bt_automorphism_group(G::Matrix{Int}; verbose::Bool = false)
  res = _bt_automorphism_group_data(G; verbose)
  return res[1], res[2]
end

################################################################################
#
#  Isometry test
#
################################################################################

# Decide whether the lattices with Gram matrices `G1` and `G2` (positive
# definite and integral) are isometric.  On success the returned matrix `M`
# satisfies M*G2*transpose(M) == G1.
function _bt_isometry(G1::Matrix{Int}, G2::Matrix{Int})
  n = size(G1, 1)
  n == size(G2, 1) || return false, zeros(Int, 0, 0)
  bound = 0
  for i in 1:n
    bound = max(bound, G1[i, i])
  end
  c1 = BTCtx(G1)
  c2 = BTCtx(G2, bound)
  if eltype(c1.V) !== eltype(c2.V)
    # the search state ties the two contexts together, so widen both
    c1 = BTCtx(G1; force = Int32)
    c2 = BTCtx(G2, bound; force = Int32)
  end
  # the orthogonal decompositions have to match; the component search gives up
  # on very sparse graphs, and whether it does so may depend on the numbering of
  # the short vectors, so the invariant is only used if both sides have it
  if c1.comps_ok && c2.comps_ok
    c1.comp_sig == c2.comp_sig || return false, zeros(Int, 0, 0)
  else
    c1.colors = UInt64[]
    c2.colors = UInt64[]
  end
  # cheap invariant: the number of vectors of each norm up to the bound must
  # agree
  h1 = zeros(Int, bound + 1)
  h2 = zeros(Int, bound + 1)
  for j in 1:c1.nv
    h1[c1.nrm[j] + 1] += 1
  end
  for j in 1:c2.nv
    h2[c2.nrm[j] + 1] += 1
  end
  h1 == h2 || return false, zeros(Int, 0, 0)
  F = _bt_fingerprint(c1)
  bcol = _bt_basis_colors(c1)
  S = BTSearch(c2, F.per, G1, F.fp, F.fpd, bcol; src = c1)
  S.step = 1
  S.bktfor = 0
  S.usepool = _bt_prefer_pool(F, S.per, 1, min(S.n, S.maxlevel), S.n, c2.nv)
  _bt_init_pool_free!(S, c2) || return false, zeros(Int, 0, 0)
  found = false
  while true
    S.aborted = false
    S.solved = false
    S.nodelimit = S.usecombs ? typemax(Int) : S.nodes + 400
    S.worklimit = S.usecombs ? typemax(Int) : S.work + 32 * c2.nv
    t0iso = time()
    found = _bt_extend!(S, 0)
    if S.aborted && !S.usecombs
      _bt_setup_combs!(S, c1; budget = time() - t0iso)
      S.usecombs = true
      S.usepool = _bt_prefer_pool(F, S.per, 1, min(S.n, S.maxlevel), S.n, c2.nv)
      continue
    end
    break
  end
  if found
    M = S.solved ? S.solution : _bt_matrix(S)
    _bt_verify(M, G2, G1) ||
      throw(BTError("internal error: produced matrix is not an isometry"))
    return true, M
  end
  return false, zeros(Int, 0, 0)
end

################################################################################
#
#  Interface for integer lattices
#
################################################################################

# Turn the Gram matrix of a definite lattice into a positive definite, integral,
# primitive and LLL reduced matrix with `Int` entries.  Returns the matrix, the
# base change `T` (with `T*G*transpose(T)` the reduced matrix) and the scaling
# factor which was divided out, or `nothing` if the entries do not fit into an
# `Int`.
# The enumeration bound is the largest diagonal entry of the Gram matrix, so a
# basis made of short vectors makes the whole problem smaller -- and the two can
# differ a lot: on one lattice of this rank the LLL basis has a vector of norm 6
# where the lattice is generated by its vectors of norm 4, which is the
# difference between a hundred thousand short vectors and six thousand.
#
# Vectors are taken in increasing norm and kept whenever they increase the rank.
# The selection is made in Float64, which only decides which vectors to try; the
# result is accepted only after checking exactly that the matrix is unimodular,
# so a misjudged rank costs an opportunity and never correctness.  LLL is
# deliberately not applied to the outcome: it optimises the orthogonality defect
# and pushes the largest norm straight back up.
#
# Returns the new Gram matrix and the transform, or `nothing` to keep the basis.
function _bt_short_basis(G::Matrix{Int})
  n = size(G, 1)
  b0 = G[1, 1]
  lo = b0
  for i in 1:n
    G[i, i] > b0 && (b0 = G[i, i])
    G[i, i] < lo && (lo = G[i, i])
  end
  lo >= b0 && return nothing                 # already flat, nothing to gain
  # the distinct diagonal entries below the largest one are the natural guesses
  trials = Int[]
  for i in 1:n
    G[i, i] < b0 && !(G[i, i] in trials) && push!(trials, G[i, i])
  end
  sort!(trials)
  # every trial enumerates less than the bound we would otherwise use, so the
  # work wasted when none of them succeeds is bounded by a few times that; a
  # lattice with many distinct diagonal entries would otherwise try them all
  length(trials) > 3 && resize!(trials, 3)
  A = Matrix{Float64}(undef, n, n)           # row echelon form of what we took
  piv = Vector{Int}(undef, n)
  row = Vector{Float64}(undef, n)
  for b in trials
    V, nrm = _bt_short_vectors(G, b)
    nv = size(V, 2)
    nv >= n || continue
    ord = sortperm(nrm)
    k = 0
    sel = Vector{Int}(undef, n)
    for t in 1:nv
      j = ord[t]
      @inbounds for i in 1:n
        row[i] = Float64(V[i, j])
      end
      # reduce against the rows taken so far
      @inbounds for r in 1:k
        f = row[piv[r]]
        f == 0 && continue
        for i in 1:n
          row[i] -= f * A[r, i]
        end
      end
      p = 0
      big = 1.0e-6
      @inbounds for i in 1:n
        a = abs(row[i])
        a > big && (big = a; p = i)
      end
      p == 0 && continue                     # dependent on what we have
      @inbounds for i in 1:n
        A[k + 1, i] = row[i] / row[p]
      end
      k += 1
      piv[k] = p
      sel[k] = j
      k == n && break
    end
    k == n || continue
    U = Matrix{Int}(undef, n, n)
    @inbounds for a in 1:n, i in 1:n
      U[a, i] = Int(V[i, sel[a]])
    end
    UZ = matrix(ZZ, n, n, [ZZRingElem(U[a, i]) for a in 1:n for i in 1:n])
    abs(det(UZ)) == 1 || continue             # a basis, not just a sublattice
    GZ = matrix(ZZ, n, n, [ZZRingElem(G[i, j]) for i in 1:n for j in 1:n])
    GnZ = UZ * GZ * transpose(UZ)
    all(x -> fits(Int, x), GnZ) || continue
    Gn = Matrix{Int}(GnZ)
    mx = Gn[1, 1]
    for i in 1:n
      Gn[i, i] > mx && (mx = Gn[i, i])
    end
    mx < b0 || continue
    return Gn, UZ
  end
  return nothing
end

function _bt_reduce_gram(L::ZZLat)
  G = gram_matrix(L)
  s = sign(G[1, 1])
  d = denominator(G)
  Gint = change_base_ring(ZZ, s * d * G)
  c = content(Gint)
  Gint = divexact(Gint, c)
  Glll, T = lll_gram_with_transform(Gint)
  all(x -> fits(Int, x), Glll) || return nothing
  Gm = Matrix{Int}(Glll)
  sb = _bt_short_basis(Gm)
  if sb !== nothing
    Gm, U = sb
    T = U * T
  end
  return Gm, T, d//c
end

@doc raw"""
    _automorphism_group_backtrack(L::ZZLat) -> Vector{ZZMatrix}, ZZRingElem

Return generators of the isometry group of the definite lattice `L` (with
respect to the basis of `L`) together with its order, using the short vector
backtrack search.  Returns `nothing` if the lattice is out of range for the
implementation, in which case the caller should fall back to the general
Plesken--Souvignier implementation.
"""
function _automorphism_group_backtrack(L::ZZLat)
  @req is_definite(L) "Lattice must be definite"
  n = rank(L)
  if n == 0
    return ZZMatrix[identity_matrix(ZZ, 0)], one(ZZRingElem)
  end
  if n == 1
    return ZZMatrix[-identity_matrix(ZZ, 1)], ZZRingElem(2)
  end
  red = _bt_reduce_gram(L)
  red === nothing && return nothing
  G, T = red[1], red[2]
  # A lattice whose short vectors do not span needs a long basis vector, and
  # the shell of that norm can be astronomically large: one lattice of
  # 81.lattices has a basis of norms 2 and 4 with a single vector of norm 30,
  # and its vectors of norm at most 6 still only reach rank 16 of 17.  Since
  # everything here starts by enumerating up to the largest diagonal entry,
  # such a lattice has to be handed back to the caller rather than attempted.
  bnd = G[1, 1]
  for i in 1:n
    G[i, i] > bnd && (bnd = G[i, i])
  end
  let lv = _bt_ball_volumes(n), A = Matrix{Float64}(undef, n, n),
      q = Vector{Float64}(undef, n)
    if _bt_gs_norms!(q, A, G, collect(1:n), n)
      _bt_enum_cost(q, n, Float64(bnd), lv) > log(2.0e7) && return nothing
    end
  end
  local gens0, ord
  try
    gens0, ord = _bt_automorphism_group(G)
  catch e
    e isa BTOverflow && return nothing
    rethrow(e)
  end
  Tinv = inv(T)
  gens = ZZMatrix[Tinv * matrix(ZZ, g) * T for g in gens0]
  @hassert :Lattice 1 all(g -> change_base_ring(QQ, g) * gram_matrix(L) *
                          transpose(change_base_ring(QQ, g)) == gram_matrix(L), gens)
  return gens, ord
end

@doc raw"""
    _is_isometric_with_isometry_backtrack(L::ZZLat, M::ZZLat) -> Bool, QQMatrix

Decide whether the definite lattices `L` and `M` are isometric.  If so, the
second return value is a matrix `T` with
`T*gram_matrix(M)*transpose(T) == gram_matrix(L)`.  Returns `nothing` if the
lattices are out of range for the implementation.
"""
function _is_isometric_with_isometry_backtrack(L::ZZLat, M::ZZLat)
  @req is_definite(L) && is_definite(M) "Lattices must be definite"
  if rank(L) != rank(M)
    return false, zero_matrix(QQ, 0, 0)
  end
  if rank(L) == 0
    return true, zero_matrix(QQ, 0, 0)
  end
  if sign(gram_matrix(L)[1, 1]) != sign(gram_matrix(M)[1, 1])
    return false, zero_matrix(QQ, 0, 0)
  end
  if rank(L) == 1
    gL = gram_matrix(L)[1, 1]
    gM = gram_matrix(M)[1, 1]
    gL == gM && return true, identity_matrix(QQ, 1)
    return false, zero_matrix(QQ, 0, 0)
  end
  redL = _bt_reduce_gram(L)
  redM = _bt_reduce_gram(M)
  (redL === nothing || redM === nothing) && return nothing
  G1, TL, sL = redL
  G2, TM, sM = redM
  # a scaling is an invariant of the isometry class
  sL == sM || return false, zero_matrix(QQ, 0, 0)
  local fl, T0
  try
    fl, T0 = _bt_isometry(G1, G2)
  catch e
    e isa BTOverflow && return nothing
    rethrow(e)
  end
  fl || return false, zero_matrix(QQ, 0, 0)
  T = change_base_ring(QQ, inv(TL) * matrix(ZZ, T0) * TM)
  @hassert :Lattice 1 T * gram_matrix(M) * transpose(T) == gram_matrix(L)
  return true, T
end

# Fill in `L.automorphism_group_generators` and `L.automorphism_group_order`
# using the backtrack search.  Falls back to the Plesken--Souvignier
# implementation for input which is out of range.
function _assert_has_automorphisms_backtrack(L::ZZLat; redo::Bool = false)
  if !redo && isdefined(L, :automorphism_group_generators)
    return nothing
  end
  if !is_definite(L)
    return __assert_has_automorphisms(L; redo)
  end
  res = _automorphism_group_backtrack(L)
  if res === nothing
    return __assert_has_automorphisms(L; redo)
  end
  L.automorphism_group_generators = res[1]
  L.automorphism_group_order = res[2]
  return nothing
end
