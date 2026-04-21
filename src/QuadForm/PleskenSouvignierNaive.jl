# Plesken-Souvignier lattice automorphism algorithm (naive implementation)
# Original algorithm by B. Souvignier
# Julia implementation for Hecke

################################################################################
#
#  Data structures
#
################################################################################

mutable struct _QfAutoFingerprint
  diag::Vector{Int}    # diagonal of fingerprint matrix
  per::Vector{Int}     # permutation of basis indices
  e::Vector{Int}       # indices of standard basis vectors in V
end

mutable struct _QfAutoGroup
  ng::Vector{Int}      # number of generators at each level
  nsg::Vector{Int}     # number of stabilizer generators at each level
  ord::Vector{Int}     # orbit length at each level
  g::Vector{Vector{Matrix{Int}}}  # generators at each level
end

mutable struct _QfAutoCtx
  dim::Int
  F::Vector{Matrix{Int}}   # list of invariant forms (just [gram] for us)
  V::Vector{Vector{Int}}   # short vectors, canonicalized (first nonzero > 0)
  W::Vector{Vector{Int}}   # W[j][k] = norm of V[j] w.r.t. F[k]
  v::Vector{Matrix{Int}}   # v[k] = F[k] * V (precomputed; v[k][:,j] = F[k]*V[j])
  p::Int                   # prime for modular arithmetic
end

const _CombEntry = Tuple{Vector{Vector{Int}}, Matrix{Int}, Matrix{Int}, Vector{Matrix{Int}}}
const _BacherEntry = Tuple{Tuple{Int, Int, Int}, Vector{Int}}

mutable struct _QfAutoCand
  cdep::Int
  comb::Union{Nothing, Vector{Union{Nothing, _CombEntry}}}
  bacher_pol::Vector{_BacherEntry}
end

################################################################################
#
#  Helper: scalar product via precomputed v
#
################################################################################

# scp(V[i], F[k], V[j]) = dot(V[i], v[k][:,j])
@inline function _scp(Vi::AbstractVector{Int}, vkj::AbstractVector{Int})
  s = 0
  @inbounds @simd for l in eachindex(Vi)
    s += Vi[l] * vkj[l]
  end
  return s
end

# scp with direct column access: dot(Vi, M[:, col]) — avoids SubArray creation
@inline function _scp_col(Vi::Vector{Int}, M::Matrix{Int}, col::Int)
  s = 0
  @inbounds @simd for l in eachindex(Vi)
    s += Vi[l] * M[l, col]
  end
  return s
end

################################################################################
#
#  Canonicalize a vector: first nonzero entry positive;
#  returns (sign, canonical_vector)
#
################################################################################

function _zv_canon!(w::Vector{Int})
  @inbounds for i in eachindex(w)
    if w[i] != 0
      if w[i] < 0
        @simd for j in eachindex(w)
          w[j] = -w[j]
        end
        return -1
      else
        return 1
      end
    end
  end
  return 1
end

################################################################################
#
#  operate: apply matrix A to V[|nr|], with sign(nr), return signed index
#
################################################################################

function _operate(nr::Int, A::Matrix{Int}, V::Vector{Vector{Int}},
                  Vdict::Dict{Vector{Int}, Int})
  w = Vector{Int}(undef, length(V[1]))
  return _operate!(w, nr, A, V, Vdict)
end

function _operate!(w::Vector{Int}, nr::Int, A::Matrix{Int}, V::Vector{Vector{Int}},
                   Vdict::Dict{Vector{Int}, Int})
  idx = abs(nr)
  dim = length(w)
  Vi = V[idx]
  # Column-major access: iterate over columns of A (contiguous in memory)
  @inbounds begin
    for i in 1:dim
      w[i] = 0
    end
    for j in 1:dim
      vj = Vi[j]
      vj == 0 && continue
      if vj == 1
        @simd for i in 1:dim
          w[i] += A[i, j]
        end
      elseif vj == -1
        @simd for i in 1:dim
          w[i] -= A[i, j]
        end
      else
        @simd for i in 1:dim
          w[i] += A[i, j] * vj
        end
      end
    end
  end
  eps = _zv_canon!(w)
  if nr < 0
    eps = -eps
  end
  im = get(Vdict, w, 0)
  if im == 0
    error("qfauto: image of vector not found")
  end
  return eps * im
end

################################################################################
#
#  Orbit computation
#
################################################################################

function _orbit(pt::Vector{Int}, H::Vector{Matrix{Int}},
                V::Vector{Vector{Int}}, Vdict::Dict{Vector{Int}, Int})
  n = length(V)
  flag = zeros(Int8, 2 * n + 1)  # index im ∈ [-n, n], offset n+1
  orb = Int[]
  opbuf = Vector{Int}(undef, length(V[1]))
  for p in pt
    push!(orb, p)
    @inbounds flag[p + n + 1] = 1
  end
  cnd = 1
  while cnd <= length(orb)
    for H_i in H
      im = _operate!(opbuf, orb[cnd], H_i, V, Vdict)
      @inbounds if flag[im + n + 1] == 0
        push!(orb, im)
        flag[im + n + 1] = 1
      end
    end
    cnd += 1
  end
  return orb
end

function _orbitlen(pt::Int, maxlen::Int, H::Vector{Matrix{Int}},
                   V::Vector{Vector{Int}}, Vdict::Dict{Vector{Int}, Int})
  n = length(V)
  flag = falses(2 * n + 1)
  orb = Int[pt]
  opbuf = Vector{Int}(undef, length(V[1]))
  @inbounds flag[pt + n + 1] = true
  cnd = 1
  while cnd <= length(orb) && length(orb) < maxlen
    for H_i in H
      length(orb) >= maxlen && break
      im = _operate!(opbuf, orb[cnd], H_i, V, Vdict)
      @inbounds if !flag[im + n + 1]
        push!(orb, im)
        flag[im + n + 1] = true
      end
    end
    cnd += 1
  end
  return length(orb)
end

################################################################################
#
#  orbdelete: remove elements of orb2 from orb1 (in-place), return new length
#
################################################################################

function _orbdelete!(orb1::Vector{Int}, orb2::Vector{Int})
  s = Set(orb2)
  filter!(x -> !(x in s), orb1)
  return length(orb1)
end

function _orbsubtract!(Cs::Vector{Int}, pt::Vector{Int},
                       H::Vector{Matrix{Int}},
                       V::Vector{Vector{Int}}, Vdict::Dict{Vector{Int}, Int})
  orb = _orbit(pt, H, V, Vdict)
  _orbdelete!(Cs, orb)
  return length(Cs), length(orb)
end

################################################################################
#
#  Fingerprint computation
#
################################################################################

function _possible_count(F::Vector{Matrix{Int}}, V::Vector{Vector{Int}},
                         W::Vector{Vector{Int}}, v::Vector{Matrix{Int}},
                         per::Vector{Int}, I::Int, J::Int)
  n = length(V)
  f = length(F)
  count = 0
  for j in 1:n
    Wj = W[j]
    Vj = V[j]
    okp = true
    okm = true
    for k in 1:f
      if Wj[k] != F[k][J, J]
        okp = false
        okm = false
        break
      end
      for i in 1:I
        sp = _scp_col(Vj, F[k], per[i])
        target = F[k][J, per[i]]
        if sp != target
          okp = false
        end
        if sp != -target
          okm = false
        end
        if !okp && !okm
          break
        end
      end
      if !okp && !okm
        break
      end
    end
    if okp
      count += 1
    end
    if okm
      count += 1
    end
  end
  return count
end

################################################################################
#
#  Fingerprint: _qf_fingerprint!
#
################################################################################

function _qf_fingerprint!(fp, qf)
  V = qf.V
  W = qf.W
  dim = qf.dim
  F = qf.F
  n = length(V)
  f = length(F)

  fp.per = collect(1:dim)
  fp.e = zeros(Int, dim)
  fp.diag = zeros(Int, dim)

  # Mf[i,j] is the fingerprint matrix
  Mf = zeros(Int, dim, dim)

  # First row: count vectors with same norm as basis vector j
  for j in 1:n
    Wj = W[j]
    for i in 1:dim
      ok = true
      for k in 1:f
        if Wj[k] != F[k][i, i]
          ok = false
          break
        end
      end
      if ok
        Mf[1, i] += 2  # count both v and -v
      end
    end
  end

  for i in 1:dim-1
    # find min entry in row i among remaining columns
    min_idx = i
    for j in i+1:dim
      if Mf[i, fp.per[j]] < Mf[i, fp.per[min_idx]]
        min_idx = j
      end
    end
    fp.per[i], fp.per[min_idx] = fp.per[min_idx], fp.per[i]

    # set column below min to 0
    for j in i+1:dim
      Mf[j, fp.per[i]] = 0
    end

    # compute row i+1
    for j in i+1:dim
      Mf[i+1, fp.per[j]] = _possible_count(F, V, W, qf.v, fp.per, i, fp.per[j])
    end
  end

  # Extract diagonal and find standard basis vectors
  ei = zeros(Int, dim)
  for i in 1:dim
    fp.diag[i] = Mf[i, fp.per[i]]
    # find e_{per[i]} in V
    fill!(ei, 0)
    ei[fp.per[i]] = 1
    found = false
    for j in 1:n
      if V[j] == ei
        fp.e[i] = j
        found = true
        break
      end
    end
    if !found
      error("qfauto: standard basis vector e_$(fp.per[i]) not found in V")
    end
  end
end

################################################################################
#
#  matgen: generate matrix from assignment x and permutation per
#
################################################################################

function _matgen(x::Vector{Int}, per::Vector{Int}, V::Vector{Vector{Int}})
  dim = length(x)
  X = zeros(Int, dim, dim)
  _matgen!(X, x, per, V)
  return X
end

function _matgen!(X::Matrix{Int}, x::Vector{Int}, per::Vector{Int}, V::Vector{Vector{Int}})
  dim = length(x)
  @inbounds begin
    for j in 1:dim, i in 1:dim
      X[i, j] = 0
    end
    for i in 1:dim
      xi = x[i]
      pi = per[i]
      if xi > 0
        Vi = V[xi]
        for l in 1:dim
          X[l, pi] = Vi[l]
        end
      elseif xi < 0
        Vi = V[-xi]
        for l in 1:dim
          X[l, pi] = -Vi[l]
        end
      end
    end
  end
  return X
end

################################################################################
#
#  stabil: compute stabilizer element
#
################################################################################

function _stabil(x1::Vector{Int}, x2::Vector{Int}, per::Vector{Int},
                 G_mat::Matrix{Int}, V::Vector{Vector{Int}},
                 Vdict::Dict{Vector{Int}, Int}, p::Int)
  dim = length(x1)
  XG = Matrix{Int}(undef, dim, dim)
  X2 = Matrix{Int}(undef, dim, dim)
  S = Matrix{Int}(undef, dim, dim)
  M = Matrix{Int}(undef, dim, 2 * dim)
  x = Vector{Int}(undef, dim)
  opbuf = Vector{Int}(undef, dim)
  _stabil!(S, XG, X2, M, x, opbuf, x1, x2, per, G_mat, V, Vdict, p)
  return S
end

function _stabil!(S::Matrix{Int}, XG::Matrix{Int}, X2::Matrix{Int},
                  M::Matrix{Int}, xtmp::Vector{Int}, opbuf::Vector{Int},
                  x1::Vector{Int}, x2::Vector{Int}, per::Vector{Int},
                  G_mat::Matrix{Int}, V::Vector{Vector{Int}},
                  Vdict::Dict{Vector{Int}, Int}, p::Int)
  dim = length(x1)
  # Compute xtmp[i] = operate(x1[i], G_mat)
  for i in 1:dim
    xtmp[i] = _operate!(opbuf, x1[i], G_mat, V, Vdict)
  end
  _matgen!(XG, xtmp, per, V)
  _matgen!(X2, x2, per, V)
  # S = X2^{-1} * XG mod p
  _zm_divmod!(S, X2, XG, p, M)
  return S
end

function _zm_divmod(A::Matrix{Int}, B::Matrix{Int}, p::Int)
  # Compute A^{-1} * B mod p, lift to centered residues
  # Native implementation avoiding Nemo overhead
  n = size(A, 1)
  M = Matrix{Int}(undef, n, 2 * n)
  @inbounds for i in 1:n, j in 1:n
    M[i, j] = mod(A[i, j], p)
    M[i, n + j] = mod(B[i, j], p)
  end
  # Gauss-Jordan elimination on [A | B] → [I | A^{-1}*B]
  @inbounds for col in 1:n
    # Find pivot
    pivot = col
    while pivot <= n && M[pivot, col] == 0
      pivot += 1
    end
    # Swap rows
    if pivot != col
      for j in 1:2*n
        M[col, j], M[pivot, j] = M[pivot, j], M[col, j]
      end
    end
    # Scale pivot row
    inv_piv = invmod(M[col, col], p)
    for j in col:2*n
      M[col, j] = mod(M[col, j] * inv_piv, p)
    end
    # Eliminate column
    for row in 1:n
      row == col && continue
      factor = M[row, col]
      factor == 0 && continue
      for j in col:2*n
        M[row, j] = mod(M[row, j] - factor * M[col, j], p)
      end
    end
  end
  # Extract result with centered residues
  half = p >> 1
  result = Matrix{Int}(undef, n, n)
  @inbounds for i in 1:n, j in 1:n
    v = M[i, n + j]
    result[i, j] = v > half ? v - p : v
  end
  return result
end

function _zm_divmod!(result::Matrix{Int}, A::Matrix{Int}, B::Matrix{Int}, p::Int,
                     M::Matrix{Int})
  # In-place version: writes to result, uses M as n×2n work buffer
  n = size(A, 1)
  @inbounds for i in 1:n, j in 1:n
    M[i, j] = mod(A[i, j], p)
    M[i, n + j] = mod(B[i, j], p)
  end
  @inbounds for col in 1:n
    pivot = col
    while pivot <= n && M[pivot, col] == 0
      pivot += 1
    end
    if pivot != col
      for j in 1:2*n
        M[col, j], M[pivot, j] = M[pivot, j], M[col, j]
      end
    end
    inv_piv = invmod(M[col, col], p)
    for j in col:2*n
      M[col, j] = mod(M[col, j] * inv_piv, p)
    end
    for row in 1:n
      row == col && continue
      factor = M[row, col]
      factor == 0 && continue
      for j in col:2*n
        M[row, j] = mod(M[row, j] - factor * M[col, j], p)
      end
    end
  end
  half = p >> 1
  @inbounds for i in 1:n, j in 1:n
    v = M[i, n + j]
    result[i, j] = v > half ? v - p : v
  end
  return result
end

################################################################################
#
#  Scalar product vector computation (for vector sum candidates)
#
################################################################################

function _scpvector(w::Vector{Int}, b::Vector{Int}, I::Int, dep::Int,
                    v::Vector{Matrix{Int}}, V::Vector{Vector{Int}})
  nf = length(v)
  scpvec = zeros(Int, dep * nf)
  for i in I:-1:max(1, I - dep + 1)
    bi = b[i]
    abi = abs(bi)
    sgn = bi > 0 ? 1 : -1
    for j in 1:nf
      sp = _scp_col(w, v[j], abi)
      scpvec[(j - 1) * dep + I - i + 1] = sgn * sp
    end
  end
  return scpvec
end

################################################################################
#
#  scpvecs: compute list of scalar product combinations
#
################################################################################

function _scpvecs(I::Int, b::Vector{Int}, dep::Int, qf::_QfAutoCtx)
  V = qf.V
  F = qf.F
  v = qf.v
  n = length(V)
  dim = qf.dim
  len = length(F) * dep

  # list of scpvecs (sorted), vec of corresponding vector sums
  list = [zeros(Int, len)]  # zero vector placeholder
  vec = [zeros(Int, dim)]

  for j in 1:n
    Vj = V[j]
    scpvec = _scpvector(Vj, b, I, dep, v, V)
    if iszero(scpvec)
      continue
    end
    # canonicalize
    scpvec_c = copy(scpvec)
    sign = _zv_canon!(scpvec_c)

    nr = searchsortedfirst(list, scpvec_c)
    if nr <= length(list) && list[nr] == scpvec_c
      # already in list, add vector
      @inbounds for l in 1:dim
        vec[nr][l] += sign * Vj[l]
      end
    else
      # new entry
      insert!(list, nr, scpvec_c)
      newvec = sign < 0 ? -copy(Vj) : copy(Vj)
      insert!(vec, nr, newvec)
    end
  end

  return list, vec
end

################################################################################
#
#  scpforms: Gram matrices of basis vectors b w.r.t. each form
#
################################################################################

function _scpforms(b::Vector{Vector{Int}}, F::Vector{Matrix{Int}})
  nf = length(F)
  nb = length(b)
  dim = size(F[1], 1)
  gram = Vector{Matrix{Int}}(undef, nf)
  for i in 1:nf
    Fi = F[i]
    g = zeros(Int, nb, nb)
    # Fbi[j] = Fi * b[j]
    Fbi = [zeros(Int, dim) for _ in 1:nb]
    @inbounds for j in 1:nb
      for r in 1:dim, c in 1:dim
        Fbi[j][r] += Fi[r, c] * b[j][c]
      end
    end
    @inbounds for j in 1:nb, k in 1:nb
      for l in 1:dim
        g[j, k] += b[j][l] * Fbi[k][l]
      end
    end
    gram[i] = g
  end
  return gram
end

################################################################################
#
#  gen_comb: compute combination data for candidate pruning
#
################################################################################

function _gen_comb(cdep::Int, A::ZZMatrix, e::Vector{Int}, qf::_QfAutoCtx;
                   lim::Int=0)
  dim = qf.dim
  comb = Vector{Union{Nothing, _CombEntry}}(undef, dim)
  for i in 1:dim
    list, sumveclist = _scpvecs(i, e, cdep, qf)

    # Convert sumveclist to ZZMatrix for LLL
    nc = length(sumveclist)
    M = zero_matrix(ZZ, nc, dim)
    for j in 1:nc, k in 1:dim
      M[j, k] = sumveclist[j][k]
    end

    # Gram = M^T * A * M (quadratic form on vectors), then LLL with image
    # In our convention (row vectors): gram = M * A * M^T, T from LLL_gram
    # But gram may be singular. Use lattice LLL on M directly via A-inner product.
    MA = M * A
    gram = MA * transpose(M)  # nc × nc, possibly singular

    # Use LLL on the rows of M with Gram matrix A
    # Alternatively, just do column-style: find an LLL-reduced basis of the
    # lattice spanned by rows of M with inner product defined by A.
    # We use the Hermite normal form approach: get rank via hnf, then LLL.
    r, hM = hnf_with_transform(M)
    # Find rank = number of non-zero rows in r
    rank = 0
    for j in 1:nrows(r)
      if !is_zero_row(r, j)
        rank += 1
      end
    end
    if rank == 0
      # No non-trivial vector sums at this level; store trivial
      comb[i] = nothing
      continue
    end

    # Extract the rank non-zero rows from hM as the transformation
    # Actually, let's use a simpler approach: just do LLL on the non-zero
    # part of M.
    # Filter non-zero rows of M
    nonzero_rows = Int[]
    for j in 1:nc
      if !is_zero_row(M, j)
        push!(nonzero_rows, j)
      end
    end
    Msub = M[nonzero_rows, :]
    gram_sub = Msub * A * transpose(Msub)
    _, Tsub = lll_gram_with_transform(gram_sub)
    
    # The LLL may not remove zero-norm rows. Filter them out.
    B_full = Tsub * Msub  # nrows(Tsub) × dim
    # Check which rows of B_full are actually nonzero (have positive norm)
    keep = Int[]
    for j in 1:nrows(B_full)
      if !is_zero_row(B_full, j)
        push!(keep, j)
      end
    end
    rank = length(keep)

    if lim > 0 && rank >= lim
      return nothing
    end

    if rank == 0
      comb[i] = nothing
      continue
    end

    B = B_full[keep, :]  # rank × dim
    Tsub_kept = Tsub[keep, :]

    # Build full T: rank × nc, mapping from all sumveclist to basis rows
    T_full = zero_matrix(ZZ, rank, nc)
    for j in 1:rank
      for (idx, orig_row) in enumerate(nonzero_rows)
        T_full[j, orig_row] = Tsub_kept[j, idx]
      end
    end

    BQ = change_base_ring(QQ, B)

    # sumvecbase (rows of B as Int vectors)
    sumvecbase = Vector{Vector{Int}}(undef, rank)
    for j in 1:rank
      sumvecbase[j] = Int[Int(B[j, k]) for k in 1:dim]
    end

    trans_mat = Matrix{Int}(undef, rank, nc)
    for j in 1:rank, k in 1:nc
      trans_mat[j, k] = Int(T_full[j, k])
    end

    # ccoef: express each row of M as linear combination of rows of B
    # M = ccoef * B, solve B * ccoef^T = M (but B is rank × dim, M is nc × dim)
    # Solve B^T * ccoef_j = M_j^T for each j, or equivalently solve
    # ccoef * B = M, i.e., ccoef = M * pinv(B)
    # Since B has full row rank: ccoef = M * B^T * (B * B^T)^{-1}
    BBt = BQ * transpose(BQ)  # rank × rank, invertible
    MQ = change_base_ring(QQ, M)
    MBt = MQ * transpose(BQ)  # nc × rank
    BBt_inv = inv(BBt)
    ccoef_Q = MBt * BBt_inv  # nc × rank
    ccoef_mat = Matrix{Int}(undef, nc, rank)
    for j in 1:nc, k in 1:rank
      ccoef_mat[j, k] = Int(ccoef_Q[j, k])
    end

    cF = _scpforms(sumvecbase, qf.F)

    comb[i] = (list, trans_mat, ccoef_mat, cF)
  end
  return comb
end

function _init_comb(A::ZZMatrix, e::Vector{Int}, qf::_QfAutoCtx)
  dim = qf.dim
  cdep = 1
  while true
    comb = _gen_comb(cdep, A, e, qf; lim = div(dim + 1, 2))
    if comb === nothing
      break
    end
    cdep += 1
  end
  cdep = max(1, cdep - 1)
  comb = _gen_comb(cdep, A, e, qf)
  return cdep, comb
end

################################################################################
#
#  Bacher polynomials
#
################################################################################

function _bacher(I::Int, S::Int, qf::_QfAutoCtx)
  V = qf.V
  W = qf.W
  Fv = qf.v[1]
  n = length(V)
  absI = abs(I)

  # find vectors with same length as V[absI] and scalar product S with V[absI]
  vI = V[absI]
  list = Int[]
  for i in 1:n
    if W[i][1] == W[absI][1]
      sp = _scp_col(vI, Fv, i)
      if sp == S
        push!(list, i)
      end
      if -sp == S
        push!(list, -i)
      end
    end
  end

  nlist = length(list)
  if nlist == 0
    return (0, 0, 0), Int[]
  end

  counts = zeros(Int, nlist)
  for i in 1:nlist
    # listxy: vectors from list that have scalar product S with V[|list[i]|]
    S1 = list[i] > 0 ? S : -S
    listxy = Int[]
    for j in 1:nlist
      S2 = list[j] > 0 ? S1 : -S1
      if _scp_col(V[abs(list[i])], Fv, abs(list[j])) == S2
        push!(listxy, list[j])
      end
    end
    nxy = length(listxy)
    cnt = 0
    for j in 1:nxy
      S1j = listxy[j] > 0 ? S : -S
      Vj = V[abs(listxy[j])]
      for k in j+1:nxy
        S2k = listxy[k] > 0 ? S1j : -S1j
        if _scp_col(Vj, Fv, abs(listxy[k])) == S2k
          cnt += 1
        end
      end
    end
    counts[i] = cnt
  end

  mind = minimum(counts)
  maxd = maximum(counts)
  coef = zeros(Int, maxd - mind + 1)
  for c in counts
    coef[c - mind + 1] += 1
  end
  return (nlist, mind, maxd), coef
end

function _init_bacher(bachdep::Int, fp::_QfAutoFingerprint, qf::_QfAutoCtx)
  result = Vector{_BacherEntry}(undef, bachdep)
  for i in 1:bachdep
    bachscp = W_norm(qf, fp.e[i]) ÷ 2
    result[i] = _bacher(fp.e[i], bachscp, qf)
  end
  return result
end

function W_norm(qf::_QfAutoCtx, idx::Int)
  return qf.W[idx][1]
end

function _bachcomp(pol::Tuple, coef::Vector{Int}, I::Int, qf::_QfAutoCtx)
  V = qf.V
  W = qf.W
  Fv = qf.v[1]
  n = length(V)
  sum_val, mind, maxd = pol
  S = W[I][1] ÷ 2
  vI = V[I]

  list = Int[]
  for i in 1:n
    length(list) > sum_val && return false
    if W[i][1] == W[I][1]
      sp = _scp_col(vI, Fv, i)
      if sp == S
        push!(list, i)
      end
      if -sp == S
        push!(list, -i)
      end
    end
  end
  if length(list) != sum_val
    return false
  end
  if length(list) == 0
    return true
  end

  co = zeros(Int, maxd - mind + 1)
  for i in eachindex(list)
    S1 = list[i] > 0 ? S : -S
    Vi = V[abs(list[i])]
    listxy = Int[]
    for j in eachindex(list)
      S2 = list[j] > 0 ? S1 : -S1
      if _scp_col(Vi, Fv, abs(list[j])) == S2
        push!(listxy, list[j])
      end
    end
    count = 0
    for j in eachindex(listxy)
      S1j = listxy[j] > 0 ? S : -S
      Vj = V[abs(listxy[j])]
      for k in j+1:length(listxy)
        count > maxd && break
        S2k = listxy[k] > 0 ? S1j : -S1j
        if _scp_col(Vj, Fv, abs(listxy[k])) == S2k
          count += 1
        end
      end
    end
    if count < mind || count > maxd
      return false
    end
    idx = count - mind + 1
    if co[idx] >= coef[idx]
      return false
    end
    co[idx] += 1
  end
  return true
end

################################################################################
#
#  Candidate computation (with vector sums)
#
################################################################################

function _candidates_novec!(CI::Vector{Int}, I::Int, x::Vector{Int},
                            qf::_QfAutoCtx, qff::_QfAutoCtx,
                            fp::_QfAutoFingerprint)
  V = qff.V
  W = qff.W
  v = qff.v
  F = qf.F
  n = length(V)
  f = length(F)
  dim = length(V[1])
  diagI = fp.diag[I]

  nr = 0
  fail = false
  @inbounds for j in 1:n
    Vj = V[j]
    Wj = W[j]
    okp = 0
    okm = 0
    for ki in 1:f
      # check norms
      if Wj[ki] != F[ki][fp.per[I], fp.per[I]]
        break
      end
      # check scalar products with previously assigned basis vectors
      good_p = true
      good_m = true
      for kk in 1:I-1
        xk = x[kk]
        if xk > 0
          sp = _scp_col(Vj, v[ki], xk)
        else
          sp = -_scp_col(Vj, v[ki], -xk)
        end
        if sp != F[ki][fp.per[I], fp.per[kk]]
          good_p = false
        end
        if sp != -F[ki][fp.per[I], fp.per[kk]]
          good_m = false
        end
        if !good_p && !good_m
          break
        end
      end
      if good_p
        okp += 1
      end
      if good_m
        okm += 1
      end
    end
    if okp == f
      if nr >= diagI
        return 0  # too many
      end
      nr += 1
      CI[nr] = j
    end
    if okm == f
      if nr >= diagI
        return 0
      end
      nr += 1
      CI[nr] = -j
    end
  end
  return nr
end

function _candidates!(CI::Vector{Int}, I::Int, x::Vector{Int},
                      qf::_QfAutoCtx, qff::_QfAutoCtx,
                      fp::_QfAutoFingerprint, cand::_QfAutoCand)
  if I >= 2 && I <= length(cand.bacher_pol)
    t = abs(x[I - 1])
    pol, coef = cand.bacher_pol[I - 1]
    if !_bachcomp(pol, coef, t, qff)
      return 0
    end
  end

  if I == 1 || cand.cdep == 0 || cand.comb === nothing
    return _candidates_novec!(CI, I, x, qf, qff, fp)
  end

  DEP = cand.cdep
  V = qff.V
  W = qff.W
  v = qff.v
  F = qf.F
  FF = qff.F
  n = length(V)
  f = length(F)
  dim = qf.dim
  len = f * DEP
  diagI = fp.diag[I]

  com = cand.comb[I - 1]
  if com === nothing
    return _candidates_novec!(CI, I, x, qf, qff, fp)
  end
  list, trans, ccoef, cF = com::_CombEntry
  rank = size(trans, 1)
  nc = length(list) - 1  # exclude zero vector at index 1

  # xvec: vector sums indexed by list position (flat matrix)
  nlist = length(list)
  xvec = zeros(Int, nlist, dim)
  nr = 0
  scpvec = zeros(Int, len)
  scpvec_c = zeros(Int, len)
  vec = zeros(Int, I - 1)

  @inbounds for j in 1:n
    Vj = V[j]
    Wj = W[j]
    okp = 0
    okm = 0
    fill!(scpvec, 0)

    for ki in 1:f
      # Compute scalar products with all previous basis vectors (unconditionally)
      for kk in 1:I-1
        xk = x[kk]
        if xk > 0
          vec[kk] = _scp_col(Vj, v[ki], xk)
        elseif xk < 0
          vec[kk] = -_scp_col(Vj, v[ki], -xk)
        else
          vec[kk] = 0
        end
      end

      # Check okp: all scalar products match AND norm matches
      all_match_p = true
      all_match_m = true
      for kk in 1:I-1
        if vec[kk] != F[ki][fp.per[I], fp.per[kk]]
          all_match_p = false
        end
        if vec[kk] != -F[ki][fp.per[I], fp.per[kk]]
          all_match_m = false
        end
        if !all_match_p && !all_match_m
          break
        end
      end
      if all_match_p && Wj[ki] == F[ki][fp.per[I], fp.per[I]]
        okp += 1
      end
      if all_match_m && Wj[ki] == F[ki][fp.per[I], fp.per[I]]
        okm += 1
      end

      # Fill scpvec (unconditionally, no norm check)
      for kk in I-1:-1:max(1, I - DEP)
        scpvec[(ki - 1) * DEP + I - kk] = vec[kk]
      end
    end

    if !iszero(scpvec)
      copyto!(scpvec_c, scpvec)
      sign = _zv_canon!(scpvec_c)
      num = searchsortedfirst(list, scpvec_c)
      if num > length(list) || list[num] != scpvec_c
        return 0  # not a partial automorphism
      end
      @inbounds for l in 1:dim
        xvec[num, l] += sign * Vj[l]
      end
    end

    if okp == f
      if nr >= diagI
        return 0
      end
      nr += 1
      CI[nr] = j
    end
    if okm == f
      if nr >= diagI
        return 0
      end
      nr += 1
      CI[nr] = -j
    end
  end

  if nr == diagI
    # verify vector sum lattice
    xbase = zeros(Int, rank, dim)
    @inbounds for i in 1:rank
      for jj in 1:dim
        s = 0
        for kk in 1:nc+1
          s += trans[i, kk] * xvec[kk, jj]
        end
        xbase[i, jj] = s
      end
    end

    # check scalar products
    fbi = zeros(Int, rank, dim)
    @inbounds for ki in 1:f
      fill!(fbi, 0)
      for jj in 1:rank
        for kk in 1:dim
          s = 0
          for l in 1:dim
            s += FF[ki][kk, l] * xbase[jj, l]
          end
          fbi[jj, kk] = s
        end
      end
      for jj in 1:rank, kk in 1:jj
        sp = 0
        for l in 1:dim
          sp += xbase[jj, l] * fbi[kk, l]
        end
        if sp != cF[ki][jj, kk]
          return 0
        end
      end
    end

    # check coefficients
    @inbounds for i in 1:nc+1
      for jj in 1:dim
        vj = 0
        for kk in 1:rank
          vj += ccoef[i, kk] * xbase[kk, jj]
        end
        if vj != xvec[i, jj]
          return 0
        end
      end
    end
  end

  return nr
end

################################################################################
#
#  stab: compute stabilizer elements
#
################################################################################

function _stab!(I::Int, G::_QfAutoGroup, fp::_QfAutoFingerprint,
                V::Vector{Vector{Int}}, Vdict::Dict{Vector{Int}, Int}, p::Int)
  dim = length(fp.diag)
  n = length(V)
  opbuf = Vector{Int}(undef, length(V[1]))

  # Preallocate buffers for _stabil!
  XG_buf = Matrix{Int}(undef, dim, dim)
  X2_buf = Matrix{Int}(undef, dim, dim)
  S_buf = Matrix{Int}(undef, dim, dim)
  M_buf = Matrix{Int}(undef, dim, 2 * dim)
  xtmp_buf = Vector{Int}(undef, dim)

  Rest = 0
  for i in I:dim
    if fp.diag[i] > 1 && G.ord[i] < fp.diag[i]
      Rest += 1
    end
  end
  Maxfail = Rest
  for i in 1:dim
    if fp.diag[i] > 1
      Maxfail += 1
    end
  end

  # Collect all generators from level I onwards
  H = Matrix{Int}[]
  for i in I:dim
    for j in 1:G.ng[i]
      push!(H, G.g[i][j])
    end
  end

  # w[im] stores element mapping fp.e[I] to im
  w = Dict{Int, Vector{Int}}()
  orb = Int[]
  flag = falses(2 * n + 1)

  push!(orb, fp.e[I])
  @inbounds flag[fp.e[I] + n + 1] = true
  w[fp.e[I]] = [fp.e[i] for i in 1:dim]

  cnd = 1
  fail = 0
  while cnd <= length(orb) && fail < Maxfail + Rest
    nH = length(H)
    i = 1
    while i <= nH && fail < Maxfail + Rest
      if fail >= Maxfail
        cnd_use = rand(1:length(orb))
        i_use = rand(1:nH)
      else
        cnd_use = cnd
        i_use = i
      end

      im = _operate!(opbuf, orb[cnd_use], H[i_use], V, Vdict)
      @inbounds if !flag[im + n + 1]
        push!(orb, im)
        flag[im + n + 1] = true
        wim = Vector{Int}(undef, dim)
        for j in 1:dim
          wim[j] = _operate!(opbuf, w[orb[cnd_use]][j], H[i_use], V, Vdict)
        end
        w[im] = wim
      else
        # find first index where images differ
        j_diff = 0
        for j in I:dim
          if _operate!(opbuf, w[orb[cnd_use]][j], H[i_use], V, Vdict) != w[im][j]
            j_diff = j
            break
          end
        end
        if j_diff > 0 && (G.ord[j_diff] < fp.diag[j_diff] || fail >= Maxfail)
          _stabil!(S_buf, XG_buf, X2_buf, M_buf, xtmp_buf, opbuf,
                   w[orb[cnd_use]], w[im], fp.per, H[i_use], V, Vdict, p)
          # test if S enlarges orbit
          Hj = vcat([S_buf], [G.g[k][l] for k in j_diff:dim for l in 1:G.ng[k]])
          tmplen = _orbitlen(fp.e[j_diff], fp.diag[j_diff], Hj, V, Vdict)
          if tmplen > G.ord[j_diff] || fail >= Maxfail
            G.ord[j_diff] = tmplen
            G.ng[j_diff] += 1
            G.nsg[j_diff] += 1
            # Insert S at position nsg[j_diff] (copy since S_buf is reused)
            S = copy(S_buf)
            insert!(G.g[j_diff], G.nsg[j_diff], S)
            push!(H, S)
            nH += 1
            if fail < Maxfail
              fail = 0
            else
              fail += 1
            end
          else
            fail += 1
          end
        elseif (j_diff > 0 && j_diff < dim && fail < Maxfail) ||
               (j_diff == dim && fail >= Maxfail)
          fail += 1
        end
      end
      i += 1
    end
    if fail < Maxfail
      cnd += 1
    end
  end
end

################################################################################
#
#  aut: recursive backtrack search for automorphisms
#
################################################################################

function _aut(step::Int, x::Vector{Int}, C::Vector{Vector{Int}},
              G::_QfAutoGroup, qf::_QfAutoCtx,
              fp::_QfAutoFingerprint, cand::_QfAutoCand)
  dim = qf.dim
  if step == dim && length(C[dim]) > 0 && C[dim][1] != 0
    x[dim] = C[dim][1]
    return true
  end

  while length(C[step]) > 0 && C[step][1] != 0
    x[step] = C[step][1]
    # Ensure C[step+1] has correct size (filter! in recursive calls may have shrunk it)
    resize!(C[step + 1], fp.diag[step + 1])
    nbc = _candidates!(C[step + 1], step + 1, x, qf, qf, fp, cand)
    if nbc == fp.diag[step + 1]
      if _aut(step + 1, x, C, G, qf, fp, cand)
        return true
      end
    end
    # delete chosen vector
    deleteat!(C[step], 1)
  end
  return false
end

################################################################################
#
#  autom: main search loop
#
################################################################################

function _autom!(G::_QfAutoGroup, qf::_QfAutoCtx, fp::_QfAutoFingerprint,
                 cand::_QfAutoCand, Vdict::Dict{Vector{Int}, Int})
  dim = qf.dim
  V = qf.V
  n = length(V)

  C = [zeros(Int, fp.diag[i]) for i in 1:dim]
  x = zeros(Int, dim)

  for step in 1:dim
    # Collect generators from step onwards
    H = Matrix{Int}[]
    for i in step:dim
      for j in 1:G.ng[i]
        push!(H, G.g[i][j])
      end
    end

    bad = Int[]

    # Fix first step-1 basis vectors
    for i in 1:step-1
      x[i] = fp.e[i]
    end

    # Compute candidates for x[step]
    if fp.diag[step] > 1
      resize!(C[step], fp.diag[step])
      nC = _candidates!(C[step], step, x, qf, qf, fp, cand)
    else
      C[step] = [fp.e[step]]
      nC = 1
    end

    # Remove orbit of step-th basis vector from candidates
    orb = _orbit([fp.e[step]], H, V, Vdict)
    G.ord[step] = length(orb)
    _orbdelete!(C[step], orb)
    nC = length(C[step])

    while nC > 0
      im = C[step][1]
      found = false
      x[step] = im

      if step < dim
        # Ensure C[step+1] has correct size (may have been shrunk by filter! in _aut)
        resize!(C[step + 1], fp.diag[step + 1])
        nbc = _candidates!(C[step + 1], step + 1, x, qf, qf, fp, cand)
        if nbc == fp.diag[step + 1]
          found = _aut(step + 1, x, C, G, qf, fp, cand)
        end
      else
        found = true
      end

      if !found
        # Remove orbit of im
        orb_im = _orbit([im], H, V, Vdict)
        _orbdelete!(C[step], orb_im)
        push!(bad, im)
        nC = length(C[step])
      else
        # New generator found
        new_gen = _matgen(x, fp.per, V)
        G.ng[step] += 1
        push!(G.g[step], new_gen)

        # Add new generator to H (avoid full rebuild)
        push!(H, new_gen)

        orb = _orbit([fp.e[step]], H, V, Vdict)
        G.ord[step] = length(orb)
        _orbdelete!(C[step], orb)
        _orbdelete!(C[step], bad)
        nC = length(C[step])
      end
    end

    # Prune generators at step 1
    if step == 1
      tries = G.nsg[step] + 1
      while tries <= G.ng[step]
        Htest = Matrix{Int}[]
        for j in 1:G.ng[step]
          j == tries && continue
          push!(Htest, G.g[step][j])
        end
        for i in step+1:dim
          for j in 1:G.ng[i]
            push!(Htest, G.g[i][j])
          end
        end
        if _orbitlen(fp.e[step], G.ord[step], Htest, V, Vdict) == G.ord[step]
          deleteat!(G.g[step], tries)
          G.ng[step] -= 1
        else
          tries += 1
        end
      end
    end

    # Compute stabilizer
    if step < dim && G.ord[step] > 1
      _stab!(step, G, fp, V, Vdict, qf.p)
    end
  end
end

################################################################################
#
#  Initialize short vectors and context
#
################################################################################

function _init_qfauto(G::ZZMatrix)
  dim = nrows(G)
  A = Matrix{Int}(G)
  F = [A]

  # Compute max diagonal entry
  maxdiag = maximum(A[i, i] for i in 1:dim)

  # Enumerate short vectors (input assumed LLL reduced)
  sv = _short_vectors_gram_integral(Vector, G, ZZRingElem(maxdiag);
                                    is_lll_reduced_known=true)

  # Build vector list: canonicalize (first nonzero > 0), sort, unique
  Vraw = Vector{Vector{Int}}()
  for (v, _) in sv
    w = Int[Int(v[i]) for i in eachindex(v)]
    _zv_canon!(w)
    push!(Vraw, w)
  end
  sort!(Vraw)
  unique!(Vraw)

  # Compute norm vectors W[j][k] for each vector j and form k
  # Filter to keep only vectors whose norms match some basis vector norm
  f = length(F)
  norm_set = Set{Vector{Int}}()
  for i in 1:dim
    nv = Int[F[k][i, i] for k in 1:f]
    push!(norm_set, nv)
  end

  V = Vector{Vector{Int}}()
  W = Vector{Vector{Int}}()
  max_entry = 0
  for v in Vraw
    nv = Int[_scp_gram(v, F[k], v) for k in 1:f]
    if nv in norm_set
      push!(V, v)
      push!(W, nv)
      for c in v
        max_entry = max(max_entry, abs(c))
      end
    end
  end

  # Compute prime for modular arithmetic
  p = Int(next_prime(ZZRingElem(2 * max_entry + 1)))

  # Precompute v[k][:,j] = F[k] * V[j]
  n = length(V)
  v = Vector{Matrix{Int}}(undef, f)
  for k in 1:f
    Fk = F[k]
    vk = zeros(Int, dim, n)
    for j in 1:n
      Vj = V[j]
      for r in 1:dim
        s = 0
        @inbounds for c in 1:dim
          s += Fk[r, c] * Vj[c]
        end
        vk[r, j] = s
      end
    end
    v[k] = vk
  end

  qf = _QfAutoCtx(dim, F, V, W, v, p)
  return qf
end

function _scp_gram(x::Vector{Int}, G::Matrix{Int}, y::Vector{Int})
  n = length(x)
  s = 0
  @inbounds for i in 1:n
    xi = x[i]
    if xi != 0
      for j in 1:n
        s += xi * G[i, j] * y[j]
      end
    end
  end
  return s
end

################################################################################
#
#  Build dictionary for fast vector lookup
#
################################################################################

function _build_vdict(V::Vector{Vector{Int}})
  d = Dict{Vector{Int}, Int}()
  for i in eachindex(V)
    d[V[i]] = i
  end
  return d
end

################################################################################
#
#  Initialize group with -Id
#
################################################################################

function _init_group(fp::_QfAutoFingerprint, qf::_QfAutoCtx,
                     Vdict::Dict{Vector{Int}, Int})
  dim = qf.dim
  V = qf.V

  G = _QfAutoGroup(
    zeros(Int, dim),
    zeros(Int, dim),
    ones(Int, dim),
    [Matrix{Int}[] for _ in 1:dim]
  )

  # -Id is always an automorphism
  negId = -Matrix{Int}(I, dim, dim)
  push!(G.g[1], negId)
  G.ng[1] = 1

  # Compute orbit lengths
  for i in 1:dim
    H = Matrix{Int}[]
    for j in i:dim
      for k in 1:G.ng[j]
        push!(H, G.g[j][k])
      end
    end
    if !isempty(H)
      G.ord[i] = _orbitlen(fp.e[i], fp.diag[i], H, V, Vdict)
    else
      G.ord[i] = 1
    end
  end

  return G
end

################################################################################
#
#  Main entry point: qfauto
#
################################################################################

@doc raw"""
    _autgrp_naive(G::ZZMatrix; flags=nothing) -> (ZZRingElem, Vector{ZZMatrix})

Compute the automorphism group of the lattice with Gram matrix `G` using
the Plesken-Souvignier algorithm.

Returns a tuple `(order, generators)` where `order` is the group order
and `generators` is a vector of generator matrices.

If `flags` is set to a tuple `(cdep, bach)`, the vector sum depth `cdep`
and Bacher polynomial depth `bach` are used directly instead of being
automatically determined. When `flags` is `nothing` (the default), `cdep`
is auto-determined and `bach` defaults to `0`.
"""
function _autgrp_naive(G::ZZMatrix; flags=nothing)
  dim = nrows(G)
  if dim == 0
    return ZZRingElem(1), ZZMatrix[]
  end

  # LLL preprocessing
  maxdiag = maximum(G[i, i] for i in 1:dim)
  G2, U_lll = lll_gram_with_transform(G)
  maxdiag2 = maximum(G2[i, i] for i in 1:dim)
  if maxdiag2 < maxdiag
    G_use = G2
    U_transform = U_lll
  else
    G_use = G
    U_transform = nothing
  end

  qf = _init_qfauto(G_use)
  Vdict = _build_vdict(qf.V)

  fp = _QfAutoFingerprint(Int[], Int[], Int[])
  _qf_fingerprint!(fp, qf)

  cand = _QfAutoCand(0, nothing, _BacherEntry[])

  # Initialize candidate depth and combinations
  A_zz = G_use
  if flags === nothing
    cand.cdep, cand.comb = _init_comb(A_zz, fp.e, qf)
    cand.bacher_pol = _init_bacher(0, fp, qf)
  else
    cdep, bach = flags
    bach = min(bach, dim - 1)
    @req cdep >= 0 && bach >= 0 "flags must be non-negative"
    cand.cdep = cdep
    cand.comb = cdep > 0 ? _gen_comb(cdep, A_zz, fp.e, qf) : nothing
    cand.bacher_pol = _init_bacher(bach, fp, qf)
  end

  group = _init_group(fp, qf, Vdict)
  _autom!(group, qf, fp, cand, Vdict)

  # Compute order = product of orbit lengths
  order = ZZRingElem(1)
  for i in 1:dim
    order *= ZZRingElem(group.ord[i])
  end

  # Collect generators (exclude stabilizer gens), transform back if LLL was applied
  # If G_red = U * G * U^T, and g' is an automorphism of G_red, then
  # g_orig = U^T * g' * inv(U^T) is the corresponding automorphism of G
  gens = ZZMatrix[]
  Ut = U_transform !== nothing ? transpose(U_transform) : nothing
  for i in 1:dim
    for j in group.nsg[i]+1:group.ng[i]
      g = matrix(ZZ, group.g[i][j])
      if Ut !== nothing
        g = Ut * g * inv(Ut)
      end
      push!(gens, g)
    end
  end

  return order, gens
end
