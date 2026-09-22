# The function orbmod2 and dependencies were ported by and AI from the Pari/GP code of Gaëtan Chenevier and Olivier Taïbi, 2026:
# https://olitb.net/pro/uni29/
# The functionality to compute orbits and stabilizers of subspaces was added in cooperation with AI assistants (Glaude Opus 4.8, GPT 5.4), 2026.
# Simon Brandhorst takes responsibility for correctness.
#
# Copyright (C) 2026 Simon Brandhorst, Gaëtan Chenevier and Olivier Taïbi, 2026
# Permission to use, copy, modify, and/or distribute this software for any purpose with or without fee is hereby granted, provided that the above copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED “AS IS” AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.


_mod2_bit(::Type{T}, x::Integer) where {T <: Unsigned} = isodd(x) ? one(T) : zero(T)
_mod2_bit(::Type{T}, x::ZZRingElem) where {T <: Unsigned} = is_odd(x) ? one(T) : zero(T)
_mod2_bit(::Type{T}, x::FqFieldElem) where {T <: Unsigned} = iszero(x) ? zero(T) : one(T)

# Inputs: T is the packed word type, gens is a nonempty vector of n x n matrices.
function _pack_linear_generators_mod2(::Type{T}, gens::Vector) where {T <: Unsigned}
  isempty(gens) && throw(ArgumentError("at least one generator is required"))
  n = nrows(gens[1])
  ncols(gens[1]) != n && throw(ArgumentError("generators must be square matrices"))
  maxdim = 8 * sizeof(T) - 1
  n > maxdim && throw(ArgumentError("dimension > $maxdim not implemented for $T"))
  packed = Vector{T}(undef, n * length(gens))
  pos = 1
  for g in gens
    nrows(g) == n && ncols(g) == n || throw(ArgumentError("generators must have common size"))
    # Pack each column as a bit vector so row-action becomes bit operations.
    @inbounds for j in 1:n
      x = zero(T)
      for i in 1:n
        x |= _mod2_bit(T, g[i, j]) << (i - 1)
      end
      packed[pos] = x
      pos += 1
    end
  end
  return packed, n
end

@inline _parity_popcnt_mod2(x::T) where {T <: Unsigned} = isodd(count_ones(x)) ? one(T) : zero(T)

# Inputs: M is packed column data, offset selects one generator block, x is a packed row vector, n is the dimension.
function _matact_mod2(M::Vector{T}, offset::Int, x::T, n::Int) where {T <: Unsigned}
  res = zero(T)
  @inbounds for i in 0:(n - 1)
    res |= _parity_popcnt_mod2(M[offset + i] & x) << i
  end
  return res
end

#=
# this is slightly faster (5%) than _matact_mod2, but more complicated and not verified to be correct yet.
# hence disabled for now
# Inputs: packed stores generators as packed columns; output stores basis-row images per generator.
function _precompute_basis_images_mod2(::Type{T}, packed::Vector{T}, n::Int, ngens::Int) where {T <: Unsigned}
  basis_images = Vector{T}(undef, n * ngens)
  @inbounds for g in 0:(ngens - 1)
    offset = g * n + 1
    for i in 0:(n - 1)
      bit = one(T) << i
      row_img = zero(T)
      for j in 0:(n - 1)
        if !iszero(packed[offset + j] & bit)
          row_img |= one(T) << j
        end
      end
      basis_images[offset + i] = row_img
    end
  end
  return basis_images
end

# Inputs: basis_images stores basis-row images for one generator block selected by offset.
@inline function _matact_mod2_basis_images(basis_images::Vector{T}, offset::Int, x::T) where {T <: Unsigned}
  res = zero(T)
  y = x
  @inbounds while !iszero(y)
    b = trailing_zeros(y)
    res ⊻= basis_images[offset + b]
    y &= y - one(T)
  end
  return res
end
=#

function _is_new_mod2!(x::T, seen::Vector{T}, chunk_shift::Int, chunk_mask::T) where {T <: Unsigned}
  # Chunked bitset membership test/update for x.
  i = Int(x >> chunk_shift) + 1
  b = one(T) << (x & chunk_mask)
  @inbounds if !iszero(seen[i] & b)
    return false
  end
  @inbounds seen[i] |= b
  return true
end

# Inputs: x is the current scan position; seen is the visited bitset split into chunks.
function _find_next_after_mod2!(x::T, seen::Vector{T}, chunk_shift::Int, chunk_mask::T) where {T <: Unsigned}
  i = Int(x >> chunk_shift) + 1
  # Skip chunks that are fully marked, then locate first zero bit in the next chunk.
  @inbounds while seen[i] == typemax(T)
    i += 1
  end
  y = @inbounds seen[i]
  v = (i - 1) << chunk_shift
  v += trailing_ones(y)
  xnew = T(v)
  @inbounds seen[Int(xnew >> chunk_shift) + 1] |= one(T) << (xnew & chunk_mask)
  return xnew
end

# Inputs: seen is the visited bitset; n and chunk_shift define the expected full pattern.
function _check_seen_mod2(seen::Vector{T}, n::Int, chunk_shift::Int) where {T <: Unsigned}
  if n < chunk_shift
    expected = (one(T) << (1 << n)) - one(T)
    seen[1] == expected || error("not finished")
    return
  end
  for x in seen
    x == typemax(T) || error("not finished")
  end
end

# Inputs: x is a packed mod-2 vector and n is the output length.
function _unpack_mod2_vector(x::T, n::Int) where {T <: Unsigned}
  return [iszero((x >> (i - 1)) & one(T)) ? 0 : 1 for i in 1:n]
end

@doc raw"""
    orbmod2([T::Type{<:Unsigned},] gens::Vector)

Compute the orbits of the right linear action of `gens` on `F_2^n`
(row vectors, `v -> v * g`, entries reduced modulo `2`).

# Input
- `T`: optional unsigned word type (`UInt16`, `UInt32`, `UInt64`, ...),
  default is `UInt64`.
- `gens`: a nonempty vector of square `n×n` matrices with entries interpreted modulo `2`.
  All matrices must have the same size, and `n <= 8*sizeof(T)-1`.

# Output
Return a vector of pairs `(len, rep)` of type `Tuple{T, T}`.
Each pair describes one orbit:
- `len`: orbit length,
- `rep`: orbit representative encoded as a bit vector in `T`
  (bit `i-1` is the `i`-th coordinate in `F_2`).
"""
function orbmod2(::Type{T}, gens::Vector) where {T <: Unsigned}
  packed, n = _pack_linear_generators_mod2(T, gens)
  ngens = length(gens)
  # if T = Uint32, then chunk_shift = 5, chunk_mask = 31 = in binary: 0...011111
  chunk_shift = trailing_zeros(8 * sizeof(T))  #
  chunk_mask = T((8 * sizeof(T)) - 1)  #
  # Split the state space into word-sized chunks: `x >> chunk_shift` gives the
  # chunk index in `seen`, and `x & chunk_mask` gives the bit position inside
  # that chunk.
  seen = zeros(T, 1 << max(n - chunk_shift, 0))
  todo = T[]
  seen[1] = one(T)
  seen_cnt = UInt128(1)
  total = UInt128(1) << n
  next = zero(T)
  orb_len = one(T)
  res = Tuple{T, T}[]
  while true
    if !isempty(todo)
      x = pop!(todo)
      @inbounds for i in 0:(ngens - 1)
        y = _matact_mod2(packed, i * n + 1, x, n)
        if _is_new_mod2!(y, seen, chunk_shift, chunk_mask)
          push!(todo, y)
          seen_cnt += 1
          orb_len += 1
        end
      end
    else
      # Finished one orbit: record its size and representative.
      push!(res, (orb_len, next))
      if seen_cnt == total
        _check_seen_mod2(seen, n, chunk_shift)
        break
      end
      next = _find_next_after_mod2!(next, seen, chunk_shift, chunk_mask)
      seen_cnt += 1
      push!(todo, next)
      orb_len = one(T)
    end
  end
  return res
end
orbmod2(gens::Vector) = orbmod2(UInt64, gens)

# Inputs: T is the packed word type, G is a vector of n x n matrices over integers or mod 2.
function line_orbits_mod_2(::Type{T}, G::Vector) where T<:Unsigned
  isempty(G) && throw(ArgumentError("at least one generator is required"))
  n = nrows(G[1])
  return [(Int(orblen),_unpack_mod2_vector(i, n)) for (orblen,i) in orbmod2(T, G)]
end

# Inputs: T is the packed word type, G is a vector of Fq matrices over GF(2).
function line_orbits_mod_2(::Type{T}, G::Vector{FqMatrix}) where T<:Unsigned
  isempty(G) && throw(ArgumentError("at least one generator is required"))
  n = nrows(G[1])
  order(base_ring(G[1])) == 2 || throw(ArgumentError("matrices must be integers or in GF(2)"))
  orbits_sizes = [(Int(orblen),_unpack_mod2_vector(i, n)) for (orblen,i) in orbmod2(T, G)]
  a = popfirst!(orbits_sizes) # remove the zero vector orbit
  @assert iszero(a[2]) "first orbit should be the zero vector"
  return orbits_sizes
end

# Inputs: rows is a vector of packed rows; n is the ambient dimension.
function _rref_rows_mod2!(rows::Vector{T}, n::Int) where {T <: Unsigned}
  # In-place Gaussian elimination over F_2 on packed rows.
  m = length(rows)
  rank = _rref_rows_mod2_rank!(rows, n, m)
  resize!(rows, rank)
  return rank
end

# Inputs: rows stores at least m packed rows; only the first m rows are reduced.
function _rref_rows_mod2_rank!(rows::Vector{T}, n::Int, m::Int) where {T <: Unsigned}
  ridx = 1
  for col in 0:(n - 1)
    pivot = 0
    for i in ridx:m
      if !iszero((rows[i] >> col) & one(T))
        pivot = i
        break
      end
    end
    pivot == 0 && continue
    rows[ridx], rows[pivot] = rows[pivot], rows[ridx]
    for i in 1:m
      if i != ridx && !iszero((rows[i] >> col) & one(T))
        rows[i] ⊻= rows[ridx]
      end
    end
    ridx += 1
    ridx > m && break
  end
  return ridx - 1
end

# Inputs: T is the packed word type, n is ambient dimension, k is target rank, code consumes each RREF representative.
function _for_all_k_subspaces_rref(::Type{T}, n::Int, k::Int, code::Function) where {T <: Unsigned}
  # Enumerate all k-dimensional subspaces of F_2^n in RREF-packed form and
  # call code(rep) for each representative; stop early if code returns true.
  if k == 0
    return code(T[])
  end
  pivots = Vector{Int}(undef, k)
  rowbase = Vector{T}(undef, k)
  rowfree = Vector{T}(undef, k)
  rows = Vector{T}(undef, k)

  # Inputs: i is the current row index (1..k+1).
  # For fixed pivots, enumerate all free-entry choices row by row.
  function rec_rows(i::Int)
    if i > k
      # `rows` is a reusable buffer; the callback must copy it if it needs to
      # keep the representative beyond the call.
      return code(rows)
    end
    mask = rowfree[i]
    sub = mask
    while true
      rows[i] = rowbase[i] | sub
      rec_rows(i + 1) && return true
      iszero(sub) && break
      sub = (sub - one(T)) & mask
    end
    return false
  end

  # Inputs: pos is the pivot number to choose next (1..k+1),
  # start is the smallest admissible pivot column.
  # Enumerate strictly increasing pivot columns, then initialize row masks.
  function rec_piv(pos::Int, start::Int)
    if pos > k
      # For fixed pivot columns, enumerate all RREF rows via free entries.
      pivotmask = zero(T)
      for p in pivots
        pivotmask |= one(T) << (p - 1)
      end
      for i in 1:k
        pivot = pivots[i]
        rowbase[i] = one(T) << (pivot - 1)
        free = zero(T)
        for c in (pivot + 1):n
          bit = one(T) << (c - 1)
          iszero(pivotmask & bit) && (free |= bit)
        end
        rowfree[i] = free
      end
      return rec_rows(1)
    end
    for c in start:(n - (k - pos))
      pivots[pos] = c
      rec_piv(pos + 1, c + 1) && return true
    end
    return false
  end

  return rec_piv(1, 1)
end

# Inputs: scratch is overwritten with the image of rep under one generator block, offset=gen_index*n+1
function _act_subspace_mod2!(scratch::Vector{T}, packed::Vector{T}, offset::Int, n::Int, k::Int, rep) where {T <: Unsigned}
  @inbounds for j in eachindex(rep)
    scratch[j] = _matact_mod2(packed, offset, rep[j], n)
  end
  rank = _rref_rows_mod2_rank!(scratch, n, k)
  rank == k || throw(ArgumentError("generators must preserve subspace dimension"))
  return scratch
end

@inline _pivot_bit_mod2_row(x::T) where {T <: Unsigned} = x & (~x + one(T))

@inline _vector_to_ntuple_mod2(::Val{k}, v::Vector{T}) where {k, T <: Unsigned} = ntuple(i -> @inbounds(v[i]), Val(k))

# Inputs: Val(k) fixes tuple size and rep is an RREF basis of length k.
# Output key layout: (pivot_mask, free_row_1, ..., free_row_k).
@inline function _subspace_key_mod2(::Val{k}, rep::Vector{T}) where {k, T <: Unsigned}
  pivmask = zero(T)
  @inbounds for i in 1:k
    pivmask |= _pivot_bit_mod2_row(rep[i])
  end
  free_rows = ntuple(i -> begin
    row = @inbounds rep[i]
    row ⊻ _pivot_bit_mod2_row(row)
  end, Val(k))
  return (pivmask, free_rows...)
end

################################################################################
#
#  Perfect ranking of k-dimensional subspaces in RREF
#
################################################################################
#
# Every k-subspace of F_2^n has a unique reduced row echelon form. It is
# determined by its pivot columns p_1 < ... < p_k together with the free
# entries, which sit in the non-pivot columns to the right of each pivot.
#
# We turn this into a bijection to 0, 1, ..., N-1, where N is the number of
# k-subspaces (a Gaussian binomial coefficient):
#
#   index(U) = base[rank(pivots)] + free_index
#
# Here `rank(pivots)` is the combinadic (colex) rank of the pivot set and
# `base` stores, for each pivot pattern, the cumulative number of subspaces
# with a smaller pivot rank. Within a fixed pivot pattern the free entries form
# a dense integer `free_index`, obtained by compressing the free bits of each
# row (via `_pext_mod2`) and concatenating them.
#
# This lets us replace the hash `Set` of RREF keys by a single `BitVector`,
# which is faster (no hashing/collisions) and uses far less memory.

# Parallel bit extract: gather the bits of `x` selected by `mask` into the low
# bits of the result (software emulation of `pext`).
@inline function _pext_mod2(x::T, mask::T) where {T <: Unsigned}
  res = zero(T)
  bit = one(T)
  m = mask
  @inbounds while !iszero(m)
    low = m & (~m + one(T))     # lowest set bit of m
    if !iszero(x & low)
      res |= bit
    end
    bit <<= 1
    m ⊻= low
  end
  return res
end

# Precomputed data to rank k-subspaces of F_2^n in RREF form.
# - `binom[a+1, b+1] = binomial(a, b)` for combinadic ranking of pivot sets.
# - `base[r+1]` is the number of subspaces whose pivot pattern has rank < r.
# - `rowfreemask[i, r+1]` selects the free columns of row `i` for pivot rank `r`.
# - `rowshift[i, r+1]` is the bit offset of that row's free bits in `free_index`.
# - `total` is the number of k-subspaces (the length of the visited bitset).
struct _SubspaceRankerMod2{T <: Unsigned}
  n::Int
  k::Int
  binom::Matrix{Int}
  base::Vector{Int}
  rowfreemask::Matrix{T}
  rowshift::Matrix{Int}
  total::Int
end

# Build the ranker for (n, k), or return `nothing` if the number of subspaces or
# pivot patterns is too large to tabulate (the caller then falls back to a
# hashed set).
function _build_subspace_ranker_mod2(::Type{T}, n::Int, k::Int;
    pattern_limit::Int = 1 << 20, bit_limit::Int = 1 << 31) where {T <: Unsigned}
  (k <= 0 || k >= n) && return nothing
  # Pascal triangle of binomial coefficients up to n choose (k+1).
  binom = zeros(Int, n + 1, k + 2)
  for a in 0:n
    binom[a + 1, 1] = 1
    if a >= 1
      for b in 1:(k + 1)
        binom[a + 1, b + 1] = binom[a, b] + binom[a, b + 1]
      end
    end
  end
  npat = binom[n + 1, k + 1]                 # number of pivot patterns = C(n, k)
  npat > pattern_limit && return nothing

  rowfreemask = zeros(T, k, npat)
  rowshift = zeros(Int, k, npat)
  fpat = zeros(Int, npat)                    # number of free bits per pattern
  pivots = Vector{Int}(undef, k)

  function process()
    r = 0
    @inbounds for i in 1:k
      r += binom[pivots[i] + 1, i + 1]       # combinadic (colex) rank
    end
    pivotmask = zero(T)
    @inbounds for i in 1:k
      pivotmask |= one(T) << pivots[i]
    end
    sh = 0
    @inbounds for i in 1:k
      fm = zero(T)
      for c in (pivots[i] + 1):(n - 1)
        bit = one(T) << c
        iszero(pivotmask & bit) && (fm |= bit)
      end
      rowfreemask[i, r + 1] = fm
      rowshift[i, r + 1] = sh
      sh += count_ones(fm)
    end
    fpat[r + 1] = sh
    return nothing
  end

  # Enumerate all strictly increasing pivot column tuples (0-indexed).
  function rec(pos::Int, start::Int)
    if pos > k
      process()
      return
    end
    for c in start:((n - 1) - (k - pos))
      pivots[pos] = c
      rec(pos + 1, c + 1)
    end
    return nothing
  end
  rec(1, 0)

  base = Vector{Int}(undef, npat + 1)
  base[1] = 0
  acc = Int128(0)
  for r in 0:(npat - 1)
    acc += Int128(1) << fpat[r + 1]
    acc > bit_limit && return nothing
    base[r + 2] = Int(acc)
  end
  return _SubspaceRankerMod2{T}(n, k, binom, base, rowfreemask, rowshift, Int(acc))
end

# Map an RREF subspace `rep` (length k) to its integer index in 0:total-1.
@inline function _rank_subspace_mod2(ranker::_SubspaceRankerMod2{T}, rep) where {T <: Unsigned}
  k = ranker.k
  binom = ranker.binom
  r = 0
  @inbounds for i in 1:k
    r += binom[trailing_zeros(rep[i]) + 1, i + 1]
  end
  idx = @inbounds ranker.base[r + 1]
  @inbounds for i in 1:k
    row = rep[i]
    piv = trailing_zeros(row)
    freebits = row ⊻ (one(T) << piv)
    idx += Int(_pext_mod2(freebits, ranker.rowfreemask[i, r + 1])) << ranker.rowshift[i, r + 1]
  end
  return idx
end

################################################################################
#
#  Visited-set backends
#
################################################################################

# Dense bitset backend, keyed by the perfect rank of a subspace.
struct _BitSeenMod2{T <: Unsigned}
  ranker::_SubspaceRankerMod2{T}
  bits::BitVector
end

@inline _encode_seen(s::_BitSeenMod2, rep) = _rank_subspace_mod2(s.ranker, rep)
@inline _contains_seen(s::_BitSeenMod2, key::Int) = @inbounds s.bits[key + 1]
@inline _add_seen!(s::_BitSeenMod2, key::Int) = (@inbounds s.bits[key + 1] = true; nothing)

# Fallback backend, keyed by the canonical RREF tuple and stored in a `Set`.
struct _SetSeenMod2{K, KV}
  set::Set{K}
  kval::KV
end

@inline _encode_seen(s::_SetSeenMod2, rep) = _subspace_key_mod2(s.kval, rep)
@inline _contains_seen(s::_SetSeenMod2, key) = key in s.set
@inline _add_seen!(s::_SetSeenMod2, key) = (push!(s.set, key); nothing)

################################################################################
#
#  Packed F_2 matrix arithmetic (for stabilizer generators)
#
################################################################################
#
# Group elements are stored like the generators: a length-n vector of words,
# where word j holds column j (bit i-1 is the (i, j) entry).

# Transpose a packed bit matrix (columns <-> rows).
function _transpose_packed_mod2(v::Vector{T}, n::Int) where {T <: Unsigned}
  w = zeros(T, n)
  @inbounds for a in 1:n
    x = v[a]
    while !iszero(x)
      b = trailing_zeros(x)
      w[b + 1] |= one(T) << (a - 1)
      x &= x - one(T)
    end
  end
  return w
end

# Inverse of a packed (column-major) invertible F_2 matrix.
function _invert_cols_mod2(a::Vector{T}, n::Int) where {T <: Unsigned}
  rows = _transpose_packed_mod2(a, n)
  inv = T[one(T) << (i - 1) for i in 1:n]     # identity rows
  @inbounds for col in 0:(n - 1)
    p = 0
    for i in (col + 1):n
      if !iszero((rows[i] >> col) & one(T))
        p = i
        break
      end
    end
    p == 0 && throw(ArgumentError("generator is not invertible mod 2"))
    rows[col + 1], rows[p] = rows[p], rows[col + 1]
    inv[col + 1], inv[p] = inv[p], inv[col + 1]
    for i in 1:n
      if i != (col + 1) && !iszero((rows[i] >> col) & one(T))
        rows[i] ⊻= rows[col + 1]
        inv[i] ⊻= inv[col + 1]
      end
    end
  end
  return _transpose_packed_mod2(inv, n)
end

# Convert a packed (column-major) F_2 matrix to a 0/1 integer matrix.
function _packed_cols_to_zzmatrix_mod2(s::Vector{T}, n::Int) where {T <: Unsigned}
  M = zero_matrix(ZZ, n, n)
  @inbounds for j in 1:n
    col = s[j]
    for i in 1:n
      if !iszero((col >> (i - 1)) & one(T))
        M[i, j] = one(ZZRingElem)
      end
    end
  end
  return M
end

# In-place F_2 matrix product: writes `A * B` (packed columns) into `dest`
# starting at column offset `doff`, reading `A` from `a` at `aoff` and `B` from
# `b` at `boff`. Offsets let us multiply matrices stored contiguously in a flat
# arena without allocating any temporaries.
@inline function _mm_into!(dest::Vector{T}, doff::Int, a::Vector{T}, aoff::Int,
    b::Vector{T}, boff::Int, n::Int) where {T <: Unsigned}
  @inbounds for i in 1:n
    acc = zero(T)
    y = b[boff + i]
    while !iszero(y)
      j = trailing_zeros(y)
      acc ⊻= a[aoff + j + 1]
      y &= y - one(T)
    end
    dest[doff + i] = acc
  end
  return nothing
end

# Product `a * b` of two packed (column-major) F_2 matrices (allocating).
function _matmul_cols_mod2(a::Vector{T}, b::Vector{T}, n::Int) where {T <: Unsigned}
  c = Vector{T}(undef, n)
  _mm_into!(c, 0, a, 0, b, 0, n)
  return c
end

# Image `v * a` of the packed row vector `v` under the packed matrix `a`.
@inline _vecact_mod2(a::Vector{T}, v::T, n::Int) where {T <: Unsigned} =
  _matact_mod2(a, 1, v, n)

# Bookkeeping used when stabilizer generators are requested. During the orbit
# traversal we assign each visited subspace a local id and store the group
# element `u_X` mapping the representative to it, together with `u_X^{-1}`.
# These are kept in flat arenas (`us`, `uinvs`, `n` words per element) to avoid
# per-element allocations, with `id_of` mapping a subspace key to its id. On
# every non-tree edge Schreier's lemma yields the generator `u_X g u_Y^{-1}`,
# computed into the scratch buffer `sgen` and deduplicated in `gens`.
mutable struct _StabCtxMod2{T <: Unsigned, K}
  n::Int
  gcols::Vector{Vector{T}}
  ginvcols::Vector{Vector{T}}
  id::Vector{T}
  id_of::Dict{K, Int}
  us::Vector{T}
  uinvs::Vector{T}
  gens::Set{Vector{T}}
  uxg::Vector{T}
  sgen::Vector{T}
  count::Int
end

function _make_stab_ctx_mod2(::Type{T}, ::Type{K}, packed::Vector{T},
    offsets::Vector{Int}, n::Int) where {T <: Unsigned, K}
  gcols = Vector{T}[copy(packed[o:(o + n - 1)]) for o in offsets]
  ginvcols = Vector{T}[_invert_cols_mod2(g, n) for g in gcols]
  id = T[one(T) << (i - 1) for i in 1:n]
  return _StabCtxMod2{T, K}(n, gcols, ginvcols, id, Dict{K, Int}(), T[], T[],
                            Set{Vector{T}}(), Vector{T}(undef, n),
                            Vector{T}(undef, n), 0)
end

# Reset the per-orbit state (arenas are kept and reused across orbits).
@inline function _stab_reset!(stab::_StabCtxMod2)
  empty!(stab.id_of)
  empty!(stab.gens)
  stab.count = 0
  return nothing
end

# Allocate a fresh local id for `key`, growing the transversal arenas if needed.
@inline function _stab_new_id!(stab::_StabCtxMod2, key)
  id = stab.count
  stab.count = id + 1
  need = (id + 1) * stab.n
  if length(stab.us) < need
    newlen = max(need, 2 * length(stab.us))
    resize!(stab.us, newlen)
    resize!(stab.uinvs, newlen)
  end
  stab.id_of[key] = id
  return id
end

# Record a stabilizer generator held in the scratch vector `s` (deduplicated,
# skipping the identity). Returns `true` if `s` was a genuinely new generator
# (copied and kept), `false` otherwise.
@inline function _stab_add_gen!(stab::_StabCtxMod2{T}, s::Vector{T}) where {T <: Unsigned}
  s == stab.id && return false
  s in stab.gens && return false
  push!(stab.gens, copy(s))
  return true
end

################################################################################
#
#  Schreier-Sims: base and strong generating set for a subgroup of GL(n, 2)
#
################################################################################
#
# The group acts on row vectors by `v -> v * M`. We fix the base to the standard
# basis vectors `e_1, ..., e_n`: only the identity fixes all of them, so this is
# a base for *every* matrix subgroup and no dynamic base points are needed.
#
# Level `i` stores the basic orbit of `e_i` under the strong generators that fix
# `e_1, ..., e_{i-1}`, together with a transversal `u` (`e_i * u[pt] = pt`) and
# its inverse `w` (`w[pt] = u[pt]^{-1}`). The group order is the product of the
# basic orbit sizes. Feeding the (many, redundant) Schreier generators of a
# subspace orbit through this turns them into a small strong generating set.

mutable struct _BSGSMod2{T <: Unsigned}
  n::Int
  gens::Vector{Vector{T}}               # all strong generators
  geninv::Vector{Vector{T}}             # their inverses (cached, parallel to gens)
  slevel::Vector{Vector{Vector{T}}}     # slevel[i]: strong gens fixing e_1..e_{i-1}
  slevelinv::Vector{Vector{Vector{T}}}  # their inverses, per level
  orbits::Vector{Vector{T}}             # orbits[i]: basic orbit points of e_i
  u::Vector{Dict{T, Vector{T}}}         # u[i][pt]: element with e_i * u = pt
  w::Vector{Dict{T, Vector{T}}}         # w[i][pt]: its inverse
  id::Vector{T}                         # identity matrix (packed)
  b1::Vector{T}                         # scratch buffers
  b2::Vector{T}
  b3::Vector{T}
  b4::Vector{T}
  pool::Vector{Vector{T}}               # reusable transversal vectors
end

# Allocate an empty chain (base = standard basis, no strong generators yet).
function _new_bsgs_mod2(::Type{T}, n::Int) where {T <: Unsigned}
  id = T[one(T) << (i - 1) for i in 1:n]
  return _BSGSMod2{T}(n, Vector{T}[], Vector{T}[], [Vector{T}[] for _ in 1:n],
                     [Vector{T}[] for _ in 1:n], [T[] for _ in 1:n],
                     [Dict{T, Vector{T}}() for _ in 1:n],
                     [Dict{T, Vector{T}}() for _ in 1:n], id,
                     Vector{T}(undef, n), Vector{T}(undef, n),
                     Vector{T}(undef, n), Vector{T}(undef, n), Vector{Vector{T}}())
end

# Does `s` fix the base prefix `e_1, ..., e_{i-1}`?
@inline function _fixes_prefix_mod2(s::Vector{T}, i::Int, n::Int) where {T <: Unsigned}
  @inbounds for j in 1:(i - 1)
    ej = one(T) << (j - 1)
    _vecact_mod2(s, ej, n) == ej || return false
  end
  return true
end

# Add a strong generator together with its (cached) inverse.
@inline function _bsgs_push_gen!(bsgs::_BSGSMod2{T}, g::Vector{T}) where {T <: Unsigned}
  push!(bsgs.gens, g)
  push!(bsgs.geninv, _invert_cols_mod2(g, bsgs.n))
  return nothing
end

# Borrow / return length-n vectors from the reuse pool.
@inline _pool_get!(bsgs::_BSGSMod2{T}) where {T <: Unsigned} =
  isempty(bsgs.pool) ? Vector{T}(undef, bsgs.n) : pop!(bsgs.pool)

# Recompute all basic orbits and transversals from the current strong generators.
# Transversal vectors are recycled through `bsgs.pool` to avoid reallocating on
# every rebuild.
function _bsgs_recompute!(bsgs::_BSGSMod2{T}) where {T <: Unsigned}
  n = bsgs.n
  # Reclaim all currently stored transversal vectors into the pool.
  for i in 1:n
    for v in values(bsgs.u[i])
      push!(bsgs.pool, v)
    end
    for v in values(bsgs.w[i])
      push!(bsgs.pool, v)
    end
    empty!(bsgs.u[i])
    empty!(bsgs.w[i])
  end
  for i in 1:n
    ei = one(T) << (i - 1)
    Si = bsgs.slevel[i]
    Sinv = bsgs.slevelinv[i]
    empty!(Si)
    empty!(Sinv)
    for gi in eachindex(bsgs.gens)
      if _fixes_prefix_mod2(bsgs.gens[gi], i, n)
        push!(Si, bsgs.gens[gi])
        push!(Sinv, bsgs.geninv[gi])
      end
    end
    u = bsgs.u[i]
    w = bsgs.w[i]
    orbit = bsgs.orbits[i]
    empty!(orbit)
    uei = _pool_get!(bsgs); copyto!(uei, bsgs.id)
    wei = _pool_get!(bsgs); copyto!(wei, bsgs.id)
    u[ei] = uei
    w[ei] = wei
    push!(orbit, ei)
    q = 1
    while q <= length(orbit)
      x = orbit[q]
      q += 1
      ux = u[x]
      wx = w[x]
      for t in eachindex(Si)
        y = _vecact_mod2(Si[t], x, n)
        if !haskey(u, y)
          uy = _pool_get!(bsgs); _mm_into!(uy, 0, ux, 0, Si[t], 0, n)
          wy = _pool_get!(bsgs); _mm_into!(wy, 0, Sinv[t], 0, wx, 0, n)
          u[y] = uy
          w[y] = wy
          push!(orbit, y)
        end
      end
    end
  end
  return nothing
end

# Sift `g` through the chain into the scratch buffers `ba`/`bb` (no allocation).
# Returns `(residue_buffer, dropout_level)`; the residue is the identity exactly
# when `g` lies in the group described by the current (complete) chain.
function _bsgs_strip!(bsgs::_BSGSMod2{T}, g::Vector{T}, ba::Vector{T}, bb::Vector{T}) where {T <: Unsigned}
  n = bsgs.n
  copyto!(ba, g)
  cur = ba
  oth = bb
  @inbounds for i in 1:n
    ei = one(T) << (i - 1)
    y = _vecact_mod2(cur, ei, n)
    haskey(bsgs.u[i], y) || return (cur, i)
    _mm_into!(oth, 0, cur, 0, bsgs.w[i][y], 0, n)
    cur, oth = oth, cur
  end
  return (cur, n + 1)
end

# Complete the chain: keep adding non-trivial sifted Schreier generators until
# every Schreier generator sifts to the identity (a genuine strong generating set).
# If `target_order` is given and the chain reaches it, we stop early: the chain
# order is always at most the order of the group, so equality proves completeness.
function _bsgs_complete!(bsgs::_BSGSMod2{T};
    target_order::Union{Nothing, ZZRingElem} = nothing) where {T <: Unsigned}
  id = bsgs.id
  n = bsgs.n
  while true
    _bsgs_recompute!(bsgs)
    target_order !== nothing && _bsgs_order_mod2(bsgs) == target_order && return nothing
    newgen = nothing
    for i in 1:n
      Si = bsgs.slevel[i]
      isempty(Si) && continue
      ui = bsgs.u[i]
      wi = bsgs.w[i]
      for x in bsgs.orbits[i]
        ux = ui[x]
        for s in Si
          y = _vecact_mod2(s, x, n)
          # Schreier generator u_x * s * w_{x*s}, computed into scratch buffers.
          _mm_into!(bsgs.b3, 0, ux, 0, s, 0, n)
          _mm_into!(bsgs.b4, 0, bsgs.b3, 0, wi[y], 0, n)
          bsgs.b4 == id && continue
          buf, _ = _bsgs_strip!(bsgs, bsgs.b4, bsgs.b1, bsgs.b2)
          if buf != id
            newgen = copy(buf)
            break
          end
        end
        newgen === nothing || break
      end
      newgen === nothing || break
    end
    newgen === nothing && break
    _bsgs_push_gen!(bsgs, newgen)
  end
  return nothing
end

# Build a base and strong generating set for the group generated by `gens_in`
# (packed n x n matrices over F_2). Input generators are sifted first to keep the
# strong generating set small, then the chain is completed. If the group order
# `target_order` is known, the build stops as soon as the chain reaches it
# (skipping the more expensive completion pass); this must be the true order of
# `<gens_in>` or the result may be a proper subgroup.
function _bsgs_build_mod2(::Type{T}, gens_in::Vector{Vector{T}}, n::Int;
    target_order::Union{Nothing, ZZRingElem} = nothing) where {T <: Unsigned}
  bsgs = _new_bsgs_mod2(T, n)
  _bsgs_recompute!(bsgs)
  for g in gens_in
    g == bsgs.id && continue
    buf, _ = _bsgs_strip!(bsgs, g, bsgs.b1, bsgs.b2)
    if buf != bsgs.id
      _bsgs_push_gen!(bsgs, copy(buf))
      _bsgs_recompute!(bsgs)
      target_order !== nothing && _bsgs_order_mod2(bsgs) == target_order && return bsgs
    end
  end
  _bsgs_complete!(bsgs; target_order = target_order)
  return bsgs
end

# Reset a chain to the trivial group so it can be reused across orbits.
function _bsgs_reset!(bsgs::_BSGSMod2)
  empty!(bsgs.gens)
  empty!(bsgs.geninv)
  _bsgs_recompute!(bsgs)
  return nothing
end

# Sift `g` into a *complete* chain; if it enlarges the group, add it and
# re-complete. Returns `true` if the group (hence its order) grew. The chain must
# be complete on entry and is complete on exit, so `_bsgs_order_mod2` is exact.
function _bsgs_sift_add!(bsgs::_BSGSMod2{T}, g::Vector{T}) where {T <: Unsigned}
  buf, _ = _bsgs_strip!(bsgs, g, bsgs.b1, bsgs.b2)
  buf == bsgs.id && return false
  _bsgs_push_gen!(bsgs, copy(buf))
  _bsgs_complete!(bsgs)
  return true
end

# Order of the group described by a completed chain.
function _bsgs_order_mod2(bsgs::_BSGSMod2)
  ord = one(ZZRingElem)
  for o in bsgs.orbits
    ord = mul!(ord, length(o))
  end
  return ord
end

################################################################################
#
#  Generic orbit traversal
#
################################################################################

# Explore the orbit of `seed_rep` (already encoded as `seed_key`) and return its
# length. This is the lean path used when no stabilizer is requested.
function _orbit_bfs_mod2!(seen, todo::Vector{NTuple{W, T}}, packed::Vector{T},
    offsets::Vector{Int}, n::Int, k::Int, kval::Val, scratch::Vector{T},
    seed_rep, seed_key) where {T <: Unsigned, W}
  orb_len = UInt64(1)
  empty!(todo)
  _add_seen!(seen, seed_key)
  push!(todo, _vector_to_ntuple_mod2(kval, seed_rep))
  while !isempty(todo)
    x = pop!(todo)
    @inbounds for gi in 1:length(offsets)
      _act_subspace_mod2!(scratch, packed, offsets[gi], n, k, x)
      ykey = _encode_seen(seen, scratch)
      if !_contains_seen(seen, ykey)
        _add_seen!(seen, ykey)
        push!(todo, _vector_to_ntuple_mod2(kval, scratch))
        orb_len += 1
      end
    end
  end
  return orb_len
end

# Same traversal, but additionally build a base and strong generating set of the
# stabilizer of the representative (Schreier's lemma + interleaved Schreier-Sims).
# `bsgs` is kept complete after every added generator, so its order is exact at
# all times. When the group order `gtarget` is known (`!= 0`), we use the
# invariant `m * s <= |G|` (m = orbit elements found, s = current stabilizer
# order): equality forces `m = orbit length` and `s = |stabilizer|`, so we can
# stop immediately and skip the rest of the traversal (switching to "done").
function _orbit_bfs_stab_mod2!(seen, stab::_StabCtxMod2{T, K}, bsgs::_BSGSMod2{T},
    todo::Vector{Tuple{Int, NTuple{W, T}}}, packed::Vector{T},
    offsets::Vector{Int}, n::Int, k::Int, kval::Val, scratch::Vector{T},
    seed_rep, seed_key, gtarget::T2) where {T <: Unsigned, K, W, T2 <:IntegerUnion}
  _stab_reset!(stab)
  _bsgs_reset!(bsgs)
  empty!(todo)
  _add_seen!(seen, seed_key)
  seedid = _stab_new_id!(stab, seed_key)
  soff = seedid * n
  @inbounds for i in 1:n
    stab.us[soff + i] = stab.id[i]
    stab.uinvs[soff + i] = stab.id[i]
  end
  push!(todo, (seedid, _vector_to_ntuple_mod2(kval, seed_rep)))
  orb_len = UInt64(1)
  cur_grp_ord = one(T2)
  scur = ZZ(1)                    # current stabilizer order (used when gtarget != 0)
  uxg = stab.uxg
  sgen = stab.sgen
  while !isempty(todo)
    xid, x = pop!(todo)
    xoff = xid * n
    @inbounds for gi in 1:length(offsets)
      _act_subspace_mod2!(scratch, packed, offsets[gi], n, k, x)
      ykey = _encode_seen(seen, scratch)
      # uxg = u_X * g_i (needed both to extend the tree and to close edges)
      _mm_into!(uxg, 0, stab.us, xoff, stab.gcols[gi], 0, n)
      if !_contains_seen(seen, ykey)
        _add_seen!(seen, ykey)
        yid = _stab_new_id!(stab, ykey)
        yoff = yid * n
        # u_Y = u_X g_i and u_Y^{-1} = g_i^{-1} u_X^{-1}
        for i in 1:n
          stab.us[yoff + i] = uxg[i]
        end
        _mm_into!(stab.uinvs, yoff, stab.ginvcols[gi], 0, stab.uinvs, xoff, n)
        push!(todo, (yid, _vector_to_ntuple_mod2(kval, scratch)))
        orb_len += 1
        cur_grp_ord = add!(cur_grp_ord, scur)
        @assert iszero(gtarget) || cur_grp_ord <= gtarget "input group order wrong"
        # Orbit fully found and stabilizer complete: stop and drop the queue.
        if !iszero(gtarget) && cur_grp_ord == gtarget
          empty!(todo)
          break
        end
      else
        # Non-tree edge: Schreier generator u_X g_i u_Y^{-1}, folded into the BSGS.
        yoff = stab.id_of[ykey] * n
        _mm_into!(sgen, 0, uxg, 0, stab.uinvs, yoff, n)
        if _stab_add_gen!(stab, sgen) && _bsgs_sift_add!(bsgs, sgen) && gtarget != 0
          scur = _bsgs_order_mod2(bsgs)
          cur_grp_ord = mul!(cur_grp_ord, orb_len, scur)
          @assert iszero(gtarget) || cur_grp_ord <= gtarget "input group order wrong"
          if cur_grp_ord == gtarget
            empty!(todo)
            break
          end
        end
      end
    end
  end
  return orb_len
end

# Number of k-dimensional subspaces of F_2^n, i.e. the Gaussian binomial
# coefficient [n, k]_2. Used only for cheap correctness assertions.
function _num_subspaces_mod2(n::Int, k::Int)
  num = one(ZZRingElem)
  den = one(ZZRingElem)
  for i in 0:(k - 1)
    num *= (ZZRingElem(2)^(n - i) - 1)
    den *= (ZZRingElem(2)^(i + 1) - 1)
  end
  return divexact(num, den)
end

# True if the packed (column-major) matrix `s` fixes the row space of the RREF
# `rep` (length k). `scratch` (length k) is used as working storage. Used only
# for correctness assertions.
function _stabilizes_subspace_mod2(s::Vector{T}, rep, n::Int, k::Int,
    scratch::Vector{T}) where {T <: Unsigned}
  @inbounds for j in 1:k
    scratch[j] = _matact_mod2(s, 1, rep[j], n)
  end
  _rref_rows_mod2_rank!(scratch, n, k) == k || return false
  @inbounds for j in 1:k
    scratch[j] == rep[j] || return false
  end
  return true
end

@doc raw"""
    orbmod2_subspaces([T::Type{<:Unsigned},] gens::Vector, k::Int; stabilizer::Bool = false)

Compute the orbits of the right linear action of `gens` on `k`-dimensional
subspaces of `F_2^n` (row spaces, `U -> U * g`, entries reduced modulo `2`).

Subspaces are represented in reduced row echelon form (RREF), encoded as vectors
of machine words. Whenever the number of `k`-subspaces is small enough to
tabulate, visited states are tracked in a `BitVector` indexed by a perfect
ranking of the RREF form; otherwise a hashed `Set` of canonical keys is used as
a fallback.

# Input
- `T`: optional unsigned word type (`UInt16`, `UInt32`, `UInt64`, ...),
  default is `UInt64`.
- `gens`: a nonempty vector of square `n×n` matrices with entries interpreted modulo `2`.
- `k`: target subspace dimension, must satisfy `0 <= k <= n` and `n <= 8*sizeof(T)-1`.
- `stabilizer`: if `true`, also compute, for each orbit representative, a base
  and strong generating set (Schreier-Sims) of its stabilizer.
- `group_order`: optional known order of the group generated by `gens`. When
  given (and `stabilizer` is `true`), the Schreier-Sims for each orbit is built
  interleaved with the orbit traversal, and both stop as soon as
  `len * stabilizer_order == group_order` (which proves the orbit is fully
  enumerated and the stabilizer is complete). This can skip a large part of the
  traversal for big orbits. It must be the true group order, otherwise a
  too-small stabilizer may be returned. When omitted, the order is determined
  exactly from the first orbit and then reused as the target for the rest.

# Output
If `stabilizer` is `false`, return a vector of pairs `(len, rep)` where
- `len::UInt64` is the orbit length,
- `rep::Vector{T}` is an RREF representative of length `k` (one packed row per entry).

If `stabilizer` is `true`, return a vector of tuples `(len, rep, gens, order)` where
additionally
- `gens::Vector{ZZMatrix}` is a strong generating set of the stabilizer of `rep`
  in the group generated by `gens`, given as `n×n` integer matrices with `0/1`
  entries (reduced from the redundant Schreier generators via Schreier-Sims),
- `order::ZZRingElem` is the order of that stabilizer. Note `len * order` equals
  the order of the group generated by `gens` and is therefore the same for every
  orbit.
"""
function orbmod2_subspaces(::Type{T}, gens::Vector, k::Int;
    stabilizer::Bool = false,
    group_order::Union{Nothing, IntegerUnion} = nothing) where {T <: Unsigned}
  packed, n = _pack_linear_generators_mod2(T, gens)
  0 <= k <= n || throw(ArgumentError("k must satisfy 0 <= k <= n"))
  ngens = length(gens)
  offsets = [i * n + 1 for i in 0:(ngens - 1)]
  gorder = group_order === nothing ? nothing : ZZRingElem(group_order)

  # Trivial subspaces (the zero subspace and the full space) are fixed by every
  # generator, so the whole group is the stabilizer.
  if k == 0 || k == n
    rep = k == 0 ? T[] : T[one(T) << (i - 1) for i in 1:n]
    if stabilizer
      bsgs = _bsgs_build_mod2(T, Vector{T}[copy(packed[o:(o + n - 1)]) for o in offsets], n;
                             target_order = gorder)
      ord = _bsgs_order_mod2(bsgs)
      # The whole group stabilizes the trivial subspaces, so its order is |G|.
      @assert gorder === nothing || ord == gorder
      sg = ZZMatrix[_packed_cols_to_zzmatrix_mod2(s, n) for s in bsgs.gens]
      return [(UInt64(1), rep, sg, ord)]
    end
    return [(UInt64(1), rep)]
  end

  kval = Val(k)
  scratch = Vector{T}(undef, k)

  # Pick the visited-set backend: dense bitset when feasible, hashed set else.
  ranker = _build_subspace_ranker_mod2(T, n, k)
  if ranker === nothing
    seen = _SetSeenMod2(Set{NTuple{k + 1, T}}(), kval)
    K = NTuple{k + 1, T}
  else
    # The tabulated number of subspaces must match the Gaussian binomial.
    @assert ZZRingElem(ranker.total) == _num_subspaces_mod2(n, k)
    seen = _BitSeenMod2(ranker, falses(ranker.total))
    K = Int
  end

  if stabilizer
    stab = _make_stab_ctx_mod2(T, K, packed, offsets, n)
    bsgs = _new_bsgs_mod2(T, n)
    todo = Tuple{Int, NTuple{k, T}}[]
    res = Tuple{UInt64, Vector{T}, Vector{ZZMatrix}, ZZRingElem}[]
    # Known group order (given or learned from the first orbit) lets each orbit
    # stop as soon as `orbit_len * stabilizer_order == |G|`.
    gord = Ref{Union{Nothing, ZZRingElem}}(gorder)
    _for_all_k_subspaces_rref(T, n, k, function(rep)
      key = _encode_seen(seen, rep)
      _contains_seen(seen, key) && return false
      g = gord[]
      if g===nothing
        gtarget = 0
      else
        gtarget = (g <= typemax(Int)) ? Int(g) : g
      end
      orb_len = _orbit_bfs_stab_mod2!(seen, stab, bsgs, todo, packed, offsets, n, k,
                                      kval, scratch, rep, key, gtarget)
      ord = _bsgs_order_mod2(bsgs)
      # Orbit-stabilizer theorem: orbit_len * |stab| is the (constant) group
      # order. Learn it from the first orbit; check every later orbit against it.
      if g === nothing
        gord[] = ZZRingElem(orb_len) * ord
      else
        @assert ZZRingElem(orb_len) * ord == g
      end
      # Deeper check: the strong generators really do fix the representative.
      @hassert :Lattice 2 all(s -> _stabilizes_subspace_mod2(s, rep, n, k, scratch), bsgs.gens)
      sg = ZZMatrix[_packed_cols_to_zzmatrix_mod2(s, n) for s in bsgs.gens]
      push!(res, (orb_len, copy(rep), sg, ord))
      return false
    end)
    @assert sum(x -> ZZRingElem(x[1]), res; init = zero(ZZRingElem)) == _num_subspaces_mod2(n, k)
    return res
  end

  todo = NTuple{k, T}[]
  res = Tuple{UInt64, Vector{T}}[]
  _for_all_k_subspaces_rref(T, n, k, function(rep)
    key = _encode_seen(seen, rep)
    _contains_seen(seen, key) && return false
    orb_len = _orbit_bfs_mod2!(seen, todo, packed, offsets, n, k, kval,
                               scratch, rep, key)
    push!(res, (orb_len, copy(rep)))
    return false
  end)
  # The orbits partition all k-subspaces, so the lengths sum to [n, k]_2.
  @assert sum(x -> ZZRingElem(x[1]), res; init = zero(ZZRingElem)) == _num_subspaces_mod2(n, k)
  return res
end

orbmod2_subspaces(gens::Vector, k::Int; stabilizer::Bool = false,
    group_order::Union{Nothing, IntegerUnion} = nothing) =
  orbmod2_subspaces(UInt64, gens, k; stabilizer = stabilizer, group_order = group_order)


# Smallest unsigned word type that can hold vectors of dimension `n`
# (`_pack_linear_generators_mod2` requires `n <= 8*sizeof(T) - 1`).
function _word_type_mod2(n::Int)
  n <= 15 && return UInt16
  n <= 31 && return UInt32
  n <= 63 && return UInt64
  throw(ArgumentError("dimension n = $n is too large (at most 63 supported)"))
end

# Build the `k×n` matrix over `F` whose rows are the unpacked RREF basis `rep`.
function _packed_rows_to_fqmatrix_mod2(rep::Vector{T}, n::Int, F) where {T <: Unsigned}
  k = length(rep)
  M = zero_matrix(F, k, n)
  o = one(F)
  @inbounds for i in 1:k
    row = rep[i]
    for j in 1:n
      iszero((row >> (j - 1)) & one(T)) || (M[i, j] = o)
    end
  end
  return M
end

@doc raw"""
    orbit_representatives_and_sizes_mod_2(G::Vector{FqMatrix}, k::Int)
    orbit_representatives_and_sizes_mod_2(T::Type{<:Unsigned}, G::Vector{FqMatrix}, k::Int)

Return representatives and sizes of the orbits of the group generated by `G` on
the `k`-dimensional subspaces of $\mathrm{GF}(2)^n$, where the action is on row
spaces by right multiplication ($U \mapsto U g$).

# Input
- `G`: a nonempty vector of invertible `n×n` matrices over $\mathrm{GF}(2)$
  (the generators of the group).
- `k`: the subspace dimension, `0 <= k <= n`.
- `T`: optional unsigned word type used internally to pack `\mathrm{GF}(2)`
  vectors. By default the smallest type that can hold the dimension `n` is chosen
  automatically.

# Output
A vector of pairs `(rep, len)`, one per orbit, where
- `rep::FqMatrix` is a `k×n` matrix over $\mathrm{GF}(2)$ in reduced row echelon
  form whose rows span an orbit representative, and
- `len::Int` is the length of that orbit.

See also [`orbit_representatives_and_stabilizers_mod_2`](@ref).
"""
function orbit_representatives_and_sizes_mod_2(::Type{T}, G::Vector{FqMatrix}, k::Int) where T<:Unsigned
  isempty(G) && throw(ArgumentError("at least one generator is required"))
  n = nrows(G[1])
  F = base_ring(G[1])
  order(F) == 2 || throw(ArgumentError("matrices must be over GF(2)"))
  return [(_packed_rows_to_fqmatrix_mod2(rep, n, F), Int(orblen))
          for (orblen, rep) in orbmod2_subspaces(T, G, k)]
end

function orbit_representatives_and_sizes_mod_2(G::Vector{FqMatrix}, k::Int)
  isempty(G) && throw(ArgumentError("at least one generator is required"))
  return orbit_representatives_and_sizes_mod_2(_word_type_mod2(nrows(G[1])), G, k)
end

@doc raw"""
    orbit_representatives_and_stabilizers_mod_2(G::Vector{FqMatrix}, k::Int; group_order = nothing)
    orbit_representatives_and_stabilizers_mod_2(T::Type{<:Unsigned}, G::Vector{FqMatrix}, k::Int; group_order = nothing)

Return representatives, sizes and stabilizers of the orbits of the group
generated by `G` on the `k`-dimensional subspaces of $\mathrm{GF}(2)^n$, where
the action is on row spaces by right multiplication ($U \mapsto U g$).

The stabilizer of each representative is computed directly (Schreier-Sims,
interleaved with the orbit traversal) as a small strong generating set, without
enumerating the orbit twice.

# Input
- `G`: a nonempty vector of invertible `n×n` matrices over $\mathrm{GF}(2)$
  (the generators of the group).
- `k`: the subspace dimension, `0 <= k <= n`.
- `T`: optional unsigned word type used internally; by default the smallest type
  that can hold the dimension `n` is chosen automatically.
- `group_order`: optional known order of the group generated by `G`. If given,
  the computation stops each orbit as soon as `len * stabilizer_order` reaches it,
  which can be faster. It must be the true group order.

# Output
A vector of tuples `(rep, len, stab, order)`, one per orbit, where
- `rep::FqMatrix` is a `k×n` matrix over $\mathrm{GF}(2)$ in reduced row echelon
  form whose rows span an orbit representative,
- `len::Int` is the length of that orbit,
- `stab::Vector{FqMatrix}` is a strong generating set of the stabilizer of `rep`
  (`n×n` matrices over $\mathrm{GF}(2)$), and
- `order::ZZRingElem` is the order of that stabilizer.

Note that `len * order` is the order of the group generated by `G` and is
therefore the same for every orbit.

See also [`orbit_representatives_and_sizes_mod_2`](@ref).
"""
function orbit_representatives_and_stabilizers_mod_2(::Type{T}, G::Vector{FqMatrix}, k::Int;
    group_order::Union{Nothing, IntegerUnion} = nothing) where T<:Unsigned
  isempty(G) && throw(ArgumentError("at least one generator is required"))
  n = nrows(G[1])
  F = base_ring(G[1])
  order(F) == 2 || throw(ArgumentError("matrices must be over GF(2)"))
  return [(_packed_rows_to_fqmatrix_mod2(rep, n, F), Int(orblen),
           FqMatrix[map_entries(F, s) for s in sgens], ord)
          for (orblen, rep, sgens, ord) in
              orbmod2_subspaces(T, G, k; stabilizer = true, group_order = group_order)]
end

function orbit_representatives_and_stabilizers_mod_2(G::Vector{FqMatrix}, k::Int;
    group_order::Union{Nothing, IntegerUnion} = nothing)
  isempty(G) && throw(ArgumentError("at least one generator is required"))
  return orbit_representatives_and_stabilizers_mod_2(_word_type_mod2(nrows(G[1])), G, k;
                                                     group_order = group_order)
end
