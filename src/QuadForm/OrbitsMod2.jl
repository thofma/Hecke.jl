# The function orbmod2 and dependencies were ported from the Pari/GP code of Gaëtan Chenevier and Olivier Taïbi, 2026:
# https://olitb.net/pro/uni29/
# The port is due to AI. The functionality to compute orbits of subspaces was added in cooperation with an AI assistant, 2026.
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
  @assert iszero(a[1]) "first orbit should be the zero vector"
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
      return code(copy(rows))
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

# Inputs: Val(k) fixes tuple size and rep is an RREF basis as a fixed tuple.
# Output key layout: (pivot_mask, free_row_1, ..., free_row_k).
@inline function _subspace_key_mod2(::Val{k}, rep::NTuple{k, T}) where {k, T <: Unsigned}
  pivmask = zero(T)
  @inbounds for i in 1:k
    pivmask |= _pivot_bit_mod2_row(rep[i])
  end
  free_rows = ntuple(i -> rep[i] ⊻ _pivot_bit_mod2_row(rep[i]), Val(k))
  return (pivmask, free_rows...)
end

@doc raw"""
    orbmod2_subspaces([T::Type{<:Unsigned},] gens::Vector, k::Int)

Compute the orbits of the right linear action of `gens` on `k`-dimensional
subspaces of `F_2^n` (row spaces, `U -> U * g`, entries reduced modulo `2`).

Subspaces are represented in reduced row echelon form (RREF), encoded as vectors
of machine words. Visited states are hashed by the canonical packed key
`(pivot_mask, free_row_1, ..., free_row_k)`.

# Input
- `T`: optional unsigned word type (`UInt16`, `UInt32`, `UInt64`, ...),
  default is `UInt64`.
- `gens`: a nonempty vector of square `n×n` matrices with entries interpreted modulo `2`.
- `k`: target subspace dimension, must satisfy `0 <= k <= n` and `n <= 8*sizeof(T)-1`.

# Output
Return a vector of pairs `(len, rep)` where
- `len::UInt64` is the orbit length,
- `rep::Vector{T}` is an RREF representative of length `k` (one packed row per entry).
"""
function orbmod2_subspaces(::Type{T}, gens::Vector, k::Int) where {T <: Unsigned}
  packed, n = _pack_linear_generators_mod2(T, gens)
  0 <= k <= n || throw(ArgumentError("k must satisfy 0 <= k <= n"))
  if k == 0
    return [(UInt64(1), T[])]
  end
  if k == n
    rep = [one(T) << (i - 1) for i in 1:n]
    return [(UInt64(1), rep)]
  end
  ngens = length(gens)
  # basis_images = _precompute_basis_images_mod2(T, packed, n, ngens)  #disabled for now
  offsets = [i * n + 1 for i in 0:(ngens - 1)]
  kval = Val(k)
  keytype = NTuple{k + 1, T}
  seen = Set{keytype}()
  todo = Vector{NTuple{k, T}}()
  res = Tuple{UInt64, NTuple{k, T}}[]
  scratch = Vector{T}(undef, k)
  _for_all_k_subspaces_rref(T, n, k, function(rep)
    key = _subspace_key_mod2(kval, rep)
    key in seen && return false
    empty!(todo)
    push!(todo, _vector_to_ntuple_mod2(kval, rep))
    push!(seen, key)
    orb_len = UInt64(1)
    while !isempty(todo)
      x = pop!(todo)
      @inbounds for offset in offsets  # offset picks the generator
        y = _act_subspace_mod2!(scratch, packed, offset, n, k, x)
        #y = _act_subspace_mod2!(scratch, basis_images, offset, n, k, x)
        ykey = _subspace_key_mod2(kval, scratch)
        if !(ykey in seen)
          push!(seen, ykey)
          push!(todo, _vector_to_ntuple_mod2(kval, y))
          orb_len += 1
        end
      end
    end
    push!(res, (orb_len, _vector_to_ntuple_mod2(kval, rep)))
    return false
  end)
  return [(len, collect(rep)) for (len, rep) in res]
end

orbmod2_subspaces(gens::Vector, k::Int) = orbmod2_subspaces(UInt64, gens, k)


# Inputs: T is the packed word type, G is a vector of GF(2) matrices, k is subspace dimension.
function orbit_representatives_and_sizes_mod_2(::Type{T}, G::Vector{FqMatrix}, k::Int) where T<:Unsigned
  isempty(G) && throw(ArgumentError("at least one generator is required"))
  n = nrows(G[1])
  order(base_ring(G[1])) == 2 || throw(ArgumentError("matrices must be integers or in GF(2)"))
  return [([_unpack_mod2_vector(i, n) for i in j], Int(orblen)) for (orblen,j) in orbmod2_subspaces(T, G, k)]
end
