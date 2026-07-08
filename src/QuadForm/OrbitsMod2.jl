# The function orbmod2 and dependencies were ported from the Pari/GP code of Gaëtan Chenevier and Olivier Taïbi, 2026:
# https://olitb.net/pro/uni29/
# They were extended to compute orbits of subspaces by an AI assistant, 2026. 
# Simon Brandhorst takes responsibility for the correctness of this implementation and its extensions.
# 
# Copyright (C) 2026 Simon Brandhorst, Gaëtan Chenevier and Olivier Taïbi, 2026
# Permission to use, copy, modify, and/or distribute this software for any purpose with or without fee is hereby granted, provided that the above copyright notice and this permission notice appear in all copies.
# 
# THE SOFTWARE IS PROVIDED “AS IS” AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.


_mod2_bit(::Type{T}, x::Integer) where {T <: Unsigned} = isodd(x) ? one(T) : zero(T)
_mod2_bit(::Type{T}, x::ZZRingElem) where {T <: Unsigned} = is_odd(x) ? one(T) : zero(T)

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

function _matact_mod2(M::Vector{T}, offset::Int, x::T, n::Int) where {T <: Unsigned}
  res = zero(T)
  @inbounds for i in 0:(n - 1)
    res |= _parity_popcnt_mod2(M[offset + i] & x) << i
  end
  return res
end

function _is_new_mod2!(x::T, seen::Vector{T}, chunk_shift::Int, chunk_mask::T) where {T <: Unsigned}
  i = Int(x >> chunk_shift) + 1
  b = one(T) << (x & chunk_mask)
  @inbounds if !iszero(seen[i] & b)
    return false
  end
  @inbounds seen[i] |= b
  return true
end

function _find_next_after_mod2!(x::T, seen::Vector{T}, chunk_shift::Int, chunk_mask::T) where {T <: Unsigned}
  i = Int(x >> chunk_shift) + 1
  @inbounds while seen[i] == typemax(T)
    i += 1
  end
  y = @inbounds seen[i]
  v = (i - 1) << chunk_shift
  while !iszero(y & one(T))
    v += 1
    y >>= 1
  end
  xnew = T(v)
  @inbounds seen[Int(xnew >> chunk_shift) + 1] |= one(T) << (xnew & chunk_mask)
  return xnew
end

function _check_seen_mod2(seen::Vector{T}, n::Int, chunk_shift::Int) where {T <: Unsigned}
  if n < chunk_shift
    expected = (one(T) << (1 << n)) - one(T)
    seen[1] == expected || error("not really finished")
    return
  end
  for x in seen
    x == typemax(T) || error("not really finished")
  end
end

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
  chunk_shift = trailing_zeros(8 * sizeof(T))
  chunk_mask = T((8 * sizeof(T)) - 1)
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

function line_orbits_mod_2(::Type{T}, G::Vector{ZZMatrix}) where T<:Unsigned
  isempty(G) && throw(ArgumentError("at least one generator is required"))
  n = nrows(G[1])
  return [(Int(orblen),_unpack_mod2_vector(i, n)) for (orblen,i) in orbmod2(T, G)]
end
  
  
  

function _rref_rows_mod2!(rows::Vector{T}, n::Int) where {T <: Unsigned}
  m = length(rows)
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
  rank = ridx - 1
  resize!(rows, rank)
  return rank
end

function _for_all_k_subspaces_rref(::Type{T}, n::Int, k::Int, code::Function) where {T <: Unsigned}
  if k == 0
    return code(T[])
  end
  pivots = Vector{Int}(undef, k)
  rowbase = Vector{T}(undef, k)
  rowfree = Vector{T}(undef, k)
  rows = Vector{T}(undef, k)

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

  function rec_piv(pos::Int, start::Int)
    if pos > k
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

function _act_subspace_mod2(::Type{T}, packed::Vector{T}, n::Int, gen_index::Int, rep::Vector{T}) where {T <: Unsigned}
  y = [_matact_mod2(packed, gen_index * n + 1, x, n) for x in rep]
  rank = _rref_rows_mod2!(y, n)
  rank == length(rep) || throw(ArgumentError("generators must preserve subspace dimension"))
  return y
end

@doc raw"""
    orbmod2_subspaces([T::Type{<:Unsigned},] gens::Vector, k::Int)

Compute the orbits of the right linear action of `gens` on `k`-dimensional
subspaces of `F_2^n` (row spaces, `U -> U * g`, entries reduced modulo `2`).

Subspaces are represented in reduced row echelon form (RREF), encoded as vectors
of machine words.

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
  ngens = length(gens)
  keytype = NTuple{k, T}
  seen = Set{keytype}()
  todo = Vector{Vector{T}}()
  res = Tuple{UInt64, Vector{T}}[]
  _for_all_k_subspaces_rref(T, n, k, function(rep)
    key = keytype(Tuple(rep))
    key in seen && return false
    empty!(todo)
    push!(todo, rep)
    push!(seen, key)
    orb_len = UInt64(1)
    while !isempty(todo)
      x = pop!(todo)
      @inbounds for i in 0:(ngens - 1)
        y = _act_subspace_mod2(T, packed, n, i, x)
        ykey = keytype(Tuple(y))
        if !(ykey in seen)
          push!(seen, ykey)
          push!(todo, y)
          orb_len += 1
        end
      end
    end
    push!(res, (orb_len, rep))
    return false
  end)
  return res
end
orbmod2_subspaces(gens::Vector, k::Int) = orbmod2_subspaces(UInt64, gens, k)

