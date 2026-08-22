function _matrix_from_rows(v::Vector{Vector{ZZRingElem}}, n::Int)
  M = zero_matrix(ZZ, length(v), n)
  for i in 1:length(v)
    for j in 1:n
      M[i, j] = v[i][j]
    end
  end
  return M
end

# Return the non-trivial elementary divisors of Z^n/rowspan(B). A zero is
# included for every missing rank. This is the row-oriented analogue of
# matsnf(B, 4) in PARI.
function _good_basis_defects(B::ZZMatrix, n::Int)
  if iszero(nrows(B))
    return fill(ZZ(0), n)
  end
  d = filter(!isone, elementary_divisors(B))
  append!(d, fill(ZZ(0), n - rank(B)))
  return d
end

function _try_good_basis(
  G::ZZMatrix,
  bound::ZZRingElem,
  max_tries::Int,
  rng::AbstractRNG,
)
  n = nrows(G)
  L = integer_lattice(; gram=G, check=false, cached=false)
  short = short_vectors(L, bound)
  isempty(short) && return nothing

  vectors = first.(short)
  M = _matrix_from_rows(vectors, n)
  isempty(_good_basis_defects(M, n)) || return nothing

  shorter = Vector{Vector{ZZRingElem}}()
  for (v, q) in short
    q < bound && push!(shorter, v)
  end

  first_k = isempty(shorter) ? n : 1
  N = zero_matrix(ZZ, n, n)
  for k in first_k:n
    for _ in 1:max_tries
      for i in 1:n
        source = i <= k ? vectors : shorter
        v = rand(rng, source)
        for j in 1:n
          N[i, j] = v[j]
        end
      end
      isone(abs(det(N))) && return deepcopy(N)
    end
  end
  return nothing
end

function _good_basis_random(
  G::ZZMatrix,
  target::ZZRingElem,
  even::Bool,
  max_tries::Int,
  rng::AbstractRNG,
)
  n = nrows(G)
  iszero(n) && return identity_matrix(ZZ, 0)

  Gred, U = lll_gram_with_transform(G)
  m = maximum(diagonal(Gred))
  m <= target && return U

  step = even ? ZZ(2) : ZZ(1)
  bound = ZZ(2)
  while bound <= m - step
    N = _try_good_basis(Gred, bound, max_tries, rng)
    if N !== nothing
      @vprintln :Lattice 1 "Found a basis of maximum norm $bound"
      return N * U
    end
    bound += step
  end
  return U
end

# Select independent short vectors greedily. The positive semidefinite matrix
# T represents the form induced on the orthogonal complement of the vectors
# selected so far.
function _compact_lattice(G::ZZMatrix, vectors::Vector{Vector{ZZRingElem}})
  n = nrows(G)
  T = change_base_ring(QQ, G)
  d = one(QQ)
  selected = Vector{Vector{ZZRingElem}}()

  for _ in 1:n
    best = 0
    best_norm = zero(QQ)
    for i in 1:length(vectors)
      v = vectors[i]
      q = zero(QQ)
      for j in 1:n
        for k in 1:n
          q += v[j] * T[j, k] * v[k]
        end
      end
      if q > 0 && (iszero(best) || q < best_norm)
        best = i
        best_norm = q
      end
    end
    iszero(best) && break

    v = vectors[best]
    push!(selected, v)
    w = zero_matrix(QQ, 1, n)
    for j in 1:n
      for k in 1:n
        w[1, j] += v[k] * T[k, j]
      end
    end
    T = divexact(best_norm * T - transpose(w) * w, d)
    d = best_norm
  end
  return _matrix_from_rows(selected, n)
end

function _is_primitive_corank_one(B::ZZMatrix, n::Int)
  d = _good_basis_defects(B, n)
  return length(d) == 1 && iszero(d[1])
end

# Complete a primitive rank n-1 system B, then replace the final vector by a
# shortest vector in its coset modulo rowspan(B).
function _complete_good_basis(G::ZZMatrix, B::ZZMatrix)
  n = nrows(G)
  @assert nrows(B) == n - 1
  @assert _is_primitive_corank_one(B, n)

  C0 = _complete_to_basis(B)
  if n == 1
    return C0
  end
  C = C0[vcat(collect(2:n), [1]), :]
  @assert C[1:(n - 1), :] == B

  GC = C * G * transpose(C)
  S = GC[1:(n - 1), 1:(n - 1)]
  center = -change_base_ring(QQ, GC[n:n, 1:(n - 1)]) *
           inv(change_base_ring(QQ, S))

  y0 = zero_matrix(ZZ, 1, n - 1)
  for i in 1:(n - 1)
    y0[1, i] = round(ZZRingElem, center[1, i])
  end
  delta_vector = change_base_ring(QQ, y0) - center
  upper_bound = (delta_vector * change_base_ring(QQ, S) *
                 transpose(delta_vector))[1, 1]

  LS = integer_lattice(; gram=S, check=false, cached=false)
  closest = close_vectors_iterator(LS, vec(collect(center)), upper_bound; check=false)
  next = iterate(closest)
  @assert next !== nothing
  best, state = next
  while true
    next = iterate(closest, state)
    next === nothing && break
    candidate, state = next
    candidate[2] < best[2] && (best = candidate)
  end

  D = identity_matrix(ZZ, n)
  for i in 1:(n - 1)
    D[n, i] = best[1][i]
  end
  return D * C
end

function _good_basis_hybrid(
  G::ZZMatrix,
  target::ZZRingElem,
  even::Bool,
  rng::AbstractRNG;
  multiplier::Int,
  compact_tries::Int,
  random_tries::Int,
  codimension::Union{Nothing, Int}=nothing,
)
  n = nrows(G)
  L = integer_lattice(; gram=G, check=false, cached=false)
  short = short_vectors(L, target)
  vectors = first.(short)

  if codimension === nothing
    M = _matrix_from_rows(vectors, n)
    codimension = length(_good_basis_defects(M, n))
    if codimension > 1
      return _good_basis_random(G, target, even, random_tries, rng)
    end
  end

  shorter = Vector{Vector{ZZRingElem}}()
  boundary = Vector{Vector{ZZRingElem}}()
  for (v, q) in short
    if q < target
      push!(shorter, v)
    elseif q == target
      push!(boundary, v)
    end
  end

  if isempty(boundary)
    step = even ? ZZ(2) : ZZ(1)
    if isempty(short) || target <= step
      return _good_basis_random(G, target, even, random_tries, rng)
    end
    return _good_basis_hybrid(
      G,
      target - step,
      even,
      rng;
      multiplier,
      compact_tries,
      random_tries,
      codimension,
    )
  end

  for _ in 1:compact_tries
    candidates = copy(shorter)
    sizehint!(candidates, length(shorter) + multiplier * n)
    for _ in 1:(multiplier * n)
      push!(candidates, rand(rng, boundary))
    end
    B = _compact_lattice(G, candidates)

    if codimension == 0 && isempty(_good_basis_defects(B, n))
      return B
    end

    if codimension == 1 && nrows(B) == n &&
       length(_good_basis_defects(B, n)) == 1
      for i in n:-1:1
        rows = [j for j in 1:n if j != i]
        C = B[rows, :]
        if _is_primitive_corank_one(C, n)
          B = C
          break
        end
      end
    end

    if codimension == 1 && _is_primitive_corank_one(B, n)
      return _complete_good_basis(G, B)
    end
  end

  if codimension == 0
    return _good_basis_hybrid(
      G,
      target,
      even,
      rng;
      multiplier,
      compact_tries,
      random_tries,
      codimension=1,
    )
  end
  return _good_basis_random(G, target, even, random_tries, rng)
end

@doc raw"""
    good_basis(
      L::ZZLat;
      target::IntegerUnion=4,
      rng::AbstractRNG=Random.default_rng(),
      multiplier::Int=20,
      compact_tries::Int=30,
      random_tries::Int=10000,
    ) -> ZZLat

Search for a basis of `L` consisting of short vectors. The returned lattice is
equal to `L`, lies in the same ambient space, and is represented using the
best basis found.

The function first LLL-reduces the basis. If its largest absolute squared
length is larger than `target`, short vectors are combined using a hybrid
deterministic/randomized search. The result is never worse than the
LLL-reduced basis with respect to the largest absolute squared length.

The lattice must be integral and definite. The keyword `rng` can be used to
make the randomized parts of the search reproducible. The remaining keywords
control the number of sampled boundary vectors, hybrid attempts, and random
basis attempts, respectively.

This implementation is adapted from
[`good_bases.gp`](https://github.com/olitb/lattools/blob/main/good_bases.gp).

# Examples
```jldoctest
julia> L = root_lattice(:E, 8);

julia> M = good_basis(L);

julia> M == L
true

julia> maximum(abs, diagonal(gram_matrix(M)))
2
```
"""
function good_basis(
  L::ZZLat;
  target::IntegerUnion=4,
  rng::AbstractRNG=Random.default_rng(),
  multiplier::Int=20,
  compact_tries::Int=30,
  random_tries::Int=10000,
)
  @req is_integral(L) "Lattice must be integral"
  @req is_definite(L) "Lattice must be definite"
  @req target > 0 "Target must be positive"
  @req multiplier > 0 "Multiplier must be positive"
  @req compact_tries > 0 "Number of compact tries must be positive"
  @req random_tries > 0 "Number of random tries must be positive"

  n = rank(L)
  iszero(n) && return L
  G, d = _integral_split_gram(L)
  @assert isone(d)
  if G[1, 1] < 0
    G = -G
  end

  Gred, Ulll = lll_gram_with_transform(G)
  lll_max = maximum(diagonal(Gred))
  _target = ZZ(target)
  if iseven(L) && isodd(_target)
    _target -= 1
  end

  if lll_max <= _target || _target <= 0
    U = Ulll
  else
    Uhybrid = _good_basis_hybrid(
      Gred,
      _target,
      iseven(L),
      rng;
      multiplier,
      compact_tries,
      random_tries,
    )
    @hassert :Lattice 1 isone(abs(det(Uhybrid)))
    hybrid_max = maximum(diagonal(Uhybrid * Gred * transpose(Uhybrid)))
    U = hybrid_max <= lll_max ? Uhybrid * Ulll : Ulll
  end

  B = U * basis_matrix(L)
  return lattice_in_same_ambient_space(L, B; isbasis=true, check=false)
end
