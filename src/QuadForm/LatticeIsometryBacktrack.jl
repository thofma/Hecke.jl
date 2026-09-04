################################################################################
#
#  Plain partition backtracking for definite integer lattices
#
################################################################################

# This is a direct implementation of the basis-image search of
# Plesken--Souvignier.  If G is the Gram matrix of a positive definite lattice,
# every image of a basis vector belongs to the finite set of vectors of norm at
# most maximum(diagonal(G)).  Isometries permute this signed short-vector set.
# The search individualizes basis images one after another.  After each choice,
# an ordered partition of the short vectors is refined by their scalar products
# with the chosen image.
#
# The implementation deliberately keeps the setup and the search elementary:
# Hecke's short_vectors performs the enumeration, all vector coordinates and
# matrix entries are ZZRingElem values, and partition cells are ordinary Julia
# vectors and dictionaries.  The only group-theoretic bookkeeping is the
# stabilizer chain needed to turn found automorphisms into generators and an
# order.

struct LatticeIsometryBacktrackCtx
  gram::ZZMatrix
  vectors::Vector{Vector{ZZRingElem}}
  gram_products::Vector{Vector{ZZRingElem}}
  norms::Vector{ZZRingElem}
  vectors_by_norm::Dict{ZZRingElem, Vector{Int}}
  lookup::Dict{Vector{ZZRingElem}, Int}
  basis_positions::Vector{Int}
  image_cache::IdDict{ZZMatrix, Vector{Int}}
end

function LatticeIsometryBacktrackCtx(G::ZZMatrix, bound::ZZRingElem)
  L = integer_lattice(gram = G, cached = false)
  vectors = Vector{ZZRingElem}[]
  gram_products = Vector{ZZRingElem}[]
  norms = ZZRingElem[]
  gram_entry = zero(ZZRingElem)

  # short_vectors returns one representative of each pair {v, -v}.  Both
  # signs are possible basis images, so store both explicitly.
  for (v, q) in short_vectors(L, bound, ZZRingElem)
    w = ZZRingElem[x for x in v]
    wG = [zero(ZZRingElem) for _ in eachindex(w)]
    for j in eachindex(w)
      for i in eachindex(w)
        getindex!(gram_entry, G, i, j)
        addmul!(wG[j], w[i], gram_entry)
      end
    end
    nw = numerator(q)
    push!(vectors, w)
    push!(gram_products, wG)
    push!(norms, nw)
    push!(vectors, -w)
    push!(gram_products, -wG)
    push!(norms, nw)
  end

  vectors_by_norm = Dict{ZZRingElem, Vector{Int}}()
  lookup = Dict{Vector{ZZRingElem}, Int}()
  for (i, v) in enumerate(vectors)
    push!(get!(Vector{Int}, vectors_by_norm, norms[i]), i)
    lookup[v] = i
  end

  # Record which short vectors are signed standard basis vectors.  Pairing
  # against one of these then amounts to reading one entry of v * G.
  basis_positions = zeros(Int, length(vectors))
  e = zeros(ZZRingElem, nrows(G))
  for i in eachindex(e)
    e[i] = 1
    j = get(lookup, e, 0)
    iszero(j) || (basis_positions[j] = i)
    e[i] = -1
    j = get(lookup, e, 0)
    iszero(j) || (basis_positions[j] = -i)
    e[i] = 0
  end

  return LatticeIsometryBacktrackCtx(
    G,
    vectors,
    gram_products,
    norms,
    vectors_by_norm,
    lookup,
    basis_positions,
    IdDict{ZZMatrix, Vector{Int}}(),
  )
end

function _lattice_backtrack_pairing(
  C::LatticeIsometryBacktrackCtx,
  i::Int,
  j::Int,
)
  vG = C.gram_products[i]
  basis_position = C.basis_positions[j]
  if basis_position > 0
    return vG[basis_position]
  elseif basis_position < 0
    return -vG[-basis_position]
  end

  w = C.vectors[j]
  result = zero(ZZRingElem)
  for k in eachindex(vG)
    addmul!(result, vG[k], w[k])
  end
  return result
end

function _lattice_backtrack_basis_indices(C::LatticeIsometryBacktrackCtx)
  n = nrows(C.gram)
  result = Vector{Int}(undef, n)
  e = zeros(ZZRingElem, n)
  for i in 1:n
    e[i] = 1
    result[i] = C.lookup[e]
    e[i] = 0
  end
  return result
end

struct LatticeBacktrackPartition
  points::Vector{Int}
  starts::Vector{Int}
  stops::Vector{Int}
  cell_of::Vector{Int}
end

struct LatticeBacktrackRefinement
  value_indices::Vector{Dict{ZZRingElem, Int}}
  sizes::Vector{Vector{Int}}
end

struct LatticeBacktrackFingerprint
  order::Vector{Int}
  counts::Vector{Int}
  basis_indices::Vector{Int}
  initial_norms::Vector{ZZRingElem}
  partitions::Vector{LatticeBacktrackPartition}
  candidate_cells::Vector{Int}
  refinements::Vector{LatticeBacktrackRefinement}
end

function _lattice_backtrack_initial_partition(
  C::LatticeIsometryBacktrackCtx,
  norms::Vector{ZZRingElem},
)
  points = Int[]
  starts = Int[]
  stops = Int[]
  cell_of = zeros(Int, length(C.vectors))
  for norm in norms
    cell = get(C.vectors_by_norm, norm, nothing)
    cell === nothing && return nothing
    push!(starts, length(points) + 1)
    append!(points, cell)
    push!(stops, length(points))
    cell_number = length(starts)
    for point in cell
      cell_of[point] = cell_number
    end
  end
  return LatticeBacktrackPartition(points, starts, stops, cell_of)
end

function _lattice_backtrack_same_shape(
  left::LatticeBacktrackPartition,
  right::LatticeBacktrackPartition,
)
  length(left.starts) == length(right.starts) || return false
  for cell in eachindex(left.starts)
    left.stops[cell] - left.starts[cell] ==
      right.stops[cell] - right.starts[cell] || return false
  end
  return true
end

function _lattice_backtrack_refine_source(
  C::LatticeIsometryBacktrackCtx,
  partition::LatticeBacktrackPartition,
  pivot::Int,
  remaining_basis_points::BitSet,
)
  points = Int[]
  starts = Int[]
  stops = Int[]
  cell_of = zeros(Int, length(C.vectors))
  value_indices = Vector{Dict{ZZRingElem, Int}}(undef, length(partition.starts))
  sizes = Vector{Vector{Int}}(undef, length(partition.starts))

  for cell in eachindex(partition.starts)
    blocks = Dict{ZZRingElem, Vector{Int}}()
    for position in partition.starts[cell]:partition.stops[cell]
      point = partition.points[position]
      value = _lattice_backtrack_pairing(C, point, pivot)
      push!(get!(Vector{Int}, blocks, value), point)
    end

    kept_values = ZZRingElem[]
    for (value, block) in blocks
      any(point -> point in remaining_basis_points, block) || continue
      push!(kept_values, value)
    end
    sort!(kept_values)

    indices = Dict{ZZRingElem, Int}()
    kept_sizes = Int[]
    for value in kept_values
      block = blocks[value]
      push!(starts, length(points) + 1)
      append!(points, block)
      push!(stops, length(points))
      new_cell = length(starts)
      for point in block
        cell_of[point] = new_cell
      end
      indices[value] = length(kept_sizes) + 1
      push!(kept_sizes, length(block))
    end
    value_indices[cell] = indices
    sizes[cell] = kept_sizes
  end

  refined = LatticeBacktrackPartition(points, starts, stops, cell_of)
  refinement = LatticeBacktrackRefinement(value_indices, sizes)
  return refined, refinement
end

function _lattice_backtrack_refine_target(
  C::LatticeIsometryBacktrackCtx,
  partition::LatticeBacktrackPartition,
  pivot::Int,
  refinement::LatticeBacktrackRefinement,
)
  points = Int[]
  starts = Int[]
  stops = Int[]

  for cell in eachindex(partition.starts)
    expected_sizes = refinement.sizes[cell]
    isempty(expected_sizes) && continue
    blocks = [Int[] for _ in expected_sizes]
    indices = refinement.value_indices[cell]
    for position in partition.starts[cell]:partition.stops[cell]
      point = partition.points[position]
      value = _lattice_backtrack_pairing(C, point, pivot)
      child = get(indices, value, 0)
      iszero(child) || push!(blocks[child], point)
    end

    for child in eachindex(blocks)
      length(blocks[child]) == expected_sizes[child] || return nothing
      push!(starts, length(points) + 1)
      append!(points, blocks[child])
      push!(stops, length(points))
    end
  end
  return LatticeBacktrackPartition(points, starts, stops, Int[])
end

# Choose a basis order by individualizing a basis vector in a smallest cell and
# refining every cell by its scalar product with that vector.  Cells containing
# no remaining basis vector can never supply a later basis image and are dropped.
function _lattice_backtrack_fingerprint(C::LatticeIsometryBacktrackCtx)
  n = nrows(C.gram)
  basis_indices = _lattice_backtrack_basis_indices(C)
  initial_norms = unique!(sort!(ZZRingElem[C.gram[i, i] for i in 1:n]))
  initial_partition = _lattice_backtrack_initial_partition(C, initial_norms)
  initial_partition === nothing && error("a basis norm has no short vectors")

  order = Int[]
  counts = Int[]
  candidate_cells = Int[]
  partitions = LatticeBacktrackPartition[initial_partition]
  refinements = LatticeBacktrackRefinement[]
  remaining = collect(1:n)

  while !isempty(remaining)
    partition = partitions[end]
    best_position = 1
    best_count = typemax(Int)
    for position in eachindex(remaining)
      point = basis_indices[remaining[position]]
      cell = partition.cell_of[point]
      count = partition.stops[cell] - partition.starts[cell] + 1
      if count < best_count
        best_position = position
        best_count = count
      end
    end

    source_index = remaining[best_position]
    deleteat!(remaining, best_position)
    push!(order, source_index)
    push!(counts, best_count)
    push!(candidate_cells, partition.cell_of[basis_indices[source_index]])

    remaining_points = BitSet(basis_indices[i] for i in remaining)
    refined, refinement = _lattice_backtrack_refine_source(
      C, partition, basis_indices[source_index], remaining_points,
    )
    push!(partitions, refined)
    push!(refinements, refinement)
  end

  return LatticeBacktrackFingerprint(
    order,
    counts,
    basis_indices,
    initial_norms,
    partitions,
    candidate_cells,
    refinements,
  )
end

function _lattice_backtrack_matrix(
  images::Vector{Int},
  order::Vector{Int},
  target::LatticeIsometryBacktrackCtx,
)
  n = length(order)
  M = zero_matrix(ZZ, n, n)
  for depth in 1:n
    image = target.vectors[images[depth]]
    for j in 1:n
      M[order[depth], j] = image[j]
    end
  end
  return M
end

function _lattice_backtrack_extend!(
  images::Vector{Int},
  depth::Int,
  source_gram::ZZMatrix,
  fingerprint::LatticeBacktrackFingerprint,
  target::LatticeIsometryBacktrackCtx,
  partition::LatticeBacktrackPartition,
)
  if depth > length(fingerprint.order)
    M = _lattice_backtrack_matrix(images, fingerprint.order, target)
    if abs(det(M)) == 1 && M * target.gram * transpose(M) == source_gram
      return M
    end
    return nothing
  end

  cell = fingerprint.candidate_cells[depth]
  cell <= length(partition.starts) || return nothing
  first_candidate = partition.starts[cell]
  last_candidate = partition.stops[cell]
  last_candidate - first_candidate + 1 == fingerprint.counts[depth] || return nothing

  for position in first_candidate:last_candidate
    image = partition.points[position]
    images[depth] = image
    refined = _lattice_backtrack_refine_target(
      target, partition, image, fingerprint.refinements[depth],
    )
    refined === nothing && continue
    M = _lattice_backtrack_extend!(
      images, depth + 1, source_gram, fingerprint, target, refined,
    )
    M === nothing || return M
  end
  return nothing
end

function _lattice_backtrack_histogram(C::LatticeIsometryBacktrackCtx)
  result = Dict{ZZRingElem, Int}()
  for norm in C.norms
    result[norm] = get(result, norm, 0) + 1
  end
  return result
end

function _lattice_backtrack_isometry(G1::ZZMatrix, G2::ZZMatrix)
  nrows(G1) == nrows(G2) || return nothing
  det(G1) == det(G2) || return nothing

  n = nrows(G1)
  bound = maximum(G1[i, i] for i in 1:n)
  source = LatticeIsometryBacktrackCtx(G1, bound)
  target = LatticeIsometryBacktrackCtx(G2, bound)
  _lattice_backtrack_histogram(source) == _lattice_backtrack_histogram(target) ||
    return nothing

  fingerprint = _lattice_backtrack_fingerprint(source)
  partition = _lattice_backtrack_initial_partition(target, fingerprint.initial_norms)
  partition === nothing && return nothing
  _lattice_backtrack_same_shape(fingerprint.partitions[1], partition) || return nothing
  images = Vector{Int}(undef, n)
  return _lattice_backtrack_extend!(images, 1, G1, fingerprint, target, partition)
end

function _lattice_backtrack_image(
  C::LatticeIsometryBacktrackCtx,
  point::Int,
  M::ZZMatrix,
)
  cache = get!(() -> zeros(Int, length(C.vectors)), C.image_cache, M)
  cached_image = cache[point]
  iszero(cached_image) || return cached_image

  v = C.vectors[point]
  n = length(v)
  image = [zero(ZZRingElem) for _ in 1:n]
  matrix_entry = zero(ZZRingElem)
  for j in 1:n
    for i in 1:n
      getindex!(matrix_entry, M, i, j)
      addmul!(image[j], v[i], matrix_entry)
    end
  end
  result = get(C.lookup, image, 0)
  iszero(result) && error("an automorphism did not preserve the short vectors")
  cache[point] = result
  return result
end

function _lattice_backtrack_orbit(
  C::LatticeIsometryBacktrackCtx,
  points::Vector{Int},
  generators::Vector{ZZMatrix},
)
  orbit = copy(points)
  seen = BitSet(points)
  next = 1
  while next <= length(orbit)
    point = orbit[next]
    for generator in generators
      image = _lattice_backtrack_image(C, point, generator)
      if !(image in seen)
        push!(seen, image)
        push!(orbit, image)
      end
    end
    next += 1
  end
  return seen
end

function _lattice_backtrack_automorphism_group(G::ZZMatrix)
  n = nrows(G)
  bound = maximum(G[i, i] for i in 1:n)
  C = LatticeIsometryBacktrackCtx(G, bound)
  fingerprint = _lattice_backtrack_fingerprint(C)
  order = fingerprint.order
  base = Int[fingerprint.basis_indices[i] for i in order]
  generators = [ZZMatrix[] for _ in 1:n]
  orbit_lengths = ones(Int, n)

  # Negation is always an automorphism.  Treat it like every other generator;
  # at later levels it drops out because it does not fix the first base point.
  push!(generators[1], -identity_matrix(ZZ, n))

  images = Vector{Int}(undef, n)
  for step in 1:n
    for i in 1:(step - 1)
      images[i] = base[i]
    end

    partition = fingerprint.partitions[step]
    cell = fingerprint.candidate_cells[step]
    candidates = partition.points[partition.starts[cell]:partition.stops[cell]]
    length(candidates) == fingerprint.counts[step] ||
      error("inconsistent automorphism partition")

    stabilizer_generators = ZZMatrix[]
    for level in step:n
      append!(stabilizer_generators, generators[level])
    end

    failed_representatives = Int[]
    while true
      good = _lattice_backtrack_orbit(C, Int[base[step]], stabilizer_generators)
      bad = _lattice_backtrack_orbit(C, failed_representatives, stabilizer_generators)
      candidate = findfirst(i -> !(i in good) && !(i in bad), candidates)
      if candidate === nothing
        orbit_lengths[step] = length(good)
        break
      end

      images[step] = candidates[candidate]
      refined = _lattice_backtrack_refine_target(
        C, partition, images[step], fingerprint.refinements[step],
      )
      M = refined === nothing ? nothing : _lattice_backtrack_extend!(
        images, step + 1, G, fingerprint, C, refined,
      )
      if M === nothing
        push!(failed_representatives, images[step])
      else
        push!(generators[step], M)
        push!(stabilizer_generators, M)
      end
    end
  end

  result = ZZMatrix[]
  for level in generators
    append!(result, level)
  end
  @assert all(M -> M * G * transpose(M) == G, result)
  group_order = prod(ZZRingElem.(orbit_lengths); init = one(ZZRingElem))
  return result, group_order
end

# Make a definite rational Gram matrix positive, primitive, integral, and LLL
# reduced.  If T is the returned transformation, then the reduced matrix is a
# scalar multiple of T * gram_matrix(L) * transpose(T).
function _lattice_backtrack_reduce_gram(L::ZZLat)
  G = gram_matrix(L)
  s = sign(G[1, 1])
  d = denominator(G)
  integral_gram = change_base_ring(ZZ, s * d * G)
  c = content(integral_gram)
  primitive_gram = divexact(integral_gram, c)
  reduced_gram, transformation = lll_gram_with_transform(primitive_gram)
  return reduced_gram, transformation, d//c
end

function _automorphism_group_backtrack_vanilla(L::ZZLat)
  @req is_definite(L) "Lattice must be definite"
  n = rank(L)
  if n == 0
    return ZZMatrix[identity_matrix(ZZ, 0)], one(ZZRingElem)
  elseif n == 1
    return ZZMatrix[-identity_matrix(ZZ, 1)], ZZRingElem(2)
  end

  G, T, _ = _lattice_backtrack_reduce_gram(L)
  reduced_generators, group_order = _lattice_backtrack_automorphism_group(G)
  inverse_transformation = inv(T)
  generators = ZZMatrix[inverse_transformation * M * T for M in reduced_generators]
  @hassert :Lattice 1 all(
    M -> change_base_ring(QQ, M) * gram_matrix(L) *
         transpose(change_base_ring(QQ, M)) == gram_matrix(L),
    generators,
  )
  return generators, group_order
end

function _is_isometric_with_isometry_backtrack_vanilla(L::ZZLat, M::ZZLat)
  @req is_definite(L) && is_definite(M) "Lattices must be definite"
  if rank(L) != rank(M)
    return false, zero_matrix(QQ, 0, 0)
  elseif rank(L) == 0
    return true, zero_matrix(QQ, 0, 0)
  elseif sign(gram_matrix(L)[1, 1]) != sign(gram_matrix(M)[1, 1])
    return false, zero_matrix(QQ, 0, 0)
  elseif rank(L) == 1
    if gram_matrix(L) == gram_matrix(M)
      return true, identity_matrix(QQ, 1)
    end
    return false, zero_matrix(QQ, 0, 0)
  end

  G1, T1, scale1 = _lattice_backtrack_reduce_gram(L)
  G2, T2, scale2 = _lattice_backtrack_reduce_gram(M)
  scale1 == scale2 || return false, zero_matrix(QQ, 0, 0)

  reduced_isometry = _lattice_backtrack_isometry(G1, G2)
  reduced_isometry === nothing && return false, zero_matrix(QQ, 0, 0)
  isometry = change_base_ring(QQ, inv(T1) * reduced_isometry * T2)
  @hassert :Lattice 1 isometry * gram_matrix(M) * transpose(isometry) ==
                          gram_matrix(L)
  return true, isometry
end
