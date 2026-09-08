################################################################################
#
#  Partition backtracking for definite integer lattices
#
################################################################################
#
# This is the plain version of the search, written to be read rather than to be
# fast; `IsometryBacktrack.jl` is the optimized variant.  It computes isometries
# and automorphism groups of an ordered list of integral symmetric forms of
# which the first one is positive definite.
#
#  The setting.  Let G_1, ..., G_r be the forms and let b = max_i (G_1)_{ii}.
#  Any isometry maps each standard basis vector to a vector of the same norm
#  under G_1, hence to one of the finitely many vectors of norm at most b.  The
#  *points* of the search are therefore the vectors v with 0 < v G_1 v' <= b,
#  each stored together with -v, and an isometry is determined by the images of
#  the n basis vectors among them.  This is exactly the setup of
#  Plesken--Souvignier.  What is different is only how the candidates for those
#  images are maintained.
#
#  Partition backtracking, in one paragraph.  Instead of testing a candidate
#  image against the already chosen ones one scalar product at a time, the
#  search maintains an *ordered partition* of the whole point set: an ordered
#  list of cells whose defining property is that a point can only be mapped to a
#  point sitting in the cell of the same index on the other side.  The search
#  tree has two nodes at each step, one for the source and one for the target,
#  each carrying such a partition.  A step consists of *individualizing* a point
#  -- putting it into a cell of its own -- and then *refining*: splitting every
#  cell by an invariant that an isometry must preserve, here the scalar products
#  with the individualized point under all the forms.  The refinement is one
#  function applied on both sides, which is what makes the cells of the two
#  nodes correspond.  Two nodes can only be matched if the resulting partitions
#  have the same *shape*, and that test is the pruning.
#
#  The dictionary to Plesken--Souvignier.  The initial partition, grouping the
#  points by their norms, is the classification of the short vectors by norm.
#  The cell containing the k-th base point is the candidate list for the k-th
#  basis image, and its size is the k-th entry of the fingerprint.  The
#  refinement by scalar products with the pivot is the scalar product test,
#  performed for all points at once and remembered, rather than recomputed for
#  each candidate.  The choice of base, individualizing in a smallest cell, is
#  the reordering of the basis by the fingerprint.  The automorphism group is
#  computed exactly as in Plesken--Souvignier, from a base and the orbits of the
#  stabilizer chain.
#
#  What is certified.  The images found are checked by M G'_k M' == G_k for
#  every k, so a returned isometry is correct independently of the search.  The
#  determinant test at the start makes an integral solution automatically
#  unimodular.  Completeness rests on every pruning step being a necessary
#  condition; there are exactly two, the shape test and the orbit test, and both
#  are justified where they occur.  All search arithmetic is in `Int`.
#
#  What was left out on purpose.  Every node here rebuilds its partition as
#  fresh vectors, and every cell is refined even when it can no longer contain
#  the image of a basis vector.  Both are wasteful and both are easy to change
#  once the structure above is agreed on: the partition can be kept in one array
#  of points with the cells as index ranges, refined in place and undone on
#  backtracking, and the refinement can be restricted to the cells that a later
#  base point can still land in.  The scalar products with the already chosen
#  images can be accumulated instead of recomputed.  The isometry search can use
#  the automorphism group of the source to skip images that differ by an
#  automorphism.  Of these, only the first two are pure bookkeeping; dropping
#  cells makes the shape test weaker and can enlarge the tree, and skipping
#  images by automorphisms is a third pruning criterion that has to be justified
#  like the two above.

################################################################################
#
#  The points
#
################################################################################

struct LatticeIsometryBacktrackCtx
  grams::Vector{Matrix{Int}}                   # the forms; grams[1] is definite
  vectors::Vector{Vector{Int}}                 # the points of the search
  gram_products::Vector{Vector{Vector{Int}}}   # gram_products[i][k] = v_i * G_k
  norms::Vector{Vector{Int}}                   # norms[i][k] = v_i * G_k * v_i'
  lookup::Dict{Vector{Int}, Int}               # the inverse of `vectors`
end

function _lattice_backtrack_check_grams(grams)
  @req !isempty(grams) "At least one Gram matrix is required"
  n = size(first(grams), 1)
  @req all(G -> size(G) == (n, n), grams) "Gram matrices must be square and have the same size"
  @req all(G -> G == transpose(G), grams) "Gram matrices must be symmetric"
  return n
end

function LatticeIsometryBacktrackCtx(G::Matrix{Int}, bound::Int)
  return LatticeIsometryBacktrackCtx([G], bound)
end

function LatticeIsometryBacktrackCtx(grams::Vector{Matrix{Int}}, bound::Int)
  n = _lattice_backtrack_check_grams(grams)
  L = integer_lattice(gram = matrix(ZZ, grams[1]), cached = false)
  @req is_positive_definite(L) "The first Gram matrix must be positive definite"
  vectors = Vector{Int}[]
  gram_products = Vector{Vector{Int}}[]
  norms = Vector{Int}[]

  # short_vectors returns one representative of each pair {v, -v}.  Both signs
  # are possible basis images, so both are points of the search.
  for (w, _) in short_vectors(L, bound, Int)
    wGs = Vector{Vector{Int}}(undef, length(grams))
    nw = Vector{Int}(undef, length(grams))
    for k in eachindex(grams)
      G = grams[k]
      wG = zeros(Int, n)
      for j in 1:n
        for i in 1:n
          wG[j] += w[i] * G[i, j]
        end
      end
      wGs[k] = wG
      nw[k] = sum(w[i] * wG[i] for i in 1:n)
    end
    push!(vectors, w)
    push!(gram_products, wGs)
    push!(norms, nw)
    push!(vectors, -w)
    push!(gram_products, [-wG for wG in wGs])
    push!(norms, nw)
  end

  lookup = Dict{Vector{Int}, Int}()
  for (i, v) in enumerate(vectors)
    lookup[v] = i
  end
  return LatticeIsometryBacktrackCtx(grams, vectors, gram_products, norms, lookup)
end

# The one invariant the search uses:  pairing(i, j)[k] = v_i * G_k * v_j'.  An
# isometry preserves it, and this is the only reason the refinement below is
# isometry invariant.
function _lattice_backtrack_pairing(C::LatticeIsometryBacktrackCtx, i::Int, j::Int)
  w = C.vectors[j]
  values = Vector{Int}(undef, length(C.grams))
  for k in eachindex(C.grams)
    vG = C.gram_products[i][k]
    value = 0
    for t in eachindex(w)
      value += vG[t] * w[t]
    end
    values[k] = value
  end
  return values
end

# The points of the standard basis vectors.  Each has norm at most the
# enumeration bound, so each of them really is a point.
function _lattice_backtrack_basis_points(C::LatticeIsometryBacktrackCtx)
  n = size(C.grams[1], 1)
  points = Vector{Int}(undef, n)
  e = zeros(Int, n)
  for i in 1:n
    e[i] = 1
    points[i] = C.lookup[e]
    e[i] = 0
  end
  return points
end

################################################################################
#
#  Ordered partitions
#
################################################################################

# An ordered partition of the set of points, together with the invariant value
# that created each cell.  The cells are disjoint and cover all points.
struct LatticeBacktrackPartition
  cells::Vector{Vector{Int}}
  labels::Vector{Vector{Int}}
end

function _lattice_backtrack_cell(P::LatticeBacktrackPartition, point::Int)
  return findfirst(cell -> point in cell, P.cells)::Int
end

# The shape of a node.  Two nodes, one on the source and one on the target side,
# can only be matched by an isometry if their partitions agree here: an isometry
# carries the cells of the source partition onto the cells of the target
# partition in order, so corresponding cells carry the same label and have the
# same size.  This is the pruning criterion of the search.
function _lattice_backtrack_same_shape(
  P::LatticeBacktrackPartition,
  Q::LatticeBacktrackPartition,
)
  P.labels == Q.labels || return false
  return all(k -> length(P.cells[k]) == length(Q.cells[k]), eachindex(P.cells))
end

# The root of the search tree:  the points grouped by their norms under all the
# forms, the cells ordered by that norm vector.  It is the coarsest partition
# that an isometry has to respect.
function _lattice_backtrack_initial_partition(C::LatticeIsometryBacktrackCtx)
  blocks = Dict{Vector{Int}, Vector{Int}}()
  for i in eachindex(C.vectors)
    push!(get!(Vector{Int}, blocks, C.norms[i]), i)
  end
  labels = sort!(collect(keys(blocks)))
  return LatticeBacktrackPartition([blocks[label] for label in labels], labels)
end

# One step down the search tree: individualize `pivot` and refine.
#
#   individualize  the pivot is taken out of its cell and put into a cell of its
#                  own.  On its own this is not an isometry invariant operation
#                  -- it is the choice the search branches over -- but both
#                  sides do it to their respective pivot, which is precisely the
#                  assertion that the pivot is mapped to the pivot.
#   refine         every cell is split by the pairing with the pivot, and the
#                  new cells are ordered by that value.  Only points with equal
#                  pairing can still correspond to each other.
#
# Both sides run this same function, so the k-th cell on one side corresponds to
# the k-th cell on the other; the label records the parent cell and the pairing
# value, so that a mismatch of the two trees cannot hide inside equal labels.
function _lattice_backtrack_split(
  C::LatticeIsometryBacktrackCtx,
  P::LatticeBacktrackPartition,
  pivot::Int,
)
  cells = Vector{Int}[]
  labels = Vector{Int}[]
  for k in eachindex(P.cells)
    blocks = Dict{Vector{Int}, Vector{Int}}()
    for point in P.cells[k]
      value = _lattice_backtrack_pairing(C, point, pivot)
      push!(get!(Vector{Int}, blocks, value), point)
    end
    for value in sort!(collect(keys(blocks)))
      block = blocks[value]
      label = pushfirst!(copy(value), k)
      if pivot in block
        push!(cells, [pivot])
        push!(labels, label)
        block = filter(!=(pivot), block)
        isempty(block) && continue
      end
      push!(cells, block)
      push!(labels, label)
    end
  end
  return LatticeBacktrackPartition(cells, labels)
end

################################################################################
#
#  The base and the source side of the tree
#
################################################################################

# The source side of the search tree is a single path, fixed before the search
# starts.  Its nodes are obtained by individualizing basis vectors one after the
# other, and the basis vectors are taken in the order that individualizes in a
# smallest cell first.  The cell of the k-th base point is the list of its
# possible images, so its size is the branching factor at level k; in the
# language of Plesken--Souvignier this chooses the basis order by the
# fingerprint.
struct LatticeBacktrackBase
  order::Vector{Int}                            # order[k] is the basis vector
  points::Vector{Int}                           # its point in the source
  partitions::Vector{LatticeBacktrackPartition} # the nodes, one per level plus the leaf
end

function _lattice_backtrack_base(C::LatticeIsometryBacktrackCtx)
  n = size(C.grams[1], 1)
  basis_points = _lattice_backtrack_basis_points(C)
  partitions = [_lattice_backtrack_initial_partition(C)]
  order = Int[]
  points = Int[]
  remaining = collect(1:n)

  while !isempty(remaining)
    P = partitions[end]
    best = 1
    best_size = typemax(Int)
    for position in eachindex(remaining)
      size = length(P.cells[_lattice_backtrack_cell(P, basis_points[remaining[position]])])
      if size < best_size
        best = position
        best_size = size
      end
    end
    push!(order, remaining[best])
    push!(points, basis_points[remaining[best]])
    deleteat!(remaining, best)
    push!(partitions, _lattice_backtrack_split(C, P, points[end]))
  end
  return LatticeBacktrackBase(order, points, partitions)
end

################################################################################
#
#  The search
#
################################################################################

# A search maps the source, of which only the base path is ever needed, into the
# target.  For the automorphism group the two contexts coincide.
struct LatticeBacktrackSearch
  grams::Vector{Matrix{Int}}      # the forms on the source side
  base::LatticeBacktrackBase
  target::LatticeIsometryBacktrackCtx
end

function _lattice_backtrack_matrix(S::LatticeBacktrackSearch, images::Vector{Int})
  n = length(S.base.order)
  M = zeros(Int, n, n)
  for depth in 1:n
    image = S.target.vectors[images[depth]]
    for j in 1:n
      M[S.base.order[depth], j] = image[j]
    end
  end
  return M
end

# Descend from a node of the tree.  `partition` is the target node paired with
# the source node `S.base.partitions[depth]`; `images[1:depth - 1]` are the
# images of the base points chosen so far.  Returns the first isometry found
# below this node, or nothing.
function _lattice_backtrack_extend!(
  S::LatticeBacktrackSearch,
  images::Vector{Int},
  depth::Int,
  partition::LatticeBacktrackPartition,
)
  if depth > length(S.base.order)
    # The base points determine a full basis image.  Certify it.
    M = _lattice_backtrack_matrix(S, images)
    all(k -> M * S.target.grams[k] * transpose(M) == S.grams[k], eachindex(S.grams)) || return nothing
    return M
  end

  # The candidates are the points of the target cell corresponding to the cell
  # of the base point on the source side; every other point is excluded by the
  # invariants accumulated so far.
  source = S.base.partitions[depth]
  candidates = partition.cells[_lattice_backtrack_cell(source, S.base.points[depth])]

  for image in candidates
    images[depth] = image
    refined = _lattice_backtrack_split(S.target, partition, image)
    _lattice_backtrack_same_shape(S.base.partitions[depth + 1], refined) || continue
    M = _lattice_backtrack_extend!(S, images, depth + 1, refined)
    M === nothing || return M
  end
  return nothing
end

function _lattice_backtrack_isometry(G1::Matrix{Int}, G2::Matrix{Int})
  return _lattice_backtrack_isometry([G1], [G2])
end

# Find M in GL(n, Z) with M * grams2[k] * M' == grams1[k] for every k.
function _lattice_backtrack_isometry(
  grams1::Vector{Matrix{Int}},
  grams2::Vector{Matrix{Int}},
)
  n = _lattice_backtrack_check_grams(grams1)
  m = _lattice_backtrack_check_grams(grams2)
  length(grams1) == length(grams2) && n == m || return nothing
  n == 0 && return zeros(Int, 0, 0)

  # Equal determinants of the positive definite forms make an integral solution
  # of the Gram equations automatically unimodular.  Check this exactly.
  det(matrix(ZZ, grams1[1])) == det(matrix(ZZ, grams2[1])) || return nothing

  bound = maximum(grams1[1][i, i] for i in 1:n)
  source = LatticeIsometryBacktrackCtx(grams1, bound)
  target = LatticeIsometryBacktrackCtx(grams2, bound)
  base = _lattice_backtrack_base(source)
  partition = _lattice_backtrack_initial_partition(target)
  # The root shape test compares the two norm distributions.
  _lattice_backtrack_same_shape(base.partitions[1], partition) || return nothing

  S = LatticeBacktrackSearch(grams1, base, target)
  return _lattice_backtrack_extend!(S, Vector{Int}(undef, n), 1, partition)
end

################################################################################
#
#  The automorphism group
#
################################################################################

# The point that M maps `point` to.
function _lattice_backtrack_image(
  C::LatticeIsometryBacktrackCtx,
  point::Int,
  M::Matrix{Int},
)
  v = C.vectors[point]
  n = length(v)
  image = zeros(Int, n)
  for j in 1:n
    for i in 1:n
      image[j] += v[i] * M[i, j]
    end
  end
  result = get(C.lookup, image, 0)
  iszero(result) && error("an automorphism did not preserve the short vectors")
  return result
end

function _lattice_backtrack_orbit(
  C::LatticeIsometryBacktrackCtx,
  points::Vector{Int},
  generators::Vector{Matrix{Int}},
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

function _lattice_backtrack_automorphism_group(G::Matrix{Int})
  return _lattice_backtrack_automorphism_group([G])
end

# The common stabilizer of all the forms, as generators and an order.  The base
# points are the images of a basis, so only the identity fixes all of them and
# the order is the product of the orbit lengths along the stabilizer chain.
function _lattice_backtrack_automorphism_group(grams::Vector{Matrix{Int}})
  n = _lattice_backtrack_check_grams(grams)
  n == 0 && return Matrix{Int}[zeros(Int, 0, 0)], one(ZZRingElem)
  bound = maximum(grams[1][i, i] for i in 1:n)
  C = LatticeIsometryBacktrackCtx(grams, bound)
  base = _lattice_backtrack_base(C)
  S = LatticeBacktrackSearch(grams, base, C)
  generators = [Matrix{Int}[] for _ in 1:n]
  orbit_lengths = ones(Int, n)

  # Negation is always an automorphism.  It is treated like any other generator;
  # at later levels it drops out because it moves the first base point.
  negation = zeros(Int, n, n)
  for i in 1:n
    negation[i, i] = -1
  end
  push!(generators[1], negation)

  images = Vector{Int}(undef, n)
  for step in 1:n
    # Fix the first step - 1 base points.  The target node paired with the
    # source node at this level is then the source node itself.
    for i in 1:(step - 1)
      images[i] = base.points[i]
    end
    partition = base.partitions[step]
    candidates = partition.cells[_lattice_backtrack_cell(partition, base.points[step])]

    # Everything found so far that fixes the earlier base points.
    stabilizer = Matrix{Int}[]
    for level in step:n
      append!(stabilizer, generators[level])
    end

    # The second pruning criterion.  Candidates in the orbit of the base point
    # are already realized by known automorphisms.  Candidates in the orbit of a
    # candidate that has been shown to be impossible are impossible as well: if
    # g maps the failed point to c and some h mapped the base point to c, then
    # g^-1 h would map the base point to the failed point.  So one candidate per
    # orbit has to be searched, and the loop stops once all are classified.
    failed = Int[]
    while true
      good = _lattice_backtrack_orbit(C, Int[base.points[step]], stabilizer)
      bad = _lattice_backtrack_orbit(C, failed, stabilizer)
      candidate = findfirst(i -> !(i in good) && !(i in bad), candidates)
      if candidate === nothing
        orbit_lengths[step] = length(good)
        break
      end

      images[step] = candidates[candidate]
      refined = _lattice_backtrack_split(C, partition, images[step])
      M = if _lattice_backtrack_same_shape(base.partitions[step + 1], refined)
        _lattice_backtrack_extend!(S, images, step + 1, refined)
      else
        nothing
      end
      if M === nothing
        push!(failed, images[step])
      else
        push!(generators[step], M)
        push!(stabilizer, M)
      end
    end
  end

  result = Matrix{Int}[]
  for level in generators
    append!(result, level)
  end
  @assert all(M -> all(G -> M * G * transpose(M) == G, grams), result)
  return result, prod(ZZRingElem.(orbit_lengths); init = one(ZZRingElem))
end

################################################################################
#
#  Entry points for lattices
#
################################################################################

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

  reduced_gram, T, _ = _lattice_backtrack_reduce_gram(L)
  G = Matrix{Int}(reduced_gram)
  reduced_generators, group_order = _lattice_backtrack_automorphism_group(G)
  inverse_transformation = inv(T)
  generators = ZZMatrix[
    inverse_transformation * matrix(ZZ, M) * T for M in reduced_generators
  ]
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

  reduced_gram1, T1, scale1 = _lattice_backtrack_reduce_gram(L)
  reduced_gram2, T2, scale2 = _lattice_backtrack_reduce_gram(M)
  scale1 == scale2 || return false, zero_matrix(QQ, 0, 0)
  det(reduced_gram1) == det(reduced_gram2) || return false, zero_matrix(QQ, 0, 0)
  G1 = Matrix{Int}(reduced_gram1)
  G2 = Matrix{Int}(reduced_gram2)

  reduced_isometry = _lattice_backtrack_isometry(G1, G2)
  reduced_isometry === nothing && return false, zero_matrix(QQ, 0, 0)
  isometry = change_base_ring(QQ, inv(T1) * matrix(ZZ, reduced_isometry) * T2)
  @hassert :Lattice 1 isometry * gram_matrix(M) * transpose(isometry) ==
                          gram_matrix(L)
  return true, isometry
end
