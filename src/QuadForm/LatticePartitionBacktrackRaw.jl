################################################################################
#
#  Raw partition backtracking for definite lattice automorphisms
#
################################################################################
#
#  Purpose
#  -------
#
#  This file is a deliberately stripped and heavily documented reference
#  implementation. It is intended to show the essential partition-backtracking
#  algorithm without hiding it behind the performance heuristics used in
#  `IsometryBacktrack.jl`.
#
#  The implementation shares three pieces of infrastructure with the optimized
#  version:
#
#    1. Hecke's existing exact short-vector enumeration;
#    2. construction of the ordered-partition fingerprint; and
#    3. refinement of the candidate pool after fixing one more basis image.
#
#  On this experimental branch `IsometryBacktrack.jl` is intentionally not
#  included by `QuadForm.jl`. For an interactive experiment, load that file
#  first and this file second; the raw implementation depends only on the
#  shared pieces listed above.
#
#  It deliberately does *not* use the following optional refiners or engineering
#  optimizations:
#
#    * the non-orthogonality component graph and its colours;
#    * scalar-product combination tests or Bacher invariants;
#    * batched candidate filtering;
#    * switching between pool refinement and bucket search;
#    * pseudo-random choice of orbit representatives;
#    * cached permutations of the short-vector set; or
#    * narrow integer storage.
#
#  Orbit pruning and a stabilizer chain remain. They are not optional pruning
#  refiners: they are how the algorithm turns individual automorphisms into a
#  generating set and proves the order of the resulting group without
#  enumerating all its elements.
#
#
#  Mathematical setup
#  ------------------
#
#  Let G be the positive definite integral Gram matrix of a rank-n lattice. We
#  use row vectors, so an integral matrix M is an automorphism precisely when
#
#                         M * G * transpose(M) == G.                 (1)
#
#  Let V be all non-zero lattice vectors of norm at most
#
#                         B = max_i G[i, i],
#
#  stored up to sign. Every standard basis vector has norm at most B, so V
#  contains a representative of each pair {e_i, -e_i}. Since an isometry
#  preserves norms, it permutes V union -V. Consequently the image of every
#  basis vector must be a signed member of this finite set.
#
#  We encode v_j by the positive integer j and -v_j by -j. A partial search
#  state
#
#                         x[1], ..., x[d]
#
#  means that the first d basis vectors in the chosen base order have been sent
#  to those signed short vectors. It can extend to an automorphism only if all
#  already determined scalar products agree:
#
#             <x[i], x[j]> = G[per[i], per[j]]  for i, j <= d.      (2)
#
#
#  Where the partition enters
#  --------------------------
#
#  Before the recursive search, `_bt_fingerprint` repeatedly refines an ordered
#  partition of V union -V using scalar products with selected basis vectors.
#  It returns:
#
#    * `per`: an order of the basis vectors chosen to make branching small;
#    * `fp[d, per[i]]`: the required number of candidates for basis position i
#      after d - 1 earlier images have been fixed; and
#    * block boundaries used to initialize the candidate pool for every level
#      of the stabilizer chain.
#
#  During recursion, `_bt_descend!` refines the pool with the scalar product
#  against the newly fixed image. A branch is rejected if the resulting cells
#  do not have the sizes recorded in the source fingerprint. Thus the recursive
#  routine below contains only the familiar pattern
#
#      choose a candidate -> refine the partition -> recurse -> backtrack.
#
#  There is no graph involved in this raw path.
#
#
#  From individual maps to the full group
#  --------------------------------------
#
#  Let b_i = e_{per[i]} and let H_i be the subgroup fixing
#  b_1, ..., b_{i-1}. At outer step i, partition refinement gives all possible
#  images of b_i under H_i. Known generators split those candidates into
#  orbits. We search only one representative of each not-yet-known orbit:
#
#    * a successful search supplies a new generator and enlarges the known
#      orbit of b_i;
#    * a failed search rules out the representative and its entire orbit under
#      the currently known subgroup.
#
#  When no candidates remain, the orbit is complete. Orbit-stabilizer gives
#
#                |Aut(G)| = product_i |b_i ^ H_i|.                  (3)
#
#  The matrices found at step i fix b_1, ..., b_{i-1}; retaining them by level
#  therefore gives a stabilizer chain and a certificate for the product in
#  (3). Every returned matrix is additionally checked directly against (1).
#
#
#  Why the finite search is complete
#  ---------------------------------
#
#  Completeness rests on three facts:
#
#    * the short-vector set contains every possible basis image;
#    * scalar-product and partition-cell tests are necessary conditions only,
#      so they never discard an actual automorphism; and
#    * once images of all n basis vectors are chosen, they determine one and
#      only one linear map.
#
#  Hecke's exact enumerator is responsible for the first fact. This file does
#  not implement a second enumerator.
#
#
#  Reading map
#  -----------
#
#  The code below follows the mathematics in this order:
#
#    `_automorphism_group_backtrack_raw`
#      Reduce the input Gram matrix and conjugate the answer back afterwards.
#
#    `_raw_bt_automorphism_group_data`
#      Enumerate short vectors, construct the fingerprint, and run the outer
#      stabilizer-chain loop. This is the best entry point for reading the
#      algorithm itself.
#
#    `_raw_bt_extend!`
#      Perform the actual depth-first partition backtrack for one proposed
#      image of the current base point.
#
#    `_raw_bt_close!`
#      Close a set of signed short vectors under the generators already found.
#      This is ordinary orbit computation, kept explicit instead of using a
#      general permutation-group package.
#
#  A few low-level data structures are shared with the optimized implementation
#  so that this reference path stays small and, in particular, does not grow a
#  second short-vector enumerator:
#
#    `BTCtx`
#      Owns G, the enumerated short vectors, scalar-product tables, and lookup
#      storage. In this file it is constructed with the component graph turned
#      off and with `Int` coordinates.
#
#    `_bt_fingerprint`
#      Builds the source ordered partition and chooses the basis order `per`.
#
#    `BTSearch`, `_bt_init_pool_std!`, and `_bt_descend!`
#      Store, initialize, and refine the candidate partition. The raw path
#      always uses this pool-based refinement and disables its switching limits.
#
#    `_bt_matrix` and `_bt_verify`
#      Reconstruct a matrix from a leaf and verify equation (1) exactly.
#
#
#  References
#  ----------
#
#  [PS97] W. Plesken and B. Souvignier, "Computing Isometries of Lattices",
#         Journal of Symbolic Computation 24 (1997), 327--334.
#         https://doi.org/10.1006/jsco.1996.0130
#
#  [Leo91] J. S. Leon, "Permutation Group Algorithms Based on Partitions, I:
#          Theory and Algorithms", Journal of Symbolic Computation 12 (1991),
#          533--583.
#          https://doi.org/10.1016/S0747-7171(08)80103-4
#
#  [Leo97] J. S. Leon, "Partitions, Refinements, and Permutation Group
#          Computation", in Groups and Computation II, DIMACS Series 28,
#          American Mathematical Society (1997), 123--158.
#
#  [Sim71] C. C. Sims, "Computation with Permutation Groups", Proceedings of
#          SYMSAC '71, ACM (1971), 23--28.
#          https://doi.org/10.1145/800204.806264
#
#  The Magma handbook describes its lattice automorphism search as a
#  Plesken--Souvignier-style basis-image backtrack enhanced by ordered partition
#  methods:
#  https://docs.magma-maths.org/LatticesQuadraticForms/LatticesWithGroupAction/auto-isom.html
#
################################################################################

# A known lattice automorphism.
#
# `M` uses the row-image convention: row i is the image of e_i. `Mt` is cached
# only as a transposed matrix, not as a permutation of all short vectors. The
# latter cache is one of the optimizations intentionally omitted here.
struct RawBTGen{T <: Signed}
  M::Matrix{Int}
  Mt::Matrix{T}
end

# Convert the transpose once when a generator is found. Since the raw context is
# forced to use `Int`, this conversion does not introduce narrow arithmetic.
function RawBTGen(ctx::BTCtx{T}, M::Matrix{Int}) where {T <: Signed}
  n = size(M, 1)
  Mt = Matrix{T}(undef, n, n)
  @inbounds for i in 1:n, j in 1:n
    Mt[i, j] = T(M[j, i])
  end
  return RawBTGen{T}(M, Mt)
end

function _raw_bt_image_coords!(w::Vector{T}, ctx::BTCtx{T},
                               g::RawBTGen{T}, k::Int) where {T <: Signed}
  # Column k of `ctx.V` contains v_k. With row images in `g.M`, the image is
  # v_k * g.M; equivalently its transpose is g.Mt * v_k^t. The loop below uses
  # the latter form because short vectors are stored as columns.
  fill!(w, T(0))
  @inbounds for j in 1:ctx.n
    c = ctx.V[j, k]
    if !iszero(c)
      @simd for i in 1:ctx.n
        w[i] += c * g.Mt[i, j]
      end
    end
  end
  return w
end

@inline function _raw_bt_apply(ctx::BTCtx{T}, g::RawBTGen{T},
                               p::Int) where {T <: Signed}
  # Strip the sign, apply the matrix to the stored representative, and look the
  # resulting vector up in the short-vector hash table. `_bt_find` returns a
  # signed index, so the sign stripped from `p` is restored at the end.
  #
  # The optimized implementation changes to a cached permutation after enough
  # applications. This reference implementation always performs the matrix
  # action and lookup explicitly.
  k = abs(p)
  w = _raw_bt_image_coords!(ctx.wtmp, ctx, g, k)
  q = _bt_find(ctx, w)
  iszero(q) && throw(BTError("image of a short vector is not short"))
  return p < 0 ? -q : q
end

# An incrementally maintained orbit of signed short-vector indices.
#
# A generator may be appended after an orbit has already been partially closed.
# `cursor[i]` records how many existing orbit points have been acted on by the
# i-th generator. This permits `_raw_bt_close!` to resume instead of rebuilding
# the orbit from scratch.
#
# `seen[j]` is a two-bit set: bit 0 records +j and bit 1 records -j. At the first
# stabilizer level the central automorphism -I is known in advance, so the orbit
# is closed under negation and both bits can be marked together.
mutable struct RawBTOrbit
  points::Vector{Int}
  seen::Vector{UInt8}
  cursor::Vector{Int}
  closed_under_negation::Bool
end

# Construct a non-empty orbit whose first point is `point`.
function RawBTOrbit(nv::Int, point::Int, closed_under_negation::Bool = false)
  seen = zeros(UInt8, nv)
  k = abs(point)
  seen[k] = closed_under_negation ? 0x03 : (point < 0 ? 0x02 : 0x01)
  return RawBTOrbit(Int[point], seen, Int[], closed_under_negation)
end

# Construct an empty set of points. This is used to collect images which have
# been proved impossible.
RawBTOrbit(nv::Int, closed_under_negation::Bool) =
  RawBTOrbit(Int[], zeros(UInt8, nv), Int[], closed_under_negation)

@inline function _raw_bt_orbit_size(orbit::RawBTOrbit)
  # When negation is implicit, `points` stores only one representative of each
  # pair {p, -p}; the mathematical orbit is twice as large.
  return orbit.closed_under_negation ? 2 * length(orbit.points) :
                                      length(orbit.points)
end

@inline function _raw_bt_seen(orbit::RawBTOrbit, point::Int)
  # Positive and negative representatives share one byte but occupy different
  # bits. This avoids allocating a table indexed from -nv to nv.
  mask = point < 0 ? 0x02 : 0x01
  return orbit.seen[abs(point)] & mask != 0
end

@inline function _raw_bt_mark!(orbit::RawBTOrbit, point::Int)
  orbit.seen[abs(point)] |= orbit.closed_under_negation ? 0x03 :
                           (point < 0 ? 0x02 : 0x01)
  return nothing
end

function _raw_bt_add!(orbit::RawBTOrbit, point::Int)
  # Return whether `point` was new; callers do not currently need the result,
  # but the convention makes the set operation explicit.
  _raw_bt_seen(orbit, point) && return false
  _raw_bt_mark!(orbit, point)
  push!(orbit.points, point)
  return true
end

function _raw_bt_close!(orbit::RawBTOrbit, ctx::BTCtx{T},
                        generators::Vector{RawBTGen{T}},
                        target::Int = typemax(Int)) where {T <: Signed}
  # Breadth-first orbit closure, interleaved over generators. If a new generator
  # was appended since the preceding call, its cursor starts at zero and it is
  # applied to every known point. Newly discovered points are subsequently
  # processed by all generators.
  #
  # The optional target is known from the partition fingerprint. Once that many
  # points have been found, the orbit cannot grow further without contradicting
  # the fingerprint, so closure may stop early. This is a logical consequence
  # of the partition data, rather than an additional invariant.
  ngens = length(generators)
  iszero(ngens) && return orbit
  while length(orbit.cursor) < ngens
    push!(orbit.cursor, 0)
  end
  _raw_bt_orbit_size(orbit) >= target && return orbit

  @inbounds while true
    moved = false
    for i in 1:ngens
      if orbit.cursor[i] < length(orbit.points)
        orbit.cursor[i] += 1
        moved = true
        point = orbit.points[orbit.cursor[i]]
        image = _raw_bt_apply(ctx, generators[i], point)
        if !_raw_bt_seen(orbit, image)
          _raw_bt_mark!(orbit, image)
          push!(orbit.points, image)
          _raw_bt_orbit_size(orbit) >= target && return orbit
        end
      end
    end
    moved || return orbit
  end
end

function _raw_bt_orbit(ctx::BTCtx{T}, generators::Vector{RawBTGen{T}},
                       point::Int, target::Int = typemax(Int);
                       closed_under_negation::Bool = false) where {T <: Signed}
  # Convenience wrapper for constructing and closing a fresh orbit.
  orbit = RawBTOrbit(ctx.nv, point, closed_under_negation)
  return _raw_bt_close!(orbit, ctx, generators, target)
end

function _raw_bt_remove!(points::Vector{Int}, orbit::RawBTOrbit)
  # Stable in-place set difference. The order is retained so the raw algorithm
  # deterministically tries the first surviving representative.
  keep = 0
  @inbounds for point in points
    if !_raw_bt_seen(orbit, point)
      keep += 1
      points[keep] = point
    end
  end
  resize!(points, keep)
  return points
end

# Extend a partial basis image using only the partition pool refinement.
#
# On entry, images through `depth` have been fixed and `search.cand[depth + 1]`
# is the corresponding partition cell. For every candidate we individualize
# that point, let `_bt_descend!` refine the remaining cells by its scalar
# products, and recurse. There is intentionally no secondary invariant between
# refinement and recursion.
#
# Returning `true` means that `search.x[1:n]` now describes a complete basis
# image. Returning `false` means that every candidate below this node failed.
function _raw_bt_extend!(search::BTSearch, depth::Int)
  depth == search.n && return true
  level = depth + 1
  @inbounds for image in search.cand[level]
    search.x[level] = image
    level == search.n && return true
    if _bt_descend!(search, level) && _raw_bt_extend!(search, level)
      return true
    end
  end
  return false
end

@doc raw"""
    _raw_bt_automorphism_group_data(G::Matrix{Int}; verbose::Bool = false)

Run the stripped partition-backtracking algorithm on a positive definite,
integral Gram matrix `G` and return

    generators, order, orbit_lengths, nodes

The matrices use the row-image convention `M*G*transpose(M) == G`.
`orbit_lengths` contains the factors in the orbit-stabilizer product, and
`nodes` counts partition-refinement nodes visited by the recursive searches.

This low-level function assumes that `G` has already been reduced and that its
entries fit in `Int`; use `_automorphism_group_backtrack_raw` for a `ZZLat`.
"""
function _raw_bt_automorphism_group_data(G::Matrix{Int}; verbose::Bool = false)
  # Phase 1: construct the finite support and its ordered partition.
  #
  # A zero component budget disables the auxiliary non-orthogonality graph.
  # `force = Int` also disables the optimized implementation's narrow-storage
  # choice. Thus the only colours initially present are the vector norms used by
  # the ordered partition itself.
  ctx = BTCtx(G; comp_budget = 0, force = Int)
  fingerprint = _bt_fingerprint(ctx)
  n = ctx.n
  nv = ctx.nv

  # `BTSearch` is reused solely as storage for the partition pool. The following
  # settings make its behavior unambiguous:
  #
  #   * `usepool = true`: always refine the ordered pool; never use buckets;
  #   * unlimited node/work bounds: never switch to combination tests; and
  #   * no basis colours: the component graph was disabled above.
  search = BTSearch(ctx, fingerprint.per, G, fingerprint.fp, fingerprint.fpd)
  search.usepool = true
  search.nodelimit = typemax(Int)
  search.worklimit = typemax(Int)

  # Signed short-vector indices of the ordered basis itself. At stabilizer level
  # `step`, the earlier entries are fixed and this entry is the base point whose
  # orbit is being completed.
  # Convert the signed indices owned by the shared context to ordinary `Int`
  # immediately. The raw algorithm deliberately exposes no narrow integer
  # representation in its own state.
  standard = Int[ctx.bidx[fingerprint.per[i]] for i in 1:n]

  # `_bt_init_pool_std!` writes one bit mask for +v and one for -v. Bit i says
  # that this signed vector remains a possible image at basis level i. These
  # buffers are allocated once and reused at every stabilizer level.
  words = search.nw
  positive_masks = zeros(UInt64, nv * words)
  negative_masks = zeros(UInt64, nv * words)
  # `generators[i]` contains automorphisms first discovered at stabilizer level
  # i. Every such matrix fixes the preceding base points. The subgroup acting at
  # level i is therefore generated by the union of generators[i:n].
  T = eltype(ctx.V)
  generators = [RawBTGen{T}[] for _ in 1:n]
  orders = ones(Int, n)

  # Phase 2: build a stabilizer chain from left to right.
  for step in 1:n
    # A fingerprint entry of one says that the already fixed images determine
    # this basis image uniquely. Its orbit contributes the factor one and no
    # generator search is necessary.
    isone(fingerprint.fpd[step]) && continue

    # Known generators at levels >= step fix the first step - 1 base points.
    stabilizer = RawBTGen{T}[]
    for i in step:n
      append!(stabilizer, generators[i])
    end
    for i in 1:(step - 1)
      search.x[i] = standard[i]
    end

    # Initialize the partition at the node where the earlier base points map to
    # themselves. The resulting candidate cell is exactly the set of possible
    # images of the current base point allowed by the fingerprint.
    search.step = step
    search.bktfor = 0
    _bt_init_pool_std!(search, fingerprint, step, ctx,
                       positive_masks, negative_masks)
    # The experimental shared search structure stores these indices in its
    # private representation. Convert at the boundary so every raw orbit and
    # candidate list uses `Int`.
    remaining = Int.(search.cand[step])
    candidate_count = length(remaining)

    # Images already reached by the known subgroup need not be searched. At the
    # first level, -I is known a priori, so p and -p belong to the same orbit
    # even though -I is appended to the returned generators only at the end.
    orbit = _raw_bt_orbit(ctx, stabilizer, standard[step], candidate_count;
                          closed_under_negation = step == 1)
    orders[step] = _raw_bt_orbit_size(orbit)
    _raw_bt_remove!(remaining, orbit)

    # A failed representative proves that no automorphism in the desired group
    # maps the base point to it. Applying a known automorphism to that point
    # preserves failure, so failed representatives are also maintained as a
    # union of complete stabilizer orbits.
    impossible = RawBTOrbit(ctx.nv, step == 1)

    while !isempty(remaining)
      # No randomized selection: the raw version always takes the first
      # representative which is in neither a known-success nor known-failure
      # orbit.
      image = first(remaining)
      search.x[step] = image

      # Search for one complete automorphism extending b_step -> image. We need
      # only one: if it exists, it is a new group generator; if it does not,
      # this entire stabilizer orbit is impossible.
      found = step == n ||
              (_bt_descend!(search, step) && _raw_bt_extend!(search, step))

      if found
        # A full list of basis images is the row-image matrix of the candidate
        # automorphism. Verify it exactly before using it for group operations.
        matrix = _bt_matrix(search)
        _bt_verify(matrix, G, G) ||
          throw(BTError("internal error: produced matrix is not an automorphism"))
        generator = RawBTGen(ctx, matrix)
        push!(generators[step], generator)
        push!(stabilizer, generator)

        # The new generator can merge several formerly distinct success orbits.
        # It can also merge failure orbits, so both closures must be resumed.
        _raw_bt_close!(orbit, ctx, stabilizer, candidate_count)
        orders[step] = _raw_bt_orbit_size(orbit)
        _raw_bt_remove!(remaining, orbit)
        if !isempty(impossible.points)
          _raw_bt_close!(impossible, ctx, stabilizer)
          _raw_bt_remove!(remaining, impossible)
        end
      else
        # Close the failed point under the subgroup currently known. None of
        # these images can be the image of the base point in an automorphism.
        _raw_bt_add!(impossible, image)
        _raw_bt_close!(impossible, ctx, stabilizer)
        _raw_bt_remove!(remaining, impossible)
      end
    end

    verbose && println("raw backtrack step ", step, ": order ", orders[step],
                       ", generators ", length(generators[step]),
                       ", nodes ", search.nodes)
  end

  # Phase 3: finish and certify the stabilizer chain.
  #
  # Negation is central and always preserves G. It was treated implicitly in
  # the first orbit, so it must be present explicitly in the generators for the
  # product of orbit lengths to describe the returned group.
  minus_identity = zeros(Int, n, n)
  for i in 1:n
    minus_identity[i, i] = -1
  end
  _bt_verify(minus_identity, G, G) ||
    throw(BTError("internal error: -1 is not an automorphism"))
  push!(generators[1], RawBTGen(ctx, minus_identity))

  # Check the defining invariant of the level assignment: generators found at
  # level i must fix all earlier base points. Together with exact verification
  # of every matrix, this makes the orbit-stabilizer product auditable.
  for i in 1:n
    for generator in generators[i]
      for j in 1:(i - 1)
        _raw_bt_apply(ctx, generator, standard[j]) == standard[j] ||
          throw(BTError("internal error: broken stabilizer chain"))
      end
    end
  end

  result = Matrix{Int}[]
  for level_generators in generators
    append!(result, (generator.M for generator in level_generators))
  end
  # Use arbitrary precision for the product: automorphism group orders easily
  # exceed the native integer range (the Leech lattice is a standard example).
  order = prod(ZZRingElem.(orders); init = one(ZZRingElem))
  return result, order, orders, search.nodes
end

function _raw_bt_automorphism_group(G::Matrix{Int}; verbose::Bool = false)
  # Public-to-this-file low-level convenience interface: most callers need only
  # the generators and total order, not the chain factors or diagnostic count.
  result = _raw_bt_automorphism_group_data(G; verbose)
  return result[1], result[2]
end

@doc raw"""
    _automorphism_group_backtrack_raw(L::ZZLat) -> Vector{ZZMatrix}, ZZRingElem

Compute the automorphism group of a definite integer lattice using the stripped
partition-backtracking reference implementation. Returns nothing when its
machine-integer arithmetic cannot safely represent the input, allowing the
caller to use the general implementation.

The lattice is first rescaled to a primitive integral Gram matrix and LLL
reduced. If `T*G*transpose(T)` is the reduced Gram matrix, an automorphism `g`
found in the reduced basis is returned in the original basis as
`inv(T)*g*T`.
"""
function _automorphism_group_backtrack_raw(L::ZZLat)
  @req is_definite(L) "Lattice must be definite"
  n = rank(L)
  if n == 0
    return ZZMatrix[identity_matrix(ZZ, 0)], one(ZZRingElem)
  elseif n == 1
    return ZZMatrix[-identity_matrix(ZZ, 1)], ZZRingElem(2)
  end

  # Reduction makes the enumerated short-vector coordinates smaller and gives
  # the partition search a substantially better basis order. It is a change of
  # coordinates only, so it does not change the abstract automorphism group.
  reduced = _bt_reduce_gram(L)
  reduced === nothing && return nothing
  G, transform = reduced[1], reduced[2]
  local generators, order
  try
    generators, order = _raw_bt_automorphism_group(G)
  catch e
    # The optional algorithm is deliberately restricted to safe machine-integer
    # arithmetic. `nothing` asks the caller to fall back to Hecke's general
    # Plesken--Souvignier implementation rather than compromising exactness.
    e isa BTOverflow && return nothing
    rethrow(e)
  end

  # Conjugate each row-image matrix from the reduced basis back to the basis of
  # `L`, then check the original rational Gram matrix at assertion level 1.
  inverse_transform = inv(transform)
  result = ZZMatrix[inverse_transform * matrix(ZZ, generator) * transform
                    for generator in generators]
  @hassert :Lattice 1 all(g -> change_base_ring(QQ, g) * gram_matrix(L) *
                          transpose(change_base_ring(QQ, g)) == gram_matrix(L),
                          result)
  return result, order
end
