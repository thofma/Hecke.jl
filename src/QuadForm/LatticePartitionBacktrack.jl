################################################################################
#
#  Partition backtracking for automorphisms of definite lattices
#
################################################################################
#
#  Purpose
#  -------
#
#  This file is a small, self-contained and heavily documented reference
#  implementation of partition backtracking for definite integer lattices. It
#  favours readability over speed: there are no optional refiners, no caches
#  and no narrow integer types. It is meant as a seed which can be reviewed
#  line by line and then extended.
#
#  Everything lives in the submodule `Hecke.LatticePartitionBacktrack`, so the
#  short names used below (`Search`, `Orbit`, `refine!`, ...) cannot clash with
#  anything else in Hecke. The only pieces of Hecke used are the exact
#  short-vector enumeration and LLL reduction of Gram matrices.
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
#  We encode v_j by the positive integer j and -v_j by -j, and call such a
#  signed index a *point*. Let b_i = e_{order[i]} be the basis in the order
#  chosen by the fingerprint (see below). A partial search state
#
#                         image[1], ..., image[d]
#
#  means that b_1, ..., b_d are sent to those points. It can extend to an
#  automorphism only if all already determined scalar products agree:
#
#             <image[i], image[j]> = <b_i, b_j>  for i, j <= d.      (2)
#
#
#  Where the partition enters
#  --------------------------
#
#  For every position k the search maintains a *cell*: the set of points which
#  are still possible images of b_k. Initially this is the set of points of
#  norm <b_k, b_k>. Whenever image[d] is fixed, `refine!` shrinks the cell of
#  every later position k > d to the points p with
#
#                         <p, image[d]> = <b_k, b_d>.
#
#  The identity map is an automorphism. Running the same refinement along the
#  identity therefore tells us how large every cell must be at every depth;
#  these numbers form the `Fingerprint`. A branch whose cell sizes differ from
#  the fingerprint cannot lead to an automorphism and is abandoned at once.
#  The fingerprint also fixes the base order: greedily, the next base vector
#  is the one whose cell is currently smallest.
#
#  Cells are stored as bit vectors.
#
#  Thus the recursion in `extend!` is the familiar pattern
#
#      choose a point of the cell -> refine the partition -> recurse.
#
#
#  From individual maps to the full group
#  --------------------------------------
#
#  Let H_i be the subgroup fixing b_1, ..., b_{i-1}. At outer step i the cell
#  of position i consists of all possible images of b_i under H_i. Known
#  generators split those candidates into orbits. We search only one
#  representative of each not-yet-known orbit:
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
#    * the short-vector set contains every possible basis image;
#    * scalar-product and cell-size tests are necessary conditions only, so
#      they never discard an actual automorphism; and
#    * once images of all n basis vectors are chosen, they determine one and
#      only one linear map.
#
#
#  Reading map
#  -----------
#
#    `ShortVectors`      the finite set V union -V the group acts on
#    `Fingerprint`       base order and expected cell sizes (source side)
#    `Search`, `refine!`, `extend!`
#                        the depth-first partition backtrack (target side)
#    `Generator`, `Orbit`, `close!`
#                        explicit orbit computation on points
#    `stabilizer_chain`  the outer loop; best entry point for the algorithm
#    `automorphism_group`
#                        interface for `ZZLat`: reduce, run, conjugate back
#
#
#  Extension points
#  ----------------
#
#  The design keeps the *source* (a `Fingerprint`: base order, Gram matrix in
#  base order, expected cell sizes) apart from the *target* (a `ShortVectors`
#  set in which images are searched). `Search` only ever combines the two.
#
#    * Isometry testing: build the fingerprint from one lattice and the
#      `ShortVectors` from the other, then call `extend!(search, 0)`.
#    * Stronger refiners (vector sums, Bacher polynomials, ...): add the test
#      to `refine!` and the matching expected value to `Fingerprint`.
#    * Canonical forms: the sequence of cell sizes produced by `refine!` is an
#      isometry invariant of a search node. A canonizer does not compare it
#      to a fixed fingerprint but orders the nodes by it, explores all nodes
#      with the best invariant, and compares the Gram matrices found at the
#      leaves (`image_matrix`); automorphisms found on the way prune via
#      `Orbit` exactly as in `stabilizer_chain`. For this the base order must
#      be chosen from invariant data only, which the greedy rule in
#      `Fingerprint` is not yet (ties are broken by basis index).
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
################################################################################

module LatticePartitionBacktrack

import ..Hecke: @req, @hassert, @vprintln, ZZ, QQ, ZZLat, ZZMatrix,
                ZZRingElem, change_base_ring, content, diagonal, divexact,
                fits, gram_matrix, identity_matrix, is_definite,
                lll_gram_with_transform, matrix, rank, __short_vectors

################################################################################
#
#  The finite set of short vectors
#
################################################################################

# The set V union -V of all non-zero vectors of norm at most `max_i G[i, i]`.
#
# Column j of `vectors` is v_j; only one of v_j, -v_j is stored. A *point* is a
# signed index: p > 0 stands for v_p and p < 0 for -v_{-p}.
#
# A set of points is stored as a `BitVector` of length 2 * nv, in which the
# point p > 0 has the index p and the point -p has the index nv + p.
struct ShortVectors
  gram::Matrix{Int}               # G
  vectors::Matrix{Int}            # n x nv, column j is v_j
  gram_vectors::Matrix{Int}       # G * vectors, to speed up scalar products
  norms::Vector{Int}              # norms[j] = <v_j, v_j>
  index::Dict{Vector{Int}, Int}   # v_j => j
  basis::Vector{Int}              # basis[i] is the point equal to e_i
end

dim(S::ShortVectors) = size(S.vectors, 1)

number_of_vectors(S::ShortVectors) = size(S.vectors, 2)

# Conversion between points and their indices in a set of points.
bit_index(S::ShortVectors, p::Int) = p > 0 ? p : number_of_vectors(S) - p

function point(S::ShortVectors, i::Int)
  nv = number_of_vectors(S)
  return i <= nv ? i : nv - i
end

# The elements of a set of points.
points(S::ShortVectors, set::BitVector) = Int[point(S, i) for i in findall(set)]

# All arithmetic is done in `Int`. The scalar products themselves are bounded
# by the norm bound (Cauchy--Schwarz), but intermediate sums need not be, so
# we bound them once and for all here. An `OverflowError` tells the caller to
# use a different algorithm.
function ShortVectors(G::Matrix{Int})
  n = size(G, 1)
  bound = maximum(G[i, i] for i in 1:n)
  list = __short_vectors(matrix(ZZ, G), nothing, bound)
  nv = length(list)
  vectors = Matrix{Int}(undef, n, nv)
  norms = Vector{Int}(undef, nv)
  index = Dict{Vector{Int}, Int}()
  for (j, (v, norm)) in enumerate(list)
    vectors[:, j] = v
    norms[j] = norm
    index[v] = j
  end

  max_entry = maximum(abs, vectors; init = 0)
  max_gram = maximum(abs, G; init = 0)
  limit = typemax(Int)
  # |entries of G * v| <= n * max_gram * max_entry, and one more factor of
  # n * max_entry bounds every partial sum of a scalar product or of a matrix
  # times vector product.
  widemul(n, max_gram) * max_entry * widemul(n, max_entry) < limit ||
    throw(OverflowError("lattice too large for machine integers"))

  S = ShortVectors(G, vectors, G * vectors, norms, index, zeros(Int, n))
  e = zeros(Int, n)
  for i in 1:n
    e[i] = 1
    S.basis[i] = find_point(S, e)
    @assert S.basis[i] != 0
    e[i] = 0
  end
  return S
end

# The point with coordinate vector `w`, or 0 if `w` is not a short vector.
function find_point(S::ShortVectors, w::Vector{Int})
  j = get(S.index, w, 0)
  j != 0 && return j
  return -get(S.index, -w, 0)
end

# The coordinate vector of the point `p`.
function coordinates(S::ShortVectors, p::Int)
  v = S.vectors[:, abs(p)]
  return p < 0 ? -v : v
end

# The scalar product <p, q> of two points.
function scalar_product(S::ShortVectors, p::Int, q::Int)
  j, k = abs(p), abs(q)
  s = 0
  @inbounds @simd for i in 1:dim(S)
    s += S.vectors[i, j] * S.gram_vectors[i, k]
  end
  return (p < 0) == (q < 0) ? s : -s
end

# Set `refined` to {p in cell : <p, x> = c} and return it. The two sets may
# be the same object.
function refine_cell!(refined::BitVector, S::ShortVectors, cell::BitVector,
                      x::Int, c::Int)
  i = findfirst(cell)
  while i !== nothing
    refined[i] = scalar_product(S, point(S, i), x) == c
    i = findnext(cell, i + 1)
  end
  refined === cell || map!(&, refined, refined, cell)
  return refined
end

# The set of all points of a given norm.
function points_of_norm(S::ShortVectors, norm::Int)
  set = S.norms .== norm
  return vcat(set, set)
end

################################################################################
#
#  Fingerprint
#
################################################################################

# The source side of a search: what an image of the basis has to look like.
#
#   `order`       the base; b_i = e_{order[i]}
#   `products`    products[k, d] = <b_k, b_d>
#   `cell_sizes`  for d <= k, cell_sizes[d, k] is the size of the cell of
#                 position k after b_1, ..., b_{d-1} have been fixed
#
# In particular `cell_sizes[d, d]` is the number of candidates for the image
# of b_d once the earlier images are known.
struct Fingerprint
  order::Vector{Int}
  products::Matrix{Int}
  cell_sizes::Matrix{Int}
end

# Choose the base greedily: the next base vector is the one with the smallest
# cell, which keeps the branching of the search small.
function base_order(S::ShortVectors)
  n = dim(S)
  cells = [points_of_norm(S, S.gram[i, i]) for i in 1:n]
  order = Int[]
  remaining = collect(1:n)
  for d in 1:n
    _, position = findmin(i -> count(cells[i]), remaining)
    b = popat!(remaining, position)
    push!(order, b)
    for i in remaining
      refine_cell!(cells[i], S, cells[i], S.basis[b], S.gram[i, b])
    end
  end
  return order
end

# Compute the fingerprint by refining along the identity map.
function Fingerprint(S::ShortVectors)
  n = dim(S)
  order = base_order(S)
  base = S.basis[order]
  products = S.gram[order, order]
  cell_sizes = zeros(Int, n, n)
  cells = [points_of_norm(S, products[k, k]) for k in 1:n]
  for d in 1:n
    cell_sizes[d, d:n] = count.(cells[d:n])
    for k in (d + 1):n
      refine_cell!(cells[k], S, cells[k], base[d], products[k, d])
    end
  end
  return Fingerprint(order, products, cell_sizes)
end

################################################################################
#
#  The backtrack search
#
################################################################################

# State of one depth-first search for an image of the base.
#
#   `image[d]`     the point b_d is currently sent to
#   `cells[d][k]`  for d <= k, the set of possible images of b_k once
#                  image[1], ..., image[d-1] are fixed
#   `nodes`        number of search nodes visited (diagnostics only)
#
# The cells of all depths are kept, so backtracking needs no undo step.
mutable struct Search
  source::Fingerprint
  target::ShortVectors
  image::Vector{Int}
  cells::Vector{Vector{BitVector}}
  nodes::Int
end

function Search(source::Fingerprint, target::ShortVectors)
  n = dim(target)
  cells = [Vector{BitVector}(undef, n) for _ in 1:n]
  for d in 1:n, k in d:n
    cells[d][k] = d == 1 ? points_of_norm(target, source.products[k, k]) :
                           falses(2 * number_of_vectors(target))
  end
  return Search(source, target, zeros(Int, n), cells, 0)
end

# Individualize `image[depth]` and refine the cells of all later positions.
#
# Returns `false` as soon as a cell does not have the size prescribed by the
# fingerprint; then no isometry extends `image[1:depth]`.
function refine!(search::Search, depth::Int)
  search.nodes += 1
  source, target = search.source, search.target
  x = search.image[depth]
  for k in (depth + 1):dim(target)
    refined = refine_cell!(search.cells[depth + 1][k], target,
                           search.cells[depth][k], x,
                           source.products[k, depth])
    count(refined) == source.cell_sizes[depth + 1, k] || return false
  end
  return true
end

# Extend a partial image to a complete one.
#
# On entry `image[1:depth]` is fixed and has been refined. Returns `true` if
# `image` now describes an isometry, and `false` if every extension failed.
function extend!(search::Search, depth::Int)
  n = dim(search.target)
  depth == n && return true
  level = depth + 1
  for p in points(search.target, search.cells[level][level])
    search.image[level] = p
    refine!(search, level) && extend!(search, level) && return true
  end
  return false
end

# The matrix of the map described by a complete `image`; row i is the image
# of e_i.
function image_matrix(search::Search)
  n = dim(search.target)
  M = Matrix{Int}(undef, n, n)
  for i in 1:n
    M[search.source.order[i], :] = coordinates(search.target, search.image[i])
  end
  return M
end

# Equation (1), generalised to an isometry from `source` to `target`.
is_isometry(M::Matrix{Int}, source::Matrix{Int}, target::Matrix{Int}) =
  M * target * transpose(M) == source

################################################################################
#
#  Generators and orbits
#
################################################################################

# A known automorphism, as a matrix whose row i is the image of e_i.
struct Generator
  matrix::Matrix{Int}
end

# The image of the point `p` under `g`.
function apply(S::ShortVectors, g::Generator, p::Int)
  w = transpose(g.matrix) * view(S.vectors, :, abs(p))    # v * M as a column
  q = find_point(S, w)
  q == 0 && error("image of a short vector is not short")
  return p < 0 ? -q : q
end

# An incrementally maintained orbit of points.
#
# A generator may be appended after an orbit has already been partially
# closed. `cursor[i]` records how many orbit points have been acted on by the
# i-th generator, so that `close!` can resume instead of starting again.
#
# `seen[j]` is a two-bit set: bit 0 records +j and bit 1 records -j. If
# `closed_under_negation` is set, the orbit is that of a group containing -1:
# only one of p, -p is stored in `points`, and both bits are marked together.
mutable struct Orbit
  points::Vector{Int}
  seen::Vector{UInt8}
  cursor::Vector{Int}
  closed_under_negation::Bool
end

# An empty union of orbits; `push!` adds starting points.
Orbit(S::ShortVectors; closed_under_negation::Bool = false) =
  Orbit(Int[], zeros(UInt8, number_of_vectors(S)), Int[],
        closed_under_negation)

Base.length(orbit::Orbit) =
  orbit.closed_under_negation ? 2 * length(orbit.points) : length(orbit.points)

Base.isempty(orbit::Orbit) = isempty(orbit.points)

Base.in(p::Int, orbit::Orbit) =
  orbit.seen[abs(p)] & (p < 0 ? 0x02 : 0x01) != 0

function Base.push!(orbit::Orbit, p::Int)
  p in orbit && return orbit
  orbit.seen[abs(p)] |= orbit.closed_under_negation ? 0x03 :
                        (p < 0 ? 0x02 : 0x01)
  push!(orbit.points, p)
  return orbit
end

# Close `orbit` under `generators` (breadth first). The list of generators may
# only grow between calls. Closure stops early once the orbit has `target`
# points; the fingerprint bounds the size of an orbit, so nothing is lost.
function close!(orbit::Orbit, S::ShortVectors, generators::Vector{Generator};
                target::Int = typemax(Int))
  while length(orbit.cursor) < length(generators)
    push!(orbit.cursor, 0)
  end
  progress = true
  while progress && length(orbit) < target
    progress = false
    for (i, g) in enumerate(generators)
      orbit.cursor[i] < length(orbit.points) || continue
      orbit.cursor[i] += 1
      progress = true
      push!(orbit, apply(S, g, orbit.points[orbit.cursor[i]]))
    end
  end
  return orbit
end


################################################################################
#
#  Stabilizer chain
#
################################################################################

@doc raw"""
    stabilizer_chain(G::Matrix{Int})

Given a positive definite integral Gram matrix `G`, compute its automorphism
group by partition backtracking. Return a named tuple with entries

- `generators`: matrices `M` with `M*G*transpose(M) == G` generating the group;
- `order`: the order of the group;
- `orbit_lengths`: the factors of the orbit-stabilizer product for `order`;
- `nodes`: the number of search nodes visited.

Throws an `OverflowError` if the computation does not fit into machine
integers. For good performance `G` should be LLL reduced.
"""
function stabilizer_chain(G::Matrix{Int})
  # Phase 1: the finite set acted upon and the fingerprint of the identity.
  S = ShortVectors(G)
  fingerprint = Fingerprint(S)
  search = Search(fingerprint, S)
  n = dim(S)

  # The base as points: at level `step` the entries before `step` are fixed
  # and `base[step]` is the point whose orbit is being completed.
  base = S.basis[fingerprint.order]

  # `generators[i]` holds the automorphisms first found at level i. Each of
  # them fixes base[1:i-1], so the stabilizer of base[1:i-1] is generated by
  # the union of generators[i:n].
  generators = [Generator[] for _ in 1:n]
  orbit_lengths = ones(Int, n)

  # Phase 2: build the stabilizer chain from left to right.
  for step in 1:n
    # Move the search to the node where base[1:step-1] is mapped to itself.
    # Its cell at position `step` is the set of possible images of base[step].
    if step > 1
      search.image[step - 1] = base[step - 1]
      refine!(search, step - 1) || error("identity violates the fingerprint")
    end
    candidates = points(S, search.cells[step][step])

    # A cell of size one: the earlier images determine this one.
    length(candidates) == 1 && continue

    stabilizer = reduce(vcat, generators[step:n])

    # Images already reached by the known subgroup need not be searched. At
    # the first level -1 is known a priori, so p and -p lie in the same orbit
    # even though -1 is added to the generators only at the end.
    negation = step == 1
    orbit = push!(Orbit(S; closed_under_negation = negation), base[step])
    close!(orbit, S, stabilizer; target = length(candidates))

    # Points proven not to be an image of base[step]. This is a union of
    # orbits of the known subgroup: if no automorphism fixing base[1:step-1]
    # maps base[step] to p, then the same holds for every point in the orbit
    # of p.
    impossible = Orbit(S; closed_under_negation = negation)

    remaining = filter(p -> !(p in orbit), candidates)
    while !isempty(remaining)
      # One automorphism base[step] -> p is enough: if it exists it is a new
      # generator, if not the whole orbit of p is impossible.
      p = first(remaining)
      search.image[step] = p
      if refine!(search, step) && extend!(search, step)
        M = image_matrix(search)
        is_isometry(M, G, G) || error("search returned a non-isometry")
        g = Generator(M)
        push!(generators[step], g)
        push!(stabilizer, g)
      else
        push!(impossible, p)
      end
      # A new generator can merge orbits of either kind, so close both.
      close!(orbit, S, stabilizer; target = length(candidates))
      close!(impossible, S, stabilizer)
      filter!(q -> !(q in orbit) && !(q in impossible), remaining)
    end
    orbit_lengths[step] = length(orbit)

    @vprintln :Lattice 2 "partition backtrack step $step: orbit length " *
      "$(orbit_lengths[step]), generators $(length(generators[step])), " *
      "nodes $(search.nodes)"
  end

  # Phase 3: finish and certify the chain.
  #
  # Negation was treated implicitly in the first orbit, so it has to be among
  # the generators for the product of orbit lengths to be the group order.
  if n > 0
    push!(generators[1], Generator(-Matrix{Int}(identity_matrix(ZZ, n))))
  end

  # Generators found at level i must fix all earlier base points. Together
  # with the exact check of every matrix this makes equation (3) auditable.
  for i in 1:n, g in generators[i], j in 1:(i - 1)
    apply(S, g, base[j]) == base[j] || error("broken stabilizer chain")
  end

  return (generators = Matrix{Int}[g.matrix for level in generators
                                   for g in level],
          order = prod(ZZRingElem.(orbit_lengths); init = one(ZZRingElem)),
          orbit_lengths = orbit_lengths,
          nodes = search.nodes)
end

################################################################################
#
#  Interface for lattices
#
################################################################################

@doc raw"""
    automorphism_group(L::ZZLat) -> Vector{ZZMatrix}, ZZRingElem

Given a definite lattice `L`, return generators and the order of its
automorphism group, computed by partition backtracking. The generators act on
the coordinates with respect to the basis of `L`, that is, they satisfy
`g*G*transpose(g) == G` for the Gram matrix `G` of `L`.

Return `nothing` if the computation does not fit into machine integers.
"""
function automorphism_group(L::ZZLat)
  @req is_definite(L) "Lattice must be definite"
  n = rank(L)
  n == 0 && return ZZMatrix[identity_matrix(ZZ, 0)], one(ZZRingElem)

  # Rescale to a primitive positive definite integral form and LLL reduce.
  # Neither changes the automorphism group; reduction makes the set of short
  # vectors small. With T*G*transpose(T) reduced, an automorphism g of the
  # reduced form is inv(T)*g*T in the original basis.
  G = gram_matrix(L)
  G = change_base_ring(ZZ, sign(G[1, 1]) * denominator(G) * G)
  G = divexact(G, content(G))
  reduced, T = lll_gram_with_transform(G)
  # The short vectors are enumerated up to the largest diagonal entry and
  # their number prices every node of the search. LLL does not minimise that
  # entry, so keep the given basis if it is at least as good.
  if maximum(diagonal(G)) <= maximum(diagonal(reduced))
    reduced, T = G, identity_matrix(ZZ, n)
  end
  all(x -> fits(Int, x), reduced) || return nothing

  local chain
  try
    chain = stabilizer_chain(Matrix{Int}(reduced))
  catch e
    e isa OverflowError && return nothing
    rethrow()
  end

  Tinv = inv(T)
  generators = ZZMatrix[Tinv * matrix(ZZ, g) * T for g in chain.generators]
  @hassert :Lattice 1 all(g -> g * gram_matrix(L) * transpose(g) ==
                               gram_matrix(L), generators)
  return generators, chain.order
end

end # module LatticePartitionBacktrack
