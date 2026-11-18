################################################################################
#
#  Partition backtracking for automorphisms and isometries of definite
#  lattices
#
################################################################################
#
#  Purpose
#  -------
#
#  This file is a small, self-contained and heavily documented implementation
#  of partition backtracking for definite integer lattices, possibly with
#  additional bilinear forms. It is meant to be reviewed line by line and
#  then extended. Structure like roots or invariant sublattices is detected
#  beforehand by the callers and handed over as additional forms and as
#  labels of the short vectors, see `automorphism_group`.
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
#  More generally the input is a list of integral matrices F_1, ..., F_m,
#  where F_1 = G is as above and the others are arbitrary, also skew-symmetric
#  or not symmetric at all. Then (1) is required for every F_i, and the
#  scalar product <x, y> below stands for a fixed combination of all the
#  F_i(x, y) and F_i(y, x), see `ShortVectors`. The caller may also supply
#  the set V itself together with a label for every vector; then an
#  automorphism has to map every basis vector to a vector with the same
#  label. The norm and the label of a point make up its *colour*.
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
#  the colour of b_k. Whenever image[d] is fixed, `refine!` shrinks the cell of
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
#  Cells are stored as bit vectors, and for every point x that is used and
#  every relevant value c the set {p : <p, x> = c} is tabulated. Refining a
#  cell is then a bitwise `and` and its size a population count.
#
#  The cell sizes alone are a weak test on lattices whose short vectors all
#  look alike, for example when they form a spherical design. Therefore the
#  fingerprint also records the scalar products of the *sums* of the cells,
#  see `Fingerprint`; these depend on the scalar products inside the cells.
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
#  (3).
#
#  If -1 respects the colours it is an automorphism; this is used at the
#  first level. With labels this need not be the case.
#
#
#  Machine integers
#  ----------------
#
#  The search computes with `Int` and lets it wrap around, see `wrap`. All
#  its tests remain necessary conditions for an isometry. In return every
#  complete image is checked against (1) in exact arithmetic before it is
#  accepted, so the search works for forms with entries of any size.
#
#
#  Isometries
#  ----------
#
#  The fingerprint describes the *source*, the short vectors in which images
#  are searched are the *target*. For automorphisms the two belong to the
#  same lattice. For an isometry test they belong to two lattices, and the
#  first complete image is an isometry, see `isometry`.
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
#    `wrap`              why machine integers suffice
#    `ShortVectors`      the finite set V union -V the group acts on
#    `Fingerprint`       base order and expected cell sizes (source side)
#    `Search`, `refine!`, `extend!`
#                        the depth-first partition backtrack (target side)
#    `Generator`, `Orbit`, `close!`
#                        explicit orbit computation on points
#    `stabilizer_chain`  the outer loop; best entry point for the algorithm
#    `automorphism_group`, `isometry`
#                        the interface used by Hecke
#
#
#  Extension points
#  ----------------
#
#    * Stronger refiners (Bacher polynomials, ...): add the test to `refine!`
#      and the matching expected value to `Fingerprint`, as is done for the
#      sums of cells.
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

import ..Hecke: @req, @vprintln, ZZ, ZZLat, ZZMatrix, ZZRingElem,
                change_base_ring, content, denominator, det, diagonal,
                divexact, gram_matrix, identity_matrix, is_definite,
                is_symmetric, lll_gram_with_transform, matrix, mul!, nbits,
                ncols, nrows, rank, zero_matrix, __short_vectors,
                _short_vectors_gram_integral

################################################################################
#
#  Machine integers
#
################################################################################

# The search computes with `Int` and lets the arithmetic wrap around. This is
# harmless: reduction modulo 2^64 is a ring homomorphism, so an equation
# between scalar products which holds over the integers also holds for the
# wrapped values. Every test of the search is such an equation, satisfied by
# all isometries; hence wrapping never discards an isometry. It may let a
# wrong candidate pass, which is why a complete image is checked with exact
# arithmetic, see `is_isometry`. Only the coordinates of the short vectors
# have to fit into an `Int`.
wrap(x::ZZRingElem) = BigInt(x) % Int

wrap(A::ZZMatrix) = Int[wrap(A[i, j]) for i in 1:nrows(A), j in 1:ncols(A)]

################################################################################
#
#  The finite set of short vectors
#
################################################################################

# A finite set V union -V of lattice vectors, together with the bilinear
# forms the isometries have to preserve and a colouring they have to respect.
#
# Column j of `vectors` is v_j; only one of v_j, -v_j is stored. A *point* is a
# signed index: p > 0 stands for v_p and p < 0 for -v_{-p}.
#
# A set of points is stored as a `BitVector` of length 2 * nv, in which the
# point p > 0 has the index p and the point -p has the index nv + p.
#
# `exact_forms` are the forms F_1, ..., F_m as given; F_1 is symmetric and
# positive definite, the others are arbitrary. The search does not look at
# them one by one. It uses `gram`, which is F_1 with wrapped entries, and
#
#     `form` = F_1 + sum_{i > 1} (c_i * F_i + d_i * transpose(F_i))
#
# with fixed pseudo-random c_i and d_i (d_i = 0 if F_i is symmetric), again
# with wrapped arithmetic. We write <x, y> = x * form * transpose(y); this is
# not symmetric in general. An isometry preserves <x, y>, and up to the
# unlikely event of a collision <p, x> determines all F_i(p, x) and
# F_i(x, p). A collision only weakens the tests of the search, see `wrap`.
#
# `colours` assigns to every point (by its index in a set of points) a hash
# of its norm <v, v> and of its label. An isometry has to map every base
# vector to a point of the same colour. A label is a pair of a signed and an
# unsigned integer supplied by the caller; the label of -v is that of v with
# the signed part negated. Labels must be invariant under the group that is
# to be computed, and V must be invariant as a set.
#
# The search spends its time intersecting sets of points with sets of the
# form {p : <p, x> = c}. These sets are tabulated for all c in `values`, the
# off-diagonal entries of `form` and their negatives; no other values are
# ever asked for. Then `masks[r, j]` is the set {p : <p, v_j> = values[r]},
# and it is left unassigned if this set is empty. The scalar products with
# v_j are first computed on demand, for the points of the cell at hand only.
# The table is filled for v_j once the scalar products computed for it,
# counted in `work[j]`, would have paid for it, see `tabulate!`; so an easy
# search or one with small cells tabulates little. The table is quadratic
# in the number of vectors, so at most `budget` further bits are spent on it.
struct ShortVectors
  exact_forms::Vector{ZZMatrix}
  gram::Matrix{Int}
  form::Matrix{Int}
  vectors::Matrix{Int}                  # n x nv, column j is v_j
  form_vectors::Matrix{Int}             # form * vectors
  values::Vector{Int}
  masks::Matrix{BitVector}
  tabulated::BitVector                  # whether masks[:, j] is filled
  work::Vector{Int}
  budget::Base.RefValue{Int}
  colours::Vector{UInt}
  index::Dict{Vector{Int}, Int}         # v_j => j
  buffer::Vector{Int}                   # work space of `apply`
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

colour(norm::Int, label::Int, unsigned_label::UInt) =
  hash((norm, label, unsigned_label))

# The matrices `gram` and `form` of `ShortVectors`.
function search_forms(exact_forms::Vector{ZZMatrix})
  gram = wrap(exact_forms[1])
  form = copy(gram)
  for i in 2:length(exact_forms)
    F = wrap(exact_forms[i])
    form += (hash(i) % Int) * F
    if !is_symmetric(exact_forms[i])
      form += (hash(-i) % Int) * transpose(F)
    end
  end
  return gram, form
end

# All non-zero vectors of norm at most `bound` with respect to the positive
# definite form `G`, up to sign.
function enumerate_vectors(G::ZZMatrix, bound = maximum(diagonal(G)))
  if all(x -> nbits(x) < 62, G)
    return Vector{Int}[v for (v, _) in __short_vectors(G, nothing, bound)]
  end
  list = _short_vectors_gram_integral(Vector, G, ZZ(0), bound, ZZRingElem)
  return Vector{Int}[Int.(v) for (v, _) in list]
end

# The set V is given by `list`, up to sign; by default it consists of all
# vectors whose norm with respect to the first form is at most its largest
# diagonal entry. Vectors which do not have the colour of a standard basis
# vector cannot be the image of one and are dropped.
#
# `source` is only passed when an isometry from `source` onto this set is
# sought: then the search asks for the colours and the scalar products of
# the basis of `source`.
function ShortVectors(exact_forms::Vector{ZZMatrix},
                      list::Vector{Vector{Int}} =
                        enumerate_vectors(exact_forms[1]);
                      labels::Vector{Int} = zeros(Int, length(list)),
                      unsigned_labels::Vector{UInt} = zeros(UInt, length(list)),
                      source = nothing,
                      masks_max_bytes::Int = MASKS_MAX_BYTES)
  gram, form = search_forms(exact_forms)
  n = size(gram, 1)
  all_vectors = Matrix{Int}(undef, n, length(list))
  for (j, v) in enumerate(list)
    all_vectors[:, j] = v
  end

  # the colours of v_j and of -v_j
  all_form_vectors = form * all_vectors
  all_colours = Matrix{UInt}(undef, length(list), 2)
  for j in 1:length(list)
    s = 0
    @inbounds @simd for i in 1:n
      s += all_vectors[i, j] * all_form_vectors[i, j]
    end
    all_colours[j, 1] = colour(s, labels[j], unsigned_labels[j])
    all_colours[j, 2] = colour(s, -labels[j], unsigned_labels[j])
  end
  needed = Set{UInt}()
  if source === nothing
    for j in 1:length(list)
      v = view(all_vectors, :, j)
      if count(!iszero, v) == 1
        sum(v) == 1 && push!(needed, all_colours[j, 1])
        sum(v) == -1 && push!(needed, all_colours[j, 2])
      end
    end
    values = sort!(unique!(Int[s * form[i, j] for i in 1:n, j in 1:n,
                               s in (1, -1) if i != j]))
  else
    for p in basis_points(source)
      push!(needed, source.colours[bit_index(source, p)])
    end
    values = source.values
  end
  keep = Int[j for j in 1:length(list)
             if all_colours[j, 1] in needed || all_colours[j, 2] in needed]
  vectors = all_vectors[:, keep]
  nv = length(keep)

  index = sizehint!(Dict{Vector{Int}, Int}(), nv)
  for j in 1:nv
    index[list[keep[j]]] = j
  end
  return ShortVectors(exact_forms, gram, form, vectors,
                      all_form_vectors[:, keep], values,
                      Matrix{BitVector}(undef, length(values), nv),
                      falses(nv), zeros(Int, nv), Ref(8 * masks_max_bytes),
                      vcat(all_colours[keep, 1], all_colours[keep, 2]), index,
                      zeros(Int, n))
end

const MASKS_MAX_BYTES = 2^28

# Whether the sets {p : <p, v_j> = c} are tabulated, where a set of
# `cell_size` points is about to be refined. They are tabulated here if the
# scalar products computed on demand for v_j so far would have sufficed for
# all points, unless the budget is used up.
function tabulate!(S::ShortVectors, j::Int, cell_size::Int)
  S.tabulated[j] && return true
  n = dim(S)
  nv = number_of_vectors(S)
  S.work[j] += cell_size
  (S.work[j] >= nv && S.budget[] > 0) || return false
  vals = S.values
  masks = S.masks
  @inbounds for k in 1:nv
    s = 0
    @simd for i in 1:n
      s += S.vectors[i, k] * S.form_vectors[i, j]
    end
    r = searchsortedfirst(vals, s)
    (r <= length(vals) && vals[r] == s) || continue
    # <v_k, v_j> = s and <-v_k, v_j> = -s
    for (row, i) in ((r, k), (searchsortedfirst(vals, -s), nv + k))
      if !isassigned(masks, row, j)
        masks[row, j] = falses(2 * nv)
        S.budget[] -= 2 * nv
      end
      masks[row, j][i] = true
    end
  end
  S.tabulated[j] = true
  return true
end

# The point with coordinate vector `w`, or 0 if `w` is not a short vector.
function find_point(S::ShortVectors, w::Vector{Int})
  j = get(S.index, w, 0)
  j != 0 && return j
  w .= .-w
  j = get(S.index, w, 0)
  w .= .-w
  return -j
end

# The points e_1, ..., e_n.
function basis_points(S::ShortVectors)
  n = dim(S)
  basis = zeros(Int, n)
  e = zeros(Int, n)
  for i in 1:n
    e[i] = 1
    basis[i] = find_point(S, e)
    basis[i] != 0 || error("basis vector is not among the short vectors")
    e[i] = 0
  end
  return basis
end

# The coordinate vector of the point `p`.
function coordinates(S::ShortVectors, p::Int)
  v = S.vectors[:, abs(p)]
  return p < 0 ? -v : v
end

# The value <p, q> on two points.
function scalar_product(S::ShortVectors, p::Int, q::Int)
  j, k = abs(p), abs(q)
  s = 0
  @inbounds @simd for i in 1:dim(S)
    s += S.vectors[i, j] * S.form_vectors[i, k]
  end
  return (p < 0) == (q < 0) ? s : -s
end

# Set `refined` to {p in cell : <p, x> = c} and return it. The two sets may
# be the same object.
function refine_cell!(refined::BitVector, S::ShortVectors, cell::BitVector,
                      x::Int, c::Int)
  if S.tabulated[abs(x)] || tabulate!(S, abs(x), count(cell))
    # <p, -x> = c if and only if <p, x> = -c
    r = searchsortedfirst(S.values, x > 0 ? c : -c)
    isassigned(S.masks, r, abs(x)) || return fill!(refined, false)
    return map!(&, refined, cell, S.masks[r, abs(x)])
  end
  i = findfirst(cell)
  while i !== nothing
    refined[i] = scalar_product(S, point(S, i), x) == c
    i = findnext(cell, i + 1)
  end
  refined === cell || map!(&, refined, refined, cell)
  return refined
end

# Add up the coordinate vectors of the points in `cell`.
function cell_sum!(sum::AbstractVector{Int}, S::ShortVectors, cell::BitVector)
  fill!(sum, 0)
  nv = number_of_vectors(S)
  i = findfirst(cell)
  @inbounds while i !== nothing
    if i <= nv
      @simd for l in 1:dim(S)
        sum[l] += S.vectors[l, i]
      end
    else
      @simd for l in 1:dim(S)
        sum[l] -= S.vectors[l, i - nv]
      end
    end
    i = findnext(cell, i + 1)
  end
  return sum
end

# The number of common elements of two sets of points.
function count_common(a::BitVector, b::BitVector)
  c = 0
  @inbounds @simd for i in 1:length(a.chunks)
    c += count_ones(a.chunks[i] & b.chunks[i])
  end
  return c
end

# An invariant of the point `p` relative to a set of points: a fixed
# combination of the numbers of q in `cell` with <q, p> = c, where c runs
# over `values`. An isometry mapping `cell` to a set of points preserves it.
function count_invariant(S::ShortVectors, p::Int, cell::BitVector,
                         cell_size::Int)
  vals = S.values
  j = abs(p)
  t = 0
  if S.tabulated[j] || tabulate!(S, j, cell_size)
    for r in 1:length(vals)
      # <q, -v_j> = c if and only if <q, v_j> = -c
      row = p > 0 ? r : searchsortedfirst(vals, -vals[r])
      isassigned(S.masks, row, j) || continue
      t += (hash(vals[r]) % Int) * count_common(S.masks[row, j], cell)
    end
    return t
  end
  i = findfirst(cell)
  while i !== nothing
    c = scalar_product(S, point(S, i), p)
    r = searchsortedfirst(vals, c)
    if r <= length(vals) && vals[r] == c
      t += hash(c) % Int
    end
    i = findnext(cell, i + 1)
  end
  return t
end

# Refining by `count_invariant` is only done for cells for which it is cheap.
const COUNT_LIMIT = 2^20

# Set `candidates` to the points of `cell` whose `count_invariant` relative
# to `cell` is that of the point `b`, or is `value` if `b == 0`. Return this
# value and a hash of the invariants of all points of `cell`.
function refine_by_counts!(candidates::BitVector, S::ShortVectors,
                           cell::BitVector, b::Int, value::Int)
  copyto!(candidates, cell)
  size = count(cell)
  if size <= 1 || size * number_of_vectors(S) > COUNT_LIMIT
    return 0, 0
  end
  if b != 0
    value = count_invariant(S, b, cell, size)
  end
  total = 0
  i = findfirst(cell)
  while i !== nothing
    t = count_invariant(S, point(S, i), cell, size)
    total += hash(t) % Int
    candidates[i] = t == value
    i = findnext(cell, i + 1)
  end
  return value, total
end

# The set of all points of a given colour.
points_of_colour(S::ShortVectors, c::UInt) = BitVector(S.colours .== c)

################################################################################
#
#  Fingerprint
#
################################################################################

# The source side of a search: what an image of the basis has to look like.
#
#   `source`      the short vectors the fingerprint was computed from
#   `order`       the base; b_i = e_{order[i]}
#   `base`        the base as points of the source
#   `colours`     colours[i] is the colour of b_i
#   `products`    products[k, d] = <b_k, b_d>
#   `cell_sizes`  for d <= k, cell_sizes[d, k] is the size of the cell of
#                 position k after b_1, ..., b_{d-1} have been fixed
#   `representative`
#                 for d <= k, the smallest position l >= d which has the
#                 same cell as k after b_1, ..., b_{d-1} have been fixed
#
# In particular `cell_sizes[d, d]` is the number of candidates for the image
# of b_d once the earlier images are known.
#
# Two positions k and l have the same cell at depth d whenever b_k and b_l
# have the same colour and the same scalar products with b_1, ..., b_{d-1}.
# This happens a lot (in the beginning every cell is determined by a colour),
# so the search stores and refines a cell only for its representative.
#
#   `sum_products`
#                 sum_products[d] is the Gram matrix, with respect to
#                 `gram`, of the vectors s_k, the sum of all points in
#                 the cell of position k at depth d, where k runs over the
#                 representatives at depth d
#
# An isometry mapping b_1, ..., b_{d-1} to image[1], ..., image[d-1] maps the
# cells of the source onto the cells of the target, hence the sums s_k onto
# the corresponding sums, and it preserves their scalar products. Unlike
# the cell sizes this takes the scalar products between the points of the
# cells into account. These are the vector sums of [PS97, Section 4], taken
# over the cells.
#
#   `counts`      counts[:, d] describes the *candidates*, the cell of
#                 position d at depth d refined once more: by the numbers
#                 of points in the cell with given scalar product, see
#                 `refine_by_counts!`. Its entries are the invariant of
#                 b_d, a hash of the invariants of all points of the cell,
#                 and the number of candidates. Only the candidates can be
#                 images of b_d. The cell itself is left as it is, because
#                 it is shared with later positions. This refinement costs
#                 more than the others and is only switched on, and
#                 `counts` filled, when a search turns out to be hard, see
#                 `use_counts!`.
#   `negation`    whether -b_i has the colour of b_i for all i; then -1 is
#                 an automorphism
struct Fingerprint
  source::ShortVectors
  order::Vector{Int}
  base::Vector{Int}
  colours::Vector{UInt}
  products::Matrix{Int}
  cell_sizes::Matrix{Int}
  representative::Matrix{Int}
  sum_products::Vector{Matrix{Int}}
  counts::Matrix{Int}
  negation::Bool
end

function cell_representatives(colours::Vector{UInt}, products::Matrix{Int})
  n = length(colours)
  representative = zeros(Int, n, n)
  for d in 1:n, k in d:n
    representative[d, k] = findfirst(d:n) do l
      colours[l] == colours[k] &&
        all(products[l, j] == products[k, j] for j in 1:d-1)
    end + d - 1
  end
  return representative
end

# Choose the base greedily: the next base vector is the one with the smallest
# cell, which keeps the branching of the search small.
function base_order(S::ShortVectors, basis::Vector{Int}, colours::Vector{UInt})
  n = dim(S)
  cells = [points_of_colour(S, colours[i]) for i in 1:n]
  order = Int[]
  remaining = collect(1:n)
  for d in 1:n
    _, position = findmin(i -> count(cells[i]), remaining)
    b = popat!(remaining, position)
    push!(order, b)
    for i in remaining
      refine_cell!(cells[i], S, cells[i], basis[b], S.form[i, b])
    end
  end
  return order
end

# Compute the fingerprint by refining along the identity map.
function Fingerprint(S::ShortVectors)
  n = dim(S)
  basis = basis_points(S)
  basis_colours = UInt[S.colours[bit_index(S, p)] for p in basis]
  negation = all(p -> S.colours[bit_index(S, p)] == S.colours[bit_index(S, -p)],
                 basis)
  order = base_order(S, basis, basis_colours)
  base = basis[order]
  colours = basis_colours[order]
  products = S.form[order, order]
  representative = cell_representatives(colours, products)
  cell_sizes = zeros(Int, n, n)
  sum_products = Matrix{Int}[]
  cells = [points_of_colour(S, colours[k]) for k in 1:n]
  for d in 1:n
    cell_sizes[d, d:n] = count.(cells[d:n])
    sums = zeros(Int, n, 0)
    for k in d:n
      if representative[d, k] == k
        sums = hcat(sums, cell_sum!(zeros(Int, n), S, cells[k]))
      end
    end
    push!(sum_products, transpose(sums) * S.gram * sums)
    for k in (d + 1):n
      refine_cell!(cells[k], S, cells[k], base[d], products[k, d])
    end
  end
  return Fingerprint(S, order, base, colours, products, cell_sizes,
                     representative, sum_products, zeros(Int, 3, n), negation)
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
#                  image[1], ..., image[d-1] are fixed; only filled if k is
#                  the representative of its cell, see `cell`
#   `candidates[d]`
#                  the possible images of b_d, see `Fingerprint`
#   `nodes`        number of search nodes visited (diagnostics only)
#   `sums`, `gram_sums`
#                  work space of `cell_sums_match!`
#
# The cells of all depths are kept, so backtracking needs no undo step.
mutable struct Search
  source::Fingerprint
  target::ShortVectors
  image::Vector{Int}
  cells::Vector{Vector{BitVector}}
  candidates::Vector{BitVector}
  use_counts::Bool
  nodes::Int
  sums::Matrix{Int}
  gram_sums::Matrix{Int}
  product::ZZMatrix               # work space of `is_isometry`
end

function Search(source::Fingerprint, target::ShortVectors)
  n = dim(target)
  cells = [Vector{BitVector}(undef, n) for _ in 1:n]
  for d in 1:n, k in d:n
    if source.representative[d, k] == k
      cells[d][k] = d == 1 ? points_of_colour(target, source.colours[k]) :
                             falses(2 * number_of_vectors(target))
    end
  end
  candidates = [falses(2 * number_of_vectors(target)) for _ in 1:n]
  return Search(source, target, zeros(Int, n), cells, candidates, false, 0,
                zeros(Int, n, n), zeros(Int, n, n), zero_matrix(ZZ, n, n))
end

# The set of possible images of b_k once image[1], ..., image[depth-1] are
# fixed.
cell(search::Search, depth::Int, k::Int) =
  search.cells[depth][search.source.representative[depth, k]]

# Whether the cells at depth 1 look like those of the source. This always
# holds if the target is the source.
function initial_cells_match!(search::Search)
  source = search.source
  n = dim(search.target)
  n == 0 && return true
  for k in 1:n
    count(cell(search, 1, k)) == source.cell_sizes[1, k] || return false
  end
  return cell_sums_match!(search, 1) && candidates_match!(search, 1)
end

# The number of nodes after which a search counts as hard.
const HARD_SEARCH = 1000

# Switch on the refinement of the candidates by counts. For this the
# invariants of the base are computed along the identity map.
function use_counts!(search::Search)
  search.use_counts = true
  source = search.source
  S = source.source
  n = dim(S)
  identity = Search(source, S)
  candidates = falses(2 * number_of_vectors(S))
  counts = source.counts
  for d in 1:n
    if d > 1
      identity.image[d - 1] = source.base[d - 1]
      refine!(identity, d - 1)
    end
    counts[1, d], counts[2, d] =
      refine_by_counts!(candidates, S, cell(identity, d, d), source.base[d], 0)
    counts[3, d] = count(candidates)
  end
  return search
end

# Compute the candidates at `depth` and compare them with the fingerprint.
function candidates_match!(search::Search, depth::Int)
  counts = search.source.counts
  candidates = search.candidates[depth]
  if !search.use_counts
    copyto!(candidates, cell(search, depth, depth))
    return true
  end
  _, total = refine_by_counts!(candidates, search.target,
                               cell(search, depth, depth), 0, counts[1, depth])
  return total == counts[2, depth] && count(candidates) == counts[3, depth]
end

# Individualize `image[depth]` and refine the cells of all later positions.
#
# Returns `false` as soon as a cell does not have the size prescribed by the
# fingerprint, or the sums of the cells do not have the prescribed scalar
# products; then no isometry extends `image[1:depth]`.
function refine!(search::Search, depth::Int)
  search.nodes += 1
  search.nodes == HARD_SEARCH && use_counts!(search)
  source, target = search.source, search.target
  x = search.image[depth]
  for k in (depth + 1):dim(target)
    source.representative[depth + 1, k] == k || continue
    refined = refine_cell!(search.cells[depth + 1][k], target,
                           cell(search, depth, k), x,
                           source.products[k, depth])
    count(refined) == source.cell_sizes[depth + 1, k] || return false
  end
  return depth == dim(target) ||
         (cell_sums_match!(search, depth + 1) &&
          candidates_match!(search, depth + 1))
end

# Compare the scalar products of the sums of the cells at `depth` with
# `sum_products[depth]` of the fingerprint.
function cell_sums_match!(search::Search, depth::Int)
  source, target = search.source, search.target
  n = dim(target)
  G = target.gram
  expected = source.sum_products[depth]
  sums, gram_sums = search.sums, search.gram_sums
  a = 0                             # number of the current representative
  @inbounds for k in depth:n
    source.representative[depth, k] == k || continue
    a += 1
    cell_sum!(view(sums, :, a), target, search.cells[depth][k])
    for i in 1:n
      t = 0
      @simd for j in 1:n
        t += G[j, i] * sums[j, a]
      end
      gram_sums[i, a] = t
    end
    for b in 1:a
      t = 0
      @simd for i in 1:n
        t += sums[i, b] * gram_sums[i, a]
      end
      t == expected[b, a] || return false
    end
  end
  return true
end

# Extend a partial image to a complete one.
#
# On entry `image[1:depth]` is fixed and has been refined. Returns `true` if
# `image` now describes an isometry, and `false` if every extension failed.
function extend!(search::Search, depth::Int)
  n = dim(search.target)
  depth == n && return is_isometry(search)
  level = depth + 1
  for p in points(search.target, search.candidates[level])
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

# Equation (1) for all forms, generalised to an isometry from the source to
# the target, in exact arithmetic. This is the only place where the result
# of the search is trusted, see `wrap`.
function is_isometry(search::Search)
  M = matrix(ZZ, image_matrix(search))
  Mt = transpose(M)
  P = search.product
  return all(mul!(P, mul!(P, M, T), Mt) == F for (F, T) in
             zip(search.source.source.exact_forms, search.target.exact_forms))
end

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
  M = g.matrix
  w = S.buffer                                            # v * M
  @inbounds for i in 1:dim(S)
    s = 0
    @simd for k in 1:dim(S)
      s += S.vectors[k, abs(p)] * M[k, i]
    end
    w[i] = s
  end
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
    stabilizer_chain(S::ShortVectors)

Compute the group of all matrices `M` which preserve all forms of `S`, that
is, `M*F*transpose(M) == F`, and which map every basis vector to a point of
`S` of the same colour, by partition backtracking. Return a named tuple with

- `generators`: matrices generating the group;
- `order`: the order of the group;
- `orbit_lengths`: the factors of the orbit-stabilizer product for `order`;
- `nodes`: the number of search nodes visited.
"""
function stabilizer_chain(S::ShortVectors)
  # Phase 1: the fingerprint of the identity.
  fingerprint = Fingerprint(S)
  search = Search(fingerprint, S)
  initial_cells_match!(search) || error("identity violates the fingerprint")
  n = dim(S)

  # At level `step` the entries of the base before `step` are fixed and
  # `base[step]` is the point whose orbit is being completed.
  base = fingerprint.base

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
    candidates = points(S, search.candidates[step])

    # A cell of size one: the earlier images determine this one.
    length(candidates) == 1 && continue

    stabilizer = reduce(vcat, generators[step:n])

    # Images already reached by the known subgroup need not be searched. If
    # -1 is an automorphism, then at the first level p and -p lie in the same
    # orbit even though -1 is added to the generators only at the end.
    negation = step == 1 && fingerprint.negation
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
        g = Generator(image_matrix(search))
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
  if n > 0 && fingerprint.negation
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
#  Interface
#
################################################################################

# Whether Hecke uses this module to compute automorphism groups and
# isometries of lattices.
const ENABLED = Ref(false)

# The set of short vectors for the input format described in
# `automorphism_group`.
function short_vectors(forms::Vector{ZZMatrix}, vector_set, labels,
                       unsigned_labels; kwargs...)
  list = Vector{Int}[v for (v, _) in vector_set]
  nv = length(list)
  return ShortVectors(forms, list;
                      labels = isempty(labels) ? zeros(Int, nv) : labels,
                      unsigned_labels = isempty(unsigned_labels) ?
                                        zeros(UInt, nv) : unsigned_labels,
                      kwargs...)
end

@doc raw"""
    automorphism_group(forms::Vector{ZZMatrix}, [vector_set, labels,
                       unsigned_labels]) -> Vector{ZZMatrix}, ZZRingElem

Given square integer matrices `forms`, the first of which is symmetric and
positive definite, return generators and the order of the group of all
integer matrices `g` with `g*F*transpose(g) == F` for all `F` in `forms`.
For good performance the first form should be LLL reduced.

The group acts on the vectors whose norm with respect to the first form is
at most its largest diagonal entry. Alternatively a set of vectors can be
given, up to sign, which contains the standard basis vectors: `vector_set` is
a list of tuples whose first entry is a vector, and `labels` and
`unsigned_labels` are lists of integers, one for each vector, or empty. The
label of `-v` is that of `v` with the signed part negated. Then only those
`g` are returned which map every standard basis vector to a vector with the
same label. The set and the labels have to be invariant under this group.
"""
function automorphism_group(forms::Vector{ZZMatrix}, vector_set = (),
                            labels = Int[], unsigned_labels = UInt[];
                            kwargs...)
  if nrows(forms[1]) == 0
    return ZZMatrix[identity_matrix(ZZ, 0)], one(ZZRingElem)
  end
  S = isempty(vector_set) ? ShortVectors(forms; kwargs...) :
        short_vectors(forms, vector_set, labels, unsigned_labels; kwargs...)
  chain = stabilizer_chain(S)
  return ZZMatrix[matrix(ZZ, g) for g in chain.generators], chain.order
end

@doc raw"""
    isometry(forms1::Vector{ZZMatrix}, forms2::Vector{ZZMatrix},
             [vector_set1, vector_set2, labels1, labels2]) -> Bool, ZZMatrix

Given two lists of square integer matrices as in `automorphism_group`, decide
whether there is an integer matrix `g` with `g*forms2[i]*transpose(g) ==
forms1[i]` for all `i`, and return such a matrix if it exists.

If sets of vectors with labels are given, then `g` is moreover required to
map every standard basis vector to a vector in `vector_set2` with the same
label. The second set must contain every such image.
"""
function isometry(forms1::Vector{ZZMatrix}, forms2::Vector{ZZMatrix},
                  vector_set1 = (), vector_set2 = (), labels1 = Int[],
                  labels2 = Int[]; kwargs...)
  n = nrows(forms1[1])
  no = false, zero_matrix(ZZ, 0, 0)
  if n != nrows(forms2[1]) || length(forms1) != length(forms2) ||
     is_symmetric.(forms1) != is_symmetric.(forms2)
    return no
  end
  n == 0 && return true, zero_matrix(ZZ, 0, 0)
  # The search finds a matrix g of rank n with g*forms2[i]*transpose(g) ==
  # forms1[i]; it is invertible over the integers if and only if the
  # determinants agree.
  det(forms1[1]) == det(forms2[1]) || return no
  if isempty(vector_set1)
    # An isometry maps the standard basis to vectors of at most this norm.
    bound = maximum(diagonal(forms1[1]))
    S1 = ShortVectors(forms1; kwargs...)
    S2 = ShortVectors(forms2, enumerate_vectors(forms2[1], bound);
                      source = S1, kwargs...)
  else
    S1 = short_vectors(forms1, vector_set1, labels1, UInt[]; kwargs...)
    S2 = short_vectors(forms2, vector_set2, labels2, UInt[];
                       source = S1, kwargs...)
  end
  search = Search(Fingerprint(S1), S2)
  if initial_cells_match!(search) && extend!(search, 0)
    return true, matrix(ZZ, image_matrix(search))
  end
  return no
end

@doc raw"""
    automorphism_group(L::ZZLat) -> Vector{ZZMatrix}, ZZRingElem

Given a definite lattice `L`, return generators and the order of its
automorphism group, computed by partition backtracking. The generators act on
the coordinates with respect to the basis of `L`, that is, they satisfy
`g*G*transpose(g) == G` for the Gram matrix `G` of `L`.
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
  generators, order = automorphism_group(ZZMatrix[reduced])
  Tinv = inv(T)
  return ZZMatrix[Tinv * g * T for g in generators], order
end

end # module LatticePartitionBacktrack
