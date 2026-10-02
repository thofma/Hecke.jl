################################################################################
#
#  RieSrf/Paths/Topology.jl : fundamental group, monodromy, homology basis
#
#  The topological part of the period computation (Neurohr, Chapter 4):
#  1. fundamental_group_of_punctured_P1: paths in the x-plane (line pieces
#     and arcs, see CPath.jl) and generators of the fundamental group of P^1
#     minus the discriminant points as words in these paths (Algorithm 4.3.1).
#  2. _ensure_monodromy!: the permutations of the sheets along the paths, by
#     analytic continuation; from them the chains around the discriminant
#     points and around infinity and the local monodromies.
#  3. homology_basis: cycles on the surface from the local monodromies with
#     the Tretkoff algorithm (Section 4.6.1), their intersection matrix and
#     a symplectic reduction of it.
#
#  Entry points: fundamental_group_of_punctured_P1, monodromy_representation,
#  monodromy_group, homology_basis, symplectic_reduction.
#
################################################################################

################################################################################
#
#  Edges for the Tretkoff algorithm
#
################################################################################

# An edge of the tree built by the Tretkoff algorithm. The vertices are the
# ramification points (the cycles of the local monodromies, numbered 1, ..., r)
# and the sheets (numbered r + 1, ..., r + m). The tree starts at sheet 1; the
# edges on odd levels go from a sheet to a ramification point, those on even
# levels from a ramification point to a sheet. An edge whose end point is
# already in the tree is terminated: its branch ends there. The terminated
# edges come in pairs (a, b), (b, a): the P edges (a < b) and the Q edges.
mutable struct TretkoffEdge
  start_point::Int        # vertex the edge starts at
  end_point::Int          # vertex the edge ends at
  level::Int              # level in the tree (1 for the edges at sheet 1)
  terminated::Bool        # the end point was already in the tree
  branch::Vector{Int}     # the vertices from the root to end_point
  position::Int           # while building: position among the new edges of its level;
                          # then the position in the ordering of the terminated edges
  label::Int              # number of the P edge; a Q edge gets the label of its reverse

  function TretkoffEdge(start_point::Int, end_point::Int, level::Int = 0,
                        branch::Vector{Int} = [start_point, end_point], terminated::Bool = false)
    edge = new()
    edge.start_point = start_point
    edge.end_point = end_point
    edge.level = level
    edge.terminated = terminated
    edge.branch = branch
    return edge
  end
end

start_point(edge::TretkoffEdge) = edge.start_point

end_point(edge::TretkoffEdge) = edge.end_point

function isequal(edge1::TretkoffEdge, edge2::TretkoffEdge)
  return start_point(edge1) == start_point(edge2) && end_point(edge1) == end_point(edge2)
end

edge_level(edge::TretkoffEdge) = edge.level

terminate!(edge::TretkoffEdge) = (edge.terminated = true)

is_terminated(edge::TretkoffEdge) = edge.terminated

branch(edge::TretkoffEdge) = edge.branch

set_position!(edge::TretkoffEdge, position::Int) = (edge.position = position)

position(edge::TretkoffEdge) = edge.position

# True for the P edges, false for the Q edges.
PQ(edge::TretkoffEdge) = start_point(edge) < end_point(edge)

reverse(edge::TretkoffEdge) = TretkoffEdge(end_point(edge), start_point(edge))

set_label!(edge::TretkoffEdge, label::Int) = (edge.label = label)

label(edge::TretkoffEdge) = edge.label

################################################################################
#
#  Monodromy
#
################################################################################

@doc raw"""
    monodromy_representation(RS::RiemannSurfaceModel) -> Vector{Perm{Int}}

The local monodromies: for every discriminant point with nontrivial local
monodromy (in the order of the closed chains around them) the permutation of
the sheets when moving along the chain around it, followed by the permutation
for the chain around infinity.

Does not need the period matrix: if the periods have not been computed, the
monodromy is computed by analytic continuation along the paths alone.
"""
function monodromy_representation(RS::RiemannSurfaceModel)
  _ensure_monodromy!(RS)
  return RS.monodromy_representation
end

@doc raw"""
    monodromy_group(RS::RiemannSurfaceModel) -> Vector{Perm{Int}}

Return all the elements of the monodromy group of the finite cover
pi: RS -> P^1.
"""
function monodromy_group(RS::RiemannSurfaceModel)
  return closure(monodromy_representation(RS), *)
end

# The permutations of the paths of the fundamental group, and from them the
# chains around the discriminant points and around infinity, WITHOUT computing
# periods: the fibers are continued along the paths with the adaptive
# continuation (no quadrature nodes). Used for the special points and the
# monodromy of a model whose periods are not needed (yet), e.g. the original
# model when the periods are computed on another model.
# The start fibers are computed as in _stitch_path!, so a later period
# computation must find the same permutations; _refresh_chains! checks this
# and keeps the chain objects (which carry the special points).
function _ensure_monodromy!(RS::RiemannSurfaceModel)
  isdefined(RS, :monodromy_representation) && return RS
  paths, pi1_gens = fundamental_group_of_punctured_P1(RS)
  work_prec = RS.computational_precision
  f_split, Ky = _continuation_data(RS, work_prec)
  s_m = SymmetricGroup(length(f_split) - 1)

  # The steps between the targets are checked and solved at a low precision
  # (only the targets need the full precision, see _continue_adaptive!), as
  # long as that precision still resolves the discriminant points.
  low_data = nothing
  low_prec = _monodromy_precision()
  disc_points = internal_discriminant_points(RS)
  while low_prec < work_prec && !_resolvable_at(disc_points, low_prec - 30)
    low_prec *= 2
  end
  if low_prec < work_prec
    low_data = _continuation_data(RS, low_prec)
  end

  end_fibers = Vector{Vector{AcbFieldElem}}(undef, length(paths))
  Threads.@threads :dynamic for i in eachindex(paths)
    local workspace = ContinuationWorkspace(f_split, Ky)
    local low_workspace = low_data === nothing ? nothing : ContinuationWorkspace(low_data[1], low_data[2])
    end_fibers[i] = _continue_along_path(workspace, low_workspace, paths[i], work_prec)
  end
  for i in eachindex(paths)
    set_permutation!(paths[i], inv(s_m(sortperm(end_fibers[i], lt = sheet_ordering))))
  end
  _build_chains!(RS, paths, pi1_gens, s_m)
  return RS
end

# Working precision of the intermediate steps of _ensure_monodromy!
# (raised if it does not resolve the discriminant points).
_monodromy_precision() = 128

# Continue the (sorted) fiber over the start of the path to its end. Lines in
# one go (the adaptive continuation chooses the steps), arcs through 16 points
# on the arc: every chord then lies between the arc and its center, which is
# the only discriminant point closer than the arc. Intermediate steps in
# low_workspace (if given), the targets at full precision.
function _continue_along_path(workspace::ContinuationWorkspace,
                              low_workspace::Union{Nothing, ContinuationWorkspace},
                              path::CPath, prec::Int)
  CC = base_ring(workspace.Ky)
  m = workspace.m
  number_of_steps = is_line(path) ? 1 : 16
  x = start_point(path)                      # as in _stitch_path!
  fiber = sort!(_fresh_fiber!(workspace, x, prec), lt = sheet_ordering)
  @req length(fiber) == m "Wrong number of roots at the start of a path."
  if low_workspace === nothing
    CC_low = CC
    low_fiber = fiber
  else
    CC_low = base_ring(low_workspace.Ky)
    low_fiber = [CC_low() for _ in 1:m]
    for i in 1:m
      Nemo._acb_set(low_fiber[i], fiber[i], precision(CC_low))
    end
  end
  state = AdaptiveContinuationState(CC_low, m)
  _adaptive_reset!(state, x)
  for k in 1:number_of_steps
    x_next = evaluate(path, CC(-1 + 2*QQ(k, number_of_steps)))
    _continue_adaptive!(state, workspace, low_workspace, x_next, fiber, low_fiber)
  end
  return fiber
end

# The chains of the generators of the fundamental group (the permutations of
# the paths must be known), the closed chains (nontrivial monodromy), the chain
# around infinity and the monodromy representation.
function _build_chains!(RS::RiemannSurfaceModel, paths::Vector{CPath},
                        pi1_gens::Vector{Vector{Int}}, s_m)
  ordered_disc_points = RS.pi1_ordered_disc_points
  closed_chains = CChain[]
  all_chains = CChain[]
  for (i, generator) in enumerate(pi1_gens)
    # a negative index stands for the reversed path
    chain_paths = [k > 0 ? paths[k] : reverse(paths[-k]) for k in generator]
    chain = CChain(chain_paths, ordered_disc_points[i])
    push!(all_chains, chain)
    if prod(map(permutation, chain_paths)) != one(s_m)
      push!(closed_chains, chain)
    end
  end
  RS.pi1_chains = all_chains

  inf_chain = make_inf_chain(all_chains)
  RS.inf_chain = inf_chain
  RS.closed_chains = closed_chains
  RS.monodromy_representation = map(permutation, vcat(closed_chains, [inf_chain]))
  return RS
end

# After the periods have been computed for a model whose chains already exist
# (built by _ensure_monodromy!): check that the paths have the same
# permutations as before and set the integral matrices of the chains. The
# chain objects are kept, since the special points are attached to them.
function _refresh_chains!(RS::RiemannSurfaceModel)
  for chain in vcat(RS.pi1_chains, [RS.inf_chain])
    prod(map(permutation, chain.paths)) == chain.permutation ||
      error("The monodromy found while computing the periods differs from the one computed before. Please report this example.")
    _set_chain_integral!(chain)
  end
  return RS
end

################################################################################
#
#  Fundamental group of P^1 minus the discriminant points
#
################################################################################

@doc raw"""
    fundamental_group_of_punctured_P1(RS::RiemannSurfaceModel, abel_jacobi::Bool = true)
      -> Tuple{Vector{CPath}, Vector{Vector{Int}}}

Generators of the fundamental group of P^1 minus the discriminant points of
`RS`. Returns `(paths, generators)`: `paths` are line pieces and arcs in the
x-plane, and every generator is a word in them, a vector of indices into
`paths` (a negative index -k stands for `paths[k]` reversed). The generators
are loops around the discriminant points, based at an integer point left of
all discriminant points (if `abel_jacobi`, suitable for Abel-Jacobi maps), or
otherwise at the middle of the longest edge of the spanning tree.
The result is cached; `abel_jacobi` only matters for the first call.
"""
function fundamental_group_of_punctured_P1(RS::RiemannSurfaceModel, abel_jacobi::Bool = true)
  if isdefined(RS, :fundamental_group_of_P1)
    return RS.fundamental_group_of_P1
  else
    return _fundamental_group_of_punctured_P1(RS, abel_jacobi)
  end
end

# Neurohr, Algorithm 4.3.1. The paths are the line pieces along the edges of
# a minimal spanning tree of the discriminant points and the base point
# (outside the circles of radius RS.safe_radii around the discriminant
# points), and arcs on these circles. The generator for a discriminant point
# goes from the base point along the tree to its circle, once around it and
# back; at the discriminant points on the way it follows arcs of their
# circles. Arcs that were constructed for an earlier generator are reused.
function _fundamental_group_of_punctured_P1(RS::RiemannSurfaceModel, abel_jacobi::Bool = true)
  disc_points = internal_discriminant_points(RS)   # a copy: the base point is appended
  d = length(disc_points)
  CC = parent(disc_points[1])
  RR = ArbField(precision(CC))

  # The paths (end points, centers, radii, angles) get the precision of the
  # discriminant points (CC), not the working precision: their radii enter the
  # abscissae and hence the integrals, and near clustered discriminant points
  # the integrand amplifies them a lot (for g4, paths at the working precision
  # capped the periods at ~prec + 1 bits, whatever the quadrature target). The
  # discriminant points are computed at a higher precision than the working
  # precision (see Discriminant.jl), so this adapts to the difficulty of the
  # curve.

  # Step 1: a minimal spanning tree, and the base point (vertex d + 1)
  # connected to it.
  edges = minimal_spanning_tree(disc_points)
  base = d + 1
  if abel_jacobi
    # An integer point left of the discriminant points (disc_points[1] has the
    # smallest real part). If the floor is ambiguous at this precision, the
    # floor of a point 1/2 further left.
    shifted = real(disc_points[1]) - 2*_max_radius(RS)
    x0 = try
      floor(ZZRingElem, shifted)
    catch
      try
        floor(ZZRingElem, shifted - 0.5)
      catch
        error("Precision too low")
      end
    end
    _, index = closest_point(CC(x0), disc_points)
    push!(disc_points, CC(x0))
    push!(edges, (base, index))
  else
    # Neurohr's choice when no Abel-Jacobi maps are needed: the middle of the
    # longest edge (minimal_spanning_tree returns it last).
    left, right = pop!(edges)
    x0 = (disc_points[left] + disc_points[right])//2
    push!(disc_points, x0)
    push!(edges, (base, left))
    push!(edges, (base, right))
  end

  # Step 2: orient the edges away from the base point and order them breadth
  # first; the edges leaving a vertex are sorted counterclockwise, starting
  # from the direction back to the previous vertex (from angle 0 at the base
  # point).
  visited = [base]
  path_edges = _edges_by_angle(disc_points, edges, base, visited, zero(RR))
  current_level = copy(path_edges)
  while length(path_edges) < length(edges)
    next_level = Tuple{Int, Int}[]
    for (previous_vertex, vertex) in current_level
      reference_angle = angle(disc_points[previous_vertex] - disc_points[vertex])
      children = _edges_by_angle(disc_points, edges, vertex, visited, reference_angle)
      append!(next_level, children)
      append!(path_edges, children)
      push!(visited, vertex)
    end
    current_level = next_level
  end

  # Step 3: for every discriminant point the edges from the base point to it
  # (depth first search; this also fixes the order of the generators).
  edge_sequences = Vector{Tuple{Int, Int}}[]
  visit_order = Int[]
  _paths_to_disc_points([(base, base)], edge_sequences, path_edges, visit_order)
  edge_sequences = [sequence[2:end] for sequence in edge_sequences]
  ordered_disc_points = disc_points[visit_order]

  # Step 4: the circles around the discriminant points: radius a fraction of
  # the distance to the nearest other point (base point included), at most
  # _max_radius.
  safe_radii = [min(RR(_max_radius(RS)),
                    RR(_radius_factor(RS)) * minimum(abs(disc_points[k] - disc_points[j])
                                                     for k in eachindex(disc_points) if k != j))
                for j in 1:d]
  RS.safe_radii = safe_radii

  # Step 5: the line pieces: the edges without the parts inside the circles.
  line_pieces = CPath[]
  for (a_index, b_index) in path_edges
    a = disc_points[a_index]
    b = disc_points[b_index]
    difference = b - a
    piece_start = a_index == base ? a : a + safe_radii[a_index]*difference//abs(difference)
    piece_end = b - safe_radii[b_index]*difference//abs(difference)
    push!(line_pieces, line_path(piece_start, piece_end, CC))
  end
  number_of_lines = length(line_pieces)       # paths[number_of_lines + j] = arcs[j]

  # Step 6: the generators, with the arcs.
  arcs = CPath[]
  generators = Vector{Int}[]
  for indices in reverse([[findfirst(==(edge), path_edges) for edge in sequence]
                          for sequence in edge_sequences])
    # The loop around the discriminant point at the end. Parts of the circle
    # may already exist as arcs of earlier generators.
    last_line = indices[end]
    arc_start = line_pieces[last_line].end_point_high
    center = disc_points[path_edges[last_line][end]]
    reused, arc_end = _reuse_arcs(arcs, arc_start)
    loop = number_of_lines .+ reused
    push!(arcs, arc_path(arc_start, arc_end, center, CC))
    push!(loop, number_of_lines + length(arcs))

    # The way there, built backwards from the loop: at every discriminant
    # point on the way, the arc from the start of the next line piece to the
    # end of the previous one (reversed: towards the point to be encircled we
    # move clockwise).
    path_to_loop = [last_line]
    for k in length(indices)-1:-1:1
      arc_start = line_pieces[indices[k+1]].start_point_high
      reused, arc_end = _reuse_arcs(arcs, line_pieces[indices[k]].end_point_high)
      detour = -(number_of_lines .+ reused)
      if arc_start != arc_end
        center = disc_points[path_edges[indices[k]][end]]
        push!(arcs, arc_path(arc_start, arc_end, center, CC))
        push!(detour, -(number_of_lines + length(arcs)))
      end
      append!(path_to_loop, reverse(detour))
      push!(path_to_loop, indices[k])
    end
    push!(generators, vcat(reverse(path_to_loop), reverse(loop), -path_to_loop))
  end
  paths = vcat(line_pieces, arcs)
  generators = reverse(generators)

  base_point = RiemannSurfacePoint(RS)
  base_point.coordx = CC(x0)
  base_point.index = 1
  base_point.sheets = [1]
  base_point.is_finite = true
  base_point.coordy = fiber(complex_defining_polynomial(RS), CC(x0))[1]
  base_point.homog_coords = [base_point.coordx, base_point.coordy, CC(1)]
  RS.base_point = base_point
  RS.fundamental_group_of_P1 = (paths, generators)
  RS.pi1_ordered_disc_points = ordered_disc_points
  RS.ajm_starting_points = [start_point(path) for path in paths]
  return RS.fundamental_group_of_P1
end

# The edges of the tree between `vertex` and the vertices not in `visited`,
# oriented away from vertex and sorted counterclockwise by their angle,
# starting at reference_angle.
function _edges_by_angle(points::Vector{AcbFieldElem}, edges::Vector{Tuple{Int, Int}},
                         vertex::Int, visited::Vector{Int}, reference_angle::ArbFieldElem)
  outgoing = [(a, b) for (a, b) in edges if a == vertex && !(b in visited)]
  append!(outgoing, [(b, a) for (a, b) in edges if b == vertex && !(a in visited)])
  relative_angle(edge) = _mod2pi(angle(points[edge[2]] - points[edge[1]]) - reference_angle)
  return sort!(outgoing, lt = (edge1, edge2) -> relative_angle(edge1) < relative_angle(edge2))
end

# Depth first search in the ordered tree from the last vertex of `path`
# (a sequence of edges): appends the sequence of edges to every vertex below
# it to `paths`, and the vertices in the order they are reached to
# `visit_order`.
function _paths_to_disc_points(path::Vector{Tuple{Int, Int}}, paths::Vector{Vector{Tuple{Int, Int}}},
                               edges::Vector{Tuple{Int, Int}}, visit_order::Vector{Int})
  last_vertex = path[end][2]
  for edge in edges
    if edge[1] == last_vertex
      push!(visit_order, edge[2])
      new_path = vcat(path, [edge])
      push!(paths, new_path)
      _paths_to_disc_points(new_path, paths, edges, visit_order)
    end
  end
  return paths
end

# The arcs (constructed for earlier generators) that continue the circle
# backwards from arc_end, chained in the order of construction. Returns their
# indices in arcs and the start of the last one (arc_end if there are none).
function _reuse_arcs(arcs::Vector{CPath}, arc_end::AcbFieldElem)
  reused = Int[]
  for (j, arc) in enumerate(arcs)
    if contains(arc_end, end_point(arc)) && contains(end_point(arc), arc_end)
      push!(reused, j)
      arc_end = arc.start_point_high
    end
  end
  return reused, arc_end
end

# Minimal spanning tree of the complete graph on the points, with the
# distances as weights (Kruskal's algorithm). The edges are returned in
# increasing length.
function minimal_spanning_tree(points::Vector{AcbFieldElem})
  N = length(points)
  weighted_edges = Tuple{ArbFieldElem, Tuple{Int, Int}}[]
  for i in 1:N, j in i+1:N
    push!(weighted_edges, (abs(points[i] - points[j]), (i, j)))
  end
  sort!(weighted_edges)

  tree = Tuple{Int, Int}[]
  components = [Set([i]) for i in 1:N]
  k = 1
  while length(tree) < N - 1
    i, j = weighted_edges[k][2]
    component_i = components[findfirst(component -> i in component, components)]
    if !(j in component_i)
      component_j = popat!(components, findfirst(component -> j in component, components))
      push!(tree, (i, j))
      union!(component_i, component_j)
    end
    k += 1
  end
  return tree
end

################################################################################
#
#  Homology basis
#
################################################################################

@doc raw"""
    homology_basis(RS::RiemannSurfaceModel) -> Tuple{Vector{Vector{Int}}, ZZMatrix, ZZMatrix}

Cycles on the Riemann surface that generate its homology, computed with the
Tretkoff algorithm (Neurohr, Section 4.6.1 and Appendix). For the m-sheeted
cover RS -> P^1 the output `(cycles, K, S)` consists of
- r = 2g + m - 1 cycles, each encoded as a sequence
  `[s_1, c_1, s_2, c_2, ..., s_k]`: start on sheet s_1, follow the closed chain
  c_1 (an index into the local monodromies, see `monodromy_representation`)
  until sheet s_2, and so on. The cycles generate the homology, with m - 1
  relations.
- the r x r intersection matrix K of the cycles,
- a unimodular matrix S with
  ```
  S K S^T = [ 0  I  0 ]
            [-I  0  0 ]
            [ 0  0  0 ]
  ```
  (identity blocks of size g). The first 2g rows of S express a symplectic
  basis in terms of the cycles, the other rows combinations that are zero in
  homology: for the matrix P of the integrals over the cycles, S P consists
  of the periods over the symplectic basis followed by m - 1 zero rows (a
  sanity check of the numerics).
"""
function homology_basis(RS::RiemannSurfaceModel)
  if isdefined(RS, :homology_basis)
    return RS.homology_basis
  end
  return _homology_basis(RS)
end

function _homology_basis(RS::RiemannSurfaceModel)
  local_monodromies = monodromy_representation(RS)
  s_m = parent(local_monodromies[1])
  m = s_m.n

  # The ramification points: the cycles of the local monodromies, as
  # (index of the local monodromy, the sheets in the cycle, the cycle as a
  # permutation).
  ramification = Tuple{Int, Vector{Int}, Perm{Int}}[]
  ramification_indices = Int[]
  for (i, monodromy) in enumerate(local_monodromies)
    for cycle in cycles(monodromy)
      sheets = collect(cycle)
      push!(ramification, (i, sheets, s_m([s in sheets ? monodromy[s] : s for s in 1:m])))
      push!(ramification_indices, length(sheets) - 1)
    end
  end
  g = -m + 1 + divexact(sum(ramification_indices; init = 0), 2)   # Riemann-Hurwitz

  # The Tretkoff tree. Vertices: ramification points 1, ..., r, sheets
  # r + 1, ..., r + m.
  r = length(ramification)
  vertices = Set([r + 1])
  edges_on_level = Vector{TretkoffEdge}[]
  terminated_edges = TretkoffEdge[]

  # Level 1: from sheet 1 to the ramification points containing it.
  level = 1
  push!(edges_on_level, TretkoffEdge[])
  for i in 1:r
    if 1 in ramification[i][2]
      push!(vertices, i)
      edge = TretkoffEdge(r + 1, i, level, [r + 1, i])
      push!(edges_on_level[level], edge)
      set_position!(edge, length(edges_on_level[level]))
    end
  end

  all_branches_terminated = false
  while !all_branches_terminated
    # Even level: from a ramification point to the other sheets of its cycle,
    # in the order of the cycle.
    level += 1
    push!(edges_on_level, TretkoffEdge[])
    sibling_position = 0
    for edge in edges_on_level[level - 1]
      is_terminated(edge) && continue
      cycle_permutation = ramification[end_point(edge)][3]
      permutation_power = cycle_permutation
      start_sheet = start_point(edge) - r
      while !is_one(permutation_power)
        new_sheet = permutation_power[start_sheet] + r
        if !(new_sheet in branch(edge))
          new_edge = TretkoffEdge(end_point(edge), new_sheet, level, vcat(branch(edge), new_sheet))
          sibling_position += 1
          set_position!(new_edge, sibling_position)
          push!(edges_on_level[level], new_edge)
        end
        permutation_power *= cycle_permutation
      end
    end
    _terminate_or_add!(sort(edges_on_level[level], lt = (a, b) -> start_point(a) < start_point(b)),
                       vertices, terminated_edges)

    # Odd level: from a sheet to the other ramification points containing it,
    # in cyclic order starting after the ramification point it came from.
    level += 1
    push!(edges_on_level, TretkoffEdge[])
    sibling_position = 0
    for edge in edges_on_level[level - 1]
      is_terminated(edge) && continue
      sheet = end_point(edge) - r
      k = mod(start_point(edge), r) + 1
      for _ in 1:r
        if (sheet in ramification[k][2]) && !(k in branch(edge))
          new_edge = TretkoffEdge(end_point(edge), k, level, vcat(branch(edge), k))
          sibling_position += 1
          set_position!(new_edge, sibling_position)
          push!(edges_on_level[level], new_edge)
        end
        k = mod(k, r) + 1
      end
    end
    _terminate_or_add!(sort(edges_on_level[level], lt = (a, b) -> end_point(a) < end_point(b)),
                       vertices, terminated_edges)

    all_branches_terminated = all(is_terminated, edges_on_level[level])
  end

  number_of_terminated = 4*g + 2*m - 2
  number_of_cycles = divexact(number_of_terminated, 2)
  @req length(terminated_edges) == number_of_terminated "The number of terminated edges is wrong. There is a bug in the code."

  # Order the terminated edges by their branches (depth first order of the
  # tree, siblings by position), and number them in reverse order.
  function compare_branches(edge1::TretkoffEdge, edge2::TretkoffEdge)
    level1 = edge_level(edge1)
    level2 = edge_level(edge2)
    if level1 == level2
      return position(edge1) < position(edge2)
    elseif level1 < level2
      # compare with the ancestor of edge2 on the level of edge1
      ancestor = TretkoffEdge(branch(edge2)[level1], branch(edge2)[level1 + 1])
      i = findfirst(edge -> isequal(edge, ancestor), edges_on_level[level1])
      return compare_branches(edge1, edges_on_level[level1][i])
    else
      return !compare_branches(edge2, edge1)
    end
  end
  sort!(terminated_edges, lt = compare_branches)
  reverse!(terminated_edges)

  # Label the P edges in this order; a Q edge gets the label of its reverse.
  P = TretkoffEdge[]
  Q_unsorted = TretkoffEdge[]
  Q = Vector{TretkoffEdge}(undef, number_of_cycles)
  for (k, edge) in enumerate(terminated_edges)
    set_position!(edge, k)
    if PQ(edge)
      push!(P, edge)
      set_label!(edge, length(P))
    else
      push!(Q_unsorted, edge)
    end
  end
  for edge in Q_unsorted
    l = findfirst(p -> isequal(p, reverse(edge)), P)
    set_label!(edge, l)
    Q[l] = edge
  end

  # Cycle l: along the branch of P_l and back along the branch of Q_l (whose
  # last two vertices are those of P_l, reversed). Sheet vertices become sheet
  # numbers, ramification points the index of their local monodromy.
  cycles_list = Vector{Int}[]
  for l in 1:number_of_cycles
    cycle = vcat(branch(P[l]), reverse(branch(Q[l])[1:end-2]))
    k = 1
    while k <= length(cycle) - 1
      cycle[k] -= r
      cycle[k+1] = ramification[cycle[k+1]][1]
      k += 2
    end
    cycle[k] -= r
    push!(cycles_list, cycle)
  end

  # Intersection numbers: going around the boundary of the tree from P_l to
  # Q_l, every P edge passed crosses cycle l in one direction, every Q edge
  # in the other.
  intersections = zeros(Int, number_of_cycles, number_of_cycles)
  for l in 1:number_of_cycles
    k = mod(position(P[l]), number_of_terminated) + 1
    while true
      next_edge = terminated_edges[k]
      if PQ(next_edge)
        intersections[label(next_edge), l] += 1
      else
        label(next_edge) == l && break
        intersections[label(next_edge), l] -= 1
      end
      k = mod(k, number_of_terminated) + 1
    end
  end

  @req rank(intersections) == 2*g "Computed matrix has the wrong rank. There is a bug in the code."
  K = matrix(ZZ, intersections)

  RS.homology_basis = cycles_list, K, symplectic_reduction(K)
  return RS.homology_basis
end

# Terminate the edges whose end point is already in the tree, add the end
# points of the others.
function _terminate_or_add!(edges::Vector{TretkoffEdge}, vertices::Set{Int},
                            terminated_edges::Vector{TretkoffEdge})
  for edge in edges
    if end_point(edge) in vertices
      terminate!(edge)
      push!(terminated_edges, edge)
    else
      push!(vertices, end_point(edge))
    end
  end
end

@doc raw"""
    symplectic_reduction(K::ZZMatrix) -> ZZMatrix

For a skew-symmetric matrix K (with entries such that the reduction only
needs pivots 1, as for intersection matrices), a unimodular matrix S with
```
S K S^T = [ 0  I  0 ]
          [-I  0  0 ]
          [ 0  0  0 ]
```
"""
function symplectic_reduction(K::ZZMatrix)
  @req is_zero(K + transpose(K)) "Matrix needs to be skew-symmetric"
  @req nrows(K) == ncols(K) "Matrix needs to be square"
  n = nrows(K)

  # Simultaneous row and column operations on A (A = B K B^T throughout).
  A = deepcopy(K)
  B = one(parent(K))
  pair_pivots = Int[]      # pivots p of the blocks A[p:p+1, p:p+1] = [0 1; -1 0]
  zero_pivots = Int[]      # rows that became zero
  pivot = 1
  while pivot <= n
    entry = _find_entry_one(A, pivot)
    if entry === nothing
      push!(zero_pivots, pivot)
      pivot += 1
      continue
    end
    row, col = entry                          # A[row, col] = 1, so A[col, row] = -1
    _move_to_pivot!(A, B, col, row, pivot)    # now A[pivot + 1, pivot] = -1
    # Clear the rest of rows and columns pivot and pivot + 1. If something had
    # to be cleared, the same pivot is looked at again.
    zeros_only = true
    for j in pivot+2:n
      v = -A[pivot, j]
      if v != 0
        add_row!(A, v, pivot + 1, j)
        add_column!(A, v, pivot + 1, j)
        add_row!(B, v, pivot + 1, j)
        zeros_only = false
      end
      v = A[pivot + 1, j]
      if v != 0
        add_row!(A, v, pivot, j)
        add_column!(A, v, pivot, j)
        add_row!(B, v, pivot, j)
        zeros_only = false
      end
    end
    if zeros_only
      push!(pair_pivots, pivot)
      pivot += 2
    end
  end
  reverse!(pair_pivots)
  new_rows = vcat(pair_pivots, pair_pivots .+ 1, zero_pivots)
  return B[new_rows, 1:n]
end

# An entry 1 of A in rows and columns pivot, ..., n (row by row), or nothing.
function _find_entry_one(A::ZZMatrix, pivot::Int)
  n = nrows(A)
  for i in pivot:n, j in pivot:n
    A[i, j] == 1 && return (i, j)
  end
  return nothing
end

# Move the entry A[i, j] (i != j) of the skew-symmetric matrix A to the
# position (pivot + 1, pivot) by simultaneous swaps of rows and columns; the
# row swaps are also applied to B.
function _move_to_pivot!(A::ZZMatrix, B::ZZMatrix, i::Int, j::Int, pivot::Int)
  if j != pivot
    _swap_rows_and_columns!(A, B, pivot, j)
    i == pivot && (i = j)
  end
  i != pivot + 1 && _swap_rows_and_columns!(A, B, pivot + 1, i)
  return
end

function _swap_rows_and_columns!(A::ZZMatrix, B::ZZMatrix, k::Int, l::Int)
  swap_rows!(B, k, l)
  swap_rows!(A, k, l)
  swap_cols!(A, k, l)
  return
end
