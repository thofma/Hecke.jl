################################################################################
#
#  RieSrf/Topology.jl : fundamental group, monodromy, homology basis
#
################################################################################

###############################################################################
#
#  Edges for Tretkoff Algorithm
#
###############################################################################

#The edges of the tree graph in the Tretkoff algorithm.
# - Each edge has a start point and an end point.
# - Each edge has a level. The first vertex has level 1. The odd levels
#   correspond to ramification points and the even levels correspond to sheets.
# - An edge is labeled terminated if the algorithm is done with this edge
# - A branch of the graph is a sequence of edges that ends traces back to the
#   starting vertex.
# - In the algorithm the Tretkoff edges get sorted by the function
#   compare_branches. The position variable gives the position of the
#  terminated edges in this ordering
# - For "even" edges the label gives the position in the list of ordered even
#   edges. The "odd" edges have the same label as their even counterpart
# (with start point and end point reversed).

mutable struct TretkoffEdge
  start_point::Int
  end_point::Int
  level::Int
  terminated::Bool
  branch::Vector{Int}
  position::Int
  label::Int

  function TretkoffEdge(a::Int, b::Int, L::Int = 0,  B::Vector{Int} = [a, b], term::Bool = false)
    TE = new()
    TE.start_point = a
    TE.end_point = b
    TE.level = L
    TE.terminated = term
    TE.branch = B

    return TE
  end
end

function start_point(e::TretkoffEdge)
  return e.start_point
end

function end_point(e::TretkoffEdge)
  return e.end_point
end

function isequal(e1::TretkoffEdge, e2::TretkoffEdge)
  return start_point(e1) == start_point(e2) && end_point(e1) == end_point(e2)
end

function edge_level(e::TretkoffEdge)
  return e.level
end

function terminate(e::TretkoffEdge)
  e.terminated = true
end

function is_terminated(e::TretkoffEdge)
  return e.terminated
end

function branch(e::TretkoffEdge)
  return e.branch
end

function set_position(e::TretkoffEdge, s::Int)
  e.position = s
end

function get_position(e::TretkoffEdge)
  return e.position
end

function PQ(e::TretkoffEdge)
  return start_point(e) < end_point(e)
end

function reverse(e::TretkoffEdge)
  return TretkoffEdge(end_point(e), start_point(e))
end

function set_label(e::TretkoffEdge,l::Int)
  e.label = l
end

function get_label(e::TretkoffEdge)
  return e.label
end

################################################################################
#
#  Monodromy computation
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

# Permutations of the paths of the fundamental group, and from them the chains
# around the discriminant points and around infinity, WITHOUT computing
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
  max_prec = RS.computational_precision
  f = embed_mpoly(defining_polynomial(RS), embedding(RS), max_prec)
  CC = base_ring(f)
  Ky, _ = polynomial_ring(CC, "y")
  f_split = _split_in_y(f)
  m = degree(f, 2)
  s_m = SymmetricGroup(m)

  # The steps between the targets are checked and solved at a low precision
  # (only the targets need the full precision, see continue_adaptive!), as
  # long as that precision still resolves the discriminant points.
  lo_data = nothing
  lo_prec = _monodromy_precision()
  disc = internal_discriminant_points(RS)
  while lo_prec < max_prec && !_resolvable_at(disc, lo_prec - 30)
    lo_prec *= 2
  end
  if lo_prec < max_prec
    f_lo = embed_mpoly(defining_polynomial(RS), embedding(RS), lo_prec)
    Ky_lo, _ = polynomial_ring(base_ring(f_lo), "y")
    lo_data = (_split_in_y(f_lo), Ky_lo)
  end

  ends = Vector{Vector{AcbFieldElem}}(undef, length(paths))
  Threads.@threads :dynamic for i in eachindex(paths)
    ws = ContinuationWorkspace(f_split, Ky)
    lo = lo_data === nothing ? nothing : ContinuationWorkspace(lo_data[1], lo_data[2])
    ends[i] = _continue_along_path(ws, lo, paths[i], max_prec)
  end
  for i in eachindex(paths)
    assign_permutation(paths[i], inv(s_m(sortperm(ends[i], lt = sheet_ordering))))
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
# the only discriminant point closer than the arc. Intermediate steps in the
# low-precision workspace lo (if given), the targets at full precision.
function _continue_along_path(ws::ContinuationWorkspace, lo::Union{Nothing, ContinuationWorkspace},
                              path::CPath, prec::Int)
  CC = base_ring(ws.Ky)
  n = path_type(path) == 0 ? 1 : 16
  x = start_point(path)                      # as in _stitch_path!
  z = sort!(_fresh_fiber!(ws, x, prec), lt = sheet_ordering)
  @req length(z) == ws.m "Wrong number of roots at the start of a path."
  if lo === nothing
    CL = CC
    zl = z
  else
    CL = base_ring(lo.Ky)
    zl = [CL() for _ in 1:ws.m]
    for i in 1:ws.m
      Nemo._acb_set(zl[i], z[i], precision(CL))
    end
  end
  st = AdaptiveContinuationState(CL, ws.m)
  _adaptive_reset!(st, x, zl)
  for k in 1:n
    xn = evaluate(path, CC(-1 + 2*QQ(k, n)))
    continue_adaptive!(st, ws, lo, xn, z, zl)
  end
  return z
end

# The chains of the generators of the fundamental group (the permutations of
# the paths must be known), the closed chains (nontrivial monodromy), the chain
# around infinity and the monodromy representation.
function _build_chains!(RS::RiemannSurfaceModel, paths::Vector{CPath},
                        pi1_gens::Vector{Vector{Int}}, s_m)
  ordered_disc_points = RS.pi1_ordered_disc_points
  closed_chains = CChain[]
  all_chains = CChain[]
  for i in (1:length(pi1_gens))
    gamma = pi1_gens[i]
    chain = map(t -> ((t > 0) ? paths[t] : reverse(paths[-t])), gamma)
    gamma_perm = prod(map(permutation, chain))
    cchain = CChain(chain, ordered_disc_points[i])
    push!(all_chains, cchain)
    if gamma_perm != one(s_m)
      push!(closed_chains, cchain)
    end
  end
  RS.pi1_chains = all_chains

  inf_cchain = make_inf_chain(all_chains)
  RS.inf_chain = inf_cchain
  RS.closed_chains = closed_chains
  RS.monodromy_representation = map(permutation, vcat(closed_chains, [inf_cchain]))
  return RS
end

# After the periods have been computed for a model whose chains already exist
# (built by _ensure_monodromy!): check that the paths have the same
# permutations as before and set the integral matrices of the chains. The
# chain objects are kept, since the special points are attached to them.
function _refresh_chains!(RS::RiemannSurfaceModel)
  for C in vcat(RS.pi1_chains, [RS.inf_chain])
    prod(map(permutation, C.paths)) == C.permutation ||
      error("The monodromy found while computing the periods differs from the one computed before. Please report this example.")
    _set_chain_integral!(C)
  end
  return RS
end

@doc raw"""
fundamental_group_of_punctured_P1(RS::RiemannSurfaceModel) -> Tuple{Vector{CPath}, Vector{Vector{Int}}}

A set of generators of the fundamental group pi_1 of P^1/D where D is the set
of discriminant points.
The output consists of a tuple (L, G) where
- L is a list of paths
- G consists of generators for pi_1. Each generator is encoded by a
sequence of indices. These indices refer to the paths in L.
"""
function fundamental_group_of_punctured_P1(RS::RiemannSurfaceModel, abel_jacobi::Bool = true)
  if isdefined(RS, :fundamental_group_of_P1)
    return RS.fundamental_group_of_P1
  else
    return _fundamental_group_of_punctured_P1(RS, abel_jacobi)
  end
end

#Follows algorithm 4.3.1 in Neurohr
function _fundamental_group_of_punctured_P1(RS::RiemannSurfaceModel, abel_jacobi::Bool = true)

  #Compute the exceptional values x_i
  D_points = internal_discriminant_points(RS)
  d = length(D_points)
  CC = parent(D_points[1])
  RR = ArbField(precision(CC))
  prec = precision(RS)

  # The paths (end points, centers, radii, angles) get the precision of the
  # discriminant points, not the working precision: their radii enter the
  # abscissae and hence the integrals, and near clustered discriminant points
  # the integrand amplifies them a lot (for g4 paths at the working precision
  # capped the periods at ~prec + 1 bits, whatever the quadrature target).
  # The discriminant points are computed at deg * (W + bound margin) bits, so
  # this adapts to the difficulty of the curve. (Paths from splitting already
  # had this precision.)
  CC_low = CC

  #Step 1 compute a minimal spanning tree
  edges = minimal_spanning_tree(D_points)

  #Choose a suitable base point and connect it to the spanning tree

  #Multiple ways to choose the base point.
  #This one is most suitable when computing abel-jacobi maps.
  #Take some integer point to the left of the point with the smallest real part

  if abel_jacobi

    #Real part should already be minimal in D_points

    #Catch the case where flooring an arb is not ambiguous. Floor to the smallest of the two options.
    x0 = try floor(ZZRingElem, real(D_points[1]) - 2*max_radius(RS))
       catch err
       try  floor(ZZRingElem, real(D_points[1]) - 2*max_radius(RS) -0.5)
         catch err
         error("Precision too low")
       end
    end

    #Connect base point to closest point in D_points

    distance, index = closest_point(CC(x0), D_points)

    push!(D_points, CC(x0))
    push!(edges, (d +1, index))
  else
  #Here we take the one that is most suitable if one doesn't need to compute Abel-Jacobi maps according to Neurohr, i.e. we split the longest edge in the middle.
  #(Last edge should be the longest in the way we compute minimal_spanning trees right now.)

    left = edges[end][1]
    right = edges[end][2]
    pop!(edges)
    x0 = (D_points[left] + D_points[right])//2
    push!(D_points, x0)
    push!(edges, (d + 1, left))
    push!(edges, (d + 1, right))
  end
  #Now we sort the points by angle and level

  path_edges = Int[]
  past_nodes = [d + 1]
  current_node = d + 1

  left_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), edges)
  right_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), map(reverse,edges))

  leftright = vcat(left_edges, right_edges)

  current_angle = zero(RR)

  angle_ordering = function(t1::Tuple{Int, Int}, t2::Tuple{Int, Int})
    return mod2pi(angle(D_points[t1[2]] - D_points[t1[1]]) - current_angle) < mod2pi(angle(D_points[t2[2]] - D_points[t2[1]]) - current_angle)
  end

  sort!(leftright, lt = angle_ordering)

  path_edges = vcat(path_edges, leftright)
  current_level = vcat(left_edges, right_edges)

  while length(path_edges) < length(edges)
    next_level = Int[]
    for edge in current_level

      previous_node = edge[1]
      current_node = edge[2]
      current_angle = angle(D_points[previous_node] - D_points[current_node])

      left_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), edges)
      right_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), map(reverse, edges))
      leftright = vcat(left_edges, right_edges)

      angle_ordering = function(t1::Tuple{Int, Int}, t2::Tuple{Int, Int})
        return mod2pi(angle(D_points[t1[2]] - D_points[t1[1]]) - current_angle) < mod2pi(angle(D_points[t2[2]] - D_points[t2[1]]) - current_angle)
      end

      sort!(leftright, lt = angle_ordering)
      next_level = vcat(next_level, leftright)
      path_edges = vcat(path_edges, leftright)

      push!(past_nodes, current_node)
    end

    current_level = next_level
  end

  #Construct paths to every end point starting at x0 using a Depth-First Search

  #Paths to all nodes
  paths = [[(d+1, d+1)]]

  ordered_disc_points = Int64[]
  find_paths_to_end([(d+1, d+1)], paths, path_edges, ordered_disc_points)
  ordered_disc_points = map(t -> D_points[t], ordered_disc_points)

  radii = [min(RR(max_radius(RS)), RR(radius_factor(RS)) * minimum(map(t -> abs(t - D_points[j]), vcat(D_points[1:j-1], D_points[j+1:end])))) for j in (1:d)]
  RS.safe_radii = radii
  c_lines = CPath[]

  #Find the line pieces of the paths.
  for edge in path_edges
    a = D_points[edge[1]]
    b = D_points[edge[2]]
    ab_length = b - a

    #Base point is not a discriminant point, so we don't need to circle around it
    if edge[1] == d + 1
      new_start_point = a
    else
      #Intersect the line between a and b with the circle of radius r_a around a
      new_start_point = a + (radii[edge[1]])*ab_length//(abs(ab_length))
    end
    #Intersect the line between a and b with the circle of radius r_b around b
    new_end_point = b - (radii[edge[2]])*ab_length//(abs(ab_length))
    push!(c_lines, c_line(new_start_point, new_end_point, CC_low))
  end

  paths = map(t -> t[2:end], paths[2:end])
  path_indices = map(path -> map(t -> findfirst(x -> x == t, path_edges), path), paths)

  c_arcs = CPath[]
  paths_with_arcs = Vector{Int}[]

  #We reconstruct the paths
  for path in reverse(path_indices)

    i = path[end]
    loop = Int[]

    arc_start = arc_end = c_lines[i].end_point_high
    center = D_points[path_edges[i][end]]

    #We need to loop around the end of the path, but we may
    #have already constructed parts of the loop when constructing previous paths
    #We therefore find these first and add them.

    n = length(c_arcs)
    for j in (1:n)
      arc = c_arcs[j]
      if contains(arc_end, end_point(arc)) && contains(end_point(arc), arc_end)
        push!(loop, j + d)
        arc_end = arc.start_point_high
      end
    end

    push!(c_arcs, c_arc(arc_start, arc_end, center, CC_low))
    push!(loop, d + n + 1)

    path_to_loop = Int[]

    #Now we attach the line piece
    push!(path_to_loop, i)

    #We add the inverse arcs as moving towards the points we want to encircle we move clockwise
    for k in (length(path)-1:-1:1)

      arc_buffer = Int[]
      old_line_piece = c_lines[path[k+1]]
      new_line_piece = c_lines[path[k]]
      arc_start = old_line_piece.start_point_high
      arc_end = new_line_piece.end_point_high
      center = D_points[path_edges[path[k]][end]]

     #Similar to before. Maybe make a function out of it
      n = length(c_arcs)
      for j in (1:n)
        arc = c_arcs[j]
        if contains(arc_end, end_point(arc)) && contains(end_point(arc), arc_end)
          push!(arc_buffer, -j - d)
          arc_end = arc.start_point_high
        end
      end

      if arc_start != arc_end
        push!(c_arcs, c_arc(arc_start, arc_end, center, CC_low))
        push!(arc_buffer, - d - n - 1)
      end

      path_to_loop = vcat(path_to_loop, reverse(arc_buffer))
      push!(path_to_loop, path[k])
    end
    push!(paths_with_arcs, vcat(reverse(path_to_loop), reverse(loop), -path_to_loop))
  end
  paths = vcat(c_lines, c_arcs)
  pi1 = paths, reverse(paths_with_arcs)
  f = complex_defining_polynomial(RS)
  CCz, z = polynomial_ring(CC)
  ys = fiber(complex_defining_polynomial(RS), CC(x0))
  base_point = RiemannSurfacePoint(RS)
  base_point.coordx = CC(x0)
  base_point.index = 1
  base_point.sheets = [1]
  base_point.is_finite = true
  base_point.coordy = ys[1] 
  base_point.homog_coords = [base_point.coordx, base_point.coordy, CC(1)]
  RS.base_point = base_point
  RS.fundamental_group_of_P1 = pi1
  RS.pi1_ordered_disc_points = ordered_disc_points
  RS.ajm_starting_points = [ start_point(p) for p in paths]
  return paths, reverse(paths_with_arcs), ordered_disc_points
end

function find_paths_to_end(path, paths, edges, ordered_disc_points)
  end_path = path[end][2]
  temp_paths = paths
  for (start_edge, end_edge) in edges
    if start_edge == end_path
      push!(ordered_disc_points, end_edge)
      newpath = vcat(path, [(start_edge, end_edge)])
      push!(paths, newpath)
      find_paths_to_end(newpath, paths, edges, ordered_disc_points)
    end
  end
end

#Could be optimized probably. Kruskal's algorithm
function minimal_spanning_tree(v::Vector{AcbFieldElem})

  edge_weights = Tuple{ArbFieldElem, Tuple{Int64, Int64}}[]

  N = length(v)

  #Compute the weights for all the edges
  for i in (1:N)
    for j in (i+1: N)
      push!(edge_weights, (abs(v[i] - v[j]), (i, j)))
    end
  end

  sort!(edge_weights)

  tree = Tuple{Int, Int}[]

  disjoint_trees = [Set([i]) for i in (1:N)]

  i = 1

  while length(tree) < N - 1

    (s1, s2) = edge_weights[i][2]

    s1_index = findfirst(t -> s1 in t, disjoint_trees)

    s1_tree = disjoint_trees[s1_index]

    if s2 in s1_tree
      #continue
    else
      s2_tree = popat!(disjoint_trees, findfirst(t -> s2 in t, disjoint_trees))
      push!(tree, (s1, s2))
      union!(s1_tree, s2_tree)
    end
    i+= 1
  end

  return tree
end

################################################################################
#
#  Homology basis
#
################################################################################

# 
@doc raw"""
function homology_basis(RS::RiemannSurfaceModel) 
  -> Tuple{Vector{Vector{Int}}, ZZMatrix, ZZMatrix}

Computes a hoology basis for the Riemann surface RS.
Assuming the map C -> P1 is m to 1, the output consists of
- a list of cycles L corresponding to r := 2g + m - 1 cycles circling 
around at least 2 ramification points. There will be m - 1 related 
cycles in here.
- An r x r matrix K encoding the intersection pairing between the r cycles.
Its entries are either 1, 0. or -1 depending on whether the cycles intersect
and how their orientation is when they do intersect.
- A symplectic matrix S that ensure that S^T K S is equal to a matrix
where the upper left block consists of the normalized polarization and the
rest consists of zeros. I.e.:
[I  0 0 ... 0]
[0 -I 0 ... 0]
[|  | | ... 0]
[0  0 0 ... 0]
"""
function homology_basis(RS::RiemannSurfaceModel)
  if isdefined(RS, :homology_basis)
    return RS.homology_basis
  end
  return _homology_basis(RS)
end

# The homology basis is computed using the Tretkoff algorithm described
# in Neurohr's thesis 4.6.1 on page 82 and in the Appendix of the thesis.
# Assuming the map C -> P1 is m to 1, the output consists of
# - a list of cycles L corresponding to r := 2g + m - 1 cycles circling around at least
# 2 ramification points. There will be m - 1 related cycles in here
# - An r x r matrix K encoding the intersection pairing between the r cycles.
# Its entries are either 1, 0. or -1 depending on whether the cycles intersect
# and how their orientation is when they do intersect.
# - A symplectic matrix S that ensure that S^T K S is equal to a matrix
# where the upper left block consists of the normalized polarization and the
# rest consists of zeros.
# [I  0 0 ... 0]
# [0 -I 0 ... 0]
# [|  | | ... 0]
# [0  0 0 ... 0]
# This ensures that any period matrix P computed using L will have the
# property that P * S = [P1, P2, O_{m-1}]
# where [P1, P2] forms the big period matrix and O_{m-1} is supposed to be the
# zero matrix. This matrix O_{m-1} can be used as a sanity check for the
#numerical computations.

# REMARK: The choice of the polarization is a convention. We could also opt
# to adopt a different convention if we want to.
function _homology_basis(RS::RiemannSurfaceModel)
  gens = monodromy_representation(RS)
  s_n = parent(gens[1])
  n = s_n.n
  d = length(gens)

  ramification_points = Tuple{Int, SubArray{Int, 1, Vector{Int}, Tuple{UnitRange{Int}}, true}, Perm{Int}}[]
  ramification_indices = Int[]

  for i in (1:d)
    for cyc in cycles(gens[i])
      push!(ramification_points, (i, cyc, s_n("("*string(cyc)[2:end-1]*")")))
      push!(ramification_indices, length(cyc) - 1)
    end
  end

  genus = -n + 1 + divexact(sum(ramification_indices;init = zero(Int)), 2)

  all_branches_terminated = false
  ram_pts_nr = length(ramification_points)
  vertices = Set([ram_pts_nr+1])
  edges_on_level = Vector{TretkoffEdge}[]
  terminated_edges = TretkoffEdge[]

  level = 1
  push!(edges_on_level, [])

  for i in (1:ram_pts_nr)
    if 1 in ramification_points[i][2]
      edge = TretkoffEdge(ram_pts_nr + 1, i, level, [ram_pts_nr + 1, i])
      push!(vertices, i)
      push!(edges_on_level[level], edge)
    end
  end
  while !all_branches_terminated
    level += 1
    push!(edges_on_level, [])

    s = 0

    for edge in edges_on_level[level - 1]
      if !is_terminated(edge)
        start_perm = ramification_points[end_point(edge)][3]
        perm = start_perm
        start_sheet = start_point(edge) - ram_pts_nr
        while !is_one(perm)
          new_sheet = perm[start_sheet] + ram_pts_nr
          if !(new_sheet in branch(edge))
            new_edge = TretkoffEdge(end_point(edge), new_sheet, level, vcat(branch(edge), new_sheet))
            s+=1
            set_position(new_edge, s)
            push!(edges_on_level[level], new_edge)
          end
          perm *= start_perm
        end
      end
    end

    sorted_edges = sort(edges_on_level[level], lt = (a,b) -> start_point(a) < start_point(b))
    for edge in sorted_edges
      if end_point(edge) in vertices
        terminate(edge)
        push!(terminated_edges, edge)
      else
        push!(vertices, end_point(edge))
      end
    end

    level += 1
    push!(edges_on_level, [])

    s = 0

    for edge in edges_on_level[level - 1]
      if !is_terminated(edge)
        l = end_point(edge) - ram_pts_nr
        k = mod(start_point(edge), ram_pts_nr) + 1

        for i in (1:ram_pts_nr)
          if (l in ramification_points[k][2]) && !(k in branch(edge))
            new_edge = TretkoffEdge(end_point(edge), k, level, vcat(branch(edge), k))
            s+=1
            set_position(new_edge, s)
            push!(edges_on_level[level], new_edge)
          end
          k = mod(k, ram_pts_nr) + 1
        end
      end
    end

    sorted_edges = sort(edges_on_level[level], lt = (a,b) -> end_point(a) < end_point(b))
    for edge in sorted_edges
      if end_point(edge) in vertices
        terminate(edge)
        push!(terminated_edges, edge)
      else
        push!(vertices, end_point(edge))
      end
    end

    all_branches_terminated = true
    for edge in edges_on_level[level]
      if !is_terminated(edge)
        all_branches_terminated = false
      end
    end

  end

  terminated_edges_nr = (4*genus + 2*n - 2)
  PQ_size = divexact(terminated_edges_nr, 2)
  @req length(terminated_edges) == terminated_edges_nr "The number of terminated edges is wrong. There is a bug in the code."

  function compare_branches(e1::TretkoffEdge, e2::TretkoffEdge)
    l1 = edge_level(e1)
    l2 = edge_level(e2)
    if l1 == l2
      return get_position(e1) < get_position(e2)
    elseif l1 < l2

      e_temp = TretkoffEdge(branch(e2)[l1], branch(e2)[l1 + 1])
      i = findfirst(is_equal(e_temp), edges_on_level[l1])
      return compare_branches(e1, edges_on_level[l1][i])
    else
      return !compare_branches(e2, e1)
    end
  end

  sort!(terminated_edges, lt = compare_branches)

  reverse!(terminated_edges)

  P = TretkoffEdge[]
  QQ = TretkoffEdge[]
  Q = Vector{TretkoffEdge}(undef, PQ_size)
  l = 1

  for k in (1:terminated_edges_nr)
    edge = terminated_edges[k]
    set_position(edge, k)
    if PQ(edge)
      push!(P, edge)
      set_label(edge, l)
      l +=1
    else
      push!(QQ,edge)
    end
  end

  for edge in QQ
    l = findfirst(is_equal(reverse(edge)), P)
    set_label(edge, l)
    Q[l] = edge
  end

  cycles_list = Vector{Int}[]

  for i in (1:PQ_size)
    cycle = vcat(branch(P[i]), reverse(branch(Q[i])[1:end-2]))
    k = 1
    while k <= length(cycle) - 1
      cycle[k] -= ram_pts_nr
      cycle[k+1] = ramification_points[cycle[k+1]][1]
      k +=2
    end

    cycle[k] -= ram_pts_nr
    push!(cycles_list, cycle)
  end

  A = zeros(Int, PQ_size, PQ_size)
  for i in (1:PQ_size)
    j = mod(get_position(P[i]), terminated_edges_nr) + 1
    while true
      next_edge = terminated_edges[j]
      if PQ(next_edge)
        A[get_label(next_edge), i] +=1
      else
        if get_label(next_edge) == i
          break
        else
          A[get_label(next_edge), i] -=1
        end
      end
      j = mod(j, terminated_edges_nr) + 1
    end
  end

  @req rank(A) == 2*genus "Computed matrix has the wrong rank. There is a bug in the code."
  K = matrix(ZZ, A)

  RS.homology_basis = cycles_list, K, symplectic_reduction(K)
  return RS.homology_basis
end

# Given an input K this computes S as mentioned in the homology_basis function
# i,e. the output is a symplectic matrix S that ensure that S K S^T is equal to
# a matrix where the upper left block consists of the normalized polarization
# and the rest consists of zeros.
# [0  I 0 ... 0]
# [-I 0 0 ... 0]
# [|  | | ... 0]
# [0  0 0 ... 0]
function symplectic_reduction(K::ZZMatrix)

  @req is_zero(K + transpose(K)) "Matrix needs to be skew-symmetric"
  @req nrows(K) == ncols(K) "Matrix needs to be square"

  n = nrows(K)

  function find_one_above_pivot(K::ZZMatrix, pivot::Int)
    for i in (pivot:n)
      for j in (pivot:n)
        if K[i, j] == 1
          return [i, j]
        end
      end
    end
    return [0, 0]
  end

  A = deepcopy(K)
  B = one(parent(K))

  ind1 = Vector{ZZRingElem}[]
  ind2 = ZZRingElem[]
  pivot = 1

  while pivot <= n
    next = find_one_above_pivot(A, pivot)
    if next == [0,0]
      push!(ind2, pivot)
      pivot +=1
      continue
    end
    move_to_positive_pivot(next[2], next[1], pivot, A, B)
    zeros_only = true
    pivot_plus = pivot + 1
    for j in (pivot + 2:n)
      v = -A[pivot, j]
      if v != 0
        #The version with ! gave different results for some reason.

        add_row!(A, v, pivot_plus, j)
        add_column!(A,v, pivot_plus, j)
        add_row!(B, v, pivot_plus, j)

        zeros_only = false
      end
      v = A[pivot_plus, j]
      if v != 0
        add_row!(A, v, pivot, j)
        add_column!(A, v, pivot, j)
        add_row!(B, v, pivot, j)
        zeros_only = false
      end
    end
    if zeros_only
      push!(ind1, [A[pivot_plus, pivot], pivot])
      pivot += 2
    end
  end
  sort!(ind1)
  reverse!(ind1)
  new_rows_ind = vcat([i[2] for i in ind1], [i[2] + 1 for i in ind1], ind2)
  return matrix(ZZ, vcat([B[Int(i), 1:n] for i in new_rows_ind]))
end

function move_to_positive_pivot(i::Int, j::Int, pivot::Int, A::ZZMatrix, B::ZZMatrix)
  pivot_plus = pivot + 1
  v = A[i, j]
  is_pivot = false
  if [i,j] == [pivot_plus, pivot] && A[pivot_plus, pivot] != v
    is_pivot = true
    swap_rows!(B, pivot, pivot_plus)
    swap_rows!(A, pivot, pivot_plus)
    swap_cols!(A, pivot, pivot_plus)
  elseif [i,j] == [pivot, pivot_plus]
    swap_rows!(B, pivot, pivot_plus)
    swap_rows!(A, pivot, pivot_plus)
    swap_cols!(A, pivot, pivot_plus)
  elseif j != pivot && j != (pivot_plus) && i != pivot && i != (pivot_plus)
    swap_rows!(B, pivot, j)
    swap_rows!(B, pivot_plus, i)
    swap_rows!(A, pivot, j)
    swap_rows!(A, pivot_plus, i)
    swap_cols!(A, pivot, j)
    swap_cols!(A, pivot_plus, i)
  elseif j == pivot
    swap_rows!(B, pivot_plus, i)
    swap_rows!(A, pivot_plus, i)
    swap_cols!(A, pivot_plus, i)
  elseif j == pivot_plus
    swap_rows!(B, pivot, i)
    swap_rows!(A, pivot, i)
    swap_cols!(A, pivot, i)
  elseif i == pivot
    swap_rows!(B, pivot_plus, j)
    swap_rows!(A, pivot_plus, j)
    swap_cols!(A, pivot_plus, j)
  elseif i == pivot_plus
    swap_rows!(B, pivot, j)
    swap_rows!(A, pivot, j)
    swap_cols!(A, pivot, j)
  end
  if A[pivot_plus, pivot] != v && !is_pivot
    swap_rows!(B, pivot, pivot_plus)
    swap_rows!(A, pivot, pivot_plus)
    swap_cols!(A, pivot, pivot_plus)
  end
end
