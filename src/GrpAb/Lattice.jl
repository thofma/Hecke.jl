################################################################################
#
#            GrpAb/Lattice.jl : Lattice of abelian groups
#
# This file is part of Hecke.
#
# Copyright (c) 2015, 2016, 2017: Claus Fieker, Tommy Hofmann
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
# * Redistributions of source code must retain the above copyright notice, this
#   list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright notice,
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
#
#  Copyright (C) 2017 Tommy Hofmann
#
################################################################################

################################################################################
#
#  Graph with data at the edges
#
################################################################################

# A graph G consists of nested dictionaries to store edges with data attached.
# Additionally, we keep track of the degree of each vertex in the G.degrees
# field. Whenever we modify G by appending or deleting vertices, we check
# whether the degree of a vertex becomes < 2. If so, we store the vertex in
# G.new_low_degrees.

function Base.show(io::IO, G::Graph{T, M}) where {T, M}
  print("Graph with $(length(G.edges)) vertices of type $T and edge data of type $M\n")
end

# Append an element to a graph
function Base.append!(G::Graph{T, M}, a::T) where {T, M}
  if haskey(G.edges, a)
    error("Element already a vertex of the graph")
  end
  G.edges[a] = Dict{T, M}()
  G.degrees[a] = 0
  G.new_low_degrees[a] = nothing
end

# For debugging purposes
function _compute_degrees(G::Hecke.Graph{T, N}) where {T, N}
  l = Dict{T, Int}()
  for e in keys(G.edges)
    l[e] = length(G.edges[e])
    for a in keys(G.edges)
      if haskey(G.edges[a], e)
        l[e] += 1
      end
    end
  end
  return l
end

# Append an edge to a graph
function Base.append!(G::Graph{T, M}, e::Tuple{T, T}, data::M) where {T, M}
  if !haskey(G.edges, e[1])
    append!(G, e[1])
  end
  if !haskey(G.edges, e[2])
    append!(G, e[2])
  end
  G.edges[e[1]][e[2]] = data
  G.degrees[e[1]] += 1
  G.degrees[e[2]] += 1

  if G.degrees[e[1]] > 1
    delete!(G.new_low_degrees, e[1])
  else
    G.new_low_degrees[e[1]] = nothing
  end

  if G.degrees[e[2]] > 1
    delete!(G.new_low_degrees, e[2])
  else
    G.new_low_degrees[e[2]] = nothing
  end
end

# Delete a vertex from a graph
function Base.delete!(G::Graph{T, M}, a::T) where {T, M}
  Base.delete!(G.new_low_degrees, a)
  Base.delete!(G.degrees, a)

  if haskey(G.edges, a)
    for e in keys(G.edges[a])
      G.degrees[e] -= 1
      if G.degrees[e] < 2
        G.new_low_degrees[e] = nothing
      end
    end
    Base.delete!(G.edges, a)
  end

  #@show "iterating over $(length(keys(G.edges)))"
  for e in keys(G.edges)
    if haskey(G.edges[e], a)
      G.degrees[e] -= 1
      Base.delete!(G.edges[e], a)
      if G.degrees[e] < 2
        G.new_low_degrees[e] = nothing
      end
    end
  end
end

function Base.deepcopy_internal(G::Graph{T, M}, dict::IdDict) where {T, M}
  GG = Graph{T, M}()
  for g in keys(G.edges)
    GG.edges[g] = Base.deepcopy_internal(G.edges[g], dict)
  end
  GG.degrees = Base.deepcopy_internal(G.degrees, dict)
  GG.new_low_degrees = Base.deepcopy_internal(G.new_low_degrees, dict)
  return GG
end

function Base.delete!(G::Graph{T, M}, to_delete::Vector{T}) where {T, M}
  if length(to_delete) == 0
    return
  end
  #@show "have to delete $(length(to_delete)) many things"
  #@show "there will be $(length(G.edges) - length(to_delete)) left"
  if length(G.edges) - length(to_delete) < 1000
    #@show "Going through the fast path"
    #GG = deepcopy(G)
    _delete_fastpath(G, to_delete)
  else
    while length(to_delete) > 0
      a = pop!(to_delete)
      Base.delete!(G, a)
    end
  end
end

function _delete_fastpath(G::Graph{T, M}, to_delete::Vector{T}) where {T, M}
  _to_delete = T[]

  while length(to_delete) > 0
    a = pop!(to_delete)
    Base.delete!(G.new_low_degrees, a)
    Base.delete!(G.degrees, a)
    Base.delete!(G.edges, a)
    push!(_to_delete, a)
  end

  for e in keys(G.edges)
    for a in _to_delete
      delete!(G.edges[e], a)
    end
  end
  # Now compute the degrees new
  for e in keys(G.edges)
    G.degrees[e] = length(G.edges[e])
    for a in keys(G.edges)
      if haskey(G.edges[a], e)
        G.degrees[e] += 1
      end
    end
    if G.degrees[e] < 2
      G.new_low_degrees[e] = nothing
    end
  end
end

# Find the shortest path between root and target (if it exists).
# The first return value indicates on whether there exists a path.
# The second return value is an array of type Vector{T},
# with T[1] == target and T[end] == root (note that it is reversed).
function find_shortest(G::Graph{T, M}, root::T, target::T) where {T, M}
  if !(root in keys(G.edges) && target in keys(G.edges))
    error("Elements are not vertices of the graph")
  end
  S = T[]
  Swithparent = Tuple{T, T}[]
  Q = T[]
  push!(S, root)
  push!(Q, root)

  found = false

  while length(Q) > 0 && found == false
    current = pop!(Q)
    if current == target
      found = true
      break
    end
    for n in keys(G.edges[current])
      if !(n in S)
        push!(S, n)
        push!(Swithparent, (current, n))
        if n == target
          found = true
          break
        end
        prepend!(Q, n)
      end
    end
  end

  if !found
    return false, T[]
  end

  current = target
  path = [ target ]

  while current != root
    for s in Swithparent
      if s[2] == current
        current = s[1]
        push!(path, current)
        break
      end
    end
  end

  return true, path
end

# Given two vertices root1 and root2, check if the "connected components"
# intersect. If so, find two paths from root1 and root2 which end in a vertex
# of the intersect. The second and third return values are arrays T1
# and T2 with T1[1] == T2[1], T1[end] == root1 and T2[end] == root2.
function find_common(G::Graph{T, M}, root1::T, root2::T) where {T, M}
  S1 = T[]
  S1withparent = Tuple{T, T}[]
  Q1 = T[]
  push!(S1, root1)
  push!(Q1, root1)

  S2 = T[]
  S2withparent = Tuple{T, T}[]
  Q2 = T[]
  push!(S2, root2)
  push!(Q2, root2)

  found = false

  current = root1

  while length(Q1) > 0 && found == false
    current = pop!(Q1)

    if current in S2
      found = true
    end

    for n in keys(G.edges[current])
      if !(n in S1)
        push!(S1, n)
        push!(S1withparent, (current, n))
        prepend!(Q1, n)
      end
    end
  end

  while length(Q2) > 0  && found == false
    current = pop!(Q2)
    if current in S1
      found = true
      break
    end
    for n in keys(G.edges[current])
      if !(n in S2)
        push!(S2, n)
        push!(S2withparent, (current, n))
        prepend!(Q2, n)
      end
    end
  end

  if found
    target = current

    path1 = [ target ]

    while current != root1
      for s in S1withparent
        if s[2] == current
          current = s[1]
          push!(path1, current)
          break
        end
      end
    end

    path2 = [ target ]

    current = target

    while current != root2
      for s in S2withparent
        if s[2] == current
          current = s[1]
          push!(path2, current)
          break
        end
      end
    end
    return true, path1, path2
  end

  false, T[], T[]
end

################################################################################
#
#  Lattice of finitely generated abelian groups
#
################################################################################

# A lattice of groups L has basically two parts. The first is a weak dictionary
# L.weak_vertices, which hold references to all groups, which are currently
# in the lattice. The second part is an actual graph, whose vertices are the
# objectid's of the groups and whose edges represented maps (the additional
#ZZMatrix(0, 0) data at an edge is the ZZMatrix describing the map).
#
# Now things get complicated (interesting) due to the presence of the gc.
# Here is the most important rule:
#
#   A vertex in the lattice of groups is allowed to be removed only if
#   the degree is < 2.
#
# We achieve this by keeping an additional dictionary L.block_gc, which
# contains the groups which must not be gc'ed.
#
# More details:
# - L.weak_vertices_rev is the "inverse" of L.weak_vertices. For each
#   objectid it contains the corresponding group as a WeakRef.
# - Whenever a group (or a map) is added to a lattice, we check if the
#   degree of a vertex is > 1. If so, we add to L.block_gc.
# - Whenever a group is added to a lattice, a finalizer is added. If then
#   the group is gc'ed, its objectid is added to L.to_delete.
# - Before a group (or a map) is added to a lattice, we update the lattice:
#   - Remove all vertices from the graph whose vertices are in L.to_delete
#   - If the degree of a vertex drops below 2, remove the group from L.block_gc
#
# Minor but important note: Over time, it may happen that two groups (created
# at different times) have the same objectid. But this can happen only, if
# one of them was already gc'ed (so its objectid is contained in L.to_delete).
# Thus, it is important that we update the lattice before we add a new group.
# This way the correspondence G -> objectid(G) is always faithful.

# T is the type of the objects i the lattice
# D is the type of the data attached to the edges, usually some matrix
#  objects of type D need to support products
#  if would be useful if hom(::T, ::T, ::D) would exist

function Base.show(io::IO, L::RelLattice{T, D}) where {T, D}
  print("Relation lattice for $T with underlying graph \n$(L.graph)\n")
  print("In weak dict: $(length(L.weak_vertices))\n")
  print("In dict: $(length(L.block_gc))")
end

# The finalizer, which must be attached to a every group in the lattice.
# Note that it may happen to a lot of groups are gc'ed so that the
# L.to_delete queue gets too big. We cut it off at 100.
function finalizer_lattice(L::RelLattice{T, D}, A::T) where {T, D}
  # TODO: Find out why the following does not work
  #if length(L.to_delete) > 1000
  #  Hecke.update!(L)
  #end
  push!(L.to_delete, objectid(A))
end

# Add an object to a lattice of groups.
function Base.append!(L::RelLattice{T, D}, A::T) where {T, D}
  update!(L)

  L.weak_vertices[A] = nothing
  obid = objectid(A)
  L.weak_vertices_rev[obid] = WeakRef(A)
  append!(L.graph, obid)

  if L.graph.degrees[obid] > 1
    L.block_gc[A] = nothing
  end

  if !A.isfinalized
    finalizer(x -> finalizer_lattice(L, x), A)
    A.isfinalized = true
  end

  return nothing
end

# Add a map to a lattice of groups
# .. sugar for abelian groups ...
function Base.append!(L::GrpAbLattice, f::Map)
  return Base.append!(L, domain(f), codomain(f), f.map)
end

function Base.append!(L::RelLattice{T, D}, dom::T, co::T, f::D) where {T, D}
  update!(L)

  if !haskey(L.weak_vertices, dom)
    append!(L, dom)
  end

  if !haskey(L.weak_vertices, co)
    append!(L, co)
  end

  append!(L.graph, (objectid(dom), objectid(co)), f)

  if L.graph.degrees[objectid(dom)] > 1
    L.block_gc[dom] = nothing
  end

  if L.graph.degrees[objectid(co)] > 1
    L.block_gc[co] = nothing
  end

  return nothing
end

# Delete the group with objectid u from a lattice of groups.
function delete_from_lattice!(L::RelLattice, u::UInt)
  Base.delete!(L.graph, u)
  Base.delete!(L.weak_vertices_rev, u)
  return nothing
end

function delete_from_lattice!(L::RelLattice, us::Vector{UInt})
  Base.delete!(L.graph, us)
  for u in us
    Base.delete!(L.weak_vertices_rev, u)
  end
end

# Update a lattice of groups.
function update!(L::RelLattice)
  #while length(L.to_delete) > 0
  #  u = pop!(L.to_delete)
  #  delete_from_lattice!(L, u)
  #end

  delete_from_lattice!(L, L.to_delete)
  #L.to_delete = UInt[]

  for k in keys(L.graph.new_low_degrees)
    @assert haskey(L.graph.degrees, k)
    # TODO: Why does it crash without the following?
    if !haskey(L.weak_vertices_rev, k)
      delete!(L.graph.new_low_degrees, k)
      continue
    end
    if L.weak_vertices_rev[k].value === nothing
      delete!(L.graph.new_low_degrees, k)
      Base.delete!(L.graph, k)
      Base.delete!(L.weak_vertices_rev, k)
      continue
    end
    @assert L.weak_vertices_rev[k].value !== nothing
    a = L.weak_vertices_rev[k].value
    @assert k == objectid(a)
    @assert L.graph.degrees[k] < 2
    L.weak_vertices[a] = nothing
    Base.delete!(L.block_gc, a)
    delete!(L.graph.new_low_degrees, k)
  end

  return nothing
end

# For a given lattice L and groups G and H, check whether there exists a path
# from G to H. The second return value is a ZZMatrix describing the map (in
# case it exists).

function eval_path(L::RelLattice{T, D}, M::T, pG::Vector{UInt}) where {T, D}
  lG = length(pG)
  if lG == 1
    return L.make_id(M)::D
  end
  mG = L.graph.edges[pG[lG]][pG[lG - 1]]
  for i in lG-1:-1:2
    mG = L.mult(mG, (L.graph.edges[pG[i]][pG[i - 1]]))::D
  end
  return mG
end
# Todo: Reduce the entries of the final matrix.
function can_map_into(L::RelLattice{T, D}, G::T, H::T) where {T, D}
  if !(G in keys(L.weak_vertices) && H in keys(L.weak_vertices))
    return false, L.zero
  end

  b, p = find_shortest(L.graph, objectid(G), objectid(H))
  if b
    m = eval_path(L, G, p)
    return true, m
  else
    return false, L.zero
  end
end

# For a given lattice L and groups G and H, check whether there exists a common
# "overgroup" M. If so, the second return value is M and the third and fourth
# return values describe the map from G to M and H to M respectively.
function can_map_into_overstructure(L::RelLattice{T, D}, G::T, H::T) where {T, D}
  if G === H
    return true, G, L.make_id(G)::D, L.make_id(G)::D
  end

  if !(G in keys(L.weak_vertices) && H in keys(L.weak_vertices))
    return false, G, L.zero, L.zero
  end
  b, pG, pH = find_common(L.graph, objectid(G), objectid(H))
  if b
    @assert pG[1] == pH[1]
    M = L.weak_vertices_rev[pG[1]].value::T
    @assert M !== nothing

    mG = eval_path(L, M, pG)
    mH = eval_path(L, M, pH)

    return true, M, mG, mH
  else
    return false, G, L.zero, L.zero
  end
end

