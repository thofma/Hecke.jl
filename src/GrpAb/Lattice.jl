mutable struct Graph{T, M}
  edges::Dict{T, Dict{T, M}}
  degrees::Dict{T, Int}

  function Graph{T, M}() where {T, M}
    z = new{T, M}()
    z.edges = Dict{T, Dict{T, M}}()
    z.degrees = Dict{T, Int}()
    return z
  end
end

function Base.append!(G::Graph{T, M}, a::T) where {T, M}
  G.edges[a] = Dict{T, M}()
end

function Base.append!(G::Graph{T, M}, e::Tuple{T, T}, data::M) where {T, M}
  if !haskey(G.edges, e[1])
    append!(G, e[1])
    G.degrees[e[1]] = 0
  end
  if !haskey(G.edges, e[2])
    append!(G, e[2])
    G.degrees[e[2]] = 0
  end
  G.edges[e[1]][e[2]] = data
  G.degrees[e[1]] += 1
  G.degrees[e[2]] += 1
end

function Base.delete!(G::Graph{T, M}, a::T) where {T, M}
  if haskey(G.edges, a)
    G.degrees[a] -= length(G.edges[a])
    for e in keys(G.edges[a])
      G.degrees[e] -= 1
    end
    delete!(G.edges, a)
  end
  for e in keys(G.edges)
    if haskey(G.edges[e], a)
      G.degrees[a] -= 1
      G.degrees[e] -= 1
      delete!(G.edges[e], a)
    end
  end
end

mutable struct GrpAbLattice
  nvertices::Int
  weak_vertices::WeakKeyDict
  graph::Graph{UInt, fmpz_mat}
  weak_edge_data::WeakKeyDict
  block_gc::Dict{GrpAbFinGen, Bool}

  function GrpAbLattice()
    z = new()
    z.weak_vertices = WeakKeyDict()
    z.graph = Graph{UInt, fmpz_mat}()
    z.nvertices = 0
    z.weak_edge_data = WeakKeyDict()
    return z
  end
end

const GroupLattice = GrpAbLattice()

function Base.append!(G::GrpAbLattice, a::GrpAbFinGen)
  l = G.nvertices + 1
  G.weak_vertices[a] = true
  append!(G.graph, object_id(a))
end

function Base.append!(G::GrpAbLattice, f::Map)
  if !haskey(G.weak_vertices, domain(f))
    append!(G, domain(f))
  end
  if !haskey(G.weak_vertices, codomain(f))
    append!(G, codomain(f))
  end
  append!(G.graph, (object_id(domain(f)), object_id(codomain(f))), f.map)
  G.weak_edge_data[f] = object_id(f)
  if G.degrees[domain(f)] > 1
    G.block_gc[domain(f)] = true
  end
  if G.degrees[codomain(f)] > 1
    G.block_gc[codomain(f)] = true
  end
end

function delete!(G::GrpAbLattice, A::GrpAbFinGen)
  @assert haskey(G.weak_vertices, A)
  delete!(G.graph, object_id(A))
  delete!(G.weak_vertices, A)
  @assert !haskey(G.block_gc, A)
  G.nvertices -= 1
end

function update!(G::GrpAbLattice)
  for a in G.block_gc
    if G.graph.degrees[object_id(a)] < 2
      println("move $a to weak dictionary")
      G.weak_vertices[a] = true
      delete!(G.block_gc, a)
    end
  end
end

#function update!(G::GrpAbLattice)
#  if G.nvertices != length(G.weak_vertices)
#    println("something was deleteted")
#    for k in keys(G.avertices)
#      println("checking if $k was removed")
#      if any(k == object_id(x) for x in keys(G.weak_vertices))
#        continue
#      else
#        println("object with id $k was deleted")
#        delete!(G.avertices, k)
#        G.nvertices = G.nvertices - 1
#        delete!(G.edges, k)
#        for e in values(G.edges)
#          delete!(e, k)
#        end
#      end
#    end
#  end
#end

function find_shortest(G::Graph{T, M}, root::T, target::T) where {T, M}
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


# Todo: Reduce the entries of the final matrix
function can_map_into(L::GrpAbLattice, G::GrpAbFinGen, H::GrpAbFinGen)
  b, p = find_shortest(L.graph, object_id(G), object_id(H))
  if b
    l = length(p)
    m = L.graph.edges[p[l]][p[l-1]]
    for i in l-1:-1:2
      m = m*(L.graph.edges[p[i]][p[i-1]])
    end
    return true, m
  else
    return false, fmpz_mat(0, 0)
  end
end

function can_map_into_overstructure(L::GrpAbLattice, G::GrpAbFinGen, H::GrpAbFinGen)
  b, pG, pH = find_common(L.graph, object_id(G), object_id(H))
  if b
    @assert pG[1] == pH[1]
    M = G
    for g in keys(L.weak_vertices)
      if object_id(g) == pG[1]
        M = g
      end
    end

    lG = length(pG)
    mG = L.graph.edges[pG[lG]][pG[lG - 1]]
    for i in lG-1:-1:2
      mG = mG*(L.graph.edges[pG[i]][pG[i - 1]])
    end
    lH = length(pH)
    mH = L.graph.edges[pH[lH]][pH[lH - 1]]
    for i in lH-1:-1:2
      mH = mH*(L.graph.edges[pH[i]][pH[i-1]])
    end
    return true, M, mG, mH
  else
    return false, G, fmpz_mat(0, 0), fmpz_mat(0, 0)
  end
end
