export chain_complex, isexact, homology, free_resolution

######################################################################
#
# Lift of homomorphisms
#
######################################################################
#=
  G
  | phi
  V
  F <- H
    psi
 and Im(phi) subset Im(psi), then G -> H can be constructed
=#

@doc Markdown.doc"""
    lift(phi::Map, psi::Map) -> Map
Given $\phi: G\to F$ and $\psi:H \to F$ s.th. $\Im(\phi) \subseteq \Im(\psi)$
return the map $G\to H$ to make the diagram commute.
"""
function lift(phi::Map, psi::Map)
  x = [haspreimage(psi, image(phi, g)) for g = gens(domain(phi))]
  @assert all(t -> t[1], x)
  return hom(domain(phi), domain(psi), [t[2] for t = x])
end

@doc Markdown.doc"""
    zero_map(G::GrpAbFinGen) -> Map
Create the map $G \to \{0\}$.
"""
function zero_map(G::GrpAbFinGen)
  return zero_map(G, zero_obj(G))
end
function zero_map(G::GrpAbFinGen, H::GrpAbFinGen)
  return hom(G, H, [H[0] for i=1:ngens(G)])
end


######################################################################
#
# complex/ free resolution
#
######################################################################

@attributes mutable struct ChainComplex{T}
  maps::Vector{<:Map}
  direction::Symbol
  exact::Vector{Bool}
  start::Int

  function ChainComplex(A::S; check::Bool = true, direction:: Symbol = :left, start::Int = 0) where {S <:Vector{<:Map{<:T, <:T}}} where {T}
    @assert length(A) > 0
    if check
      @assert all(i-> iszero(A[i]*A[i+1]), 1:length(A)-1)
    end
    r = new{T}()
    r.maps = A
    r.start = start
    r.direction = direction
    return r
  end
  function ChainComplex(X::Type, A::S; check::Bool = true, direction:: Symbol = :left, start::Int = 0) where {S <:Vector{<:Map}}
    @assert length(A) > 0
    if check
      @assert all(i-> iszero(A[i]*A[i+1]), 1:length(A)-1)
    end
    r = new{X}()
    r.maps = A
    r.direction = direction
    r.start = start
    return r
  end

end

isfree_resolution(C::ChainComplex) = get_attribute(C, :show) === free_show

function length(C::ChainComplex)
  isfree_resolution(C) || error("must be a free-resolution")
  return length(C.maps)
end

function Base.range(C::ChainComplex) 
  len = length(C.maps)
  start = C.start
  if ischain_complex(C)
    return start+len:-1:start
  else
    return start:start+len
  end
end

ischain_complex(C::ChainComplex) = C.direction == :left
iscochain_complex(C::ChainComplex) = C.direction == :right

function zero_obj(::GrpAbFinGen) 
  A = abelian_group([1])
  set_name!(A, "Zero")
  return A
end

function obj(C::ChainComplex, i::Int) 
  #maps are Vector M[1], M[2], ..., M[n]
  # we always have domain(M[i+1]) == codomain(M[i])
  # so ALWAYS stored running left.

  #if direction ==  :left, we have a chain_complex and
  # map[l] should be : obj[l] -> obj[l-1]
  # start is the smallest index, usually(?) 0
  # number of objetcs = number of maps + 1

  #normalize, to start with obj 0:
  i -= C.start
  if ischain_complex(C)
    i < 0 && return zero_obj(domain(C.maps[1]))
    i == 0 && return codomain(C.maps[end])
    i <= length(C.maps) && return domain(C.maps[length(C.maps)-i+1])
    return zero_obj(domain(C.maps[1]))
  end
  if iscochain_complex(C)
    i < 0 && return zero_obj(domain(C.maps[1]))
    i < length(C.maps) && return domain(C.maps[i])
    i == length(C.maps) && return codomain(C.maps[end])
    return zero_obj(domain(C.maps[1]))
  end
end

function Base.map(C::ChainComplex, i::Int) 
  r = range(C)
  if ischain_complex(C)
    i<= last(r) && return zero_map(C[i], C[i-1])
    i<=first(r) && return C.maps[length(C.maps)-i+C.start+1]
    return zero_map(C[i], C[i-1])
  end
  if iscochain_complex(C)
    i <= last(r) && return zero_map(C[i], C[i+1])
    i <= first(R) && return C.maps[i-C.start]
    return zero_map(C[i], C[i+1])
  end
end

function Base.push!(C::ChainComplex{T}, M::Map{<:T, <:T}) where {T}
  if ischain_complex(C)
    @assert codomain(C.maps[end]) == domain(M)
    push!(C.maps, M)
  else
    @assert codomain(M) == domain(C.maps[1])
    pushfirst!(C.maps, M)
  end
  set_attribute!(C, :show=>nothing)
end

Base.getindex(C::ChainComplex, i::Int) = obj(C, i)

obj_type(C::ChainComplex{T}) where {T} = T
map_type(C::ChainComplex) = eltype(C.maps)

Hecke.base_ring(::GrpAbFinGen) = ZZ

function AbstractAlgebra.get_attribute(::FlintIntegerRing, s::Symbol)
  s == :name && return "ZZ"
  error("wrong symbol used")
end

function free_show(io::IO, C::ChainComplex)
  Cn = get_attribute(C, :name)
  if Cn === nothing
    Cn = "F"
  end

  name_mod = String[]
  rank_mod = Int[]

  rng = range(C)
  if C.direction == :left
    arr = ("--", "-->")
  else
    arr = ("<--", "--")
  end

  R = Nemo.base_ring(C[first(rng)])
  R_name = get_attribute(R, :name)
  if R_name === nothing
    R_name = "$R"
  end

  for i=rng
    M = C[i]
    if get_attribute(M, :name) !== nothing
      push!(name_mod, get_attribute(M, :name))
    else
      push!(name_mod, "$R_name^$(rank(M))")
    end
    push!(rank_mod, rank(M))
  end

  io = IOContext(io, :compact => true)
  print(io, "Free resolution")
  N = get_attribute(C, :free_res)
  if N !== nothing
    print(io, " of ", N)
  end
  print(io, "\n")

  pos = 0
  pos_mod = Int[]
  for i=1:length(name_mod)
    print(io, name_mod[i])
    push!(pos_mod, pos)
    pos += length(name_mod[i])
    if i < length(name_mod)
      print(io, arr[1], arr[2], " ")
      pos += length(arr[1]) + length(arr[2]) + 1
    end
  end
  print(io, "\n")
  len = 0
  for i=1:length(name_mod)
    if i>1
      print(io, " "^(pos_mod[i] - pos_mod[i-1]-len))
    end
    print(io, rank_mod[i])
    len += length("$(rank_mod[i])")
  end
  print(io, "\n")
end


function show(io::IO, C::ChainComplex)
  @show_name(io, C)
  @show_special(io, C)

  Cn = get_attribute(C, :name)
  if Cn === nothing
    Cn = "C"
  end
  name_mod = String[]
  name_map = String[]
  mis_map = Tuple{Int, <:Map}[]
  mis_mod = Tuple{Int, <:Any}[]

  rng = range(C)
  if C.direction == :left
    arr = ("--", "-->")
    dir = 1
  else
    arr = ("<--", "--")
    dir = 0
  end

  for i=rng
    M = obj(C, i)
    if get_attribute(M, :name) !== nothing
      push!(name_mod, get_attribute(M, :name))
    else
      push!(name_mod, "$(Cn)_$i")
      push!(mis_mod, (i, M))
    end
  end

  io = IOContext(io, :compact => true)
  for i=rng
    if i == first(rng)
      print(io, name_mod[i+dir])
      continue
    end
    print(io, " ", arr[1], arr[2], " ", name_mod[i+dir])
  end
  if length(mis_mod) > 0 # || length(mis_map) > 0
    print(io, "\nwhere:\n")
    for (i, M) = mis_mod
      print(io, "\t$(Cn)_$i = ", M, "\n")
    end
#    for (i, phi) = mis_map
#      print(io, "\tphi_$i = ", phi, "\n")
#    end
  end
end

@doc Markdown.doc"""
    chain_complex(A::Map{GrpAbFinGen, GrpAbFinGen, <:Any, <:Any}...) -> ChainComplex{GrpAbFinGen}
Given maps $A_i$ s.th. $\Im(A_i) \subseteq \Kern(A_{i+1})$, this creates
the chain complex.
"""
function chain_complex(A::Map{GrpAbFinGen, GrpAbFinGen, <:Any, <:Any}...)
  return ChainComplex(collect(A))
end

function chain_complex(A::Vector{<:Map{GrpAbFinGen, GrpAbFinGen, <:Any, <:Any}})
  return ChainComplex(A)
end

Base.lastindex(C::ChainComplex) = lastindex(range(C))
function getindex(C::ChainComplex{T}, u::UnitRange) where T
  @assert iscochain_complex(C)
  return ChainComplex(T, [map(C, i) for i = u])
end

function getindex(C::ChainComplex{T}, u::StepRange) where {T}
  @assert ischain_complex(C)
  return ChainComplex(T, [map(C, i) for i = u])
end

@doc Markdown.doc"""
    isexact(C::ChainComplex) -> Bool
Tests is the complex $A_i: G_i \to G_{i+1}$
is exact, ie. if $\Im(A_i) = \Kern(A_{i+1})$.
"""
function isexact(C::ChainComplex)
  return all(i->iseq(image(C.maps[i])[1], kernel(C.maps[i+1])[1]), 1:length(C.maps)-1)
end

@doc Markdown.doc"""
    free_resolution(G::GrpAbFinGen) -> ChainComplex{GrpAbFinGen}
A free resultion for $G$, ie. a chain complex terminating in
$G \to \{0\}$ that is exact.
"""
function free_resolution(G::GrpAbFinGen)
  A = free_abelian_group(ngens(G))
  R = rels(G)
  B = free_abelian_group(nrows(R))
  h_A_G = hom(A, G, gens(G))
  h_B_A = hom(B, A, [GrpAbFinGenElem(A, R[i, :]) for i=1:ngens(B)])
  Z = zero_obj(G)
  C = chain_complex(hom(Z, B, [B[0]]), h_B_A)
  set_attribute!(C, :show => free_show, :free_res => G)
  return C, h_A_G
end

mutable struct ChainComplexMap{T} <: Map{ChainComplex{T}, ChainComplex{T}, HeckeMap, ChainComplexMap}
  header::MapHeader{ChainComplex{T}, ChainComplex{T}}
  maps::Vector{<:Map{<:T, <:T}}
  function ChainComplexMap(C::ChainComplex{T}, D::ChainComplex{T}, A::S; check::Bool = !true) where {S <: Vector{<:Map{<:T, <:T}}} where {T}
    r = new{T}()
    r.header = MapHeader(C, D)
    r.maps = A
    return r
  end
end

@doc Markdown.doc"""
    hom(C::ChainComplex{T}, D::ChainComplex{T}, phi::Map{<:T, <:T}) where {T} -> ChainComplexMap
Given chain complexes $C_i: G_i \to G_{i+1}$ and $D_i: H_i \to H_{i+1}$
as well as a map $\phi = \phi_n: G_n \to H_n$, lift $\phi$ to
the entire complex: $\phi_i: G_i \to H_i$ s.th. all squares commute.
"""
function hom(C::ChainComplex{T}, D::ChainComplex{T}, phi::Map{<:T, <:T}) where {T}
  @assert range(C) == range(D)
  @assert domain(C.maps[end]) == domain(phi)
  @assert domain(D.maps[end]) == codomain(phi)

  h = [phi]
  for i=length(C.maps)-1:-1:1
    push!(h, lift(C.maps[i]*h[end], D.maps[i]))
  end
  return ChainComplexMap(C, D, reverse(h))
end

@doc Markdown.doc"""
    hom(C::ChainComplex{T}, G::T) -> ChainComplex{T}
Given a complex $A_i: G_i \to G_{i+1}$ and a module $G$,
compute the derived complex $\hom(G_i, G)$.
"""
function hom(C::ChainComplex{T}, G::T) where {T}
  A = map_type(C)[]
  H = [hom(domain(C.maps[1]), G)]
  H = vcat(H, [hom(codomain(f), G) for f = C.maps])

  R = map_type(C)[]
  for i=1:length(C.maps)
    A = H[i+1][1] # hom(C_i+1, G)
    B = H[i][1]   # hom(C_i  , G)
    #need map from A -> B
    #   C.maps[i] : E -> D
    D = codomain(C.maps[i])
    E = domain(C.maps[i])
    #  H[2][i+1]: A -> Hom(D, G)
    #  H[2][i]  : B -> hom(E, G)
    g = elem_type(obj_type(C))[]
    for h = gens(A)
      phi = H[i+1][2](h) # D -> G
      psi = C.maps[i] * phi
      push!(g, preimage(H[i][2], psi))
    end
    push!(R, hom(A, B, g))
  end
  return ChainComplex(reverse(R))
end

@doc Markdown.doc"""
    hom(C::ChainComplex{T}, G::T) -> ChainComplex{T}
Given a complex $A_i: G_i \to G_{i+1}$ and a module $G$,
compute the derived complex $\hom(G, G_i)$.
"""
function hom(G::T, C::ChainComplex{T}) where {T}

  A = map_type(C)[]
  H = [hom(G, domain(C.maps[1]))]
  H = vcat(H, [hom(G, codomain(f)) for f = C.maps])

  R = map_type(C)[]
  for i=1:length(C.maps)
    A = H[i+1][1] # hom(G, C_i+1)
    B = H[i][1]   # hom(G, C_i)
    #need map from A -> B
    #   C.maps[i] : E -> D
    D = codomain(C.maps[i])
    E = domain(C.maps[i])
    #  H[2][i+1]: A -> Hom(G, D)
    #  H[2][i]  : B -> hom(G, E)
    g = elem_type(obj_type(C))[]
    for h = gens(B)
      phi = H[i][2](h) # G -> E
      psi = phi * C.maps[i]
      push!(g, preimage(H[i+1][2], psi))
    end
    push!(R, hom(B, A, g))
  end
  return ChainComplex(R)
end

@doc Markdown.doc"""
    homology(C::ChainComplex{GrpAbFinGen}) -> Vector{GrpAbFinGen}
Given a complex $A_i: G_i \to G_{i+1}$,
compute the homology, ie. the modules $H_i = \Kern A_{i+1}/\Im A_i$
"""
function homology(C::ChainComplex)
  H = obj_type(C)[]
  for i=1:length(C.maps)-1
    push!(H, quo(kernel(C.maps[i+1])[1], image(C.maps[i])[1])[1])
  end
  return H
end

function snake_lemma(C::ChainComplex{T}, D::ChainComplex{T}, A::Vector{<:Map{T, T}}) where {T}
  @assert length(C.maps) == length(D.maps) == 3
  @assert length(A) == 3
  @assert domain(A[1]) == obj(C,0) && codomain(A[1]) == obj(D, 1)
  @assert domain(A[2]) == obj(C,1) && codomain(A[2]) == obj(D, 2)
  @assert domain(A[3]) == obj(C,2) && codomain(A[3]) == obj(D, 3)

  ka, mka = kernel(A[1])
  kb, mkb = kernel(A[2])
  kc, mkc = kernel(A[3])
  ca, mca = cokernel(A[1])
  cb, mcb = cokernel(A[2])
  cc, mcc = cokernel(A[3])

  MT = map_type(C)
  res = MT(C)[]
  push!(res, MT(mka * map(C, 1) * inv(mkb)))
  push!(res, MT(mkb * map(C, 2) * inv(mkc)))
  #now the snake
  push!(res, MT(mkc * inv(map(C, 2)) * A[2] * inv(map(D, 2)) * mca))
  #and the boring rest
  push!(res, MT(inv(mca) * map(D, 2) * mcb))
  push!(res, MT(inv(mcb) * map(D, 3) * mcc))
  return chain_complex(res...)
end


@doc Markdown.doc"""
    tensor_product(C::ChainComplex{T}, G::T) -> ChainComplex{T}
Given a complex $A_i: G_i \to G_{i+1}$ and a module $G$,
compute the derived complex $G_i \otimes G$.
"""
function tensor_product(C::ChainComplex{T}, G::T) where {T}
  A = map_type(C)[]
  H = [tensor_product(domain(C.maps[1]), G, task  = :none)]
  H = vcat(H, [tensor_product(codomain(f), G, task = :none) for f = C.maps])

  R = map_type(C)[]
  I = identity_map(G)
  for i = 1:length(C.maps)
    push!(R, hom(H[i], H[i+1], [C.maps[i], I]))
  end
  return chain_complex(R)
end
