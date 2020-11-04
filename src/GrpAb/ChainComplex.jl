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
  Z = abelian_group([1])
  set_name!(Z, "Zero")
  return hom(G, Z, [Z[0] for i=1:ngens(G)])
end

######################################################################
#
# complex/ free resolution
#
######################################################################
function iszero(h::T) where {T <: Map{<:GrpAbFinGen, <:GrpAbFinGen}}
  return all(x -> iszero(h(x)), gens(domain(h)))
end

mutable struct ChainComplex{T}
  @declare_other
  maps::Array{<:Map, 1}
  direction::Symbol
  exact::Array{Bool, 1}
  function ChainComplex(A::S; check::Bool = true, direction:: Symbol = :left) where {S <:Array{<:Map{<:T, <:T}, 1}} where {T}
    if check
      @assert all(i-> iszero(A[i]*A[i+1]), 1:length(A)-1)
    end
    r = new{T}()
    r.maps = A
    r.direction = direction
    return r
  end
  function ChainComplex(X::Type, A::S; check::Bool = true, direction:: Symbol = :left) where {S <:Array{<:Map, 1}}
    if check
      @assert all(i-> iszero(A[i]*A[i+1]), 1:length(A)-1)
    end
    r = new{X}()
    r.maps = A
    r.direction = direction
    return r
  end

end

length(C::ChainComplex) = length(C.maps)
Base.map(C::ChainComplex, i::Int) = C.maps[i]
obj(C::ChainComplex, i::Int) = (i==0 ? domain(C.maps[1]) : codomain(C.maps[i]))

obj_type(C::ChainComplex{T}) where {T} = T
map_type(C::ChainComplex) = eltype(C.maps)

function show(io::IO, C::ChainComplex)
  @show_name(io, C)
  @show_special(io, C)

  Cn = get_special(C, :name)
  if Cn === nothing
    Cn = "C"
  end
  name_mod = String[]
  name_map = String[]
  mis_map = Tuple{Int, <:Map}[]
  mis_mod = Tuple{Int, <:Any}[]

  if C.direction == :left
    rng = 0:length(C)
    arr = ("--", "-->")
    dir = 1
  else
    rng = length(C)+1:-1:1
    arr = ("<--", "--")
    dir = 0
  end

  for i=1:length(C)
    phi = map(C, i)
    if get_special(phi, :name) !== nothing
      push!(name_map, get_special(phi, :name))
    else
      push!(name_map, "")
      push!(mis_map, (i, phi))
    end
  end
  for i=0:length(C)
    M = obj(C, i)
    if get_special(M, :name) !== nothing
      push!(name_mod, get_special(M, :name))
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
    if name_map[i] != ""
      print(io, " ", arr[1], " ", name_map[i], " ", arr[2], " ", name_mod[i+dir])
    else
      print(io, " ", arr[1], arr[2], " ", name_mod[i+dir])
    end
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

function chain_complex(A::Array{<:Map{GrpAbFinGen, GrpAbFinGen, <:Any, <:Any}, 1})
  return ChainComplex(A)
end

Base.lastindex(C::ChainComplex) = length(C)
getindex(C::ChainComplex{T}, u::UnitRange) where {T} = ChainComplex(T, C.maps[u], check = false)

@doc Markdown.doc"""
    isexact(C::ChainComplex) -> Bool
Tests is the complex $A_i: G_i \to G_{i+1}$ 
is exact, ie. if $\Im(A_i) = \Kern(A_{i+1})$.
"""
function isexact(C::ChainComplex)
  return all(i->iseq(image(C.maps[i])[1], kernel(C.maps[i+1])[1]), 1:length(C)-1)
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
  Z = abelian_group(Int[1])
  set_name!(Z, "Zero")
  return chain_complex(hom(Z, B, [B[0]]), h_B_A, h_A_G, hom(G, Z, [Z[0] for i = 1:ngens(G)]))
end

mutable struct ChainComplexMap{T} <: Map{ChainComplex{T}, ChainComplex{T}, HeckeMap, ChainComplexMap}
  header::MapHeader{ChainComplex{T}, ChainComplex{T}}
  maps::Array{<:Map{<:T, <:T}, 1}
  function ChainComplexMap(C::ChainComplex{T}, D::ChainComplex{T}, A::S; check::Bool = !true) where {S <: Array{<:Map{<:T, <:T}, 1}} where {T}
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
  @assert length(C) == length(D)
  @assert domain(C.maps[end]) == domain(phi)
  @assert domain(D.maps[end]) == codomain(phi)

  h = [phi]
  for i=length(C)-1:-1:1
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
  for i=1:length(C)
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
  for i=1:length(C)
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
    homology(C::ChainComplex{GrpAbFinGen}) -> Array{GrpAbFinGen, 1}
Given a complex $A_i: G_i \to G_{i+1}$, 
compute the homology, ie. the modules $H_i = \Kern A_{i+1}/\Im A_i$
"""
function homology(C::ChainComplex)
  H = obj_type(C)[]
  for i=1:length(C)-1
    push!(H, quo(kernel(C.maps[i+1])[1], image(C.maps[i])[1])[1])
  end
  return H
end

function snake_lemma(C::ChainComplex{T}, D::ChainComplex{T}, A::Array{<:Map{T, T}, 1}) where {T}
  @assert length(C) == length(D) == 3
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
  for i = 1:length(C)
    push!(R, hom(H[i], H[i+1], [C.maps[i], I]))
  end
  return chain_complex(R)
end
