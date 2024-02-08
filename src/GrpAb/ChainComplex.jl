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

@doc raw"""
    lift(phi::Map, psi::Map) -> Map
Given $\phi: G\to F$ and $\psi:H \to F$ s.th. $\Im(\phi) \subseteq \Im(\psi)$
return the map $G\to H$ to make the diagram commute.
"""
function lift(phi::Map, psi::Map)
  x = [has_preimage_with_preimage(psi, image(phi, g)) for g = gens(domain(phi))]
  @assert all(t -> t[1], x)
  return hom(domain(phi), domain(psi), [t[2] for t = x])
end

@doc raw"""
    zero_map(G::FinGenAbGroup) -> Map
Create the map $G \to \{0\}$.
"""
function zero_map(G::FinGenAbGroup)
  return zero_map(G, zero_obj(G))
end

function zero_map(G::FinGenAbGroup, H::FinGenAbGroup)
  return hom(G, H, [H[0] for i=1:ngens(G)])
end


######################################################################
#
# complex/ free resolution
#
######################################################################

@doc raw"""
  The complex is always stored this way
```
      maps[1]   maps[2]
    * ------> * ------> * ....
```

There are logically 2 types of complexes
 - chain
 - cochain
(stored in `typ` (`type` cannot be used as it is a keyword)

The type determines, jointly with `seed` the homological, external,
numbering of the maps and object. `seed` always stores the logically
minimal object index (in the sense of homological degree)

# Chain Complex
`typ == :chain`

The definition is `d_i(d_i+1(x)) = 0` where `d_i` are the (logically) numbered
maps (differentials). The corresponding objects `M_i` are defined via

  `d_i : M_i -> M_i-1`

Thus the minimal object (index) is the image of the last map =>
  `maps[end] = d_seed+1`
  `codomain(maps[end]) = M_seed`
  `domain(maps[1]) = M_(seed+length(maps))`

# CoChain Complex
`typ == :cochain`

The definition is `d_i+1(d_i(x)) = 0` and

  `d_i : M_i -> M_i+1`

The minimal object thus is `domain(maps[1]) = M_seed`,
the largest thus `codomain(maps[end]) = M_(seed + length(maps))`

# Access

## range
the object - index - range is either
 - `(seed + length):-1:seed`     (chain complex)
 - `seed:(seed + length(maps))`  (cochain complex)

## map
  map(C, i) =
  - `maps[length - (i - s)]`      (chain)
  - `maps[i-s]`                   (cochain)

## obj
  `obj(C, i) = domain(map(C, i))` in both cases
  BUT
at the end, the last object is the codomain of the last map...

"""
@attributes mutable struct ComplexOfMorphisms{T}
  maps      ::Vector{<:Map}
  seed      ::Int
  typ       ::Symbol # :chain or :cochain
  exact     ::Vector{Bool}
  complete  ::Bool
  fill     #::Function: fill(C, i) creates the i-th map

  function ComplexOfMorphisms(A::S; check::Bool = true, typ:: Symbol = :chain, seed::Int = 0) where {S <:Vector{<:Map{<:T, <:T}}} where {T}
    return ComplexOfMorphisms(T, A, check = check, typ = typ, seed = seed)
  end

  function ComplexOfMorphisms(X::Type, A::S; check::Bool = true, typ:: Symbol = :chain, seed::Int = 0) where {S <:Vector{<:Map}}
    @assert length(A) > 0
    @assert typ in [:chain, :cochain]
    if check
      @assert all(i-> iszero(A[i]*A[i+1]), 1:length(A)-1)
    end
    r = new{X}()
    r.maps = A
    r.seed = seed
    r.typ = typ
    r.fill = function(C::ComplexOfMorphisms, i::Int)
      error("complex cannot extend")
    end
    return r
  end
end

is_free_resolution(C::ComplexOfMorphisms) = get_attribute(C, :show) === free_show

function Base.range(C::ComplexOfMorphisms)
  return object_range(C)
end

function object_range(C::ComplexOfMorphisms)
  s = C.seed
  l = length(C.maps)
  if is_chain_complex(C)
    return (s+l):-1:s
  else
    return s:(s+ l)
  end
end

function map_range(C::ComplexOfMorphisms)
  r = object_range(C)
  if is_chain_complex(C)
    return first(r):step(r):last(r)+1
  else
    return first(r):last(r)-1
  end
end

is_chain_complex(C::ComplexOfMorphisms) = C.typ == :chain
is_cochain_complex(C::ComplexOfMorphisms) = C.typ == :cochain

function zero_obj(::FinGenAbGroup)
  A = abelian_group([1])
  set_name!(A, "Zero")
  return A
end

function obj(C::ComplexOfMorphisms, i::Int)
  s = C.seed
  l = length(C.maps)
  r = object_range(C)
  if is_cochain_complex(C)
    if i == first(r)
      return domain(C.maps[1])
    end
    if i in r
      return codomain(C.maps[i-s])
    end
  else
    if i == last(r)
      return codomain(C.maps[end])
    end
    if i in r
      return domain(C.maps[s+l-i+1])
    end
  end
  f = C.fill(C, i)
  return domain(f)
end

function Base.map(C::ComplexOfMorphisms, i::Int)
  s = C.seed
  l = length(C.maps)
  r = map_range(C)
  if !(i in r)
    return C.fill(C, i)
  end
  if is_cochain_complex(C)
    return C.maps[i-s+1]
  end
  if is_chain_complex(C)
    return C.maps[s+l-i+1]
  end
end

function grp_ab_fill(C::ComplexOfMorphisms, i)
  if C.complete
    error("cannot be extended")
  end
  error("ndy - not done yet")
  start = C.start
  if is_cochain_complex(C)
    if haskey(C.maps, i-start)
      return C.maps[i-start]
    end
    #map needs to be i -> i+1
    #need to check if the objects are already there...
    #obj[i] can be domain of map[i] (missing) or
    #              codomain map[i-1]
    new_so = false
    if haskey(C.maps, i-1-start)
      so = codomain(C.maps[i-1-start])
      new_so = order(so) != 1
    else
      so = zero_obj(abelian_group([1]))
    end
    #now for obj[i+1], the codmain for the map:
    if haskey(C.maps, i+1-start)
      ta = domain(C[i+1-start])
      new_ta = order(ta) != 1
    else
      ta = zero_obj(abelian_group([1]))
    end
    if new_ta && new_so
      error("cannot construct the hom, not unique")
    end
    C.maps[i-start] = hom(so, ta, [zero(ta) for i=1:ngens(so)])
    return C.maps[i-start]
  end
  if is_chain_complex(C)
    if haskey(C.maps, start-i)
      return C.maps[start - i]
    end
    #map needs to be i -> i-1
    #need to check if the objects are already there...
    #obj[i] can be domain of map[i] (missing) or
    #              codomain map[i+1]
    new_so = false
    if haskey(C.maps, start-(i+1))
      so = domain(C.maps[start-i-1])
      new_so = order(so) != 1
    else
      so = zero_obj(abelian_group([1]))
    end
    #now for obj[i-1], the codmain for the map:
    new_ta = false
    if haskey(C.maps, start-i+1)
      ta = domain(C[start-i+1])
      new_ta = order(ta) != 1
    else
      ta = zero_obj(abelian_group([1]))
    end
    if new_ta && new_so
      error("cannot construct the hom, not unique")
    end
    C.maps[start-i] = hom(so, ta, [zero(ta) for i=1:ngens(so)])
    return C.maps[start-i]
  end
end

function Base.push!(C::ComplexOfMorphisms{T}, M::Map{<:T, <:T}) where {T}
  @assert !C.complete #otherwise makes no sense.
  #talking to Wolfram:
  # push! always adds on the right
  # pushfirst! on the left
  # thus push always extends the range at the end,
  #      pushfirst at the start
  #in terms of the map array:
  # push for chain:
  #  end, seed goes down
  # push for cochain:
  #  start, seed stable
  # pushfirst chain:
  #  start, seed stable
  # pushfirst, cochain
  #  end, seed goes down
  if is_chain_complex(C)
    @assert codomain(C.maps[end]) == domain(M)
    push!(C.maps, M)
    C.seed -= 1
  else
    @assert codomain(M) == domain(C.maps[1])
    pushfirst!(C.maps, M)
  end
  set_attribute!(C, :show=>nothing)
end

function Base.pushfirst!(C::ComplexOfMorphisms{T}, M::Map{<:T, <:T}) where {T}
  @assert !C.complete #otherwise makes no sense.
  if is_chain_complex(C)
    @assert domain(C.maps[1]) == codomain(M)
    pushfirst!(C.maps, M)
  else
    @assert domain(M) == codomain(C.maps[end])
    push!(C.maps, M)
    C.seed -= 1
  end
  set_attribute!(C, :show=>nothing)
end

function shift(C::ComplexOfMorphisms{T}, n::Int) where T
  if iseven(n)
    ComplexOfMorphisms(T, copy(C.maps), seed = C.seed+n, typ = C.typ)
  else
    ComplexOfMorphisms(T, [-f for f = C.maps], seed = C.seed+n, typ = C.typ)
  end
end

function length(C::ComplexOfMorphisms)
  is_free_resolution(C) || error("must be a free-resolution")
  return length(C.maps)
end

Base.getindex(C::ComplexOfMorphisms, i::Int) = obj(C, i)

obj_type(C::ComplexOfMorphisms{T}) where {T} = T
map_type(C::ComplexOfMorphisms) = valtype(C.maps)

Hecke.base_ring(::FinGenAbGroup) = ZZ

function pres_show(io::IO, C::ComplexOfMorphisms)
  name_mod = String[]
  rank_mod = Int[]

  rng = range(C)
  arr = ("<--", "--")

  R = Nemo.base_ring(C[first(rng)])
  R_name = get_name(R)
  if isnothing(R_name)
    R_name = "$R"
  end

  for i=reverse(rng)
    M = C[i]
    if i == -1 #the object that is presented
      M_name = get_name(M)
      if isnothing(M_name)
        M_name = "M"
      end
      push!(name_mod, M_name)
      push!(rank_mod, 0)
    else
      M_name = get_name(M)
      if isnothing(M_name)
        M_name = "$R_name^$(rank(M))"
      end
      push!(name_mod, M_name)
      push!(rank_mod, rank(M))
    end
  end

  io = IOContext(io, :compact => true)
#  print(io, "Presentation")
#  N = get_attribute(C, :free_res)
#  if N !== nothing
#    print(io, " of ", N)
#  end
#  print(io, "\n")

  pos = 0
  pos_mod = Int[]

  for i=1:length(name_mod)
    print(io, name_mod[i])
    push!(pos_mod, pos)
    pos += length(name_mod[i])
    if i < length(name_mod)
      print(io, " ", arr[1], arr[2], " ")
      pos += length(arr[1]) + length(arr[2]) + 2
    end
  end
#  print(io, "\n")
#  len = 0
#  for i=1:length(name_mod)
#    if i>1
#      print(io, " "^(pos_mod[i] - pos_mod[i-1]-len +1))
#    end
#    print(io, rng[i])
#    len += length("$(rng[i])")
#  end
#  print(io, "\n")
end


function free_show(io::IO, C::ComplexOfMorphisms)
  name_mod = String[]
  rank_mod = Int[]

  rng = range(C)
  rng = first(rng)-1:-1:0
  arr = ("<--", "--")

  R = Nemo.base_ring(C[first(rng)])
  R_name = get_name(R)
  if R_name === nothing
    R_name = "$R"
  end

  for i=reverse(rng)
    M = C[i]
    M_name = get_name(M)
    if M_name === nothing
      M_name = "$R_name^$(rank(M))"
    end
    push!(name_mod, M_name)
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
      print(io, " ", arr[1], arr[2], " ")
      pos += length(arr[1]) + length(arr[2]) + 2
    end
  end

  print(io, "\n")
  len = 0
  for i=1:length(name_mod)
    if i>1
      print(io, " "^(pos_mod[i] - pos_mod[i-1]-len))
    end
    print(io, reverse(rng)[i])
    len = length("$(reverse(rng)[i])")
  end
#  print(io, "\n")
end

function show(io::IO, C::ComplexOfMorphisms)
  @show_name(io, C)
  @show_special(io, C)

  Cn = get_name(C)
  if Cn === nothing
    Cn = "C"
  end
  name_mod = Dict{Int, String}()
  name_map = Dict{Int, String}()
  mis_map = Tuple{Int, <:Map}[]
  mis_mod = Tuple{Int, <:Any}[]

  rng = range(C)
  arr = ("<--", "--")
  if is_chain_complex(C)
    dir = 1
  else
    dir = 0
  end

  for i=rng
    M = obj(C, i)
    if is_chain_complex(C)
      name_mod[i] = "$(Cn)_$i"
    else
      name_mod[i] = "$(Cn)^$i"
    end
  end

  io = IOContext(io, :compact => true)
  for i=reverse(rng)
    if i == last(rng)
      print(io, name_mod[i])
      continue
    end
    print(io, " ", arr[1], arr[2], " ", name_mod[i])
  end
  if length(mis_mod) > 0 # || length(mis_map) > 0
    print(io, "\nwhere:\n")
    for (i, M) = mis_mod
      print(io, "\t$(name_mod[i]) = ", M, "\n")
    end
  end
end

@doc raw"""
    chain_complex(A::Map{FinGenAbGroup, FinGenAbGroup, <:Any, <:Any}...) -> ComplexOfMorphisms{FinGenAbGroup}
Given maps $A_i$ s.th. $\Im(A_i) \subseteq \Kern(A_{i+1})$, this creates
the chain complex.
"""
function chain_complex(A::Map{FinGenAbGroup, FinGenAbGroup, <:Any, <:Any}...; seed::Int = 0)
  return ComplexOfMorphisms(collect(A), seed = seed, typ = :chain)
end

function chain_complex(A::Vector{<:Map{FinGenAbGroup, FinGenAbGroup, <:Any, <:Any}}; seed::Int = 0)
  return ComplexOfMorphisms(A, seed = seed, typ = :chain)
end
function cochain_complex(A::Map{FinGenAbGroup, FinGenAbGroup, <:Any, <:Any}...; seed::Int = 0)
  return ComplexOfMorphisms(collect(A), seed = seed, typ = :cochain)
end

@doc raw"""
    chain_complex(A::Map{FinGenAbGroup, FinGenAbGroup, <:Any, <:Any}...) -> ComplexOfMorphisms{FinGenAbGroup}
Given maps $A_i$ s.th. $\Im(A_i) \subseteq \Kern(A_{i+1})$, this creates
the cochain complex.
The logical indexing and the printing for chain and cochain complexes differs.
See `Hecke.ComplexOfMorphisms` for details.
"""
function cochain_complex(A::Vector{<:Map{FinGenAbGroup, FinGenAbGroup, <:Any, <:Any}}; seed::Int = 0)
  return ComplexOfMorphisms(A, seed = seed, typ = :cochain)
end

Base.lastindex(C::ComplexOfMorphisms) = lastindex(range(C))
function getindex(C::ComplexOfMorphisms{T}, u::AbstractUnitRange) where T
  @assert is_cochain_complex(C)
  return ComplexOfMorphisms(T, [map(C, i) for i = u])
end

function getindex(C::ComplexOfMorphisms{T}, u::StepRange) where {T}
  @assert is_chain_complex(C)
  return ComplexOfMorphisms(T, [map(C, i) for i = u])
end

#TODO: Why?
# what is the intend, the specs? In particular: seed/ start?
function extract_map_range(C::ComplexOfMorphisms{T}, u::AbstractUnitRange) where T
  @assert is_cochain_complex(C)
  return ComplexOfMorphisms(T, [map(C, i) for i in u]; start=C.start, direction=:right)
end

function extract_map_range(C::ComplexOfMorphisms{T}, u::StepRange) where T
  @assert is_chain_complex(C)
  return ComplexOfMorphisms(T, [map(C, i) for i in u]; start=C.start-length(C)-1)
end

function extract_object_range(C::ComplexOfMorphisms{T}, u::AbstractUnitRange) where T
  @assert is_cochain_complex(C)
  return ComplexOfMorphisms(T, [map(C, i) for i in u if i != first(u)]; start=C.start, direction=:right)
end

function extract_object_range(C::ComplexOfMorphisms{T}, u::StepRange) where T
  @assert is_chain_complex(C)
  return ComplexOfMorphisms(T, [map(C, i) for i in u if i != last(u)]; start=C.start-length(C.maps)-1)
end

@doc raw"""
    is_exact(C::ComplexOfMorphisms) -> Bool
Tests is the complex $A_i: G_i \to G_{i+1}$
is exact, ie. if $\Im(A_i) = \Kern(A_{i+1})$.
"""
function is_exact(C::ComplexOfMorphisms)
  #should be cached and stored. Difficult for push and friends
  return all(i->is_eq(image(C.maps[i])[1], kernel(C.maps[i+1])[1]), 1:length(C.maps)-1)
end

@doc raw"""
    free_resolution(G::FinGenAbGroup) -> ComplexOfMorphisms{FinGenAbGroup}
A free resolution for $G$, ie. a chain complex terminating in
$G \to \{0\}$ that is exact.
"""
function free_resolution(G::FinGenAbGroup)
  A = free_abelian_group(ngens(G))
  R = rels(G)
  B = free_abelian_group(nrows(R))
  h_A_G = hom(A, G, gens(G))
  h_B_A = hom(B, A, [FinGenAbGroupElem(A, R[i, :]) for i=1:ngens(B)])
  Z = zero_obj(G)
  C = chain_complex(hom(Z, B, [B[0]]), h_B_A)
  set_attribute!(C, :show => free_show, :free_res => G)
  return C, h_A_G
end

mutable struct ComplexOfMorphismsMap{T} <: Map{ComplexOfMorphisms{T}, ComplexOfMorphisms{T}, HeckeMap, ComplexOfMorphismsMap}
  header::MapHeader{ComplexOfMorphisms{T}, ComplexOfMorphisms{T}}
  maps::Dict{Int, <:Map{<:T, <:T}}
  function ComplexOfMorphismsMap(C::ComplexOfMorphisms{T}, D::ComplexOfMorphisms{T}, A::S; check::Bool = !true) where {S <: Dict{Int, <:Map{<:T, <:T}}} where {T}
    r = new{T}()
    r.header = MapHeader(C, D)
    r.maps = A
    return r
  end
end

#=
@doc raw"""
    hom(C::ComplexOfMorphisms{T}, D::ComplexOfMorphisms{T}, phi::Map{<:T, <:T}) where {T} -> ComplexOfMorphismsMap
Given chain complexes $C_i: G_i \to G_{i+1}$ and $D_i: H_i \to H_{i+1}$
as well as a map $\phi = \phi_n: G_n \to H_n$, lift $\phi$ to
the entire complex: $\phi_i: G_i \to H_i$ s.th. all squares commute.
"""
function hom(C::ComplexOfMorphisms{T}, D::ComplexOfMorphisms{T}, phi::Map{<:T, <:T}) where {T}
  @assert range(C) == range(D)
  @assert domain(C.maps[end]) == domain(phi)
  @assert domain(D.maps[end]) == codomain(phi)

  h = Dict{Int, Map{T, T}}()
  h[0] = phi
  last_h = phi
  for i=length(C.maps)-1:-1:1
    h[i] = last_h = lift(C.maps[i]*last_h, D.maps[i])
  end
  return ComplexOfMorphismsMap(C, D, h)
end

@doc raw"""
    hom(C::ComplexOfMorphisms{T}, G::T) -> ComplexOfMorphisms{T}
Given a complex $A_i: G_i \to G_{i+1}$ and a module $G$,
compute the derived complex $\hom(G_i, G)$.
"""
function hom(C::ComplexOfMorphisms{T}, G::T) where {T}
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
  return ComplexOfMorphisms(reverse(R))
end

@doc raw"""
    hom(C::ComplexOfMorphisms{T}, G::T) -> ComplexOfMorphisms{T}
Given a complex $A_i: G_i \to G_{i+1}$ and a module $G$,
compute the derived complex $\hom(G, G_i)$.
"""
function hom(G::T, C::ComplexOfMorphisms{T}) where {T}

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
  return ComplexOfMorphisms(R)
end

@doc raw"""
    homology(C::ComplexOfMorphisms{FinGenAbGroup}) -> Vector{FinGenAbGroup}
Given a complex $A_i: G_i \to G_{i+1}$,
compute the homology, ie. the modules $H_i = \Kern A_{i+1}/\Im A_i$
"""
function homology(C::ComplexOfMorphisms)
  H = obj_type(C)[]
  for i=1:length(C.maps)-1
    push!(H, quo(kernel(C.maps[i+1])[1], image(C.maps[i])[1])[1])
  end
  return H
end

function snake_lemma(C::ComplexOfMorphisms{T}, D::ComplexOfMorphisms{T}, A::Vector{<:Map{T, T}}) where {T}
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


@doc raw"""
    tensor_product(C::ComplexOfMorphisms{T}, G::T) -> ComplexOfMorphisms{T}
Given a complex $A_i: G_i \to G_{i+1}$ and a module $G$,
compute the derived complex $G_i \otimes G$.
"""
function tensor_product(C::ComplexOfMorphisms{T}, G::T) where {T}
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

=#
