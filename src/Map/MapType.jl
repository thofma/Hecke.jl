###########################################################
##
## MAPS
##
## maps between residue rings of polynomials and in general
##
###########################################################

function domain(M::Map(HeckeMap))
  return M.header.domain
end

function codomain(M::Map(HeckeMap))
  return M.header.codomain
end

function image_function(f::Map(HeckeMap))
  if isdefined(f.header, :image)
    return f.header.image
  else
    return x -> image(f, x)
  end
end

function preimage_function(f::Map(HeckeMap))
  if isdefined(f.header, :preimage)
    return f.header.preimage
  else
    return x -> preimage(f, x)
  end
end

export Map

mutable struct MapCache{D, C, De, Ce}
  lim::Int

  im::Dict{De, Ce}
  imStat::Dict{De, Int}

  pr::Dict{Ce, De}
  prStat::Dict{Ce, Int}

  old_im
  old_pr

  function MapCache(dom::D, cod::C, ::Type{De}, ::Type{Ce}, lim::Int=100) where {D, C, De, Ce}
    r = new{D, C, De, Ce}()
    r.lim = lim
    r.im = Dict{De, Ce}()
    r.imStat = Dict{De, Int}()
    r.pr = Dict{Ce, De}()
    r.prStat = Dict{Ce, Int}()
    return r
  end
end

@attributes mutable struct MapHeader{D, C}
  domain::D
  codomain::C
  image
  preimage
  cache::MapCache

  function MapHeader{D, C}() where {D, C}
    z = new{D, C}()
    return z
  end

  function MapHeader{D, C}(domain::D, codomain::C) where {D, C}
    z = new{D, C}()
    z.domain = domain
    z.codomain = codomain
    return z
  end

  function MapHeader{D, C}(domain::D, codomain::C, image) where {D, C}
    z = new{D, C}()
    z.domain = domain
    z.codomain = codomain
    z.image = image
    return z
  end

  function MapHeader{D, C}(domain::D, codomain::C, image, preimage) where {D, C}
    z = new{D, C}()
    z.domain = domain
    z.codomain = codomain
    z.image = image
    z.preimage = preimage
    return z
  end
end

function MapHeader(domain::D, codomain::C) where {D, C}
  return MapHeader{D, C}(domain, codomain)
end

function MapHeader(domain::D, codomain::C, image) where {D, C}
  return MapHeader{D, C}(domain, codomain, image)
end

function MapHeader(domain::D, codomain::C, image, preimage) where {D, C}
  return MapHeader{D, C}(domain, codomain, image, preimage)
end


function preimage(f::AbstractAlgebra.Generic.CompositeMap, a)
  return preimage(f.map1, preimage(f.map2, a))
end

preimage_function(f) = a -> preimage(f, a)
image_function(f) = a -> image(f, a)

#function _compose(f, g)
#  return AbstractAlgebra.Generic.compose(g, f)
#end

#function compose(f::Map(HeckeMap){R, C}, g::Map(HeckeMap){D, R}) where {D, C, R}
#  return CompositeMap{D, C, R}(f, g)
#end

mutable struct InverseMap{D, C} <: Map{D, C, HeckeMap, InverseMap}
  header::MapHeader{D, C}
  origin::Map{C, D}

  function InverseMap{D, C}(f::Map{C, D}) where {D, C}
    z = new{D, C}()
    z.header = MapHeader(codomain(f), domain(f), preimage_function(f), image_function(f))
    z.origin = f
    return z
  end
end

function InverseMap(f::Map{C, D}) where {D, C}
  return InverseMap{D, C}(f)
end

###########################################################
# To turn a Function (method) into a map.
###########################################################

"""
    MapFromFunc(f, [g], D, C)

Creates the map `D -> C, x -> f(x)` given the callable
object `f`. If `g` is provided, it is assumed to satisfy
`f(g(x)) = x` and will be used as the preimage function.

# Example

```jldoctest
julia> F = GF(2);

julia> f = MapFromFunc(x -> F(numerator(x)) * inv(F(denominator(x))), QQ, F)
Map from
Rational field to Finite field of characteristic 2 defined by a julia-function

julia> f(QQ(1//3))
1

julia> f = MapFromFunc(x -> F(numerator(x)) * inv(F(denominator(x))), y -> QQ(lift(y)),  QQ, F)
Map from
Rational field to Finite field of characteristic 2 defined by a julia-function with inverse

julia> preimage(f, F(1))
1
```
"""
mutable struct MapFromFunc{R, T} <: Map{R, T, HeckeMap, MapFromFunc}
  header::Hecke.MapHeader{R, T}
  f
  g

  function MapFromFunc{R, T}(f, D::R, C::T) where {R, T}
    n = new{R, T}()
    n.header = Hecke.MapHeader(D, C, f)
    n.f = f
    return n
  end

  function MapFromFunc{R, T}(f, g, D::R, C::T) where {R, T}
    n = new{R, T}()
    n.header = Hecke.MapHeader(D, C, f, g)
    n.f = f
    n.g = g
    return n
  end
end

function image(f::MapFromFunc, x)
  @req parent(x) === domain(f) "Element not in the domain"
  y = f.f(x)
  @req parent(y) === codomain(f) "Image not in the codomain"
  return y
end

function preimage(f::MapFromFunc, y)
  @req parent(y) === codomain(f) "Element not in the codomain"
  x = f.g(y)
  @req parent(x) === domain(f) "Preimage not in the domain"
  return x
end

function Base.show(io::IO, M::MapFromFunc)
  @show_name(io, M)

  io = IOContext(io, :compact => true)
#  println(io, "Map from the $(M.f) julia-function")
  println(io, "Map from")
  show(io, domain(M))
  print(io, " to ")
  show(io, codomain(M))
  print(io, " defined by a julia-function")
  if isdefined(M, :g)
#    println(io, "with inverse by $(M.g)")
    print(io, " with inverse")
  end
end

function MapFromFunc(f, D, C)
  return MapFromFunc{typeof(D), typeof(C)}(f, D, C)
end

function MapFromFunc(f, g, D, C)
  return MapFromFunc{typeof(D), typeof(C)}(f, g, D, C)
end

function Base.inv(M::MapFromFunc)
  if isdefined(M, :g)
     return MapFromFunc(M.g, M.f, codomain(M), domain(M))
  else
     return MapFromFunc(x->preimage(M, x), codomain(M), domain(M))
  end
end

export MapFromFunc
