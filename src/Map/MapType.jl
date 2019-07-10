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

  old_im::Function
  old_pr::Function

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

mutable struct MapHeader{D, C}
  domain::D
  codomain::C
  image::Function
  preimage::Function
  cache::MapCache
  @declare_other

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

  function MapHeader{D, C}(domain::D, codomain::C, image::Function) where {D, C}
    z = new{D, C}()
    z.domain = domain
    z.codomain = codomain
    z.image = image
    return z
  end

  function MapHeader{D, C}(domain::D, codomain::C, image::Function, preimage::Function) where {D, C}
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

function MapHeader(domain::D, codomain::C, image::Function) where {D, C}
  return MapHeader{D, C}(domain, codomain, image)
end

function MapHeader(domain::D, codomain::C, image::Function, preimage::Function) where {D, C}
  return MapHeader{D, C}(domain, codomain, image, preimage)
end

# this type represents a -> f(g(a))
#mutable struct CompositeMap{D, C, R} <: Map{D, C, HeckeMap, CompositeMap}
#  header::MapHeader{D, C}
#  f::Map{R, C}
#  g::Map{D, R}
#
#  function CompositeMap{D, C, R}(f::Map, g::Map) where {D, C, R}
#  ##CF should be function CompositeMap(f::Map{R, C}, g::Map{D, R})
#  ## but that seems to not work:
#  # U, m = UnitGroup(ResidueRing(FlintZZ, 2^9));n
#  # q, mq = Hecke.quo(U, [preimage(m, codomain(m)(fmpz(-1)))])
#  # z = Hecke.compose(m, inv(mq))
#  # btw: m*inv(mq) also fails.
#
#
#    domain(f) == codomain(g) || throw("maps not compatible")
#    z = new{D, C, R}()
#    z.f = f
#    z.g = g
#
#    image = function(x)#x::elem_type(domain(z)))
#      parent(x) != domain(g) && error("Element not in domain of map")
#      return f(g(x))::elem_type(codomain(z))
#    end
#
#    if isdefined(f.header, :preimage) && isdefined(g.header, :preimage)
#      _preimage = function(x)#x::elem_type(codomain(z)))
#        return preimage(g, preimage(f, x))::elem_type(domain(z))
#      end
#      z.header = MapHeader(domain(g), codomain(f), image, _preimage)
#    else
#      z.header = MapHeader(domain(g), codomain(f), image)
#    end
#
#    return z
#  end
#end

#function *(f::Map{R, C}, g::Map{D, R}) where {D, C, R}
#  println("======")
#  println(stacktr()[1:2])
#  return CompositeMap{D, C, R}(f, g)
#end

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
mutable struct MapFromFunc{R, T} <: Map{R, T, HeckeMap, MapFromFunc}
  header::Hecke.MapHeader{R, T}
  f::Function
  g::Function

  function MapFromFunc{R, T}(f::Function, D::R, C::T) where {R, T}
    n = new{R, T}()
    n.header = Hecke.MapHeader(D, C, x-> f(x))
    n.f = f
    return n
  end

  function MapFromFunc{R, T}(f::Function, g::Function, D::R, C::T) where {R, T}
    n = new{R, T}()
    n.header = Hecke.MapHeader(D, C, x-> f(x), y->g(y))
    n.f = f
    n.g = g
    return n
  end
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
    println(io, " with inverse")
  end
end

function MapFromFunc(f::Function, D, C)
  return MapFromFunc{typeof(D), typeof(C)}(f, D, C)
end

function MapFromFunc(f::Function, g::Function, D, C)
  return MapFromFunc{typeof(D), typeof(C)}(f, g, D, C)
end

export MapFromFunc


