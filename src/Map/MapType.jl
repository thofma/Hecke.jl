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

export Map, CoerceMap, ResidueRingPolyMap

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

function MapHeader(domain::D, codomain::C, image::Function) where {D, C}
  return MapHeader{D, C}(domain, codomain, image)
end

function MapHeader(domain::D, codomain::C, image::Function, preimage::Function) where {D, C}
  return MapHeader{D, C}(domain, codomain, image, preimage)
end

# this type represents a -> f(g(a))
mutable struct CompositeMap{D, C, R} <: Map{D, C, HeckeMap, CompositeMap}
  header::MapHeader{D, C}
  f::Map{R, C}
  g::Map{D, R}

  function CompositeMap{D, C, R}(f::Map, g::Map) where {D, C, R}
  ##CF should be function CompositeMap(f::Map{R, C}, g::Map{D, R})
  ## but that seems to not work:
  # U, m = UnitGroup(ResidueRing(FlintZZ, 2^9));n
  # q, mq = Hecke.quo(U, [preimage(m, codomain(m)(fmpz(-1)))])
  # z = Hecke.compose(m, inv(mq))
  # btw: m*inv(mq) also fails.


    domain(f) == codomain(g) || throw("maps not compatible")
    z = new{D, C, R}()
    z.f = f
    z.g = g

    image = function(x)#x::elem_type(domain(z)))
      parent(x) != domain(g) && error("Element not in domain of map")
      return f(g(x))::elem_type(codomain(z))
    end

    if isdefined(f.header, :preimage) && isdefined(g.header, :preimage)
      _preimage = function(x)#x::elem_type(codomain(z)))
        return preimage(g, preimage(f, x))::elem_type(domain(z))
      end
      z.header = MapHeader(domain(g), codomain(f), image, _preimage)
    else
      z.header = MapHeader(domain(g), codomain(f), image)
    end

    return z
  end
end

function *(f::Map{R, C}, g::Map{D, R}) where {D, C, R}
  return CompositeMap{D, C, R}(f, g)
end

function compose(f::Map(HeckeMap){R, C}, g::Map(HeckeMap){D, R}) where {D, C, R}
  return CompositeMap{D, C, R}(f, g)
end

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

mutable struct ResidueRingPolyMap{D, C, T} <: Map{D, C, HeckeMap, ResidueRingPolyMap}
  header::MapHeader{D, C}
  gen_image::Generic.Res{T}
  coeff_map::Map # can be missing if domain and codomain have the same
                 # base_ring(base_ring())
  function ResidueRingPolyMap{D, C, T}(domain::D, codomain::C, gen_image::Generic.Res{T}, coeff_map::Map) where {D, C, T}
    z = new{D, C, T}()
    z.gen_image = gen_image
    z.coeff_map = coeff_map

    image = function(a::Generic.Res)
      #a should be in the domain of M...
      I = codomain(0)
      for i in degree(a.data):-1:0
        I = I*z.gen_image + z.coeff_map(coeff(a.data, i))
      end
      return I::elem_type(C)
    end
    
    # I need to call preimage in _preimage
    _preimage = function(a::Generic.Res)
      R = codomain
      parent(a) == R || throw("mixed rings in preimage")
      g = gens(domain)
      im_gen = map(z, g) # apply x -> z(x) to the generatotrs ## possibly should be cached and stored
          ## need to write the elements in a matrix, solve the eqn for a
      Mt = zero_matrix(base_ring(base_ring(R)), degree(R.modulus), degree(R.modulus))

      for i=1:degree(R.modulus)
        elem_to_mat_row!(Mt, i, im_gen[i])
      end
      b = zero_matrix(base_ring(base_ring(R)), 1, degree(R.modulus))
      elem_to_mat_row!(b, 1, a)
      s = solve_rational(Mt', b') # why, oh why is solve operating on columns????
      # This is the worst
      if isa(s, Tuple) ## again, why, oh why is solve doing things differently
                   ## over rings than fields?
        s = s[1] * inv(s[2]) # all rings here (type) are actually fields (math)
      end
      
      s = sum([preimage(z.coeff_map, s[i,1])*g[i] for i=1:length(g)])
      @assert parent(s) == domain
      return s::elem_type(domain)
    end

    z.header = MapHeader(domain, codomain, image, _preimage)
    return z
  end

  function ResidueRingPolyMap{D, C, T}(domain::D, codomain::C, gen_image::Generic.Res{T}) where {D, C, T}
    z = new{D, C, T}()
    z.gen_image = gen_image

    image = function(a::Generic.Res)
      I = z.codomain(0)
      for i in degree(a.data):-1:0
        I = I*z.gen_image + coeff(a.data, i)
      end
      return I::elem_type(C)
    end

    preimage = function(a::Generic.Res)
      R = z.codomain
      parent(a) == R || throw("mixed rings in preimage")
      g = gens(domain)
      im_gen = map(x -> z(x), g) # apply x -> z(x) to the generatotrs ## possibly should be cached and stored
          ## need to write the elements in a matrix, solve the eqn for a
      Mt = zero_matrix(base_ring(base_ring(R)), degree(R.modulus), degree(R.modulus))

      for i=1:degree(R.modulus)
        elem_to_mat_row!(Mt, i, im_gen[i])
      end
      b = zero_matrix(base_ring(base_ring(R)), 1, degree(R.modulus))
      elem_to_mat_row!(b, 1, a)
      s = solve_rational(Mt', b') # why, oh why is solve operating on columns????
      # This is the worst
      if isa(s, Tuple) ## again, why, oh why is solve doing things differently
                   ## over rings than fields?
        s = s[1] * inv(s[2]) # all rings here (type) are actually fields (math)
      end

      s = sum([s[i,1]*g[i] for i=1:length(g)])

      @assert parent(s) == domain
      return s::elem_type(domain)
    end

    z.header = MapHeader(domain, codomain, image, preimage)
    return z
  end
end

function ResidueRingPolyMap(domain::D, codomain::C, i::Generic.Res{T}) where {D, C, T}
  return ResidueRingPolyMap{D, C, T}(domain, codomain, i)
end

function ResidueRingPolyMap(domain::D, codomain::C, i::Generic.Res{T}, coeff_map::Map) where {D, C, T}
  return ResidueRingPolyMap{D, C, T}(domain, codomain, i, coeff_map)
end

mutable struct CoerceMap{D, C} <: Map{D, C, HeckeMap, CoerceMap}
  header::MapHeader{D, C}

  function CoerceMap{D, C}(domain::D, codomain::C) where {D, C}
    z = new{D, C}()
    z.header = MapHeader(domain, codomain)
    return z
  end

  function CoerceMap(domain::Generic.ResRing{S}, codomain::Generic.ResRing{T}) where {S, T <: PolyElem}
    z = new{Generic.ResRing{S}, Generic.ResRing{T}}()

    image = function(a::Generic.Res)
      return codomain(a)::elem_type(codomain)
    end

    preimage = function(a::Generic.Res)
      while parent(a) != domain
        degree(a.data)>0 && throw("Element not in subfield")
        a = coeff(a.data, 0)
      end
      return a::elem_type(domain)
    end

    z.header = MapHeader(domain, codomain, image, preimage)
    return z
  end
end

function CoerceMap(domain::Generic.ResRing{fmpz}, codomain::FqNmodFiniteField)
  z = CoerceMap{Generic.ResRing{fmpz}, FqNmodFiniteField}()

  image = function(a::Generic.Res{fmpz})
      parent(a) != domain && error("Element not in domain")
      return codomain(fmpz(a))
  end

  preimage = function(a::fq_nmod)
    parent(a) != codomain && error("Element not in codomain")
    a.length > 1 && throw("Element not in image")
    return domain(coeff(a, 0))::Generic.Res{fmpz}
  end

  z.header = MapHeader(domain, codomain, image, preimage)
  return z
end

function CoerceMap(domain::FqNmodFiniteField, codomain::Generic.ResRing{fq_nmod_poly})
  z = CoerceMap{FqNmodFiniteField, Generic.ResRing{fq_nmod_poly}}()

  image = function(a::fq_nmod)
    parent(a) != domain && error("Element not in domain")
    return codomain(a)::Generic.Res{fq_nmod_poly}
  end

  preimage = function(a::Generic.Res{fq_nmod_poly})
    degree(a.data) > 0 && throw("Element not in subfield")
    return domain(coeff(a.data, 0))::fq_nmod
  end

  z.header = MapHeader(domain, codomain, image, preimage)
  return z
end



function CoerceMap(domain::D, codomain::C) where {D, C}
  return CoerceMap{D, C}(domain, codomain)
end

mutable struct GrpAbFinGenMap <: Map{GrpAbFinGen, GrpAbFinGen, HeckeMap, GrpAbFinGenMap}
  header::MapHeader{GrpAbFinGen, GrpAbFinGen}

  map::fmpz_mat
  imap::fmpz_mat
  im::GrpAbFinGen  # if set
  ke::GrpAbFinGen  # if set

  function GrpAbFinGenMap(G::GrpAbFinGen)
    r = new()

    function image(a::GrpAbFinGenElem)
      return a
    end

    function preimage(a::GrpAbFinGenElem)
      return a
    end

    r.header = MapHeader(G, G, image, preimage)
    r.map = identity_matrix(FlintZZ, ngens(G))
    return r
  end

  function GrpAbFinGenMap(From::GrpAbFinGen, To::GrpAbFinGen, M::fmpz_mat, check::Bool = false)
    r = new()

    function image(a::GrpAbFinGenElem)
      return GrpAbFinGenElem(To, a.coeff*M)
    end

    function preimage(a::GrpAbFinGenElem)
      error("preimage map missing")
    end

    r.header = MapHeader(From, To, image, preimage)
    r.map = M
    return r
  end

  function GrpAbFinGenMap(From::GrpAbFinGen, To::GrpAbFinGen, M::fmpz_mat, Mi::fmpz_mat)
    r = new()
    function image(a::GrpAbFinGenElem)
      return GrpAbFinGenElem(To, a.coeff*M)
    end

    function preimage(a::GrpAbFinGenElem)
      return GrpAbFinGenElem(From, a.coeff*Mi)
    end

    r.header = MapHeader(From, To, image, preimage)
    r.map = M
    r.imap = Mi
    return r
  end

end

###########################################################
# To turn a Function (method) into a map.
###########################################################
mutable struct MapFromFunc{R, T} <: Map{R, T, HeckeMap, MapFromFunc}
  header::Hecke.MapHeader{R, T}
  f::Function

  function MapFromFunc{R, T}(f::Function, D::R, C::T) where {R, T}
    n = new{R, T}()
    n.header = Hecke.MapHeader(D, C, x-> f(x))
    n.f = f
    return n
  end
end

function Base.show(io::IO, M::MapFromFunc)
  println(io, "Map from the $(M.f) julia-function")
end

function MapFromFunc(f::Function, D, C)
  return MapFromFunc{typeof(D), typeof(C)}(f, D, C)
end

export MapFromFunc
