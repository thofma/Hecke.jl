###########################################################
## 
## MAPS
##
## maps between residue rings of polynomials and in general
##
###########################################################

function domain(M::Map)
  return M.header.domain
end

function codomain(M::Map)
  return M.header.codomain
end

function image_function(f::Map)
  return f.header.image
end

function preimage_function(f::Map)
  return f.header.preimage
end

export Map, CoerceMap, ResidueRingPolyMap

type MapCache{D, C, De, Ce}
  lim::Int

  im::Dict{De, Ce}
  imStat::Dict{De, Int}

  pr::Dict{Ce, De} 
  prStat::Dict{Ce, Int}

  old_im::Function
  old_pr::Function

  function MapCache{D, C}(dom::D, cod::C, lim::Int = 100)
    r = new()
    r.lim = lim
    r.im = Dict{De, Ce}()
    r.imStat = Dict{De, Int}()
    r.pr = Dict{Ce, De}()
    r.prStat = Dict{Ce, Int}()
    return r
  end
end

type MapHeader{D, C}
  domain::D
  codomain::C
  image::Function
  preimage::Function
  cache::MapCache

  function MapHeader()
    z = new{D, C}()
    return z
  end

  function MapHeader(domain::D, codomain::C)
    z = new{D, C}()
    z.domain = domain
    z.codomain = codomain
    return z
  end

  function MapHeader(domain::D, codomain::C, image::Function)
    z = new{D, C}()
    z.domain = domain
    z.codomain = codomain
    z.image = image
    return z
  end

  function MapHeader(domain::D, codomain::C, image::Function, preimage::Function)
    z = new{D, C}()
    z.domain = domain
    z.codomain = codomain
    z.image = image
    z.preimage = preimage
    return z
  end
end

function MapHeader{D, C}(domain::D, codomain::C, image::Function)
  return MapHeader{D, C}(domain, codomain, image)
end

function MapHeader{D, C}(domain::D, codomain::C, image::Function, preimage::Function)
  return MapHeader{D, C}(domain, codomain, image, preimage)
end

# this type represents a -> f(g(a))
type CompositeMap{D, C, R} <: Map{D, C}
  header::MapHeader{D, C}
  f::Map{R, C}
  g::Map{D, R}

  function CompositeMap(f::Map, g::Map)
  ##CF should be function CompositeMap(f::Map{R, C}, g::Map{D, R})
  ## but that seems to not work:
  # U, m = UnitGroup(ResidueRing(ZZ, 2^9));
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

function *{D, C, R}(f::Map{R, C}, g::Map{D, R})
  return CompositeMap{D, C, R}(f, g)
end

function compose{D, C, R}(f::Map{R, C}, g::Map{D, R})
  return CompositeMap{D, C, R}(f, g)
end

function compose(f::Map, g::Map)
  return CompositeMap{typeof(domain(g)), typeof(codomain(f)), Any}(f, g)
end

type InverseMap{D, C} <: Map{D, C}
  header::MapHeader{D, C}
  origin::Map{C, D}

  function InverseMap(f::Map{C, D})
    z = new{D, C}()
    z.header = MapHeader(codomain(f), domain(f), preimage_function(f), image_function(f))
    z.origin = f
    return z
  end
end

function InverseMap{D, C}(f::Map{C, D})
  return InverseMap{D, C}(f)
end

type ResidueRingPolyMap{D, C, T} <: Map{D, C}
  header::MapHeader{D, C}
  gen_image::GenRes{T}
  coeff_map::Map # can be missing if domain and codomain have the same
                 # base_ring(base_ring())
  function ResidueRingPolyMap(domain::D, codomain::C, gen_image::GenRes{T}, coeff_map::Map)
    z = new{D, C, T}()
    z.gen_image = gen_image
    z.coeff_map = coeff_map

    image = function(a::GenRes)
      #a should be in the domain of M...
      I = codomain(0)
      for i in degree(a.data):-1:0
        I = I*z.gen_image + z.coeff_map(coeff(a.data, i))
      end
      return I::elem_type(C)
    end
    
    # I need to call preimage in _preimage
    _preimage = function(a::GenRes)
      R = codomain
      parent(a) == R || throw("mixed rings in preimage")
      g = gens(domain)
      im_gen = map(z, g) # apply x -> z(x) to the generatotrs ## possibly should be cached and stored
          ## need to write the elements in a matrix, solve the eqn for a
      Mt = MatrixSpace(base_ring(base_ring(R)), degree(R.modulus), degree(R.modulus))()

      for i=1:degree(R.modulus)
        elem_to_mat_row!(Mt, i, im_gen[i])
      end
      b = MatrixSpace(base_ring(base_ring(R)), 1, degree(R.modulus))()
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

  function ResidueRingPolyMap(domain::D, codomain::C, gen_image::GenRes{T})
    z = new{D, C, T}()
    z.gen_image = gen_image

    image = function(a::GenRes)
      I = z.codomain(0)
      for i in degree(a.data):-1:0
        I = I*z.gen_image + coeff(a.data, i)
      end
      return I::elem_type(C)
    end

    preimage = function(a::GenRes)
      R = z.codomain
      parent(a) == R || throw("mixed rings in preimage")
      g = gens(domain)
      im_gen = map(x -> z(x), g) # apply x -> z(x) to the generatotrs ## possibly should be cached and stored
          ## need to write the elements in a matrix, solve the eqn for a
      Mt = MatrixSpace(base_ring(base_ring(R)), degree(R.modulus), degree(R.modulus))()

      for i=1:degree(R.modulus)
        elem_to_mat_row!(Mt, i, im_gen[i])
      end
      b = MatrixSpace(base_ring(base_ring(R)), 1, degree(R.modulus))()
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

function ResidueRingPolyMap{D, C, T}(domain::D, codomain::C, i::GenRes{T})
  return ResidueRingPolyMap{D, C, T}(domain, codomain, i)
end

function ResidueRingPolyMap{D, C, T}(domain::D, codomain::C, i::GenRes{T}, coeff_map::Map)
  return ResidueRingPolyMap{D, C, T}(domain, codomain, i, coeff_map)
end

type IdentityMap{D} <: Map{D, D}
  header::MapHeader{D, D}

  function IdentityMap(domain::D)
    z = new{D}()

    image = function(x)# (x::elem_type(D))
      return x::elem_type(D)
    end
    preimage = image

    z.header = MapHeader(domain, domain, image, preimage)
    return z
  end
end

function IdentityMap{D}(domain::D)
  return IdentityMap{D}(domain)
end

type CoerceMap{D, C} <: Map{D, C}
  header::MapHeader{D, C}

  function CoerceMap(domain::D, codomain::C)
    z = new{D, C}()
    z.header = MapHeader(domain, codomain)
    return z
  end

  function CoerceMap(domain::GenResRing{fmpz}, codomain::FqNmodFiniteField)
    z = new{GenResRing{fmpz}, FqNmodFiniteField}()

    image = function(a::GenRes{fmpz})
        parent(a) != domain && error("Element not in domain")
        return codomain(ZZ(a))
    end

    preimage = function(a::fq_nmod)
      parent(a) != codomain && error("Element not in codomain")
      a.length > 1 && throw("Element not in image")
      return domain(coeff(a, 0))::GenRes{fmpz}
    end

    z.header = MapHeader(domain, codomain, image, preimage)
    return z
  end

  function CoerceMap(domain::FqNmodFiniteField, codomain::GenResRing{fq_nmod_poly})
    z = new{FqNmodFiniteField, GenResRing{fq_nmod_poly}}()

    image = function(a::fq_nmod)
      parent(a) != domain && error("Element not in domain")
      return codomain(a)::GenRes{fq_nmod_poly}
    end

    preimage = function(a::GenRes{fq_nmod_poly})
      degree(a.data) > 0 && throw("Element not in subfield")
      return domain(coeff(a.data, 0))::fq_nmod
    end

    z.header = MapHeader(domain, codomain, image, preimage)
    return z
  end

  function CoerceMap{S, T <: PolyElem}(domain::GenResRing{S}, codomain::GenResRing{T})
    z = new{GenResRing{S}, GenResRing{T}}()

    image = function(a::GenRes)
      return codomain(a)::elem_type(codomain)
    end

    preimage = function(a::GenRes)
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

function CoerceMap{D, C}(domain::D, codomain::C)
  return CoerceMap{D, C}(domain, codomain)
end

type GrpAbFinGenMap <: Map{GrpAbFinGen, GrpAbFinGen}
  header::MapHeader{GrpAbFinGen, GrpAbFinGen}

  map::fmpz_mat
  imap::fmpz_mat
  im::GrpAbFinGen  # if set
  ke::GrpAbFinGen  # if set

  function GrpAbFinGenMap(From::GrpAbFinGen, To::GrpAbFinGen, M::fmpz_mat)
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
type MapFromFunc{R, T} <: Map{R, T}
  header::Hecke.MapHeader{R, T}
  f::Function
  function MapFromFunc(f::Function, D::R, C::T)
    n = new()
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
