###########################################################
## 
## MAPS
##
## maps between residue rings of polynomials and in general
##
###########################################################

export Map, CoerceMap, ResidueRingPolyMap

abstract Map

type MapHeader
  domain::Any
  codomain::Any
  preim:: Function
  image:: Function
  function MapHeader(a::Any, b::Any)
    r = new()
    r.domain = a
    r.codomain = b
    return a
  end
  function MapHeader(a::Any, b::Any, i::Function, p::Function)
    r = new()
    r.domain = a
    r.codomain = b
    r.image = i
    r.preim = p
    return r
  end
end


type CompositeMap <: Map
  header::MapHeader
  a::Map
  b::Map
  function CompositeMap(a::Map, b::Map)
    codomain(a) == domain(b) || throw("maps not compatible")
    r = new()
    r.a = a
    r.b = b
    image = function(M::Map, a::Any)
      return M.a(M.b(a))
    end
    preim = function(M::Map, a::Any)
      return preimage(M.b, preimage(M.a, a))
    end
    r.header = MapHeader(a.domain, b.codomain, image, preim)
    return r
  end
end


type InverseMap <: Map
  header::MapHeader
  a::Map
  function InverseMap(a::Map)
    r = new()
    r.a = a
    image = function(M::Map, a::Any)
      return preimage(M.a, a)
    end
    preim = function(M::Map, a::Any)
      return image(M.a, a)
    end
    r.header = MapHeader(a.codomain, a.domain, image, preim)
    return r
  end
end

type ResidueRingPolyMap <: Map
  header::MapHeader
  gen_image::Residue
  coeff_map::Map # can be missing if domain and codomain have the same
                 # base_ring(base_ring())
  function ResidueRingPolyMap(d::ResidueRing, c::ResidueRing, i::Residue)
    r = new()
    r.header = MapHeader(d, c, ResidueRingPolyMap_image, 
                               ResidueRingPolyMap_preimage)
    r.gen_image = i
    return r
  end
end

type CoerceMap <:Map
  header::MapHeader
  function CoerceMap(d::Nemo.Ring, c::Nemo.Ring)
    r = new()
    r.header = MapHeader(d, c)
    return r
  end
  function CoerceMap(d::ResidueRing{fmpz}, c::FqNmodFiniteField)
    r = new()
    image = function(M::Map, a::Residue{fmpz})
      return c(ZZ(a))
    end
    preim = function(M::Map, a::fq_nmod)
      a.length >1 && throw("not in image")
      return domain(M)(coeff(a,0))
    end
    r.header = MapHeader(d, c, image, preim)
    return r
  end
  function CoerceMap(d::FqNmodFiniteField, c::ResidueRing{fq_nmod_poly})
    r = new()
    image = function(M::Map, a::fq_nmod)
      return c(a)
    end
    preim = function(M::Map, a::Residue{fq_nmod_poly})
      degree(a.data) > 0 && throw("not in subfield")
      return domain(M)(coeff(a.data, 0))
    end
    r.header = MapHeader(d, c, image, preim)
    return r
  end
  function CoerceMap{T <: Poly}(d::ResidueRing, c::ResidueRing{T})
    r = new()
    image = function(M::Map, a::Residue)
      return c(a)
    end
    preim = function(M::Map, a::Residue)
      while parent(a) != domain(M)
        degree(a.data)>0 && throw("not in subfield")
        a = coeff(a.data, 0)
      end
      return a
    end
    r.header = MapHeader(d, c, image, preim)
    return r
  end
end

