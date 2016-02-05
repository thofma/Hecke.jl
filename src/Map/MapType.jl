###########################################################
## 
## MAPS
##
## maps between residue rings of polynomials and in general
##
###########################################################

export Map, CoerceMap, ResidueRingPolyMap

abstract Map{D, C}

type MapHeader{D, C}
  domain::D
  codomain::C
  preim::Function
  image::Function

  function MapHeader(a::D, b::C)
    r = new{D, C}()
    r.domain = a
    r.codomain = b
    return r
  end

  function MapHeader(a::D, b::C, i::Function, p::Function)
    r = new{D, C}()
    r.domain = a
    r.codomain = b
    r.image = i
    r.preim = p
    return r
  end
end


type CompositeMap{D, C} <: Map{D, C}
  header::MapHeader{D, C}
  a::Map
  b::Map

  function CompositeMap{R}(a::Map{D, R}, b::Map{R, C})
    codomain(a) == domain(b) || throw("maps not compatible")
    r = new{D, C}()
    r.a = a
    r.b = b

    image = function(M::Map, a::Any)
      return M.a(M.b(a))
    end

    preim = function(M::Map, a::Any)
      return preimage(M.b, preimage(M.a, a))
    end

    r.header = MapHeader{D, C}(a.domain, b.codomain, image, preim)
    return r
  end
end


type InverseMap{D, C} <: Map{D, C}
  header::MapHeader{D, C}
  a::Map

  function InverseMap(a::Map{C, D})
    r = new{D, C}()
    r.a = a
    image = function(M::Map, a::Any)
      return preimage(M.a, a)
    end
    preim = function(M::Map, a::Any)
      return image(M.a, a)
    end
    r.header = MapHeader{D, C}(a.codomain, a.domain, image, preim)
    return r
  end
end

type ResidueRingPolyMap{D, C} <: Map{D, C}
  header::MapHeader{D, C}
  gen_image::Residue
  coeff_map::Map # can be missing if domain and codomain have the same
                 # base_ring(base_ring())
  function ResidueRingPolyMap(d::D, c::C, i::Residue)
    r = new()
    r.header = MapHeader{D, C}(d, c, ResidueRingPolyMap_image, 
                               ResidueRingPolyMap_preimage)
    r.gen_image = i
    return r
  end
end

function ResidueRingPolyMap{D, C}(d::D, c::C, i::Residue)
  return ResidueRingPolyMap{D, C}(d::D, c::C, i::Residue)
end

type IdentityMap{D} <: Map{D, D}
  header::MapHeader{D, D}

  function IdentityMap(d::D)
    r = new()
    i = function(M::Map{D, D}, x::elem_type(d))
      return x
    end
    r.header = MapHeader{D, D}(d, d, i, i)
    return r
  end

end

type CoerceMap{D, C} <: Map{D, C}
  header::MapHeader{D, C}

  function CoerceMap(d::D, c::C)
    r = new()
    r.header = MapHeader{D, C}(d, c)
    return r
  end

  function CoerceMap(d::ResidueRing{fmpz}, c::FqNmodFiniteField)
    r = new{ResidueRing{fmpz}, FqNmodFiniteField}()
    image = function(M::Map, a::Residue{fmpz})
      return c(ZZ(a))
    end
    preim = function(M::Map, a::fq_nmod)
      a.length >1 && throw("not in image")
      return domain(M)(coeff(a,0))
    end
    r.header = MapHeader{ResidueRing{fmpz}, FqNmodFiniteField}(d, c, image, preim)
    return r
  end

  function CoerceMap(d::FqNmodFiniteField, c::ResidueRing{fq_nmod_poly})
    r = new{FqNmodFiniteField, ResidueRing{fq_nmod_poly}}()
    image = function(M::Map, a::fq_nmod)
      return c(a)
    end
    preim = function(M::Map, a::Residue{fq_nmod_poly})
      degree(a.data) > 0 && throw("not in subfield")
      return domain(M)(coeff(a.data, 0))
    end
    r.header = MapHeader{FqNmodFiniteField, ResidueRing{fq_nmod_poly}}(d, c, image, preim)
    return r
  end

  function CoerceMap{S, T <: Poly}(d::ResidueRing{S}, c::ResidueRing{T})
    r = new{ResidueRing{S}, ResidueRing{T}}()
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
    r.header = MapHeader{ResidueRing{S}, ResidueRing{T}}(d, c, image, preim)
    return r
  end
end

function CoerceMap{D, C}(d::D, c::C)
  return CoerceMap{D, C}(d, c)
end
